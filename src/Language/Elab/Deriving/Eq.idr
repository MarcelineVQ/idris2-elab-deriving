module Language.Elab.Deriving.Eq

import Language.Elab.Syntax
import Language.Elab.Types

import Util
import Language.Elab.Deriving.Util

import Language.Reflection
import Data.Strings -- fastAppend

-- A regular isntance might look like (Eq a, Eq b, Eq c) => ...
-- This pairing isn't actually neccesary, it's just notational convenience and
-- we don't really have a reason to emulate it.
-- Eq a => Eq b => ...  is just as valid as (Eq a, Eq b) => ...
-- It also can result in clearer errors.
addEqAutoImps : List String -> TTImp -> TTImp
addEqAutoImps xs retty
  = foldr (\arg,tt => `(Eq ~(iBindVar arg) => ~(tt))) retty xs

eqClaim : (opname : Name) -> TypeInfo -> Visibility -> Elab Decl
eqClaim op tyinfo vis = do
  let conargs = pullExplicits tyinfo
      varnames = map (show . name) conargs
      params = map (extractNameStr . name) $ filter (not . isIndex) conargs
      tysig = `(~(tyinfo.type) -> ~(tyinfo.type) -> Bool)
  logMsg 1 $ ("auto params: ") ++ show params
  -- NB: I can't think of a reason not to Inline here
  pure $ iClaim MW vis [Inline] (mkTy op (addEqAutoImps params tysig))

eqCon : (opname : Name) -> (Name, List ArgInfo, TTImp) -> Elab Clause
eqCon op (conname, args, contype) = do
    let vars = filter (isExplicitPi . piInfo) args
        (pats1, pats2) = makePatNames vars infVars
        lhs = iVar op `iApp` makePat conname pats1 `iApp` makePat conname pats2
        rhs = makeRhs (zip (catMaybes pats1) (catMaybes pats2))
        rhs2 = `(True)
    pure $ patClause lhs rhs
  where
    -- Make our pat names, we use Just to flag the vars we want to use, we used
    -- leave indices alone since they need to share their name.
    makePatNames : List ArgInfo
               -> Stream String -> (List (Maybe Name), List (Maybe Name))
    makePatNames [] vs = ([],[])
    makePatNames (a :: as) (v :: vs)
      = let (xs,ys) = makePatNames as vs
            basicname = UN v
        in case (isUse0 a.count, a.isIndex) of
             (True,_) => (Nothing :: xs, Nothing :: ys)
             (_,True) => (Just basicname :: xs, Just basicname :: ys)
             (_,False) =>
               (Just (mapName (++ "_1") basicname) :: xs
               ,Just (mapName (++ "_2") basicname) :: ys)

    makePat : (con : Name) -> (vars : List (Maybe Name)) -> TTImp
    makePat con vars = foldl (\tt,v => `(~(tt) ~(plugArg v))) (iVar con) vars
      where
        plugArg : Maybe Name -> TTImp
        plugArg Nothing = implicit'
        plugArg (Just arg) = bindNameVar arg

    -- A little wordy here, it's set up this way to avoid an extra True when
    -- building up our && chain
    makeRhs : List (Name,Name) -> TTImp
    makeRhs [] = `(True)
    makeRhs [(x,y)] = `( ~(iVar x) == ~(iVar y) )
    makeRhs ((x,y) :: xs) =
        `( ~(iVar x) == ~(iVar y)
             && ~(makeRhs xs) )

||| The record that idris would make for you when you write an implementation.
eqObject : (decname : Name) -> (funname : Name) -> TypeInfo
          -> Visibility -> Elab (Decl, Decl)
eqObject decname eqfun tyinfo vis = do
  (qname,_) <- lookupName `{{Eq}}
  [NS _ (DN _ eqcon)] <- getCons qname
    | _ => fail "showObject: error during Show constructor lookup"
  let conargs = pullExplicits tyinfo
      varnames = map (show . name) conargs
      varnames' = map (show . name) (filter (not . isIndex) conargs)
      retty = `( Eq ~(appTyCon (map (show . name) conargs)  tyinfo.name))
      tysig = addEqAutoImps varnames' retty
      claim = iClaim MW vis [Hint True] (mkTy decname tysig)
      neqfun = `(\x,y => not (x == y))
      rhs = `( ~(iVar eqcon) ~(iVar eqfun) ~(neqfun))
      body = iDef decname [(patClause (iVar decname) rhs)]
  pure $ (claim,body)


export
deriveEq : Visibility -> Name -> Elab ()
deriveEq vis sname = do
    (qname,_) <- lookupName sname -- get the qualified name of our type
    -- create human readable names for our instance components
    let decn = mapName (\d => "eqImpl" ++ d) sname
        funn = mapName (\d => "eqImpl" ++ d ++ "Fun") sname
    -- Build general info about the type we're deriving (e.g. Foo) that we want
    -- to keep around.
    tyinfo <- makeTypeInfo qname
    
    -- Our components for our showing function
    funclaim <- eqClaim funn tyinfo Private -- NB private
    funclauses <- traverseE (eqCon funn) tyinfo.cons
    
    -- Our function's complete definition
    let catchall = patClause
          `(~(iVar funn) ~(implicit') ~(implicit'))
          `(False)
        fundecl = IDef EmptyFC funn (funclauses ++ [catchall])
    
    -- TODO check if an instance exists already and abort if so
    
    -- The actual showFoo : Show Foo instance.
    (objclaim,objclause) <- eqObject decn funn tyinfo vis
    -- Place our things into the namespace
    -- Both claims first, otherwise we won't be able to find our own Show
    declare [funclaim, objclaim]
    declare [fundecl, objclause]
