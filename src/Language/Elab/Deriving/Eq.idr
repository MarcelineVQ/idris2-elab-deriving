module Language.Elab.Deriving.Eq

-- Public: Things here we actually use in deriving Eq need to be re-exported to
-- be available at the deriving use-site. A little odd but that's how it is.
-- Otherwise you get extremely vague "Can't reify as X" errors and chances are
-- you don't have an FC to track it down.

import public Language.Elab.Syntax
import public Language.Elab.Types

import public Util
import public Language.Elab.Deriving.Util

import public Language.Reflection


{-
interesting case, happens to work for Show already!
data TagField : Type where
  TF : Eq a => Show a => (name : String) -> (value : a) -> TagField
-}

-- A regular instance might look like (Eq a, Eq b, Eq c) => ...
-- This pairing isn't actually neccesary, it's just notational convenience and
-- we don't really have a reason to emulate it.
-- Eq a => Eq b => ...  is just as valid as (Eq a, Eq b) => ...
-- It also can result in clearer errors.
addEqAutoImps : List String -> TTImp -> TTImp
addEqAutoImps xs retty
  = foldr (\arg,tt => `(Eq ~(iBindVar arg) => ~(tt))) retty xs

-- I want better names here, including better index names
-- e.g we have this now
{-
Language.Elab.Deriving.Eq.eqImplFoo6'Fun : Eq arg6281 => Eq arg6282
  => Eq arg6283 => Foo6' arg6281 arg6282 arg6283 arg6284
    -> Foo6' arg6281 arg6282 arg6283 arg6284 -> Bool
-}

||| e.g. (==) : Foo a b -> Foo a b -> Bool
eqClaim : (opname : Name) -> TypeInfo -> Visibility -> Elab Decl
eqClaim op tyinfo vis = do
  let conargs = pullExplicits tyinfo
      varnames = map (show . name) conargs
      params = map (extractNameStr . name) $ filter (not . isIndex) conargs
      tysig = `(~(tyinfo.type) -> ~(tyinfo.type) -> Bool)
      tysig' = addEqAutoImps params tysig
  logMsg "eqClaim" 1 $ ("auto params: ") ++ show params
  logTerm "eqClaimTySig" 1 "" tysig'
  -- NB: I can't think of a reason not to Inline here
  pure $ iClaim MW vis [Inline] (mkTy op tysig')

eqCon : (opname : Name) -> (Name, List ArgInfo, TTImp) -> Elab Clause
eqCon op (conname, args, contype) = do
    let vars = filter (isExplicitPi . piInfo) args
        pats = makePatNames vars infVars
        lhs = iVar op `iApp` (makePat conname (map (map fst) pats)) `iApp` (makePat conname (map (map snd) pats))
        rhs = makeRhs (catMaybes pats)
    logTerm "eqconlhs" 1 "" lhs
    logTerm "eqconrhs" 1 "" rhs
    pure $ patClause lhs rhs 
  where
    -- Make our pat names, we use Just to flag the vars we want to use, we don't
    -- compare indices since they're vacuously the same for the Eq interface.
    -- It doesn't seem to matter if an index is M1 or not.
    makePatNames : List ArgInfo
               -> Stream String -> (List (Maybe (Name,Name)))
    makePatNames [] vs = []
    makePatNames (a :: as) (v :: vs)
      =  
       let xs = makePatNames as vs
           basicname = UN v
       in if isUse0 a.count || a.isIndex
          then Nothing :: xs
          else Just ((mapName (++ "_1") basicname), (mapName (++ "_2") basicname)) :: xs

    -- The lhs of our function, fields we don't want to use are replaced with _
    makePat : (con : Name) -> (vars : List (Maybe Name)) -> TTImp
    makePat con vars = foldl
      (\tt,v => `(~(tt) ~(maybe implicit' bindNameVar v))) (iVar con) vars

    -- A little wordy here, it's set up this way instead of a fold to avoid an
    -- extra True when building up our && chain. There's no reason to make the
    -- user repeat work every time they use their derived implementation.
    makeRhs : List (Name,Name) -> TTImp
    makeRhs [] = `(True)
    makeRhs [(x,y)] = `( ~(iVar x) == ~(iVar y) )
    makeRhs ((x,y) :: xs) = `( ~(iVar x) == ~(iVar y) && ~(makeRhs xs) )


||| The record that idris would make for you when you write an implementation.
eqObject : (decname : Name) -> (funname : Name) -> TypeInfo
          -> Visibility -> Elab (Decl, Decl)
eqObject decname eqfun tyinfo vis = do
  (qname,_) <- lookupName `{{Eq}}
  [NS _ (DN _ eqcon)] <- getCons qname
    | _ => fail "eqObject: error during Eq constructor lookup"
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
||| Usage: %runElab deriveEq Export `{{Foo}}
||| Currently, this adds eqImplFoo and eqImpltFooFun to the module namespace.
||| This is likely to change in the future to only have eqImplFoo being added
||| to the namespace.
deriveEq : Visibility -> Name -> Elab ()
deriveEq vis eqname = do
    (qname,_) <- lookupName eqname -- get the qualified name of our type
    -- create human readable names for our instance components
    let decn = mapName (\d => "eqImpl" ++ d) eqname
        funn = mapName (\d => "eqImpl" ++ d ++ "Fun") eqname
    -- Build general info about the type we're deriving (e.g. Foo) that we want
    -- to keep around.
    tyinfo <- makeTypeInfo qname

    -- The components of our eq-ing function
    funclaim <- eqClaim funn tyinfo Private -- NB private
    funclauses <- traverse (eqCon funn) tyinfo.cons

    -- Our function's complete definition
    let catchall = patClause `(~(iVar funn) ~implicit' ~implicit') `(False)
        fundecl = iDef funn (funclauses ++ [catchall])

    -- The actual eqImplFoo : Eq Foo record.
    (objclaim,objclause) <- eqObject decn funn tyinfo vis

    -- Declare our things into the namespace
    -- Both claims first, otherwise we won't find our own Eq in fundecl
    declare [funclaim, objclaim]
    declare [fundecl, objclause]

data Flippy = Dolphin | Shark

%language ElabReflection
%logging 1
%runElab deriveEq Export  `{{Flippy}}
  
