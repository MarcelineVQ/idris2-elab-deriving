module Language.Elab.Deriving.DecEq

-- Public: Things here we actually use in deriving DecEq need to be re-exported to
-- be available at the deriving use-site. A little odd but that's how it is.
-- Otherwise you get extremely vague "Can't reify as X" errors and chances are
-- you don't have an FC to track it down.

import public Language.Elab.Syntax
import public Language.Elab.Types

import public Util
import public Language.Elab.Deriving.Util

import public Language.Reflection

import Decidable.Equality


{-
interesting case, happens to work for Show already!
data TagField : Type where
  TF : DecEq a => Show a => (name : String) -> (value : a) -> TagField
-}

-- A regular instance might look like (DecEq a, DecEq b, DecEq c) => ...
-- This pairing isn't actually neccesary, it's just notational convenience and
-- we don't really have a reason to emulate it.
-- DecEq a => DecEq b => ...  is just as valid as (DecEq a, DecEq b) => ...
-- It also can result in clearer errors.
addDecEqAutoImps : List String -> TTImp -> TTImp
addDecEqAutoImps xs retty
  = foldr (\arg,tt => `(DecEq ~(iBindVar arg) => ~(tt))) retty xs

-- I want better names here, including better index names
-- e.g we have this now
{-
Language.Elab.Deriving.DecEq.decEqImplFoo6'Fun : DecEq arg6281 => DecEq arg6282
  => DecEq arg6283 => Foo6' arg6281 arg6282 arg6283 arg6284
    -> Foo6' arg6281 arg6282 arg6283 arg6284 -> Bool
-}

||| e.g. decEq : Foo a b -> Foo a b -> Bool
decEqClaim : (opname : Name) -> TypeInfo -> Visibility -> Elab Decl
decEqClaim op tyinfo vis = do
  let conargs = pullExplicits tyinfo
      varnames = map (show . name) conargs
      params = map (extractNameStr . name) $ filter (not . isIndex) conargs
      tysig = `((x1 : ~(tyinfo.type)) -> (x2 : ~(tyinfo.type)) -> Dec (x1 = x2))
      tysig' = addDecEqAutoImps params tysig
  logMsg "decEqClaim" 1 $ (show op) ++ (", auto params: ") ++ show params
  logTerm "decEqClaimTySig" 1 "" tysig'
  -- NB: I can't think of a reason not to Inline here
  pure $ iClaim MW vis [Inline] (mkTy op tysig')
 
-- creates a TTImp that is used for the left hand side. Uses arginfo to determine if should be implicit or explicit
lhsApp : ArgInfo -> TTImp -> TTImp -> TTImp
lhsApp ai caller callee = 
       if isImplicitPi (ai.piInfo) 
       then iNamedApp caller ai.name callee
       else iApp caller callee
          
decEqSameCon : 
               (funName : Name) -- Name of the function being constructed
               -> (conName : Name) -- Name of the constructor
               -> (argInfos : List ArgInfo) 
               -> Elab Clause
decEqSameCon funName conName argInfos = 
    let -- for decidable equality, every argument must match (besides indexes) or we can't prove it
      lp = makeLhsPat True
      rp = makeLhsPat False
      lhs = makeLhs lp rp
      rhs = makeRhs lp rp
    in
      do 
         logTerm "decEqSameConLhs" 1 "" lhs
         logTerm "decEqSameConRhs" 1 "" rhs
         --logTerm "decEqSameCon" 1 "" lp
         --pure $ patClause lhs `(believe_me) --rhs
         pure $ patClause lhs rhs --(IHole EmptyFC ("samecon" ++ show conname))
         --pure $ patClause lhs (IHole EmptyFC "samecon") --rhs  FIXME
  where
    lVarName : Int -> Name
    lVarName index = UN $ "l" ++ show index
    rVarName : Int -> Name
    rVarName index = UN $ "r" ++ show index
    prfVarName : Int -> Name
    prfVarName index = UN $ "prf" ++ show index

    isArgIndexList : List Bool
    isArgIndexList = map isIndex argInfos
       
    -- ^ List of whether each argument of the constructor are indexes, in order of the
    --   args as applied to the constructor.
    --   "index" means args that are part of the resulting type, and therefore don't need to be proved
    --   to be equal for the objects to be proven equal
    makeLhsPat : Bool -> TTImp
    makeLhsPat isLeftArg = makeLhsPatHelper (iVar conName) argInfos (rangeFrom 1)
      where
        makeLhsPatHelper : TTImp -> List ArgInfo -> Stream Int -> TTImp
        makeLhsPatHelper innerRes [] _ = innerRes 
        makeLhsPatHelper innerRes (ai :: ais) cl@(ctr :: remcl) = 
          case isIndex ai of
            True => 
               let res = lhsApp ai innerRes implicit'
               in makeLhsPatHelper res ais cl
               -- ^ regarding vbns: we don't take from the counter stream
               --   Since rhs only uses non-index variables, this way, the var counter
               --   won't skip a value for them
            False =>
              let res = lhsApp ai innerRes (iVar $ (if isLeftArg then lVarName ctr else rVarName ctr))
              in makeLhsPatHelper res ais remcl
     
    makeLhs : TTImp -> TTImp -> TTImp
    makeLhs lp rp =
      iApp (iApp (iVar funName) lp) rp
    
    makeRhs : TTImp -> TTImp -> TTImp 
    makeRhs lp rp = makeRhsHelper nonIndexVars -- we only deal with the non-index vars
      where
        nonIndexVarCount : Int
        nonIndexVarCount = cast $ length (filter not isArgIndexList)
        nonIndexVars : List Int
        nonIndexVars = if nonIndexVarCount == 0 then [] else [1..nonIndexVarCount]
        makeNoPrf : (v1 : Name) -> (v2 : Name) -> TTImp
        makeNoPrf v1 v2 =  
          let 
             --all vars on the left and on the right
             allNonIndexVarNames : List Name
             allNonIndexVarNames =
               (map lVarName nonIndexVars) ++ (map rVarName nonIndexVars)
             -- applyCon : Name -> List Name -> TTImp
             -- applyCon con xs = foldl iApp con (map iVar xs)
             foldrFun : Name -> TTImp -> TTImp
             foldrFun otr inner = IPi EmptyFC MW ImplicitArg (Just otr) implicit' inner
             makeNoPrfType : TTImp
             makeNoPrfType = 
               --this outer fold is to imply as implicit all the vars used by the proof
               --for some reason, idris gets confused if we don't do this
               foldr foldrFun
                     `((~lp = ~rp) -> (~(iVar v1) === ~(iVar v2)))
                     allNonIndexVarNames
          in 
            `(let objEqVarEqPrf : ~makeNoPrfType
            --`(let objEqVarEqPrf : (~(iVar v1) = ~(iVar v2)) -> (~(iVar v1) = (~(iVar v2)))
                  objEqVarEqPrf Refl = Refl
                  -- ^ prf that if two objects are equal
                  -- then the var we're dealing with is equal
              in 
                  --contra returns void if v1 = v2
                  --since if first object(o1) = second object(o2), then all its vars must be 
                  --equal. So if o1 = o2 then v1 = v2, and contra returns void, so
                  --therefore o1 = o2 implies void and must be false
                  No $ contra . objEqVarEqPrf
            )
        makeYesPrf : TTImp
        makeYesPrf = foldr (\prf,accPrf => `(rewrite (sym ~(prf)) in ~(accPrf))) `(Refl) 
                        (map (iVar . prfVarName) nonIndexVars )
        makeRhsHelper : List Int -> TTImp
        makeRhsHelper [] = `(Yes Refl)
        makeRhsHelper (index :: indexes) =
          let v1 = lVarName index
              v2 = rVarName index
              yp = prfVarName index
          in 
            iCase `(decEq ~(iVar v1) ~(iVar v2)) `(Dec (_ = _))
                  [patClause `(No contra) (makeNoPrf v1 v2),
                   patClause `(Yes ~(iVar yp)) 
                                   (case indexes of
                                      Nil => `(Yes ~(makeYesPrf))
                                      _ => makeRhsHelper indexes)
                  ]


decEqDiffCon : (opname : Name) -> Constructor -> Constructor -> Elab Clause
decEqDiffCon op con1 con2 =
  do
    sym1 <- readableGenSym "a"
    sym2 <- readableGenSym "b"
    logMsg "decEqCA1" 1 (show con1.args)
    logMsg "decEqCA2" 1 (show con1.args)
    (let
        pat1 = makePat con1.name sym1 con1.args
        pat2 = makePat con2.name sym2 con2.args
        lhs = iVar op `iApp` pat1 `iApp` pat2
        rhs = makeRhs sym1 sym2
     in 
      do
        --logTerm "decEqDiffCon" 1 "" rhs
        pure $ patClause lhs rhs --(IHole EmptyFC ("diffcon" ++ show cn1 ++ show cn2))
     )
  where
    -- The lhs of our function, fields we don't use are replaced with _
    makePat : (con : Name) -> (sym : Name) -> (List ArgInfo) -> TTImp
    makePat con sym argInfos = iAs sym 
        (foldl (\tt,ai => lhsApp ai tt implicit') (iVar con) argInfos)
    makeRhs : (sym1 : Name) -> (sym2 : Name) -> TTImp
    makeRhs s1 s2 = `( No (\case Refl impossible))


||| The record that idris would make for you when you write an implementation.
decEqObject : (decname : Name) -> (funname : Name) -> TypeInfo
          -> Visibility -> Elab (Decl, Decl)
decEqObject decname decEqfun tyinfo vis = do
  (qname,_) <- lookupName `{{DecEq}}
  [NS _ (DN _ decEqcon)] <- getCons qname
    | _ => fail "decEqObject: error during DecEq constructor lookup"
  let conargs = pullExplicits tyinfo
      varnames = map (show . name) conargs
      varnames' = map (show . name) (filter (not . isIndex) conargs)
      retty = `( DecEq ~(appTyCon (map (show . name) conargs)  tyinfo.name))
      tysig = addDecEqAutoImps varnames' retty
      claim = iClaim MW vis [Hint True] (mkTy decname tysig)
      rhs = `( ~(iVar decEqcon) ~(iVar decEqfun))
      body = iDef decname [(patClause (iVar decname) rhs)]
  pure $ (claim,body)


export
||| Usage: %runElab deriveEq Export `{{Foo}}
||| Currently, this adds decEqImplFoo (a function that returns the "interface" data object and marks itself
||| as with hint on, and decEqImpltFooFun which actually implements decEq.
||| This is likely to change in the future to only have decEqImplFoo being added
||| to the namespace.
deriveDecEq : Visibility -> Name -> Elab ()
deriveDecEq vis decEqname = do
    (qname,_) <- lookupName decEqname -- get the qualified name of our type
    -- create human readable names for our instance components
    let decn = mapName (\d => "decEqImpl" ++ d) decEqname
        funn = mapName (\d => "decEqImpl" ++ d ++ "Fun") decEqname
    -- Build general info about the type we're deriving (e.g. Foo) that we want
    -- to keep around.
    tyinfo <- makeTypeInfo qname

    -- The components of our decEq-ing function
    funclaim <- decEqClaim funn tyinfo Private -- NB private
    
    traverse (\con =>
      do
        logMsg "deriveDecEq" 1 $ "con name : " ++ show con.name
        logMsg "deriveDecEq" 1 $ "con list args: " ++ show con.args
        logTerm "deriveDecEq" 1 "contype: " con.type
      ) tyinfo.cons
        
    funSameClauses <- traverse (\con => decEqSameCon funn con.name con.args) tyinfo.cons
    let diffCons = filter (not . isSameCons) [ (a,b) | a <- tyinfo.cons, b <- tyinfo.cons ]
    funDiffClauses <- traverse (uncurry $ decEqDiffCon funn) diffCons
  

    -- Our function's complete definition
    let fundecl = iDef funn (funSameClauses ++ funDiffClauses)

    -- The actual decEqImplFoo : DecEq Foo record.
    (objclaim,objclause) <- decEqObject decn funn tyinfo vis

    -- Declare our things into the namespace
    -- Both claims first, otherwise we won't find our own DecEq in fundecl
    declare [funclaim, objclaim]
    declare [fundecl, objclause]
 where
   isSameCons : (Constructor, Constructor) -> Bool
   isSameCons (con1, con2) = con1.name == con2.name
   
