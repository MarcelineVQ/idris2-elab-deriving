module Language.Elab.Deriving.Show

import Language.Elab.Syntax
import Language.Reflection

import Data.Strings -- intercalate

%language ElabReflection -- you can remove this once %runElab is no longer used in this module

-- derive show

intercalate_str : String -> List String -> String
intercalate_str sep ss = fastAppend (intersperse sep ss)

-- e.g. showFoo : Show a => Foo a -> String
showClaim : (tyname : Name) -> (ty : TTImp) -> Visibility -> (used_vars : List Name) -> Elab Decl
showClaim fun ty vis used = do
    -- used are the Show's we require
    let ty' = withAutoImplicits ty used
        showty = mkTy fun $ ty'
    logTerm 1 "claim_ty" ty'
    -- complains about hinting concrete return types, but (iPrimVal StringType) is concrete.
    traverse (logMsg 1 . ("baba " ++) . show) used
    pure $ iClaim MW vis [] showty -- should be Hint, what is the bool?
  where
    showVar : Name -> TTImp
    showVar n = `(Show) `iApp` iBindVar (show n)

    withAutoImplicits : (ty : TTImp) -> (used : List Name) -> TTImp
    withAutoImplicits ty [] = iPi MW ExplicitArg Nothing ty (iPrimVal StringType)
    withAutoImplicits ty used@(n::ns)
      = iPi MW AutoImplicit Nothing
             (foldr (\n,sig => (`(Builtin.Pair) `iApp` (showVar n)) `iApp` sig) (showVar n) ns)
             (withAutoImplicits ty [])

makeTypeAndTyVars : Name -> List Name -> Elab (TTImp,List Name)
makeTypeAndTyVars n cons = do
  args <- getExplicitArgs n
  let ty = foldl (\term,arg => term `iApp` (iBindVar (show arg))) (iVar n) args
  pure (ty, args)

-- determine which tyvars are actually used. We don't need to require
-- Show a for phantom parameters.
-- e.g. data Foo : Type -> Type where Biz : Foo a
-- has no need for Show a in: show : Show a => Foo a -> String
-- as `a` is never shown.
-- TODO Finish this func last, since its only job is to prune the signature.
usedTyVars : (restype : TTImp) -> (tyvars : List Name) -> (cons : List Name) -> Elab (List Name)
usedTyVars restype vars cons = do
    cons <- traverse lookupName cons
    -- ns <- traverse (\(n,t) => logTerm 1 ("fof " ++ show n) t) cons
    -- mark and prune what tyvars were actually used
    ixes <- nub . concat <$> traverse iXUsedInCon cons
    logMsg 1 ("ixes" ++ show ixes)
    -- scan to end of type, grab (((Foo6 h) g) j)
    -- scan type for Explicit use of h g j by name or by useage as an argument
    -- getImplicit names
    -- TODO, CHANGE
    let tyixes = zip [0..cast(length vars)] vars
    logMsg 1 ("tyixes" ++ show tyixes)
    pure $ mapMaybe (\i => lookup i tyixes) ixes
  where
    getResultTy : TTImp -> Elab TTImp
    getResultTy (IPi _ _ _ _ _ r@(IPi _ _ _ _ _ _)) = getResultTy r
    getResultTy (IPi _ _ _ _ _ retTy) = pure retTy
    getResultTy _ = fail $ "Couldn't get return type in usedTyVars"
    
    typeSSS : TTImp -> List Name
    typeSSS (IApp _ x (IVar _ n)) = typeSSS x ++ [n]
    typeSSS (IApp _ (IVar _ x) (IVar _ y)) = [y]
    typeSSS _ = []

    -- gimme explict named args, iVar args and iBind
    followArgs : TTImp -> List Name
    followArgs arg@(IPi _ _ ExplicitArg (Just n) _ retTy) = n :: followArgs retTy
    followArgs arg@(IPi _ _ ExplicitArg _ (IVar _ n) retTy) = n :: followArgs retTy
    followArgs arg@(IPi _ _ _ _ _ retTy) = followArgs retTy
    followArgs _ = []

    iXUsedInCon : (Name, TTImp) -> Elab (List Int)
    iXUsedInCon (n,contt) = do
      let fargs = followArgs contt
          tyvars = typeSSS restype
          restyvec = zip tyvars [0..cast (length tyvars)]
      let d = mapMaybe (\arg => lookup arg restyvec) fargs
      logMsg 1 ("nam:" ++ show n)
      logMsg 1 ("fargs" ++ show fargs)
      logTerm 1 "tyvarbase" restype
      logMsg 1 ("tyvars" ++ show tyvars)
      logMsg 1 ("restyvec" ++ show restyvec)
      pure d


showCon : (op_name : Name) -> (con_name : Name) -> Elab Clause
showCon op con = do
    coninfo <- lookupName con
    args <- getExplicitArgs (fst coninfo)
    -- build up a list and intercalate it
    -- rhs = iPrimVal (Str (extractNameStr n))
    pure (patClause (buildLhs args) (buildRhs args))
  where
    buildLhs : List Name -> TTImp
    buildLhs ns = iVar op `iApp`
      foldl (\tt,v => tt `iApp` iBindVar (show v)) (iVar con) ns
    buildRhs : List Name -> TTImp
    buildRhs ns
      = let build = intercalate_str " "
            con_str = iPrimVal (Str (extractNameStr con))
            showv = \v => `(show) `iApp` iBindVar (show v)
        in foldl (\tt,v => (`((++)) `iApp` tt) `iApp` showv v) con_str ns

deriveShow : Visibility -> Name -> Elab ()
deriveShow vis n = do
    (name,_) <- lookupName n
    fun <- pure $ extendNameL "show" n -- create a human readable function name
    cons <- getCons name
    -- construct type and tyvar names
    (type,tyvars) <- makeTypeAndTyVars name cons
    -- logTerm 1 "makeTypeAndTyVars,type: " type
    -- traverse (logMsg 1 . ("makeTypeAndTyVars,tyvars: " ++) . show) tyvars
    -- determine which tyvars are actually used
    used <- usedTyVars type tyvars cons
    
    traverse (logMsg 1 . ("usedTyVars,used: " ++) . show) used

    -- create the claim
    c <- showClaim fun type vis used
    
    -- create our show function clauses
    cl <- IDef EmptyFC fun <$> traverse (showCon fun) cons
    
    -- logTerm 1 "fob1" $ ILocal EmptyFC [c] `( () )
    -- logTerm 1 "fob2" $ ILocal EmptyFC [cl] `( () )
    
    -- declare [c,cl]
    pure ()


export
data Foo : Type where
  Bor : Foo

export
data Foo2 : Type -> Type where
  Bor2 : a -> Foo2 a

export
data Foo3 : Type -> Type where
  Bor3 : Foo3 a

data Foo4 : Type -> Type -> Type where
  Bor4 : b -> Foo4 a b

data Foo5 : Type -> Type -> Type -> Type where
  Bor5 : b -> Foo5 a b c

data Foo6 : Type -> Type -> Type -> Type where
  Zor6 : a -> b -> Foo6 a b c
  Gor6 : b -> Foo6 a b c
  Nor6 : Foo6 a b c
  Bor6 : a -> Foo6 a b c

-- %runElab deriveShow Export `{{Foo2}}
-- %runElab deriveShow Export `{{Foo3}}
-- %runElab deriveShow Private `{{Foo5}}
%runElab deriveShow Private `{{Foo6}}

-- 
-- smt : a
-- 
-- max : (x : Int) -> (y : Int) -> (v : Int ** (v >= x = True, v >= y = True))
-- 
-- f : Int -> Int
-- f x = fst (max x (fst (MkDPair {p = (\v => v == 0 = True)} 0 smt)))
-- 
-- 