module Language.Elab.Deriving.Show

import Language.Elab.Syntax
import Language.Reflection

import Data.Strings -- intercalate
-- import Data.Vect -- intercalate

%language ElabReflection -- you can remove this once %runElab is no longer used in this module

-- derive show

export
record ArgInfo where
  constructor MkArgInfo
  count  : Count
  piInfo : PiInfo TTImp
  argName   : Name
  argType   : TTImp

-- Show ArgInfo where
--   show (MkArgInfo count piInfo argName argType) = ?showPrec_rhs_1
--     where
--       showCount : Count -> String
--       showCount : Count -> String

readableGenSym : String -> Elab String
readableGenSym s = do MN n i <- genSym s
                        | _ => fail "readableGenSym failure"
                      pure (n ++ show i)

-- Fully qualified Name
-- Vect since we want to track our indices anyway
-- `type` is our fully applied type, e.g. given args a,b,c: Foo a b c
export
record TypeInfo where
  constructor MkTypeInfo
  tiName : Name
  args : List ArgInfo
  tiType : TTImp

-- makes them unique for now
export
genArgs : Name -> Elab (List ArgInfo)
genArgs qn = do (_,tyimp) <- lookupName qn
                go tyimp
  where
    go : TTImp -> Elab (List ArgInfo)
    go (IPi _ c i n argTy retTy)
      = [| pure (MkArgInfo c i !(UN <$> readableGenSym "argu") argTy) :: go retTy |]
    go _ = pure []

makeTypeInfo : Name -> Elab TypeInfo
makeTypeInfo n = do
  args <- genArgs n
  let explArgs = filter (isExplicitPi . piInfo) args
      explArgNames = map argName explArgs
      ty = foldl (\term,arg => `( ~(term) ~(iVar arg))) (iVar n) explArgNames
  pure $ MkTypeInfo n args ty

-- determine if M0 should be excluded from Explicit as well
pullExplicits : TypeInfo -> List ArgInfo
pullExplicits x = filter (isExplicitPi . piInfo) (args x)

pullImplicits : TypeInfo -> List ArgInfo
pullImplicits x = filter (isImplicitPi . piInfo) (args x)

intercalate_str : String -> List String -> String
intercalate_str sep ss = fastAppend (intersperse sep ss)

withImplicits : Count -> (ty : TTImp) -> (used : List Name) -> TTImp
withImplicits c ty ns
  = foldr (\n,sig => iPi c ImplicitArg (Just n) implicit' sig) ty ns

-- 1. query for explicit arguments, varnames.
-- 2. build the explicit signature for our show, tysig: `Foo a -> String`
-- 3. add Show constraints, autoimps: ... -> Show a => Show b => ...
-- 4. add implicit tyvars everything else relies on, imps: {a} -> {b} -> ...
-- 5. combine into a claim: opname : {a} -> Show a => Foo a -> String
showClaim : (opname : Name) -> TypeInfo -> Visibility -> Elab Decl
showClaim op tyinfo vis = do
    let varnames = map (show . argName) (pullExplicits tyinfo)
        ty = appTyCon varnames
        tysig = `( ~(ty) -> String )
        autoimps = foldr (\v,tt => `(Show ~(iBindVar v) => ~(tt))) tysig varnames
    pure $ iClaim MW vis [] (mkTy op autoimps)
  where
    appTyCon : List String -> TTImp
    appTyCon ns = foldl (\tt,v => `( ~(tt) ~(iBindVar v) )) (iVar (tiName tyinfo)) ns

showCon : (opname : Name) -> TypeInfo -> (conname : Name) -> Elab Clause
showCon op tyinfo con = do
    coninfo <- makeTypeInfo con
    let varnames = map (show . argName) (pullExplicits coninfo)
        lhs = iVar op `iApp` foldl (\tt,v => tt `iApp` (iBindVar "h")) (iVar con) varnames
        -- rhs = foldl (\tt,v => `( ~(tt) ++ show ~(iBindVar "h")))
        rhs = foldl (\tt,v => `( ~(tt) ++ "beb")) -- show no good still
          (iPrimVal (Str "foo")) varnames
    pure $ patClause lhs rhs

-- ^ This is giving me:
-- With :set showimplicits
{-
Language.Elab.Deriving.Show> :printdef showFoo2
Language.Elab.Deriving.Show.showFoo2 : {0 argu7297 : Type} -> Show argu7297 => Foo2 argu7297 -> String
showFoo2 {argu7297} {{conArg:7300} = conArg} (Bor2 {a = argu7297} h) = "foo" ++ ?fefargu7299
-}
-- So why is it unable to find a Show instance? My claim should be providing
-- it, see how argu7297 is threaded through completely right to fulfilling
-- Bor2's `a` type argument? Why isn't Show?
-- What exactly is happening in :printdef showFoo6'? There's a ton of
-- repetition of Show constraints. Do I need to pass ty and __con to show
-- myself?


-- determine which tyvars are actually used later. We don't need to require
-- Show a for phantom parameters.
deriveShow : Visibility -> Name -> Elab ()
deriveShow vis n = do
    (name,_) <- lookupName n
    fun <- pure $ mapName ("show" ++) n -- create a human readable function name
    cons <- getCons name
    -- construct type and tyvar names

    -- (ty,tyvars) <- makeTypeAndTyVars name cons
    -- logTerm 1 "makeTypeAndTyVars,type: " type
    -- traverse (logMsg 1 . ("makeTypeAndTyVars,tyvars: " ++) . show) tyvars
    -- determine which tyvars are actually used
    -- used <- usedTyVars ty tyvars cons
    
    -- traverse (logMsg 1 . ("usedTyVars,used: " ++) . show) used

    -- create the claim
    -- c <- showClaim fun ty vis tyvars --used
    
    -- create our show function clauses
    -- cl <- IDef EmptyFC fun <$> traverse (showCon fun tyvars) cons 
    
    -- logTerm 1 "fef" $ ILocal EmptyFC [cl] `( () )
    
    logTerm 1 "faf" (tiType !(makeTypeInfo name))
    tyinfo <- makeTypeInfo name
    c <- showClaim fun tyinfo Private --logTerm 1 "faf" (tiType !(makeTypeInfo name))
    
    cs <- traverse (showCon fun tyinfo) cons
    let g = IDef EmptyFC fun cs
    -- logTerm 1 "fefa" $ ILocal EmptyFC [c] `( () )
    logTerm 1 "fefa" $ ILocal EmptyFC [c,g] `( () )
    -- logTerm 1 "fefb" $ ILocal EmptyFC [g] `( () )
    
    let j = `[ showFoo2 : {a : _} -> Show a => Foo a -> String
               showFoo2 (MkFoo x) = "MkFoo" ++ show x ]
    
    -- logTerm 1 "faf" $ ILocal EmptyFC j `( () )
    
    declare [c,g]
    
    -- declare [c]
    -- declare [cl]
    -- declare [c]
    -- declare fef
    pure ()



export
data Foo : Type -> Type where
  Bor : Foo a

export
data Foo2 : Type -> Type where
  Bor2 : a -> Foo2 a

export
data Foo3 : Type -> Type where
  Bor3 : Foo3 a

data Foo4 : Type -> Type -> Type where
  Bor4 : b -> Foo4 a b

data Foo5 : Type -> Type -> Type -> Type where
  Bor5 : a -> b -> c -> Foo5 a b c

data Foo6 : Type -> Type -> Type -> Type where
  Zor6 : a -> b -> Foo6 a b c
  Gor6 : b -> Foo6 a b c
  Nor6 : a -> b -> c -> Foo6 a b c
  Bor6 : Foo6 a b c

forfo : Show (Foo6 a b c)
forfo = ?forfo_rhs

-- %runElab deriveShow Export `{{Foo}}
%runElab deriveShow Export `{{Foo2}}
-- %runElab deriveShow Export `{{Foo3}}
-- %runElab deriveShow Private `{{Foo5}}
-- %runElab deriveShow Private `{{Foo6}}



showFoo6' : (Show c, (Show b, Show a)) => Foo6 a b c -> String
showFoo6' (Zor6 x y) = "Zor6" ++ show x ++ show y
showFoo6' (Gor6 x) = "Gor6" ++ show x
showFoo6' (Nor6 x y z) = "Nor6" ++ show z
showFoo6' (Bor6) = "Bor6" 




-- 
-- smt : a
-- 
-- max : (x : Int) -> (y : Int) -> (v : Int ** (v >= x = True, v >= y = True))
-- 
-- f : Int -> Int
-- f x = fst (max x (fst (MkDPair {p = (\v => v == 0 = True)} 0 smt)))
-- 
-- 