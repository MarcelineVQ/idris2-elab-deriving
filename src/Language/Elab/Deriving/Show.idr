module Language.Elab.Deriving.Show

import Language.Elab.Syntax
import Language.Reflection

import Language.Elab.Types

import Data.Strings -- fastAppend

intercalate_str : String -> List String -> String
intercalate_str sep ss = fastAppend (intersperse sep ss)

-- It works! We still need to prune requring Show on tvars that aren't
-- actually used, since otherwise users have to provide it.
showClaim : (opname : Name) -> TypeInfo -> Visibility -> Elab Decl
showClaim op tyinfo vis = do
    let conargs = pullExplicits tyinfo
        varnames = map (show . argName) (filter (isType . argType) conargs)
        tysig = `( ~(appTyCon (map (show . argName) conargs) (tiName tyinfo)) -> String )
        autoimps = foldr (\v,tt => `(Show ~(iBindVar v) => ~(tt))) tysig varnames
    pure $ iClaim MW vis [] (mkTy op autoimps)

showCon : (opname : Name) -> TypeInfo -> (conname : Name) -> Elab Clause
showCon op tyinfo con = do
    coninfo <- makeTypeInfo con
    conname <- showName (tiName coninfo)
    let varnames = pullExplicits coninfo
        lhsvars = map (show . argName) varnames
        rhsvars = map (\arg => if isUse0 (count arg)
                             then Nothing
                             else Just (show (argName arg))) varnames
        lhs = iVar op `iApp`
                foldl (\tt,v => tt `iApp` (iBindVar v)) (iVar con) lhsvars
        rhs = foldl (\tt,v => `( ~(tt) ++ " " ++ ~(beShown v)))
                (iPrimVal (Str conname)) rhsvars
    pure $ patClause lhs rhs
  where
    beShown : Maybe String -> TTImp
    beShown (Just x) = `(show ~(iVar (UN x)))
    beShown Nothing = `("_0") -- param is 0 use

showObject : (decname : Name) -> (funname : Name) -> TypeInfo -> Visibility -> Elab (List Decl)
showObject decname showfun tyinfo vis = do
  (qname,_) <- lookupName `{{Show}}
  [NS _ (DN _ showcon)] <- getCons qname
    | _ => fail "showObject: error during Show constructor lookup"
  let conargs = pullExplicits tyinfo
      varnames = map (show . argName) (filter (isType . argType) conargs)
      retty = `( Show ~(appTyCon (map (show . argName) conargs) (tiName tyinfo)))
      tysig = foldr (\v,tt => `(Show ~(iBindVar v) => ~(tt))) retty varnames
      -- Unclear if we need Hint False here, False supposedly chases instances
      -- but I'm not sure what that means/implies.
      claim = iClaim MW vis [Hint False] (mkTy decname tysig)
      showprecfun = `(\_,x => show x) -- Prec ignored like Prelude.Show does
      rhs = `( ~(iVar showcon) ~(iVar showfun) ~(showprecfun))
      body = iDef decname [(patClause (iVar decname) rhs)]
  pure $ [claim,body]

-- TODO determine which tyvars are actually used later. We don't need to
-- require Show for phantom parameters.
deriveShow : Visibility -> Name -> Elab ()
deriveShow vis sname = do
    (qname,_) <- lookupName sname -- get the qualified name of our type
    -- create human readable names for our instance components
    decn <- pure $ mapName (\d => "showImpl" ++ d) sname
    funn <- pure $ mapName (\d => "showImpl" ++ d ++ "Fun") sname
    -- Get our type's data constructors
    cons <- getCons qname
    -- General info about the type we're deriving (e.g. Foo) that we want to
    -- keep around.
    tyinfo <- makeTypeInfo qname
    -- Our type declaration for our showing function
    c <- showClaim funn tyinfo Private -- NB private
    -- Our clauses for showing each constructor.
    cs <- traverse (showCon funn tyinfo) cons
    let g = IDef EmptyFC funn cs
    -- The actual showFoo : Show Foo instance.
    o <- showObject decn funn tyinfo vis
    -- Place our things into the namespace
    declare $ [c,g] ++ o

-----------------------------
-- Testing
-----------------------------

%language ElabReflection -- you can remove this once %runElab is no longer used in this module
-- That time will be when deriveShow prunes extraneous Show constraints and the
-- testing types are moved to their own module

export
data Foo1 : Type -> Type where
  Bor1 : Foo1 a

export
data Foo2 : Type -> Type where
  Bor2 : a -> Foo2 a

data Foo4 : Type -> Type -> Type where
  Bor4 : b -> Foo4 a b

data Foo5 : Type -> Type -> Type -> Type where
  Bor5 : a -> b -> c -> Foo5 a b c

-- NB c is never used, so Show shouldn't be required for it
data Foo7 : Type -> Type -> Type -> Type where
  Zor7 : a -> Foo7 a b c
  Gor7 : b -> Foo7 a b c
  Nor7 : a -> b -> Foo7 a b c
  Bor7 : Foo7 a b c

-- NB a is never used, so Show shouldn't be required for it
data Foo7' : Type -> Type -> Type -> Type where
  Zor7' : c -> Foo7' a b c
  Gor7' : b -> Foo7' a b c
  Nor7' : b -> c -> Foo7' a b c
  Bor7' : Foo7' a b c

data Foo6 : Type -> Type -> Type -> Nat -> Type where
  Zor6 : a -> b -> Foo6 a b c Z
  Gor6 : b -> Foo6 a b c (S k)
  Nor6A : a -> b -> c -> Foo6 a b c n
  Nor6B : a -> (0 _ : b) -> c -> Foo6 a b c n -- NB: 0 Use arg
  Bor6 : Foo6 a b c n

-- reference impl
showFoo6' : (Show a, Show b, Show c) => Foo6 a b c n -> String
showFoo6' (Zor6 x y) = "Zor6" ++ show x ++ show y
showFoo6' (Gor6 x) = "Gor6" ++ show x
showFoo6' (Nor6A x y z) = "Nor6A" ++ show x ++ show y ++ show z
showFoo6' (Nor6B x _ z) = "Nor6B" ++ show x ++ "_0" ++ show z
showFoo6' (Bor6) = "Bor6"

-- %runElab deriveShow Export `{{Foo}}
%runElab deriveShow Export `{{Foo2}}
%runElab deriveShow Private `{{Foo5}}

-- These are created fine but use of them is overly restricted currently
-- We're generating more Show ty constraints than neccsary
-- e.g. to show Foo1 we have to write: showFoo1 (Bor1 {a=Int})
-- But in reality we don't use `show` in Bor1 so that's silly.
%runElab deriveShow Export `{{Foo1}}
%runElab deriveShow Private `{{Foo6}}
%runElab deriveShow Private `{{Foo7}}
%runElab deriveShow Private `{{Foo7'}}
