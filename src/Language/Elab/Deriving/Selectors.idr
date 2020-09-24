module Language.Elab.Deriving.Selectors

import public Language.Reflection

import public Language.Elab.Syntax
import public Language.Elab.Types

import public Util

%language ElabReflection

{-
This pattern comes up a lot

isNoSugar : UnelabMode -> Bool
isNoSugar (NoSugar _) = True
isNoSugar _ = False
isDefImp : PiInfo t -> Bool
isDefImp (DefImplicit _) = True
isDefImp _ = False

We should have a deriving or converstion for this sort of thing, where you
select the 'true' case and all others are false. e.g.

data Foo : Type where
  Bif : Foo
  Waf : Int -> Foo

deriveSelectors Foo
results in

isBif : Foo -> Bool
isBif Bif = True
isBif _ = False

isWaf : Foo -> Bool
isWaf (Waf _) = True
isWaf _ = False
-}

-- Is this name pollution? Should we prefer `isCon Waf`
-- e.g. isCon Waf  isCon Bif

data Foo : Type where
  Bif : Foo
  Waf : Int -> Foo
  (:::) : Bool -> Bool -> Foo -- not really doable with singular functions, is::: ?

select : TTImp -> Visibility -> (Name, List ArgInfo, TTImp) -> Elab ()
select dty vis (conn,args,imp) = do
  let n = mapName ("is" ++) conn -- isWaf
      c = iClaim MW vis [] $ mkTy n `( ~dty -> Bool)
      expargs = filter (isExplicitPi . piInfo) args
      c1 = patClause (iVar n `iApp` foldl (\xs,_ => `(~xs _) ) (iVar conn) expargs)
                     `(True)
      catchall = patClause `(~(iVar n) _) `(False)
      d = iDef n [c1,catchall]
  declare [c,d]
  pure ()

export
deriveSelectors : Visibility -> Name -> Elab ()
deriveSelectors vis tn = do
  ti <- makeTypeInfo tn
  traverse_ (select ti.type vis) ti.cons

%runElab deriveSelectors Private `{{Foo}}

foo1 : Foo -> Bool
foo1 x = isWaf x

foo2 : Foo -> Bool
foo2 x = isBif x

foo3 : Foo -> Bool
foo3 x = ?fsd -- is::: x  not really gonna happen
-- ^ This is why a combined approach is probably best, e.g. isCon (:::) x

