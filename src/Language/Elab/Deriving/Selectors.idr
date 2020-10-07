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

select : TTImp -> Visibility -> Constructor -> Elab ()
select dty vis con = do
  let n = mapName ("is" ++) con.name -- isWaf
      c = iClaim MW vis [] $ mkTy n `( ~dty -> Bool)
      expargs = filter (isExplicitPi . piInfo) con.args
      c1 = patClause (iVar n `iApp` foldl (\xs,_ => `(~xs _) ) (iVar con.name) expargs)
                     `(True)
      catchall = patClause `(~(iVar n) _) `(False)
      d = iDef n [c1,catchall]
  declare [c,d]
  pure ()

||| Derives a selector for any non-operator constructor
||| Simply because I'm not sure how to let you type the letters: e.g. is:::
export
deriveSelectors : Visibility -> Name -> Elab ()
deriveSelectors vis tn = do
  ti <- makeTypeInfo tn
  let cons' = filter (not . isOpName . name) ti.cons
  traverse_ (select ti.type vis) cons'

fetchRoot : TTImp -> TTImp
fetchRoot (IApp _ y _) = fetchRoot y
fetchRoot ty = ty

isCon : Name -> Constructor -> Elab Clause
isCon cn con = ?isCon_rhs

-- This is kind of tough, we don't have a good way to say
-- isFooCon (:::)   isFooCon Waf at the same type.
-- If we take a Name, e.g.:
-- isFooCon `{{(:::)}}   isFooCon `{{Waf}}
-- We don't have a good way to enforce it's valid to use
-- adding Maybe is a bit too much work for the user to deal with
deriveIsCon : Visibility -> Name -> Elab ()
deriveIsCon vis cn = do
  ti <- makeTypeInfo cn
  let n = mapName (\n => "is" ++ n ++ "Con") ti.name -- isFooCon, need to get Foo from cn
  let c = iClaim MW vis [] $ mkTy `{{Foo}} `( Name -> Bool)
  let catchall = patClause `(~(iVar n) _) `(False)

  defs <- traverse (isCon ti.name) ti.cons
  pure ()


%runElab deriveSelectors Private `{{Foo}}
-- %runElab deriveIsCon Private `{{Foo}}

foo1 : Foo -> Bool
foo1 x = isWaf x

foo2 : Foo -> Bool
foo2 x = isBif x

-- foo3 : Foo -> Bool
-- foo3 x = is::: x -- isn't generated
