module Language.Elab.Types

import Language.Elab.Syntax

import Language.Reflection

-- Helper types for deriving cleaner

public export
record ArgInfo where
  constructor MkArgInfo
  count  : Count
  piInfo : PiInfo TTImp
  name   : Name
  type   : TTImp

-- Fully qualified Name
-- Vect since we want to track our indices anyway
-- `type` is our fully applied type, e.g. given args a,b,c: Foo a b c
public export
record TypeInfo where
  constructor MkTypeInfo
  name : Name
  args : List ArgInfo
  type : TTImp

-- makes them unique for now
export
genArgs : Name -> Elab (List ArgInfo)
genArgs qn = do (_,tyimp) <- lookupName qn
                go tyimp
  where
    go : TTImp -> Elab (List ArgInfo)
    go (IPi _ c i n argTy retTy)
      = [| pure (MkArgInfo c i !(UN <$> readableGenSym "arg") argTy) :: go retTy |]
    go _ = pure []

export
makeTypeInfo : Name -> Elab TypeInfo
makeTypeInfo n = do
  args <- genArgs n
  let explArgs = filter (isExplicitPi . piInfo) args
      ty = foldl (\term,arg => `( ~(term) ~(iVar arg.name))) (iVar n) explArgs
  pure $ MkTypeInfo n args ty

export
pullExplicits : TypeInfo -> List ArgInfo
pullExplicits x = filter (isExplicitPi . piInfo) (args x)

export
pullImplicits : TypeInfo -> List ArgInfo
pullImplicits x = filter (isImplicitPi . piInfo) (args x)

-- Takes String so that you can process the names as you like
-- NB: Likely to change
export
appTyCon : List String -> Name -> TTImp
appTyCon ns n = foldl (\tt,v => `( ~(tt) ~(iBindVar v) )) (iVar n) ns
