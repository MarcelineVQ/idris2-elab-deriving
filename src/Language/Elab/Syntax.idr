module Language.Elab.Syntax

import Language.Reflection

export
iVar : Name -> TTImp
iVar n = IVar EmptyFC n

export
iBindVar : String -> TTImp
iBindVar n = IBindVar EmptyFC n

-- export
infixl 6 `iApp`
export
iApp : TTImp -> TTImp -> TTImp
iApp x y = IApp EmptyFC x y

iApp' : TTImp -> TTImp -> TTImp
iApp' x y = IApp (MkFC "iApp'" (0,0) (0,0)) x y


export
implicit' : TTImp
implicit' = Implicit EmptyFC True

export
patClause : (lhs : TTImp) -> (rhs : TTImp) -> Clause
patClause = PatClause EmptyFC

export
iClaim : Count -> Visibility -> List FnOpt -> ITy -> Decl
iClaim = IClaim EmptyFC

export
mkTy : (n : Name) -> (ty : TTImp) -> ITy
mkTy = MkTy EmptyFC

export
iPi : Count -> PiInfo TTImp -> Maybe Name ->
      (argTy : TTImp) -> (retTy : TTImp) -> TTImp
iPi = IPi EmptyFC

export
iPrimVal : (c : Constant) -> TTImp
iPrimVal = IPrimVal EmptyFC

-- test this, possibly using InCurrentNS, it's unclear whether the name results
-- list will return useful info or how namespaces affect it.
-- Fetch fully qualified name and ttinfo.
export
lookupName : Name -> Elab (Name, TTImp)
lookupName n = do
  [(name,imp)] <- getType n
    | xs => fail $ show n ++
      case xs of
        [] => " is not in scope."
        xs => " is not uniquely in scope, these conflicting names exist: " ++ concatMap (show . fst) xs
  pure (name,imp)

-- `[ ] returns a list, assert that it only returned one declaration where it
-- was used
export
singleDecl : String -> List Decl -> Elab Decl
singleDecl fun dec = do [dec] <- pure dec
                          | _ => fail $ "code error in " ++ fun
                        pure dec

export
getExplicitArgs : Name -> Elab (List Name)
getExplicitArgs n = do (_,tyimp) <- lookupName n
                       getEArgs tyimp
  where
    getEArgs : TTImp -> Elab (List Name)
    getEArgs (IPi _ _ ExplicitArg _ _ retTy)
      = [| genSym "arg" :: getEArgs retTy |]
    getEArgs (IPi _ _ _ _ _ retTy) = getEArgs retTy -- skip implicit args
    getEArgs _ = pure []

export
extendNameL : String -> Name -> Name
extendNameL x (UN y)    = UN (x ++ y)
extendNameL x (MN y z)  = MN (x ++ y) z
extendNameL x (NS xs y) = NS xs (extendNameL x y)

export
extendNameR : Name -> String -> Name
extendNameR (UN y)    x =  UN (y ++ x)
extendNameR (MN y z)  x = MN (y ++ x) z
extendNameR (NS xs y) x = NS xs (extendNameR y x)

export
extractNameStr : Name -> String
extractNameStr (UN x) = x
extractNameStr (MN x y) = x
extractNameStr (NS xs x) = extractNameStr x

-- Change/remove this later
export
implementation
Eq Name where
  (==) (UN x) (UN y) = x == y
  (==) (MN x z) (MN y w) = z == w && x == y
  (==) (NS xs x) (NS ys y) = xs == ys && x == y
  (==) _ _ = False
