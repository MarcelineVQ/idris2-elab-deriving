module Language.Elab.Syntax

import Language.Reflection

private
z : (Int,Int)
z = (0,0)

export
namedFC : String -> FC
namedFC s = MkFC s z z

export
iVar : Name -> TTImp
iVar = IVar EmptyFC

export
iVar' : String -> Name -> TTImp
iVar' s = IVar (namedFC s)

export
iBindVar : String -> TTImp
iBindVar = IBindVar EmptyFC

export
iBindVar' : String -> String -> TTImp
iBindVar' s = IBindVar (namedFC s)

-- export
infixl 6 `iApp`
export
iApp : TTImp -> TTImp -> TTImp
iApp = IApp EmptyFC

export
iApp' : String -> TTImp -> TTImp -> TTImp
iApp' s = IApp (namedFC s)


export
implicit' : TTImp
implicit' = Implicit EmptyFC True

export
implicit'' : String -> TTImp
implicit'' s = Implicit (namedFC s) True

export
patClause : (lhs : TTImp) -> (rhs : TTImp) -> Clause
patClause = PatClause EmptyFC

export
patClause' : String -> (lhs : TTImp) -> (rhs : TTImp) -> Clause
patClause' s = PatClause (namedFC s)

export
iClaim : Count -> Visibility -> List FnOpt -> ITy -> Decl
iClaim = IClaim EmptyFC

export
iClaim' : String -> Count -> Visibility -> List FnOpt -> ITy -> Decl
iClaim' s = IClaim (namedFC s)

export
mkTy : (n : Name) -> (ty : TTImp) -> ITy
mkTy = MkTy EmptyFC

export
mkTy' : String -> (n : Name) -> (ty : TTImp) -> ITy
mkTy' s = MkTy (namedFC s)

export
iPi : Count -> PiInfo TTImp -> Maybe Name ->
      (argTy : TTImp) -> (retTy : TTImp) -> TTImp
iPi = IPi EmptyFC

export
iPi' : String -> Count -> PiInfo TTImp -> Maybe Name ->
      (argTy : TTImp) -> (retTy : TTImp) -> TTImp
iPi' s = IPi (namedFC s)

export
iPrimVal : (c : Constant) -> TTImp
iPrimVal = IPrimVal EmptyFC

export
iPrimVal' : String -> (c : Constant) -> TTImp
iPrimVal' s = IPrimVal (namedFC s)

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
mapName : (String -> String) -> Name -> Name
mapName f (UN n) = UN (f n)
mapName f (MN n i) = (MN (f n) i)
mapName f (NS ns n) = (NS ns (mapName f n))

export
extractNameStr : Name -> String
extractNameStr (UN x) = x
extractNameStr (MN x y) = x
extractNameStr (NS xs x) = extractNameStr x

export
extractNameNo : Name -> Int
extractNameNo (MN _ i) = i
extractNameNo _ = 0

-- Change/remove this later
export
implementation
Eq Name where
  (==) (UN x) (UN y) = x == y
  (==) (MN x z) (MN y w) = z == w && x == y
  (==) (NS xs x) (NS ys y) = xs == ys && x == y
  (==) _ _ = False

export
isExplicitPi : PiInfo t -> Bool
isExplicitPi ExplicitArg = True
isExplicitPi _ = False

export
isImplicitPi : PiInfo t -> Bool
isImplicitPi ImplicitArg = True
isImplicitPi _ = False

export
logDecls : Nat -> String -> List Decl -> Elab ()
logDecls n s d = logTerm n s $ ILocal EmptyFC d `( () )

export
isUse0 : Count -> Bool
isUse0 M0 = True
isUse0 _ = False

export
isUse1 : Count -> Bool
isUse1 M1 = True
isUse1 _ = False

export
isUseW : Count -> Bool
isUseW MW = True
isUseW _ = False