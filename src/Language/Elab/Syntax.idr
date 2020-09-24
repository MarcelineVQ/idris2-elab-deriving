module Language.Elab.Syntax

import Language.Reflection

import Data.Strings -- strM


-- Get rid of all the instances here when we've gotten far enough along, these
-- are not things to leave laying around

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
iImplicitApp : TTImp -> Maybe Name -> TTImp -> TTImp
iImplicitApp = IImplicitApp EmptyFC

export
implicit' : TTImp
implicit' = Implicit EmptyFC True

export
implicit'' : TTImp
implicit'' = Implicit EmptyFC False

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
iLam : Count -> PiInfo TTImp -> Maybe Name ->
      (argTy : TTImp) -> (lamTy : TTImp) -> TTImp
iLam = ILam EmptyFC

export
iLet : Count -> Name -> (nTy : TTImp) -> (nVal : TTImp)
    -> (scope : TTImp) -> TTImp
iLet = ILet EmptyFC

export
iCase : TTImp -> (ty : TTImp)
     -> List Clause -> TTImp
iCase = ICase EmptyFC

export
iDef : Name -> List Clause -> Decl
iDef = IDef EmptyFC


export
iPrimVal : (c : Constant) -> TTImp
iPrimVal = IPrimVal EmptyFC

export
iPrimVal' : String -> (c : Constant) -> TTImp
iPrimVal' s = IPrimVal (namedFC s)

-- test this, possibly using InCurrentNS, it's unclear whether the name results
-- list will return useful info or how namespaces affect it.
-- Fetch fully qualified name and ttinfo.
-- TODO intersperse instead of concatmap
-- TODO This currently seems to detect names in other modules that arne't
-- actually exported, so I need to also check the visibility of the names this
-- finds.
export
lookupName : Name -> Elab (Name, TTImp)
lookupName n = do
  [(name,imp)] <- getType n
    | xs => fail $ show n ++
      case xs of
        [] => " is not in scope."
        xs => " is not uniquely in scope, these conflicting names exist: " ++
          concatMap (show . fst) xs
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
readableGenSym : String -> Elab Name
readableGenSym s = do MN n i <- genSym s
                        | _ => fail "readableGenSym failure"
                      pure (UN (n ++ show i))

export
mapName : (String -> String) -> Name -> Name
mapName f (UN n) = UN (f n)
mapName f (MN n i) = (MN (f n) i)
mapName f (NS ns n) = (NS ns (mapName f n))
mapName f (DN n realn) = (DN (f n) realn)
-- mapName f (Nested ix n) = Nested ix (mapName f n)
-- mapName f (CaseBlock outer inner) = CaseBlock outer inner

export
extractNameStr : Name -> String
extractNameStr (UN x) = x
extractNameStr (MN x y) = x
extractNameStr (NS xs x) = extractNameStr x
extractNameStr (DN x _) = x

export
extractNameNo : Name -> Int
extractNameNo (MN _ i) = i
extractNameNo _ = 0

-- Change/remove this later, we really don't want to have it, or export it
export
implementation Eq Name where
  (==) (UN x) (UN y) = x == y
  (==) (MN x z) (MN y w) = z == w && x == y
  (==) (NS (MkNS xs) x) (NS (MkNS ys) y) = xs == ys && x == y
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
logDecls : String -> Nat -> String -> List Decl -> Elab ()
logDecls ty n s d = logTerm ty n s $ ILocal EmptyFC d `( () )

-- Turn a name into a string, add parens to an operator-like string
export
showName : Name -> Elab String
showName n = let s = extractNameStr n
             in  case strM s of
                   StrNil => fail "showName: empty name"
                   StrCons x xs => pure $
                     if isAlpha x then s else "(" ++ s ++ ")"

export
bindNameVar : Name -> TTImp
bindNameVar = iBindVar . extractNameStr

-- bindNameVar = iBindVar  . show

-----------------------------
-- Predicates
-- Replace these with something better down the road, even just Eq?
-----------------------------

export
Show Count where
  show M0 = "M0"
  show M1 = "M1"
  show MW = "MW"

export
Show (PiInfo tt) where
  show ImplicitArg = "ImplicitArg"
  show ExplicitArg = "ExplicitArg"
  show AutoImplicit = "AutoImplicit"
  show (DefImplicit _) = "DefImplicit _"

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

export
isType : TTImp -> Bool
isType (IType _) = True
isType _ = False



-- e.g. %runElab printInterfaceCon `{{Eq}}
export
printInterfaceCon : Name -> Elab ()
printInterfaceCon n = do
  (qname,_) <- lookupName n
  let nstr = extractNameStr n
  [NS _ (DN _ icon)] <- getCons qname
    | _ => fail $ "showObject: error during " ++ nstr ++ " constructor lookup"
  (_, objimp) <- lookupName icon
  logTerm "printInterfaceCon" 1 (nstr ++ ": ") objimp
