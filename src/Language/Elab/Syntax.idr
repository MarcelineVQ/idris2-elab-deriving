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
iAs : Name -> TTImp -> TTImp
iAs = IAs EmptyFC UseLeft  

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
mapName f (RF n) = RF (f n)

export
extractNameStr : Name -> String
extractNameStr (UN x) = x
extractNameStr (MN x y) = x
extractNameStr (NS xs x) = extractNameStr x
extractNameStr (DN x _) = x
extractNameStr (RF x) = x

isOpChar : Char -> Bool
isOpChar c = c `elem` (unpack ":!#$%&*+./<=>?@\\^|-~")

export
isOpName : Name -> Bool
isOpName n = any isOpChar (unpack (extractNameStr n))

export
extractNameNo : Name -> Int
extractNameNo (MN _ i) = i
extractNameNo _ = 0

-- Change/remove this later, we really don't want to export it and we currently
-- do due to the nature of needing to make things public for elaboration
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
isAutoImplicitPi : PiInfo t -> Bool
isAutoImplicitPi AutoImplicit = True
isAutoImplicitPi _ = False

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


-- Don't do this yourself, use Selectors :>
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

alterTT : (TTImp -> Maybe TTImp) -> TTImp -> TTImp
alterTT f tt = maybe tt id (f tt)


Eq FC where
  (MkFC x1 y1 z1) == (MkFC x2 y2 z2) = x1 == x2 && y1 == y2 && z1 == z2
  EmptyFC == EmptyFC = True
  _ == _ = False

-- bleh, but if I can polish Eq enough to add the deriving to the compiler this can go away.
Eq TTImp where
  (IVar x1 y1) == (IVar x2 y2) = x1 == x2 && y1 == y2
  (IPi x1 y1 z1 w1 argTy1 retTy1) == (IPi x2 y2 z2 w2 argTy2 retTy2) = ?holeEq_2
  (ILam x1 y1 z1 w1 argTy1 lamTy1) == (ILam x2 y2 z2 w2 argTy2 lamTy2) = ?holeEq_3
  (ILet x1 y1 z1 nTy1 nVal1 scope1) == (ILet x2 y2 z2 nTy2 nVal2 scope2) = ?holeEq_4
  (ICase x1 y1 ty1 xs1) == (ICase x2 y2 ty2 xs2) = ?holeEq_5
  (ILocal x1 xs1 y1) == (ILocal x2 xs2 y2) = ?holeEq_6
  (IUpdate x1 xs1 y1) == (IUpdate x2 xs2 y2) = ?holeEq_7
  (IApp x1 y1 z1) == (IApp x2 y2 z2) = x1 == x2 && y1 == y2 && z1 == z2
  (IImplicitApp x1 y1 z1 w1) == (IImplicitApp x2 y2 z2 w2) = x1 == x2 && y1 == y2 && z1 == z2 && w1 == w2
  (IWithApp x1 y1 z1) == (IWithApp x2 y2 z2) = x1 == x2 && y1 == y2 && z1 == z2
  (ISearch x1 depth1) == (ISearch x2 depth2) = x1 == x2 && depth1 == depth2
  (IAlternative x1 y1 xs1) == (IAlternative x2 y2 xs2) = ?holeEq_12
  (IRewrite x1 y1 z1) == (IRewrite x2 y2 z2) = ?holeEq_13
  (IBindHere x1 y1 z1) == (IBindHere x2 y2 z2) = ?holeEq_14
  (IBindVar x1 y1) == (IBindVar x2 y2) = ?holeEq_15
  (IAs x1 y1 z1 w1) == (IAs x2 y2 z2 w2) = ?holeEq_16
  (IMustUnify x1 y1 z1) == (IMustUnify x2 y2 z2) = ?holeEq_17
  (IDelayed x1 y1 z1) == (IDelayed x2 y2 z2) = ?holeEq_18
  (IDelay x1 y1) == (IDelay x2 y2) = ?holeEq_19
  (IForce x1 y1) == (IForce x2 y2) = ?holeEq_20
  (IQuote x1 y1) == (IQuote x2 y2) = ?holeEq_21
  (IQuoteName x1 y1) == (IQuoteName x2 y2) = ?holeEq_22
  (IQuoteDecl x1 y1) == (IQuoteDecl x2 y2) = ?holeEq_23
  (IUnquote x1 y1) == (IUnquote x2 y2) = ?holeEq_24
  (IPrimVal x1 c1) == (IPrimVal x2 c2) = ?holeEq_25
  (IType x1) == (IType x2) = ?holeEq_26
  (IHole x1 y1) == (IHole x2 y2) = ?holeEq_27
  (Implicit x1 bindIfUnsolved1) == (Implicit x2 bindIfUnsolved2) = ?holeEq_28
  (IWithUnambigNames x1 xs1 y1) == (IWithUnambigNames x2 xs2 y2) = ?holeEq_29
  _ == _ = False

-- ||| target for mapping an exact given TTImp
-- target : TTImp -> (TTImp -> TTImp) -> TTImp -> TTImp
