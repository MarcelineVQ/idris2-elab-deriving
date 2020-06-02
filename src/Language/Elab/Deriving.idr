module Language.Elab.Deriving

import Language.Reflection

%language ElabReflection

-- the handy regex for eliminating FC from tests: \(MkFC.+?\)\)

-- Elaboration for == for Foo. Next step is to be able to have this work on
-- more complex types like
-- data Foo : Type -> Type where
--   Bob : a -> Foo a

-----------------------------

-- Elaboration for == for Foo

export
data Foo = Biz | Baz

{-
NB
(==) : Foo -> Foo -> Bool
(==) Biz Biz = True
(==) Baz Baz = True
(==) _ _ = False

-- == becomes basically this
(===) : Foo -> Foo -> Bool
(===) a b = case a of
             Biz => case b of
                      Biz => True
                      _   => False
             Baz => case b of
                      Baz => True
                      _   => False
-}

compareInnards : (con : TTImp) -> (b : TTImp) -> TTImp
compareInnards con@(IVar _ _) b = `(True)
compareInnards (IApp _ y z) (IApp _ y' z') = `( (~(z) == ~(z')) && compareInnards y y' )
compareInnards _ _ = `(False) -- TODO revisit this
-- compareInnards (IImplicitApp x y z w) (IImplicitApp x' y' z' w') = ?compareInnards_rhs_93
-- compareInnards (IWithApp x y z) (IWithApp x' y' z') = ?compareInnards_rhs_10


-- Did our constructor match
-- If so we need to compare their constituents
isConPat : (con : TTImp) -> (b : TTImp) -> Clause
isConPat con b = PatClause EmptyFC con (compareInnards con b)
-- isConPat con b = PatClause EmptyFC con `(True)
--                            e.g. Biz => True


-- when it did not
elseFalse : Clause
elseFalse = PatClause EmptyFC `(_) `(False)
--                         e.g. _ => False

-- compare the `con` we have against what `b` could be, matches or it's False
eqConClause : (lhs : TTImp) -> (rhs : TTImp) -> (rhs_ty : TTImp) -> Clause
eqConClause con b ty = PatClause EmptyFC
                      -- con (ICase EmptyFC b ty [isConPat con b, elseFalse])
                      con (ICase EmptyFC b ty [isConPat con b, elseFalse])
              -- e.g. Biz => case b of
              --               Biz => True
              --               _   => False

-- The body of (==)
eqDef : (ty : TTImp) -> List TTImp -> TTImp -> TTImp -> TTImp
eqDef ty cons a b = ICase EmptyFC a ty
              (map (\c => eqConClause c b ty) cons)
          -- e.g. case a of
          --        Biz => case b of
          --                 Biz => True
          --                 _   => False
          --        Baz => case b of
          --                 Baz => True
          --                 _   => False

iVar : Name -> TTImp
iVar n = IVar EmptyFC n

iBindVar : String -> TTImp
iBindVar n = IBindVar EmptyFC n

infixl 6 `iApp`
iApp : TTImp -> TTImp -> TTImp
iApp x y = IApp EmptyFC x y

implicit' : TTImp
implicit' = Implicit EmptyFC True

patClause : (lhs : TTImp) -> (rhs : TTImp) -> Clause
patClause = PatClause EmptyFC

iPi : Count -> PiInfo TTImp -> Maybe Name ->
      (argTy : TTImp) -> (retTy : TTImp) -> TTImp
iPi = IPi EmptyFC

-- export is default for now, expect that to change/be customizable
eqDecl : TTImp -> List TTImp -> Elab ()
eqDecl ty vars
  = declare `[ export
               (==) : ~(ty) -> ~(ty) -> Bool
               (==) x y = ~(eqDef ty vars `(x) `(y)) ]

export
deriveEq : (n : Name) -> Elab ()
deriveEq n = do cons@(_::_) <- getCons n
                  | [] => fail $ show n ++ " doesn't have constructors to equate"
                traverse (\x => logMsg 1 (show x)) cons
                eqDecl (iVar n) (map iVar cons)

export
data New : Type -> Type where
  MkNew : a -> New a

export
data New2 : Type -> Type -> Type where
  MkNew2 : a -> b -> g => (a,b) -> {j : a} -> New2 a b

export
data New2' : Type -> Type -> Type where
  MkNew21 : a -> b -> g => (a,b) -> {j : a} -> New2' a b
  MkNew22 : a -> (a,b) -> New2' a b
  MkNew23 : New2' a b

export
data New3 : Type -> {f : Type} -> Type -> Type where
  MkNew3 : a -> b -> g => (a,b) -> {j : a} -> New3 a {f=b} b

getArity : TTImp -> Maybe Nat
getArity (IPi _ _ ExplicitArg _ _ retTy) =  S <$> getArity retTy
getArity (IPi _ _ _ _ _ retTy) = getArity retTy -- skip implicit args
getArity (IType x) = Just Z
getArity _ = Nothing

-- given some name and arity, give filled type and required implicits
-- e.g. Foo : Type -> Type -> Type -> Type  =>  Foo ty3 ty2 ty1 : Type
-- e.g. Foo : Type =>  Foo : Type
fillType : Name -> Nat -> Elab (TTImp, List Name)
fillType n 0 = pure (iVar n, [])
fillType n (S 0) = do v <- genSym $ "ty0"
                      pure $ (IApp EmptyFC (iVar n) (iBindVar (show v)), [v])
fillType n (S k) = do v <- genSym $ "ty" ++ show k
                      (ty,imps) <- fillType n k
                      pure $ (IApp EmptyFC ty (iBindVar (show v)), v :: imps)

getExplicitArgs : Name -> Elab (List Name)
getExplicitArgs n = do [(_,nimp)] <- getType n
                         | _ => fail $ show n ++ " is not unique in scope"
                       getEArgs nimp
  where
    getEArgs : TTImp -> Elab (List Name)
    getEArgs (IPi _ _ ExplicitArg _ _ retTy)
      = [| genSym "arg" :: getEArgs retTy |]
    getEArgs (IPi _ _ _ _ _ retTy) = getEArgs retTy -- skip implicit args
    getEArgs _ = pure []

-- TODO Claim should scan for what constructors are explicitly used to determine Eq
genClaim : (ty : Name) -> TTImp -> Elab Decl
genClaim n nimp     = do Just k <- pure (getArity nimp)
                           | Nothing => fail $ show n ++ " arity check failed"
                         -- here we should scan the data constructors for what
                         -- is used as explicit arguments, this will tell us
                         -- what Eq we need. TODO
                         (ty,imps) <- fillType n k
                         [feb] <- pure `[ export
                                          (==) : ~(ty) -> (~ty) -> Bool ]
                           | _ => fail $ "code error in genClaim"
                         pure feb
-- ]`
-- Extract the explicit args for our constructor, since we're comparing two we
-- do it twice to generate fresh names for each. We use those names to
-- construct the rhs comparisons and wrap it all up in a clause.
genClause : (opname : Name) -> (con : Name) -> Elab Clause
genClause op con = do
    [(_,conimp)] <- getType con
      | _ => fail $ show con ++ " is not unique in scope"
    conargs1 <- getExplicitArgs con
    conargs2 <- getExplicitArgs con
    let rhs = zipCompare conargs1 conargs2
        lhs = iVar op `iApp` foldIApp con conargs1 `iApp` foldIApp con conargs2
    pure $ patClause lhs rhs
  where
    anded : Name -> Name -> TTImp
    anded x y = `((&&)) `iApp` (iVar x) `iApp` (iVar y)
    
    zipCompare : List Name -> List Name -> TTImp
    zipCompare [] [] = `(True)
    zipCompare (x :: xs) (y :: ys) = anded x y `iApp` zipCompare xs ys
    zipCompare _  _ = `( () ) -- TODO can't happen, should prob use Vect
    
    foldIApp : Name -> List Name -> TTImp
    foldIApp con args
      = foldl (\term,arg => term `iApp` (iBindVar (show arg))) (iVar con) args

-- generate the clauses for ==
genClauses : (opname : Name) -> (cons : List Name) -> Elab Decl
genClauses op cons = do cls <- traverse (genClause op) cons
                        pure $ IDef EmptyFC op cls

-- name _ _ = False
catchAll : Name -> Elab Decl
catchAll n = do let lhs = iVar n `iApp` implicit' `iApp` implicit'
                pure $ IDef EmptyFC n [PatClause EmptyFC lhs `(False)]
-- I'd like to write `[ ~(iVar n) _ _ = False ] but there seems to be issues
-- With it wanting not wanting to 'apply' ~(iVar n)

deriveEp : (n : Name) -> Elab ()
deriveEp n = do [(tyn,tyimp)] <- getType n
                  | _ => fail $ show n ++ " is not unique in scope"
                cons@(_::_) <- getCons n
                  | [] => fail $ show n ++ " doesn't have constructors to equate"
                Just k <- pure (getArity tyimp)
                  | Nothing => fail $ show n ++ " arity check failed"
                c <- genClaim tyn tyimp
                cs <- genClauses `{{(==)}} cons
                e <- catchAll `{{(==)}}
                declare $ [c,cs,e]


-- %runElab deriveEp `{{Language.Elab.Deriving.New}}

-- use variable lookup to pass `(Foo) or `{{Foo}}` instead and lookup Language.Elab.Deriving.Foo
namespace Foo
  %runElab (deriveEq `{{Language.Elab.Deriving.Foo}})
  -- Latest version of making ==, allowing your choice of type.

  borb1 : Biz == Baz = False
  borb1 = Refl

  borb2 : Biz == Biz = True
  borb2 = Refl

  borb3 : Baz == Baz = True
  borb3 = Refl

-- If you try proofs here yourself I think idris2 doesn't do well with private
-- definitions in a namespace. This is why Zab and (==) are marked public
-- export, it's not at all really neccesary it's just a namespacing bug.
namespace Zab
  public export
  data Zab : Type where
    Zib : Zab
    Zyb : Zab
    Zob : Zab
    Zub : Zab
    Zeb : Zab
  
  -- The meat
  %runElab deriveEq `{{Language.Elab.Deriving.Zab.Zab}}

  {- -- written yourself
  (==) : Zab -> Zab -> Bool
  (==) Zib Zib = True
  (==) Zyb Zyb = True
  (==) Zob Zob = True
  (==) Zub Zub = True
  (==) Zeb Zeb = True
  (==) _ _     = False
  -}

  borb1 : Zib == Zib = True
  borb1 = Refl
 
  borb2 : Zob == Zob = True
  borb2 = Refl

  borb3 : Zeb == Zyb = False
  borb3 = Refl


