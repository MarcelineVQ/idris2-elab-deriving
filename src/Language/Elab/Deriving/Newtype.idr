module Language.Elab.Deriving.Newtype

import Language.Reflection

import Language.Elab.Syntax

import Language.Elab.Types

import Util


-- newtype deriving
-- given a datatype name and a list of interface names, determine if it's a
-- newtype, determine if the type it's a newtype of has those instances,
-- generate them for the newtype.

-- Visibility is controlled by the user because this makes it easy enough to
-- have instances that we might want to derive them just for a private use.

%language ElabReflection


-- A more specific List for holding interface identifiers.
-- Interface identifiers are hardly ever going to be simply Type so if we want
-- to collect them we need to hold their type.
data IList : List Type -> Type where
  Nil : IList []
  (::) : (x : r) -> IList rs -> IList (r :: rs)

-- Convert our list of interfaces to qualified Names, vet them at the same time
-- for suitability for deriving. This might be the wrong place to do this check.
collectIList' : IList xs -> Elab (List (Name, (Name, List ArgInfo, TTImp)))
collectIList' [] = pure []
collectIList' (i :: is) = do
    IVar _ w <- quote i
      | _ => fail "Error with reflecting interface name in collectIList."

    -- do a tentative check that we have a valid interface
    -- namely that we're dealing with a one-constructor type and that it has
    -- only one spot let to fill, since our type fills it
    tyinfo <- makeTypeInfo w -- kinda slow
    -- (qn,imp) <- lookupName w
    unless (length (filter (isExplicitPi . piInfo) tyinfo.args) == 1)
           $ fail $ (notApro tyinfo.name)
               ++ " It has more than one type argument left to fill."
    [singlecon] <- pure $ tyinfo.cons
      | _ => fail $ (notApro tyinfo.name)
               ++ " It has more than one constructor. " ++
                  "Interfaces are essentialy records of fields."
    
    pure $ (tyinfo.name, singlecon) :: !(collectIList' is)
  where
    notApro : Name -> String
    notApro n
      = extractNameStr n ++ " is not an appropriate type for newtype deriving."
    oneFillable : TTImp -> Bool
    oneFillable imp = go imp == 1
      where
        go : TTImp -> Int
        go (IPi _ _ ExplicitArg _ _ retTy) = 1 + go retTy
        go (IPi _ _ _ _ _ retTy) = go retTy
        go _ = 0

data Foo : Type where
  MkFoo : Int -> Foo

data Foo2 : Type -> Type where
  MkFoo2 : a -> Foo2 a

interface Fez r where
  fezfo1 : r -> r -> r
  fezfo2 : r -> r

Fez Int where
  fezfo1 x y = y*2
  fezfo2 x = x+1

interface Monad a => Fez2 a (r : Type) where
  constructor Fezfoborbo
  method : a Int
  -- fezfo12 : r -> r -> r
  -- fezfo22 : r -> r

interface Gorp2 a where
  constructor MkGorp2
  fap : a -> (named : Int) -> a -> Bool
  fapo : Bool -> (1 x : a) -> Char -> a
  ofap : (0 _ : a) -> Char
  o : a
  p : Char
  q : Foo2 Bool

interface Gorp3 a (b : Nat) where
  constructor MkGorp3
  p2 : a -> Char

Gorp2 Int where
  fap x i y = x == i
  fapo b a c = a
  ofap a = 'c'
  o = 9
  p = 'p'

record Wok a where
  constructor MkWok
  bopa : a -> Int
  fifw : Int -> Char -> a

record Poo where
  constructor Wup
  bop : Int
  fif : Int -> Char

export
interface MyEq a where
  constructor MkMyEq
  eq : a -> a -> Bool
  neq : a -> a -> Bool

MyEq Int where
  eq x y = x == y
  neq x y = x /= y

%hint
fooMyEq : MyEq Foo
fooMyEq = MkMyEq (\(MkFoo x),(MkFoo y) => eq x y) (\(MkFoo x),(MkFoo y) => neq x y)

interface Gaffer where
  constructor Gaf
-- Gaf : Language.Elab.Deriving.Newtype.Gaffer

-- this is where we accum our parameters, split up the fields
-- collect our arg type names then
-- spider along and make left pi args into fields
-- our return type is the deciding parameter name and a list of fields
separateFields : TTImp -> Elab (Name, List (Name, TTImp))
separateFields (IPi _ _ ImplicitArg (Just det) (IType _) retTy) = do
    fs <- sepFields retTy
    pure $ (det, fs)
  where
    sepFields : TTImp -> Elab (List (Name, TTImp))
    sepFields (IPi _ _ _ name0 argTy retTy) = do
      Just name <- pure name0
        | _ => fail "Unexpected empty field name."
      rest <- sepFields retTy
      pure $ (name,argTy) :: rest
    sepFields retTy = pure []
separateFields _ = fail "Interface has the wrong shape."

-- I'm having issue with taking an arg at a time, take all the args then case
-- one at a time.
-- TODO, this works, so clean it up majorly.
-- NB implicit'' which might be nice to use elsewhere too
ntWrapField : (ntty : TTImp) -> (ntcon : Name) -> (wrappedty : TTImp)
           -> (det : Name) -> (fname : Name) -> (fimp : TTImp) -> Elab TTImp
ntWrapField ntty ntcon wrappedty det fname fimp = mkFun fimp
  where
    isWrappedType : TTImp -> Bool
    isWrappedType (IVar _ n) = n == det
    isWrappedType _ = False
    
    mkLam : List Name -> TTImp -> Elab TTImp
    mkLam ns (IPi _ c ExplicitArg nam argTy retTy) = do
      argname <- genSym "lam"
      let lamhead = iLam c ExplicitArg (Just argname)
      if  isWrappedType argTy
        then do
          argname' <- readableGenSym "lamc"
          cont <- mkLam (argname' :: ns) retTy
          pure $ lamhead implicit'' $ iCase (iVar argname) implicit''
                [patClause `( ~(iVar ntcon) ~(bindNameVar argname')) cont]
        else pure $ lamhead implicit'' !(mkLam (argname :: ns) retTy)
    mkLam ns (IPi _ _ _ _ _ retTy) = mkLam ns retTy
    -- Apply our field name to our collected args, we check the return
    -- type, since if it is wrapper type we should be wrapping the expression
    mkLam ns retTy = do
      let appedifacecon = IImplicitApp EmptyFC (iVar fname) (Just det) wrappedty
      -- let appedifacecon = (iVar fname)
      let body = foldr (\n,tt => tt `iApp` iVar n) appedifacecon ns
      pure $ if isWrappedType retTy
        then iVar ntcon `iApp` body
        else body
    -- mkCases : List Name -> TTImp
    -- If our field type has no argument, check if we should wrap the result type
    mkFun : TTImp -> Elab TTImp
    mkFun (IVar _ n) = pure $ if n == n then iVar ntcon `iApp` iVar fname else iVar fname
    mkFun pi@(IPi _ _ _ _ _ _) = mkLam [] pi
    mkFun _ = pure $ iVar fname


-- Derive via taking an object and spidering it, we can't get an instance object
-- programatically yet but it's probably a bug that we can't, so let's bet on
-- that changging.
-- We need the ntname, ntcontypimpl, iface name, iface conname, iface objimpl
deriveGeneralImpl : (ntname : Name) -> (nttype : TTImp) -> Visibility
                 -> (ntcon : Name) -> (wrappedtype : TTImp) -> (Name, (Name, List ArgInfo, TTImp)) -> Elab ()
deriveGeneralImpl ntname nttype vis ntcon wrappedty (iname,icon)  = do
  let defname = UN ("ntImpl_" ++ extractNameStr ntname ++ extractNameStr iname)
      hty = mkTy defname (iVar iname `iApp` nttype)
      head = iClaim MW vis [Hint True] hty
  (_,impl) <- lookupName iname
  fillty <- makeTypeInfo iname
  [arg] <- pure fillty.args
    | _ => fail "badshape"
  (_,conimp) <- lookupName icon.one
    | _ => fail "sdfsdf"
  (det,fields) <- separateFields conimp
  wrappedfs <- traverse (\(fname,imp) => ntWrapField nttype ntcon wrappedty det fname imp) fields
  
  let cac = foldl (\tt,f => tt `iApp` f) (iVar icon.one) wrappedfs
      def = iDef defname [patClause (iVar defname) cac]

  logDecls 1 "def" [head,def]
  
  declare [head,def]
  
  pure ()


-- we determine if we have a newtype constructor ourselves but we could just ask
-- idris as well since that info is in the Context
newtypeDerive : Name -> Visibility -> (ifaces : IList ts) -> Elab ()
newtypeDerive n vis ilist = do
    -- We need to very carefully check ifsomething is a newtype, otherwise we've
    -- lied.
    typeinfo <- makeTypeInfo n
    [con] <- pure $ typeinfo.cons
      | _ => fail notNT
    -- check that our constructor has the right form
    [arg] <- pure $ filter (not . isUse0 . count
                          && isExplicitPi . piInfo) con.two
      | _ => fail notNT

    -- Here we validate our list of interfaces
    ns@(_::_) <- collectIList' ilist
      | [] => fail "Interface list for deriving was empty."

    -- traverseE (deriveSpecialImpl ...) ns
    -- ^ things like Show should farm out to Show deriving

    traverseE (deriveGeneralImpl n typeinfo.type vis con.one arg.type) ns

    pure ()
  where
    notNT : String
    notNT = extractNameStr n ++ " is not a newtype. A newtype has exactly one
                                  constructor with exactly one used field."
 
%runElab newtypeDerive `{{Foo}} Private [Eq]
-- %runElab newtypeDerive `{{Foo}} Private [Gorp2, Eq, Ord]
-- %runElab newtypeDerive `{{Foo}} Private [Eq, Ord]

-- ntElim_Foo : (x : Foo) -> MkFoo x = x
-- ntElim_Foo x = ?laf_rhs

-- <int-e> @let ifM b t f = b >>= \b' -> if b' then t else f
-- <int-e> :t ifM even negate (const 0)

lef : Ord Int
lef = %search

rer : Ord Foo
rer = let r = the (Ord Int) %search
      in ?SDFfds

-----------------------------
-- Testing
-----------------------------

data Foo1 : Type where -- newtype, one con, one used field
  MkFoo1 : Int -> Foo1

-- data Foo2 : Type where 
  -- MkFoo2 : Char -> Int -> Foo2 -- not nt, two used fields

data Foo3 : Type -> Type where -- newtype
  MkFoo3 : Int -> Foo3 a

data Foo4 : Type -> Type where -- not nt, two cons
  MkFoo4 : a -> Foo4 a
  MkFoo4' : a -> Foo4 a

data Foo5 : Type -> Type -> Type where -- newtype, one used field
  MkFoo5 : a -> (0 _ : b) -> Foo5 a b

-- little ugly here
-- %runElab newtypeDerive `{{Foo1}} [`{{Eq}}, `{{Show}}, `{{Ord}}]

-- Foo2 is not a newtype
-- %runElab newtypeDerive `{{Foo2}} [`{{Eq}}, `{{Show}}, `{{Ord}}]

-- %runElab newtypeDerive `{{Foo3}} [`{{Eq}}, `{{Show}}, `{{Ord}}]

-- Foo4 is not a newtype
-- %runElab newtypeDerive `{{Foo4}} [`{{Eq}}, `{{Show}}, `{{Ord}}]

-- %runElab newtypeDerive `{{Foo5}} [`{{Eq}}, `{{Show}}, `{{Ord}}]

-- Wibble isn't in scope
-- %runElab newtypeDerive `{{Foo1}} [`{{Eq}}, `{{Show}}, `{{Ord}}, `{{Wible}}]
