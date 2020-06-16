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

-- What we do is first ensure we have a newtype, then an appropriate interface,
-- and we reflect a %search of the type our newtype wraps then type-coerce it.

-- This is a bit scummy compared to honest elaboration but forgive me, it works,
-- I don't quite have a method to grab the implementation of something like
-- :printdef does or a methd of run a search _in elaboration_ and while I can
-- 'quote' a completed %search, e.g.
-- res <- quote $ the (Eq Int) %search
-- I'd have to give it a resolved type to search (not a variable) and I'm not
-- sure how to do that programatically.
-- What we have here works but it doesn't make for super nice expressions
-- because newtypes aren't erased down until compile-time. I still want to
-- 

%language ElabReflection

foo : (sometype : TTImp) -> (iname : Name) -> Elab ()
foo sometype iname  = do
    let h = %runElab check goodExpr
    -- let i = %runElab check badExpr -- comment me to see the logged output
    logMsg  1 $ "interface: " ++ show iname
    logTerm 1 "type" $ sometype
    logTerm 1 "gt" goodType -- Exactly the same!
    logTerm 1 "bt" badType  -- Exactly the same!
    logTerm 1 "ge" goodExpr -- Exactly the same.
    logTerm 1 "be" badExpr  -- Exactly the same.
    
    r <- quote h
    logTerm 1 "r" r -- A check to see we really reflected a completed search
                    -- And that we don't just have a TTImp of ISearch
    pure ()
  where
    goodType : TTImp
    goodType = `(Prelude.Ord Int)

    goodExpr : TTImp
    goodExpr = `(the ~(goodType) %search)

    -- This will say "Can't reify as TTImp" if I don't give it a type signature,
    -- now instead this will say "Can't reify as Name"
    badType : TTImp
    badType = `(~(IVar EmptyFC iname) ~(sometype))

    badExpr : TTImp
    badExpr = `(the (~(badType)) %search)

%runElab foo `(Int) `{{Prelude.Ord}}





bop : TTImp
bop = `(Prelude.Ord Int)

bep : TTImp
bep = `(the ~(bop) %search)

frap : Elab ()
frap = do
  -- j <- check bep
  let h = %runElab check bep
  -- logTerm 1 "bep" bep
  -- r <- quote j
  r2 <- quote h
  -- logTerm 1 "j" r
  logTerm 1 "j2" r2
  pure ?psdfsd

%runElab frap

-- A more specific List for holding interface identifiers.
-- Interface identifiers are hardly ever going to be simply Type so if we want
-- to collect them we need to track their type.
data IList : List Type -> Type where
  Nil : IList []
  (::) : (x : r) -> IList rs -> IList (r :: rs)

-- Convert our list of interfaces to qualified Names, vet them at the same time
-- for suitability for deriving. This might be the wrong place to do this check.
collectIList : IList xs -> Elab (List Name)
collectIList [] = pure []
collectIList (i :: is) = do
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
    
    pure $ tyinfo.name :: !(collectIList is)
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
  -- constructor MkGorp2
  fap : a -> Int -> a -> Bool
  fapo : Bool -> (1 x : a) -> Char -> a
  ofap : (0 _ : a) -> Char
  o : a
  p : Char

Gorp2 Int where
  fap x i y = x == i
  fapo b a c = a
  ofap a = 'c'
  o = 9
  p = 'p'

deriveGeneralImpl : (ntname : Name) -> (nttype : TTImp) -> Visibility
                 -> (wrappedtype : TTImp) -> (iname : Name) -> Elab ()
deriveGeneralImpl ntname nttype vis wrappedty iname  = do
  let defname = UN ("ntImpl_" ++ extractNameStr ntname ++ extractNameStr iname)
      hty = mkTy defname (iVar iname `iApp` nttype)
      head = iClaim MW vis [Hint True] hty
  logDecls 1 "implhead" [head]
  
  -- What if I make my lambda for my type..
  -- No, because I need to know the arg count

  -- Is this %search repeated every call to our implementation? How do I do this
  -- search _in elaboration_ ?
  let left = iVar defname
      right = `(believe_me $ the (~(iVar iname `iApp` wrappedty)) %search)
      pat = patClause left right
      body = iDef defname [pat]
  logDecls 1 "implbody" [body]
  
  declare [head, body]
  
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
    ns@(_::_) <- collectIList ilist
      | [] => fail "Interface list for deriving was empty."

    -- traverseE (deriveSpecialImpl ...) ns
    -- ^ things like Show should farm out to Show deriving

    traverseE (deriveGeneralImpl n typeinfo.type vis arg.type) ns

    pure ()
  where
    notNT : String
    notNT = extractNameStr n ++ " is not a newtype. A newtype has exactly one
                                  constructor with exactly one used field."

%runElab newtypeDerive `{{Foo}} Private [Gorp2, Eq, Ord]

-- ntElim_Foo : (x : Foo) -> MkFoo x = x
-- ntElim_Foo x = ?laf_rhs


lef : Ord Int
lef = %search

rer : Ord Foo
rer = let r = the (Ord Int) %search
      in ?SDFfds

beb : (MkFoo 3 == MkFoo 9) = (the Int 3 == 9)
beb = ?beb_rhs

-----------------------------
-- Testing
-----------------------------

data Foo1 : Type where -- newtype, one con, one used field
  MkFoo1 : Int -> Foo1

data Foo2 : Type where 
  MkFoo2 : Char -> Int -> Foo2 -- not nt, two used fields

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
