module Util



import Language.Reflection.TT
import Language.Reflection.TTImp


-- export
-- data Elab : Type -> Type where
--      Pure : a -> Elab a
--      Bind : Elab a -> (a -> Elab b) -> Elab b
--      Fail : String -> Elab a
-- 
--      LogMsg : Nat -> String -> Elab ()
--      LogTerm : Nat -> String -> TTImp -> Elab ()
-- 
--      -- Elaborate a TTImp term to a concrete value
--      Check : {expected : Type} -> TTImp -> Elab expected
--      -- Quote a concrete expression back to a TTImp
--      Quote : val -> Elab TTImp
-- 
--      -- Elaborate under a lambda
--      Lambda : (0 x : Type) ->
--               {0 ty : x -> Type} ->
--               ((val : x) -> Elab (ty val)) -> Elab ((val : x) -> (ty val))
-- 
--      -- Get the current goal type, if known 
--      -- (it might need to be inferred from the solution)
--      Goal : Elab (Maybe TTImp)
--      -- Get the names of local variables in scope
--      LocalVars : Elab (List Name)
--      -- Generate a new unique name, based on the given string
--      GenSym : String -> Elab Name
--      -- Put a name in the current namespace
--      InCurrentNS : Name -> Elab Name
--      -- Get the types of every name which matches.
--      -- There may be ambiguities - returns a list of fully explicit names
--      -- and their types. If there's no results, the name is undefined.
--      GetType : Name -> Elab (List (Name, TTImp))
--      -- Get the type of a local variable
--      GetLocalType : Name -> Elab TTImp
--      -- Get the constructors of a data type. The name must be fully resolved.
--      GetCons : Name -> Elab (List Name)
--      -- Check a group of top level declarations
--      Declare : List Decl -> Elab ()
-- 
-- mutual
--   export
--   Functor Elab where
--     map f e = do e' <- e
--                  pure (f e')
-- 
--   export
--   Applicative Elab where
--     pure = Pure
--     f <*> a = do f' <- f
--                  a' <- a
--                  pure (f' a')
-- 
--   export
--   Monad Elab where
--     (>>=) = Bind

-- Monad f => Traversable List where
  -- traverse f [] = pure []
  -- traverse f (x :: xs) = f x >>= ?dfsd

-- Traversable Elab where
  -- traverse f 

-- export
-- traverseE : (a -> Elab b) -> List a -> Elab (List b)
-- traverseE f [] = pure []
-- traverseE f (x :: xs) = f x >>= \b => (b ::) <$> traverseE f xs
-- 
-- export
-- traverseE : (a -> Elab b) -> List a -> Elab (List b)
-- traverseE f [] = pure []
-- traverseE f (x :: xs) = f x >>= \b => (b ::) <$> traverseE f xs
-- traverseE' f [] = pure []
-- traverseE' f (x :: xs) = f x >>= \b => (b ::) <$> traverseE' f xs

-- export
-- traverseM : Traversable t => (a -> Elab b) -> t a -> Elab (t b)
-- traverseM f = foldr ?sdf Pure


infixl 1 <&>
export
(<&>) : Functor f => f a -> (a -> b) -> f b
x <&> f = f <$> x

export
catMaybes : List (Maybe a) -> List a
catMaybes z = foldr (\m,f => maybe f (\x => (x ::) . f) m) id z []

export
unzip : List (a,b) -> (List a, List b)
unzip = foldr (\(x,y),(xs,ys) => (x :: xs, y :: ys)) ([],[])

export
unzipM : Applicative f => List (f (a,b)) -> (f (List a), f (List b))
unzipM [] = (pure [], pure [])
unzipM (x :: xs) = let (xs,ys) = unzipM xs
                       l = fst <$> x
                       r = snd <$> x
                   in ( [| l :: xs |] , [| r :: ys |] )

-- this really eats compiler time :/
export
whackUnzipM : Monad f => List (f (a,b)) -> (List (f a), List (f b))
whackUnzipM [] = ([], [])
whackUnzipM (x :: xs) = let (xs,ys) = whackUnzipM xs
                        in ( map fst x :: xs, map snd x :: ys)

-- unzipM = foldr (\(x,y),(xs,ys) => (x :: xs, y :: ys)) ([],[])

-- This is hiiiiiideously slow!
-- Even when written with explicit arg passing instead of let recursion
export
unzip3 : List (a,b,c) -> (List a, List b, List c)
unzip3 [] = ([],[],[])
unzip3 ((x, (y, z)) :: ls) = let (xs,ys,zs) = unzip3 ls
                             in (x :: xs, y:: ys, z :: zs)


export
isJust : Maybe a -> Bool
isJust (Just _ ) = True
isJust _ = False
