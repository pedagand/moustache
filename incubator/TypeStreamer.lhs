> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module TypeStreamer where

> import Data.Functor

> import Control.Applicative
> import Control.Monad


* Strictly non-empty streams:

> infixr 9 :@:
> data StrP a 
>     = One a
>     | (:@:) a  (StrP a)
>       deriving Functor

The derived functor instance is not too strict:

> test :: StrP Int
> test = 1 :@: ((\ x -> x + 1) <$> test)

> test2 :: StrP Int
> test2 = (\ x y -> x + y) <$> test <*> test

** From positive streams to lists:

> prefix :: Int -> StrP a -> [a]
> prefix 0 _ = []
> prefix n (One a) = [a]
> prefix n (a :@: xs) = a : prefix (n-1) xs

** A Stream is a monad:

Because I'm a smartass, I try to balance the two streams:

> union :: StrP a -> StrP a -> StrP a
> union (One x) ys = x :@: ys
> union xs (One y) = y :@: xs
> union (x :@: xs) (y :@: ys) = x :@: y :@: (union xs ys) 

> instance Monad StrP where
>     return = One
>     (>>=) = bind
>         where bind :: StrP a -> (a -> StrP b) -> StrP b
>               bind (One a) f = f a
>               bind (x :@: xs) f = union (f x) (bind xs f)

Remark: a Monad is also an Applicative

> instance Applicative StrP where
>     pure = return
>     (<*>) = ap

|(<*>)| is not too strict:

> test5 = ((\x -> x + 1) :@: One (\x -> x + 3)) <*> test 

> test6 = (help 4) <*> (1 :@: 2 :@: 3 :@: 4 :@: One 5)
>     where help i = (\x -> x + i) :@: help (i+1)

** Distributivity law |StrP . Maybe -> Maybe . StrP|:

Quite frankly, this code is not exactly the one I was expecting. The
"natural" one (the one derived by Haskell's Traversable) is too
strict.

> seqS :: StrP (Maybe a) -> Maybe (StrP a)
> seqS (One (Nothing)) = Nothing
> seqS (One (Just a)) = Just (One a)
> seqS (Nothing :@: xs) = seqS xs
> seqS (Just a :@: xs) = 
>     Just $ case seqS xs of
>              Nothing -> One a
>              Just xs -> a :@: xs

> forStr :: StrP a -> (a -> Maybe b) -> Maybe (StrP b)
> forStr xs f = seqS (fmap f xs)


This implementation of |seqS| is not too strict:

> test3 :: Maybe (StrP Int)
> test3 = seqS $ (\x -> if odd x then Just x else Nothing) <$> test

> test4 :: Maybe (StrP Int)
> test4 = seqS $ Just <$> (1 :@: 2 :@: 3 :@: 4 :@: One 5)

> test41 :: Maybe (StrP Int) 
> test41 = seqS $ Just <$> test

> test42 :: Maybe (StrP Int)
> test42 = seqS $ Just 4 :@: One Nothing

* STLC, Curry-style:

> data Type
>     = Unit
>     | (:->:) Type Type
>       deriving (Show, Eq)

> data Term 
>     = Var Int
>     | App Term Term
>     | Lam Term
>     | Void

* Type-checking over streams of types:

A successful run of the typechecker returns a (non-empty, potentially
infinite) list of types:

> type Types = StrP Type

For instance, here are all the types one can ever dream of:

> allTypes :: Types
> allTypes = Unit :@: ((:->:) <$> allTypes <*> allTypes)

> allTypesB :: Int -> Types
> allTypesB 0 = One Unit
> allTypesB k = Unit :@: ((:->:) <$> allTypesB (k-1) <*> allTypesB (k-1))

The outcome of the typechecker is either a failure (no type can be
given), or a list of possible types:

> type Outcome = Maybe Types

** Typing environment and variable lookup:

> type Env = [Type]

> (!!!) :: Env -> Int -> Maybe Types
> [] !!! _ = Nothing
> (ty : _) !!! 0 = return $ One ty
> (_ : tys) !!! n = tys !!! (n - 1)

** Typechecker:

> typecheck :: Env -> Term -> Outcome
> typecheck env Void = return (One Unit)
> typecheck env (Var i) = env !!! i
> typecheck env (Lam b) = do
>   -- The domain can be *any* type:
>   let dom = allTypesB 3 
>   -- Foreach domain type, compute the codomain:
>   tys <- forStr dom $ \ domTy -> do
>      -- Infer the codomain at some domain type:
>      cod <- typecheck (domTy : env) b
>      -- Pair up |dom| and |cod|:
>      return $ ((domTy :->:) <$> cod)
>   -- Merge all results:
>   return $ join tys
> typecheck env (App f s) = do
>     -- Infer the type of the function:
>     tyf <- typecheck env f 
>     -- Infer the type of the argument
>     tys <- typecheck env s
>     -- Match them up:
>     let tyr = app <$> tyf <*> tys
>     -- Force one positive result, or fail:
>     seqS $ tyr
>         where app :: Type -> Type -> Maybe Type
>               app (a :->: b) c = do
>                   guard (a == c)
>                   return b
>               app f s = Nothing

* Examples:

> t0 = typecheck [] Void
> t1 = typecheck [] (Lam (Var 0))
> t2 = typecheck [] (App (Lam (Var 0)) Void)
> t3 = typecheck [] (App Void Void)
> t4 = typecheck [] (App (App (Lam (Var 0)) Void) Void)

> tests = zip [0..] [t0, t1, t2, t3, t4]

> showPrefix :: Int -> Outcome -> String
> showPrefix i = maybe "(nothing)" (show . prefix i)

> main = do
>   mapM_ (\(i, test) -> do
>         putStrLn $ "test (" ++ show i ++ "):"
>         putStrLn $ showPrefix 5 test)
>        tests
