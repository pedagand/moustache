> {-# LANGUAGE StandaloneDeriving #-}

> module EvalTraced where

Strictly-positive expressions:

> data Exp 
>     = Val Int
>     | Add Exp Exp
>     -- Potentially failing operation:
>     | Div Exp Exp
>       deriving Show

> data ExpP a 
>     = ValP Int
>     | AddP a a 
>     | DivP a a

> data ExpD l r 
>     = AddL l
>     | AddR r
>     | DivL l 
>     | DivR r

> deriving instance Show a => Show (ExpP a)
> deriving instance (Show a, Show b) => Show (ExpD a b)

> data Result 
>     = Value Int
>     | Err Error
>       deriving Show

> data Error 
>     = Div0 Int 
>     | Frame (ExpD Int Exp) Error
>       deriving Show

> type ExpAlgebra a = ExpP a -> Either Int a

> load :: ExpAlgebra Int -> Exp -> [ExpD Int Exp] -> Result
> load alg (Val n) stack = unload alg n stack
> load alg (Add e1 e2) stack = load alg e1 (AddR e2 : stack)
> load alg (Div e1 e2) stack = load alg e1 (DivR e2 : stack)

> unload :: ExpAlgebra Int -> Int -> [ExpD Int Exp] -> Result
> unload alg m [] = Value m
> unload alg m (AddR e : st) = load alg e (AddL m : st)
> unload alg m (AddL n : st) = catch alg (alg (AddP m n)) st
> unload alg m (DivR e : st) = load alg e (DivL m : st)
> unload alg m (DivL n : st) = catch alg (alg (DivP n m)) st

> catch :: ExpAlgebra Int -> Either Int Int -> [ExpD Int Exp] -> Result
> catch alg (Left n) st = unload alg n st
> catch alg (Right e) st = Err $ raise (Div0 e) st

> raise :: Error -> [ExpD Int Exp] -> Error
> raise err [] = err
> raise err (frame : st) = raise (Frame frame err) st

> eval :: Exp -> Result
> eval e = load (\ p -> case p of 
>                         AddP m n -> Left (m + n)
>                         DivP m n | n == 0 -> Right m
>                                  | otherwise -> Left (div m n)) e []

> main = do
>    putStrLn $ show $ eval (Add (Val 1) (Div (Val 4) (Add (Val 1) (Val 1))))
>    putStrLn $ show $ eval (Add (Val 1) (Div (Val 4) (Add (Val 0) (Val 0))))


