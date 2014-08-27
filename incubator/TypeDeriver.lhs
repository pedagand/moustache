> module TypeDeriver where

A typechecker that spits its (unique) typing derivation.

> import Data.Functor

> import Control.Applicative
> import Control.Monad


* STLC, Church-style:

> data Type
>     = Unit
>     | (:->:) Type Type
>       deriving (Show, Eq)

> data Term 
>     = Var Int
>     | App Term Term
>     | Lam Type Term
>     | Void

** Typing environment and variable lookup:

> type Env = [Type]

> (!!!) :: Env -> Int -> Maybe Type
> [] !!! _ = Nothing
> (ty : _) !!! 0 = return $ ty
> (_ : tys) !!! n = tys !!! (n - 1)

* Derivations

A positive derivation is either an axiom or an inference rule. For
simplicity, rule names are strings:

> data Derivation 
>     = Axiom Rule
>     | Inference Rule [Derivation]
>       deriving Show
>
> type Rule = String

A negative derivation, ie. an error, is a list of unsuccessful
inferences (that ended with an error) terminated with a typechecking
incompatibility:

> data Error 
>     = EInference Rule [Derivation] Error {- [Term] -}
>     | Bad Err 
>       deriving Show
>
> data Err 
>     = AppMisDomain Type Type
>     | AppNotFun Type
>     | UnboundVar Int
>       deriving Show

* Typechecking monad

The outcome of our typechecker is a bit weird: not only will it return
an |Error| or a result |a| (second projection of |Outcome|), it also
collects the successful derivations it has computed so far (first
projection of |Outcome|):

> type Outcome a = ([Derivation], Either Error a)

The idea is that those collected derivations while be commited into
atomic rules every now and then (see the |atomic| command).

The typechecker runs in a monad offering access to an environment
(Reader monad), collecting derivations (Writer monad over a monoid),
and returning error (Exception monad):

> newtype TypingM a 
>     = TypingM { run :: Env -> Outcome a }

TODO: by the above description of |TypingM|, we could obtain all the
following operations thanks to a well-chosen monad transformer.


** Monadic structure of |TypingM|

Business as usual.

> ret :: a -> TypingM a
> ret a = TypingM $ \ _ -> ([], Right a)

> bind :: TypingM a -> (a -> TypingM b) -> TypingM b
> bind ma mf = TypingM $ \ env ->
>             case run ma env of
>               (ds, Left e) -> (ds, Left e)
>               (ds, Right a) -> 
>                   case run (mf a) env of
>                     (ds', Left e) -> (ds ++ ds', Left e)
>                     (ds', Right b) -> (ds ++ ds', Right b)

Remark: |bind| carefully threads/accumulates the derivations (|ds| and
|ds'|) in the Writer monad, collapsing them with the monoid action for
lists (++).

> instance Monad TypingM where
>     return = ret
>     (>>=) = bind

** Monadic operations of |TypingM|

First, we can build positive derivations. An axiom is a rule with no
premiss, ie. that always succeed (note the similarity with |return|):

> axiom :: Rule -> a -> TypingM a
> axiom s a = TypingM $ \ _ -> ([Axiom s], Right a)

An atomic action runs a monadic computation to completion and wraps it
up into an inference rule:

> atomic :: Rule -> TypingM a -> TypingM a
> atomic s f = TypingM $ \env ->
>              case run f env of
>                (ds, Left e) -> ([], Left $ EInference s ds e)
>                (ds, Right a) -> ([Inference s ds], Right a)

Second, we can trigger negative derivations by raising an error.

> raise :: Err -> TypingM a
> raise err = TypingM $ \env -> ([], Left $ Bad err)

Third, and as usual, we can fiddle with the environment:

> addEnv :: Type -> TypingM a -> TypingM a
> addEnv ty ma = TypingM $ \env -> run ma (ty: env)

> getEnv :: Int -> TypingM (Maybe Type)
> getEnv i = TypingM $ \env -> ([], Right $ env !!! i)

* Typechecker

Well, you know what I mean.

> typecheck :: Term -> TypingM Type
> typecheck Void = 
>   axiom "Void" Unit
> typecheck (Var i) = 
>   atomic "Var" $ do
>     mv <- getEnv i
>     case mv of
>       Just ty -> return ty
>       Nothing -> raise $ UnboundVar i
> typecheck (App f s) =
>   atomic "App" $ do 
>     fTy <- typecheck f
>     sTy <- typecheck s
>     case fTy of
>       sTy' :->: tTy | sTy' == sTy -> return tTy
>                     | otherwise -> raise $ AppMisDomain sTy' sTy
>       _ -> raise $ AppNotFun fTy
> typecheck (Lam sTy b) =
>     atomic "Lam" $ do
>       addEnv sTy $ do
>         bTy <- typecheck b
>         return $ sTy :->: bTy

* Tests

> tc :: Env -> Term -> Outcome Type
> tc env tm = run (typecheck tm) env 

> t0 = tc [] Void
> t1 = tc [] (Lam Unit (Var 0))
> t2 = tc [] (App (Lam Unit (Var 0)) Void)
> t3 = tc [] (App Void Void)
> t4 = tc [] (App (App (Lam Unit (Var 0)) Void) Void)

> tests = zip [0..] [t0, t1, t2, t3, t4]

> main = do
>   mapM_ (\(i, test) -> do
>         putStrLn $ "test (" ++ show i ++ "):"
>         putStrLn $ show $ test)
>        tests
