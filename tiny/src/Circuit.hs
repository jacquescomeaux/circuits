module Circuit () where

import RIO

import Data.Kind


data Nat = Zero | Succ Nat | Plus Nat Nat

data Env :: Nat -> Type -> Type where
    Leaf :: Env Zero a
    Cons :: a -> Env n a -> Env (Succ n) a
    Node :: Env l a -> Env r a -> Env (Plus l r) a

data Circuit :: Nat -> Type -> Type where
    Con :: Int -> Circuit Zero t
    Var :: t -> Circuit Zero t
    Add :: Circuit m t -> Circuit n t -> Circuit (Plus m n) t
    Let :: Circuit m t -> (t -> Circuit n t) -> Circuit (Plus m n) t
    Fix :: (t -> Circuit n t) -> Circuit n t
    Reg :: Circuit n t -> Circuit (Succ n) t

eval :: (Circuit n Int, Env n Int) -> Int
eval (Con i    ,        _) = i
eval (Var x    ,        _) = x
eval (Add e1 e2, Node l r) = eval (e1, l) + eval (e2, r)
eval (Let e1 e2, Node l r) = eval (e2 (eval (e1, l)), r)
eval (Fix e    ,      env) = fix (\x -> eval (e x, env))
eval (Reg _    , Cons v _) = v

step :: (Circuit n Int, Env n Int) -> Env n Int
step (Con i    ,        _)  = Leaf
step (Var x    ,        _)  = Leaf
step (Add e1 e2, Node l r)  = Node (step (e1, l)) (step (e2, r))
step (Let e1 e2, Node l r)  = Node (step (e1, l)) (step (e2 (eval (e1, l)), r))
step (Fix e    ,      env)  = step (fix (\e' -> e (eval (e', env))), env)
step (Reg e    , Cons _ vs) = Cons (eval (e, vs)) (step (e, vs))

acc i = Fix (\x -> Reg (Add (Var x) (Var i)))
fib = Fix (\x -> Reg (acc x))
pipe = Reg (Reg (Reg (Reg (Reg (Reg (Con 6))))))
