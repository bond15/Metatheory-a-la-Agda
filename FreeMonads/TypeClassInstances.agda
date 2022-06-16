{-# OPTIONS --guardedness #-}
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}
module TypeClassInstances where 
    open import FreeMonad 
    open import Data.List
    open import IO renaming (_>>=_ to _>>IO=_; return to returnIO)
    open Functor
    open Monad
    
    instance 
        list-F : Functor List 
        list-F = record { fmap = map }

        list-M : Monad List 
        list-M = record { return = [_] ; _>>=_ = λ xs f → concatMap f xs }

        -- This is the only thing that requires the --type-in-type flag
        -- IO : Set ℓ → Set (suc ℓ)
        io-M : Monad IO 
        io-M ._>>=_ = _>>IO=_
        io-M .return = returnIO

        io-F : Functor IO 
        io-F .fmap f ioa = ioa >>IO= λ a → returnIO (f a)
