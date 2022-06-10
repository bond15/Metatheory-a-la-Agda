{-# OPTIONS --guardedness #-}
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}
module TypeClassInstances where 
    open import FreeMonad 
    open import Data.List
    open import IO
    
    instance 
        list-F : Functor List 
        list-F = record { fmap = map }

        list-M : Monad List 
        list-M = record { return = [_] ; _>>=_ = λ xs f → concatMap f xs }

        -- This is the only thing that requires the --type-in-type flag
        -- IO : Set ℓ → Set (suc ℓ)
        io-M : Monad IO 
        io-M = {!   !}
