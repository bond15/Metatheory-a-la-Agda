{-# OPTIONS --guardedness #-}
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Interpretations where 
open import Level
open Level
open import DSLs
open import FreeMonad
open _~>_

module KeyValDSLI where
    open KeyValDSL
    
    open import Data.List
    open import Data.Maybe hiding (map;_>>=_)
    open import Data.String
    open import Data.Product hiding(map)
    open import IO hiding(return;_>>=_)

    open Monad{{...}}

    data State (S X : Set) : Set where 
        St : (S → X × S) → State S X 

    runSt : {S X : Set} → State S X → (S → X × S)
    runSt (St x) = x

    data StateT (S : Set) (M : Set → Set){{_ : Monad M}} (X : Set) : Set where 
        ST : (S → M (X × S)) → StateT S M X

    instance 
        list-F : Functor List 
        list-F = record { fmap = map }

        list-M : Monad List 
        list-M = record { return = [_] ; _>>=_ = λ xs f → concatMap f xs }

        state-F : {S : Set} →  Functor (State S) 
        state-F = record { fmap = λ{ f (St m) → St λ s → f (proj₁ (m s)) , s }}

        state-M : {S : Set} → Monad (State S)
        state-M = record { return = λ a → St λ s → a , s ; _>>=_ = λ { (St sa) f → (St λ s → let 
                                                                                                as = sa s
                                                                                                sb = f (proj₁ as)
                                                                                                in runSt sb (proj₂ as))}}

        stateT-F : {S : Set}{M : Set → Set}{{_ : Monad M}} → Functor (StateT S M)
        stateT-F = record { fmap = λ{ f (ST m) → ST (λ s → m s  >>= λ{ (a , s') → return (f a , s')}) }}

        stateT-M : {S : Set}{M : Set → Set}{{_ : Monad M}} → Monad (StateT S M)
        stateT-M = record { return = λ a → ST (λ s → return (a , s)) ; _>>=_ = λ{(ST x) f → {!   !} }}

        io-M : Monad IO 
        io-M = {!   !}
    
    -- use a monad transformer stack
    store : IO {!   !}
    store = {!   !}
    
    kvList : {S : Set} → KeyValF ~> StateT (List S) IO 
    kvList .α (GetKey k cb) = do  
                                
                                return {!   !}
    kvList .α (PutKey k v a) = {!   !}

    


module ConsolPrograms where 
    open ConsoleDSL
    open import Data.Unit
    open Monad{{...}}
    open import Function

    prog : Console ⊤
    prog = do 
            putStrLn "hello, please enter your name"
            name ← getLine 
            case name of λ{ "jimbo"  → putStrLn "Welcome Jimbo"; 
                            s        → putStrLn "Unauthorized access"}
            return tt


module ConsoleDSLI where 
    open ConsoleDSL

    open import IO
    open import Data.String

    instance
        io-F : Functor IO
        io-F = record { fmap = _<$>_ }
        
    
    consoleIO : ConsoleF ~> IO 
    consoleIO .α (PutStrLn s a) = do 
                                    IO.putStrLn s
                                    return a
    consoleIO .α (GetLine cb) = do 
                                 x ← IO.getLine
                                 return (cb x)
    


module EvalConsole where 
    open ConsoleDSL
    open ConsoleDSLI
    open ConsolPrograms

    open import Data.Unit
    open import IO
    
    ex : IO ⊤
    ex = foldFree consoleIO prog
    

    main = run ex