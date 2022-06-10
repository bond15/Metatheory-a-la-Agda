{-# OPTIONS --guardedness #-} -- needed for IO
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --type-in-type #-} -- needed for IO
module Interpretations where 
open import Level
open Level
open import DSLs
open import FreeMonad
open _~>_

module KeyValDSLI where
    open KeyValDSL

    open Monad{{...}}
    open import Store
    open import TypeClassInstances
    open import Data.Nat


    
    kvList : KeyValF ℕ ~> M 
    kvList .α (GetKey k cb) = do  
                                v ← find k 
                                return (cb  v)
    kvList .α (PutKey k v a) = do 
                                put k v 
                                return a

    
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
    open import TypeClassInstances

    open import Data.Unit
    open import IO
    
    ex : IO ⊤
    ex = foldFree consoleIO prog
    

    main = run ex 