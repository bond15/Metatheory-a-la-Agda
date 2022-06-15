{-# OPTIONS --guardedness #-} -- needed for IO
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --type-in-type #-} -- needed for IO
module Interpretations where 
open import Level hiding (lift)
open Level hiding (lift)
open import DSLs
open import FreeMonad
open _~>_

module KeyValDSLStateT where
    open KeyValDSL

    open Monad{{...}}
    open import Store
    open import TypeClassInstances
    open import Data.String
    
    -- interpret KeyValue into the monad transformer stack using State and IO
    kvST : KeyValF String ~> M 
    kvST .α (GetKey k cb) = do      -- use a monad transformer stack?   
                                v ← find k 
                                return (cb v)
    kvST .α (PutKey k v a) = do 
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


module ConsoleDSLStateT where 
    open ConsoleDSL 
    open import Store
    open import TypeClassInstances
    open Monad{{...}}

    consoleST : ConsoleF ~> M 
    consoleST .α (PutStrLn s a) = do 
                                    print s
                                    return a
    consoleST .α (GetLine cb) = do 
                                    s ← read 
                                    return (cb s)

module ConsoleDSLIO where 
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
    


-- example of unwired ClubF in terms of unwired KeyValF and ConsoleF
module KVConsoleMap where 
    open ConsoleDSL
    open KeyValDSL
    open ClubDSL
    open Monad{{...}}
    open import Data.String
    open import Function

    KVConsole : Set → Set 
    KVConsole = Free (ConsoleF ⊹ KeyValF String)

    kv : {A : Set} → KeyVal A → KVConsole A
    kv = right .α

    con : {A : Set} → Console A → KVConsole A
    con = left .α

    clubI : ClubF ~> KVConsole
    clubI = α≔ impl
        where
            impl : {X : Set} → ClubF X → KVConsole X
            impl (GetClubMembers clubId cont)   = do 
                                                    v ← kv $ getKey ("clubs." ++ clubId ++ ".members")
                                                    return (cont v) 
            impl (GetMemberClubs memId cont)    = do
                                                    v ← kv $ getKey ("users." ++ memId ++ ".clubs")
                                                    return (cont v)
            impl (GetInput cont)                = do 
                                                    line ← con getLine
                                                    return (cont line)
            impl (Display output cont)          = do 
                                                    con $ putStrLn output
                                                    return cont

module EvalClub where
    open ClubDSL using (Club)
    open import Store using (M)
    open import TypeClassInstances

    open ConsoleDSLStateT using (consoleST)
    open KeyValDSLStateT using (kvST)
    open KVConsoleMap using (clubI)

    comp : Club ~> M
    comp = (consoleST ⊞ kvST) ⊙ clubI

module EvalConsoleStateT where 
    open ConsoleDSL
    open ConsoleDSLStateT
    open import Store
    open import TypeClassInstances

    open ConsolPrograms
    open import Data.Unit 
    
    ex : M ⊤ 
    ex = foldFree consoleST prog

    
    
module EvalConsoleIO where 
    open ConsoleDSL
    open ConsoleDSLIO
    open ConsolPrograms
    open import TypeClassInstances

    open import Data.Unit
    open import IO
    
    ex : IO ⊤
    ex = foldFree consoleIO prog
    

    main = run ex 