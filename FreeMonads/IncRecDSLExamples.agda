module IncRecDSLExamples where
open import Data.Product using (_×_;_,_)
open import Data.Unit using (⊤;tt)
open import Data.Nat
open import FreeMonad
open import DSLs
open IncRecDSL

open Monad{{...}}

module Progams where 
    -- programs written with primatives
    -- notice this is just syntax, there is no perscribed interpretation yet
    
    tick : M ℕ
    tick = do
            y ← recall
            incr 1
            incr 2
            incr 1
            return y
            

module interpretation1 where
    open Progams

    -- one possible interpretation using State

    -- a "memory" type
    data Memory : Set where Mem : ℕ → Memory

    State : Set → Set → Set 
    State S A = S → (A × S)

    -- Specify what each DSL component "means" in the State representation
    runAlg : {A : Set} → Algebra Cmds (State Memory A) -- r is a "continuation" ?
    runAlg (Incr n r) (Mem x) = r (Mem (x + n)) -- "incr n"     ⟶ increment the memory storage by n
    runAlg (Recall r) (Mem x) = r x (Mem x)     -- "x ← recall" ⟶ return the value in memory, don't update memory
    

    -- an evaluator for the run algebra
    runState : {A : Set} → M A → State Memory A
    runState = foldTerm _,_ runAlg

    -- running the program with the State interpretation
    ex = runState tick (Mem 4)
    {-
    recall definition of "tick"'

    tick : M ℕ
    tick = do
            y ← recall
            incr 1
            incr 2
            incr 1
            return y

    it binds the value in memory to `y`
    increments the memory by 1 + 2 + 1 
    and returns the initial value in memory

    so `ex` results in (4, Mem 8)
    -}
 