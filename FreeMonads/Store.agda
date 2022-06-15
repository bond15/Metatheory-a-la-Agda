{-# OPTIONS --guardedness #-}
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}
module Store where 
    open import Data.Product hiding (map)
    open import TypeClassInstances
    open import FreeMonad
    open import Data.List
    open import Data.Nat
    open import Data.Unit
    open import Data.Bool
    open import Data.Maybe hiding (map;_>>=_)
    open import IO hiding (_>>=_;_>>_; return)
    open import Agda.Builtin.String renaming (primStringEquality to _=S_)
    open Monad{{...}}

    -- A key value store
    Store : Set
    Store = List (String × String) 

    -- State and StateT monads
    data State (S X : Set) : Set where 
        St : (S → X × S) → State S X 

    runSt : {S X : Set} → State S X → (S → X × S)
    runSt (St x) = x

    data StateT (S : Set) (M : Set → Set){{_ : Monad M}} (X : Set) : Set where 
        ST : (S → M (X × S)) → StateT S M X

    runST : {S X : Set}{M : Set → Set}{{_ : Monad M}}→ StateT S M X → (S → M (X × S))
    runST (ST x) = x


    instance
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
        stateT-M = record { return = λ a → ST (λ s → return (a , s)) ; _>>=_ = λ{(ST sa) f → ST (λ s → {!   !} )}}


    -- A monad transformer Stack for stateful computation that can interact with IO
    M : Set → Set
    M = StateT Store IO 

    empty : {A : Set} → M ⊤
    empty = ST λ x → return (tt , [])

    getStore : M Store
    getStore = ST λ s → return (s , s)

    find : String → M (Maybe String)
    find k  = ST (λ s → return (find' k s , s))
        where 
            find' : String → Store → Maybe String 
            find' key [] = nothing
            find' key ((s , n) ∷ store) with(key =S s)
            ...                                  | true = just n
            ...                                  | false = find' key  store

    put : String → String → M ⊤ 
    put k v = ST (λ s → return (tt , put' s))
        where 
            put' : Store → Store
            put' [] = [ k , v ]
            put' ((k' , v') ∷ xs) with (k =S k')
            ...             | true = (k , v) ∷ xs
            ...             | false = put' xs

    print : String → M ⊤
    print s = ST λ store → do 
                            putStrLn s
                            return (tt , store)

    read : M String 
    read = ST (λ store → do 
                            s ← IO.getLine 
                            return (s , store))