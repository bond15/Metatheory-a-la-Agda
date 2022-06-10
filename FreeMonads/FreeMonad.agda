-- examples motivated from https://www.tweag.io/blog/2018-02-05-free-monads/
module FreeMonad where

-- Haskell style definitions of Functor and Monad using Agda's instance arguments as type classes
record Functor (F : Set → Set) : Set₁ where 
    field 
        fmap : ∀{A B} → (A → B) → F A → F B

open Functor{{...}}
open import Data.Sum 


--_+_ : {F G : Set → Set} → Functor F → Functor G → Functor {! [ F , G ]′  !}
-- F + G = {!   !}

record Monad (F : Set → Set) : Set₁ where 
    field
        return : ∀ {A} → A → F A
        _>>=_ : ∀{A B} → F A → (A → F B) → F B
    
    _>>_ : ∀{A B} → F A → F B → F B
    x >> y = x >>= λ _ → y
        
open Monad{{...}}

-- natural transformation
record _~>_ (F G : Set → Set){{_ : Functor F}}{{_ : Functor G}} : Set₁ where
    field
        α : ∀ {A} → F A → G A -- component of a natural transformation
open _~>_

-- definition of the free monad
{-# NO_POSITIVITY_CHECK #-}
data Free (F : Set → Set){{_ : Functor F}} (A : Set) : Set where
    Pure : A → Free F A
    ImPure : (F (Free F A)) → Free F A


-- Showing the Free Monad is a Functor and a Monad
instance
    {-# TERMINATING #-}
    Free-Functor : {F : Set → Set}{{_ : Functor F}} → Functor (Free F)
    Free-Functor {F} .fmap {A} {B} = ffmap
        where 
            ffmap : (A → B) → Free F A → Free F B
            ffmap f (Pure x) = Pure (f x)
            ffmap f (ImPure x) = ImPure (fmap (ffmap f) x)
    
    {-# TERMINATING #-}
    Free-Monad : {F : Set → Set}{{_ : Functor F}} → Monad (Free F)
    Free-Monad .return = Pure
    Free-Monad {F} ._>>=_ {A} {B}  = bbind
        where 
            bbind : Free F A → (A → Free F B) → Free F B 
            bbind (Pure x) fb = fb x
            bbind (ImPure x) fb = ImPure (fmap (_>>= fb) x)

Algebra : (Set → Set) → Set → Set 
Algebra F A = F A → A

-- how to map an interpretation of a program
{-# TERMINATING #-}
foldTerm : {A B : Set}{F : Set → Set}{{_ : Functor F}} → (A → B) → Algebra F B → Free F A → B
foldTerm pure imp (Pure x) = pure x
foldTerm pure imp (ImPure x) = imp (fmap (foldTerm pure imp) x)


-- helps wrinting smart constructors
liftF : {A : Set}{F : Set → Set}{{_ : Functor F}} → F A → Free F A
liftF command = ImPure (fmap Pure command)

-- claim: free takes functors to functors and natural transformations to natural transformation
-- its an endofunctor on the functor category?
{-# TERMINATING #-}
freeM : {F G : Set → Set}{{_ : Functor F}}{{_ : Functor G}} 
    → F ~> G → Free F ~> Free G
freeM ϕ = record { α = λ{(Pure x) → Pure x
                       ; (ImPure x) → ImPure ((ϕ .α) (fmap ((freeM ϕ) .α) x))} }

-- what is this ..?
{-# TERMINATING #-}
monad : {m : Set → Set}{{_ : Functor m}}{{_ : Monad m}} 
    → (Free m) ~> m
monad .α (Pure x) = return x
monad .α (ImPure mfx) = do 
                         fx ← mfx
                         monad .α fx


-- size issue?
-- This would be an operation in the functor category and not the underlying category
--_~+~_ : {F G T : Set → Set}{{_ : Functor F}}{{_ : Functor G}}{{_ : Functor T}}
--     → F ~> T → G ~> T → {! (F ⊹ G) ~> ?  !}
--f ~+~ g = {!   !}   