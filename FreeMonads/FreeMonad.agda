-- examples motivated from https://www.tweag.io/blog/2018-02-05-free-monads/
module FreeMonad where
open import Function using (_∘_)
-- Haskell style definitions of Functor and Monad using Agda's instance arguments as type classes

record Functor (F : Set → Set) : Set₁ where 
    field 
        fmap : ∀{A B} → (A → B) → F A → F B

open Functor{{...}}

data _⊹_ (F G : Set → Set)(E : Set): Set where 
    InL : F E → (F ⊹ G) E 
    InR : G E → (F ⊹ G) E

instance 
    ⊹-F : {F G : Set → Set}{{_ : Functor F}}{{_ : Functor G}} → Functor  (F ⊹ G) 
    ⊹-F {F}{G}{{Fin}}{{Gin}} = record { fmap = λ{ x (InL x₁) → InL (Functor.fmap Fin x x₁)
                                                ; x (InR x₁) → InR (Functor.fmap Gin x x₁) }}

record Monad (F : Set → Set) : Set₁ where 
    field
        return : ∀ {A} → A → F A
        _>>=_ : ∀{A B} → F A → (A → F B) → F B
    
    _>>_ : ∀{A B} → F A → F B → F B
    x >> y = x >>= λ _ → y
        
open Monad{{...}}

-- natural transformation
record _~>_ (F G : Set → Set){{_ : Functor F}}{{_ : Functor G}} : Set₁ where
    constructor α≔_
    field
        α : ∀ {A} → F A → G A -- component of a natural transformation
open _~>_


record _~>'_ {F G : Set → Set}(_ : Functor F)(_ : Functor G) : Set₁ where
    constructor α≔_
    field
        α : ∀ {A} → F A → G A -- component of a natural transformation
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


--\b+
_⊞_ : {F G T : Set → Set}{{_ : Functor F}}{{_ : Functor G}}{{_ : Functor T}}
     → F ~> T → G ~> T → (F ⊹ G) ~> T
(α≔ α) ⊞ (α≔ β) = α≔ λ{(InL x) → α x
                     ; (InR x) → β x}

left : {F G : Set → Set}{{_ : Functor F}}{{_ : Functor G}} → Free F ~> Free (F ⊹ G)
left = freeM (α≔ InL)

right : {F G : Set → Set}{{_ : Functor F}}{{_ : Functor G}} → Free G ~> Free (F ⊹ G)
right = freeM (α≔ InR)
                       
--https://hackage.haskell.org/package/free-5.1.8/docs/src/Control.Monad.Free.html#foldFree
{-# TERMINATING #-}
foldFree : {A : Set}{M F : Set → Set}{{_ : Functor M}}{{_ : Monad M}}{{_ : Functor F}} 
    → F ~> M → Free F A → M A
foldFree ϕ (Pure x) = return x
foldFree ϕ (ImPure x) = (ϕ .α) x >>= foldFree ϕ

{-# TERMINATING #-}
lift : {M F : Set → Set}{{_ : Functor M}}{{_ : Monad M}}{{_ : Functor F}} 
    → F ~> M → Free F ~> M 
lift ϕ .α (Pure x) = return x
lift ϕ .α (ImPure x) = (ϕ .α) x >>= lift ϕ .α

-- vertical compositon of natural transformations
_∙_ : {M F G : Set → Set}{{_ : Functor F}}{{_ : Functor G}}{{_ : Functor M}}
    → G ~> M → F ~> G → F ~> M
(α≔ β) ∙ (α≔ α) = α≔ (β ∘ α)

_∙'_ : {M F G : Set → Set}{F' : Functor F}{G' : Functor G}{M' : Functor M}
    → G' ~>' M' → F' ~>' G' → F' ~>' M'
(α≔ β) ∙' (α≔ α) = α≔ (β ∘ α)

_⊙_ : {M F G : Set → Set}{{_ : Functor F}}{{_ : Functor G}}{{_ : Functor M}}{{_ : Monad M}}
    → G ~> M → F ~> Free G → Free F ~> M
β ⊙ α = lift β ∙ lift α 