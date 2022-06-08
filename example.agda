module example where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Product using (Σ ; Σ-syntax ; _,_ ; proj₁ ; proj₂)

postulate  Extensionality : {A : Set} {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

_∘_ : {X Y Z : Set} → (f : Y → Z) → (g : X → Y) → X → Z
f ∘ g = λ x → f(g x)

record Functor(F : Set₀ → Set₀): Set₁ where
    field
        fmap : {X Y : Set} → (f : X → Y) → F X → F Y
        -- laws
open Functor {{...}} 

Algebra : (Set → Set) → Set → Set 
Algebra F A = F A → A

-- could use a church encoding here to avoid turning off positivity checker
{-# NO_POSITIVITY_CHECK #-}
data Fix (F : Set → Set) : Set where
    In : F (Fix F) → Fix F
open Fix

out : {F : Set → Set} → Fix F → F (Fix F)
out (In x) = x

data NatF (A : Set) : Set where 
    Z : NatF A
    S : A → NatF A

instance
    NatF-Functor : Functor NatF
    NatF-Functor = record {
                        fmap = λ{f Z → Z
                               ; f (S x) → S (f x) }
                    }

Nat : Set 
Nat = Fix NatF

z : Nat 
z = In Z

s : Nat → Nat 
s n = In (S n)

-- should make this an algebra instead
_+Nat_ : Nat → Nat → Nat 
In Z +Nat y = y
In (S x) +Nat y = s (x +Nat y)

ProofAlgebra : {F : Set → Set}(P : Fix F → Set) → Set 
ProofAlgebra {F} P = Algebra F (Σ[ e ∈ Fix F ] P e)

-- Could use church encoding to avoid disabling termination checking
{-# TERMINATING #-}
proof-fold : {F : Set → Set}{{_ : Functor F}}{P : Fix F → Set} → ProofAlgebra P → Fix F → Σ (Fix F) P
proof-fold alg  = alg ∘ (fmap (proof-fold alg) ∘ out)

WF-proof-alg : {F : Set → Set}{{_ : Functor F}}{P : Fix F → Set}
                → (alg : ProofAlgebra P) 
                → Set
WF-proof-alg alg = (proj₁ ∘ alg) ≡ (In ∘ fmap proj₁)

-- Natural number induction as a proof algebra
Nat-ind :   (P : Nat → Set)
            (Hz : P z)
            (Hs : ∀ (n : Nat) → P n → P (s n)) 
            → ProofAlgebra P
Nat-ind P hz hs Z = z , hz
Nat-ind P hz hs (S x) = s (proj₁ x) , hs (proj₁ x) (proj₂ x)

Nat-ind-WF : ∀(P : Nat → Set)(Hz : P z)(Hs : ∀ (n : Nat) → P n → P (s n))
    → WF-proof-alg (Nat-ind P Hz Hs)
Nat-ind-WF P Hz Hs = Extensionality λ{Z → refl
                                    ; (S x) → refl}

N+0 : Nat → Set
N+0 n = n +Nat z ≡ n

N+0-alg : ProofAlgebra N+0 
N+0-alg = Nat-ind N+0 refl (λ n nprf → cong s nprf)

-- this N+0-alg is well formed if natural number induction is well formed
_ : WF-proof-alg N+0-alg
_ = Nat-ind-WF N+0 refl (λ n nprf → cong s nprf)

prf : Σ Nat N+0
prf = proof-fold N+0-alg (s (s z))

