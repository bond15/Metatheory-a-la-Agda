{-# OPTIONS --without-K #-}
module FreeMonadCat where 
open import CatLib 
open import Level 
open Level renaming (suc to lsuc)
open import Cubical.Core.Everything using (_≡_)
open import Cubical.Foundations.Prelude using (refl)

module AgdaCat where 
    open Category
    open import Function renaming (_∘_ to _⊙_) hiding (id)
    
    Agda : Category (suc zero) zero
    Agda .Ob = Set₀
    Agda ._⇒_ x y = x → y
    Agda .id = λ x → x
    Agda ._∘_ g f = g ⊙ f
    Agda .idl = refl
    Agda .idr = refl
    Agda .assoc = refl

    open Hom-Set Agda
    
    agda-set : hom-set-cond
    agda-set A B f g f≡g₁ f≡g₂ = {!   !}
    open Functor
    open NaturalTransformation
    open NaturalTransformationT
    open import Cubical.Foundations.Prelude
    open FunctorT

    -- https://1lab.dev/Cat.Base.html#15117

    Nat-pathp : {F G : FunctorT Agda Agda}
            → {ϕ : F ~> G} {ψ : F ~> G}
            → (∀ x → (ϕ .η x) ≡ (ψ .η x))
            → ϕ ≡ ψ
    Nat-pathp = {!   !}
   {- Nat-pathp {F} {G} {ϕ} {ψ} path i .η x = path x i
    Nat-pathp {F} {G} {ϕ} {ψ} path i .commute {x} {y} f = 
        is-prop→pathp  
            (λ j → agda-set _ _   (Agda ._∘_ (path y i) (F₁ F f)) (Agda ._∘_ (F₁ G f) (path x i)))  
            (funExt λ Fx  → {! ϕ .commute f !})
            {!  !}  -- (λ x₁ → path y i (F₁ F f x₁)) ≡ (λ x₁ → F₁ G f (path x i x₁))
                                    -- (Agda ∘ η ψ y) (F₁ F f) ≡ (Agda ∘ F₁ G f) (η ψ x)
            i -}

module FunCatPoly where 
    open import Poly renaming (lift to liftPoly)
    open Poly[_,_]
    open Category
    open import Category using (PFun; PNat; Functor)


    -- Incorrect. Type in Type crap.. in Poly
    PolyCat : Category zero zero 
    PolyCat .Ob = Poly
    PolyCat ._⇒_ = Poly[_,_]
    PolyCat .id = (λ x → x) ⇒ₚ λ i x → x
    PolyCat ._∘_ p q = q ⇒∘ₚ p
    PolyCat .idr = refl
    PolyCat .idl = refl
    PolyCat .assoc = refl

    open import FreeMonad

    unwrap : {F : Set → Set} → FreeMonad.Functor F → (Set → Set)
    unwrap {F} _ = F
    
    instance
        PFun' : {p : Poly} → FreeMonad.Functor ⦅ p ⦆ 
        PFun' {p} = record { fmap = liftPoly p }


    open import Data.Product
    open import Agda.Builtin.Sigma 

    PNat' : {p q : Poly} → Poly[ p , q ] → FreeMonad._~>_  ⦅ p ⦆ ⦅ q ⦆
    PNat' p⇒q = α≔ λ ⦅p⦆A → onPos p⇒q (fst ⦅p⦆A) , λ x → snd ⦅p⦆A (onDir p⇒q (fst ⦅p⦆A) x)

    -- Displayed category using PFun and PNat??
    -- PFun And PNat include the Laws!
    open Displayed

    open AgdaCat using (Nat-pathp)
    AgdaFunCat : Displayed PolyCat (suc zero) (suc zero) 
    Ob[ AgdaFunCat ] p = FreeMonad.Functor' ⦅ p ⦆
    Hom[ AgdaFunCat ] p⇒q = FreeMonad._~>'_
    AgdaFunCat .id' = α≔ (λ x → x) st λ f → refl
    AgdaFunCat ._∘'_ = _∙'_
    AgdaFunCat .idr' f = {! idr PolyCat !} -- need a "nat path"
    AgdaFunCat .idl' = {!   !}
    AgdaFunCat .assoc' = {!   !}



-- consider only the subcategory of the endofunctor category spaned by Poly?
module AgdaFunCat where 
    open AgdaCat using (Agda)
    open Functor
    open FunctorT
    open Category
    open NaturalTransformation
    open NaturalTransformationT
    open import Cubical.Foundations.Prelude

    idF : FunctorT Agda Agda 
    idF .F₀ = λ x → x
    idF .F₁ = λ f → f
    idF .Fid = refl
    idF .Fcomp = refl

    idNat : (F : FunctorT Agda Agda) → NaturalTransformationT F F 
    idNat F .η X = Agda .id
    idNat F .commute f = refl
    
    open AgdaCat using (Nat-pathp)

    AgdaFun : Category (suc (suc zero)) (suc zero) 
    AgdaFun .Ob = FunctorT Agda Agda
    AgdaFun ._⇒_ F G = NaturalTransformationT F G
    AgdaFun .id = idNat _
    AgdaFun ._∘_ {F} {G} {H} ϕ ψ = nt
        where 
            open Category Agda renaming(_∘_ to _⊚_; assoc to assocA)
            open FunctorT F renaming (F₁ to F₁';F₀ to F₀')
            open FunctorT H renaming (F₁ to H₁; F₀ to H₀)
            open FunctorT G renaming (F₁ to G₁; F₀ to G₀)
            open NaturalTransformationT ϕ renaming (η to β; commute to commute-bot) -- G ≡> H
            open NaturalTransformationT ψ renaming (η to α; commute to commute-top) -- F ≡> G

            nt : NaturalTransformationT F H
            nt .η X = β X ⊚ α X 
            nt .commute {X} {Y} f = cond
                where
                    open NaturalTransformationT nt renaming (η to η')
                    cond = 
                        η' Y ⊚ F₁' f        ≡⟨ refl ⟩ 
                        β Y ⊚ α Y ⊚ F₁' f   ≡⟨ sym (assocA {f = β Y} {g = α Y} )⟩ 
                        β Y ⊚ (α Y ⊚ F₁' f) ≡⟨ cong ((β Y)⊚_) (commute-top f)   ⟩ 
                        β Y ⊚ (G₁ f ⊚ α X)  ≡⟨ assocA {f = β Y} {g = G₁ f} {h = α X} ⟩ 
                        (β Y ⊚ G₁ f) ⊚ α X  ≡⟨ cong₂ _⊚_ (commute-bot f) refl ⟩ 
                        (H₁ f ⊚ β X) ⊚ α X  ≡⟨ refl ⟩ 
                        H₁ f ⊚ β X ⊚ α X    ∎ 
                        
    AgdaFun .idl = Nat-pathp λ x → refl             
    AgdaFun .idr = Nat-pathp λ x → refl
    AgdaFun .assoc = Nat-pathp λ x → refl  

    data _⊹_ (F G : Set → Set)(E : Set): Set where 
        InL : F E → (F ⊹ G) E 
        InR : G E → (F ⊹ G) E
        
    _+_ : (F G : FunctorT Agda Agda) → FunctorT Agda Agda
    (F + G) .F₀ = F₀ F ⊹ F₀ G
    (F + G) .F₁ f = λ{ (InL FA) → InL ((F₁ F f) FA)
                     ; (InR GA) → InR ((F₁ G f) GA)}
    (F + G) .Fid = funExt λ{(InL x) → cong InL (funExt⁻ (Fid F) x)
                          ; (InR x) → cong InR (funExt⁻ (Fid G) x)}
    (F + G) .Fcomp = funExt λ {(InL x) → cong InL (funExt⁻ (Fcomp F) x)
                             ; (InR x) → cong InR (funExt⁻ (Fcomp G) x)}


    bar : {F G C : FunctorT Agda Agda}→ F ~> C → G ~> C  → (X : Ob Agda) → (Agda ⇒ F₀ (F + G) X) (F₀ C X)
    bar {F = F} ϕ ψ x (InL Fx) = ϕ .η x Fx
    bar {G = G} ϕ ψ x (InR Gx) = ψ .η x Gx
    
    _~+~_ : {F G H : FunctorT Agda Agda} →  F ~> H → G ~> H → (F + G) ~> H
    (ϕ ~+~ ψ) .η = bar ϕ ψ  
    (ϕ ~+~ ψ) .commute {X} {Y} f = funExt λ {(InL Fx) → funExt⁻ (ϕ .commute f) Fx
                                           ; (InR Gx) → funExt⁻ (ψ .commute f) Gx }

    
    open BinaryCoproducts AgdaFun
    open ObjectCoproduct AgdaFun

    Co : ∀ (F G : FunctorT Agda Agda) → Coproduct F G
    Co F G = record
        { A+B = F + G
        ; inj₁ = record { η = λ x → InL ; commute = λ f → refl }
        ; inj₂ = record { η = λ x → InR ; commute = λ f → refl }
        ; ⟨_+_⟩ = _~+~_
        ; inject₁ = Nat-pathp λ x → refl
        ; inject₂ = Nat-pathp λ x → refl
        ; unique = λ {h} {f} {g} p q → Nat-pathp λ ob → funExt λ {(InL l) → {! p !}
                                                    ; (InR r) → {!   !}}
        }

    AgdaFunCoproducts : BinaryCoproductsT
    AgdaFunCoproducts = record { coproduct = Co _ _ } 

-- Free  objects?
--https://github.com/agda/agda-categories/blob/29d4b15ca6e23cfb2e437b049618a4cac769d52b/src/Categories/FreeObjects/Free.agda

-- How to write Free Monad?