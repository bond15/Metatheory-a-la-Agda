module FreeMonadCat where 
open import CatLib 
open import Level 
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
    
    AgdaFun : Category (suc (suc zero)) (suc zero) 
    AgdaFun .Ob = FunctorT Agda Agda
    AgdaFun ._⇒_ F G = NaturalTransformationT F G
    AgdaFun .id = idNat _
    AgdaFun ._∘_ {F} {G} {H} ϕ ψ = nt
        where 
            open Category Agda renaming(_∘_ to _⊚_; assoc to assocA)
            open Reasonging Agda            
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
                        β Y ⊚ (α Y ⊚ F₁' f) ≡⟨ cong₂ {A = {! β Y  !}} _⊚_ refl (commute-top {X = X}{Y = Y} f)   ⟩ 
                        β Y ⊚ (G₁ f ⊚ α X)  ≡⟨ assocA {f = β Y} {g = G₁ f} {h = α X} ⟩ 
                        (β Y ⊚ G₁ f) ⊚ α X  ≡⟨ cong₂ _⊚_ (commute-bot {X = X} {Y = Y} f) refl ⟩ 
                        (H₁ f ⊚ β X) ⊚ α X  ≡⟨ refl ⟩ 
                        H₁ f ⊚ β X ⊚ α X    ∎
    
            
    AgdaFun .idl = {!   !}
    AgdaFun .idr = {!   !}
    AgdaFun .assoc = {!   !}   