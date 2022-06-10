module InitialAlg where
    open import Agda.Primitive using (Level; lsuc ; _⊔_)
    open import Cubical.Core.Everything using (_≡_)
    open import Level using (levelOfTerm)


    record Category (o h : Level) : Set (lsuc (o ⊔ h)) where 
        field 
            Ob : Set o
            _⇒_ : Ob → Ob → Set h
            id : ∀ {x} → x ⇒ x
            _∘_ : ∀{x y z} → y ⇒ z → x ⇒ y → x ⇒ z

            idr : ∀{x y}{f : x ⇒ y} → (f ∘ id) ≡ f 
            idl : ∀{x y}{f : x ⇒ y} → id ∘ f ≡ f
            assoc : ∀{w x y z} {f : y ⇒ z}{g : x ⇒ y}{h : w ⇒ x} → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h


    record Functor {o ℓ}(𝒞 𝒟 : Category o ℓ) : Set (levelOfTerm 𝒞) where 
        open Category 𝒞 renaming (Ob to Obᶜ; _⇒_ to _⇒ᶜ_; id to idᶜ; _∘_ to _∘ᶜ_)
        open Category 𝒟 renaming (Ob to Obᵈ; _⇒_ to _⇒ᵈ_; id to idᵈ; _∘_ to _∘ᵈ_)
        field
            F₀ : Obᶜ → Obᵈ
            F₁ : {A B : Obᶜ} → (f : A ⇒ᶜ B) → F₀ A ⇒ᵈ F₀ B

            Fid : {A : Obᶜ} → F₁ (idᶜ {A}) ≡ idᵈ { F₀ A }
            Fcomp : {A B C : Obᶜ}{f : A ⇒ᶜ B}{g : B ⇒ᶜ C} → F₁ (g ∘ᶜ f) ≡ (F₁ g ∘ᵈ F₁ f)


    record NaturalTransformation {o ℓ}{𝒞 𝒟 : Category o ℓ}(F G : Functor 𝒞 𝒟) : Set (o ⊔ ℓ) where 
        open Functor F 
        open Functor G renaming (F₀ to G₀; F₁ to G₁)
        open Category 𝒞 renaming (_⇒_ to _⇒C_) hiding (_∘_)
        open Category 𝒟 renaming (_⇒_ to _⇒D_; _∘_ to _∘D_)
        field 
            η : ∀ X → (F₀ X) ⇒D (G₀ X)
            commute : ∀ {X Y}(f : X ⇒C Y)→ (η Y ∘D F₁ f) ≡ (G₁ f ∘D η X)


    record F-Algebra {o ℓ}{𝒞 : Category o ℓ}(ℱ : Functor 𝒞 𝒞 ): Set (levelOfTerm 𝒞) where
        open Category 𝒞
        open Functor ℱ 
        field
            {X} : Ob
            θ : F₀ X ⇒ X
                


    record F-Alg-Hom {o ℓ}{𝒞 : Category o ℓ}{ℱ : Functor 𝒞 𝒞} ( F-alg G-alg : F-Algebra ℱ) : Set (levelOfTerm 𝒞) where 
        open Category 𝒞
        open Functor ℱ
        open F-Algebra F-alg renaming (θ to θ-F)
        open F-Algebra G-alg renaming (X to Y; θ to θ-G)

        field 
            m : X ⇒ Y
            cond : (m ∘ θ-F) ≡ (θ-G ∘ F₁ m) 

    module _ where 
        open Functor
        open import Cubical.Foundations.Prelude using (refl)
        
        id-Functor : ∀{o ℓ}{𝒞 : Category o ℓ} → Functor 𝒞 𝒞
        id-Functor .F₀ = λ x → x
        id-Functor .F₁ = λ f → f
        id-Functor .Fid = refl
        id-Functor .Fcomp = refl

        _∘F_ : {o ℓ : Level}{A B C : Category o ℓ} → Functor B C → Functor A B → Functor A C
        _∘F_ G F .F₀ = λ x → (G .F₀ (F .F₀ x))
        _∘F_ G F .F₁ = λ f → G .F₁ (F .F₁ f)
        _∘F_ G F .Fid = {!   !}
        _∘F_ G F .Fcomp = {!   !}

    record Monad {o ℓ}{𝒞 : Category o ℓ }: Set (levelOfTerm 𝒞) where 
        field 
            F : Functor 𝒞 𝒞
            η : NaturalTransformation id-Functor F
            μ : NaturalTransformation (F ∘F F) F  
        
        module η = NaturalTransformation η
        module μ = NaturalTransformation μ 

        open Category 𝒞
        open Functor F 

        field 
            assoc : ∀{X : Ob} → μ.η X ∘ F₁ (μ.η X) ≡ (μ.η X ∘ μ.η (F₀ X))
            idˡ : ∀{X : Ob} → (μ.η X ∘ F₁ (η.η X)) ≡ id
            idʳ : ∀{X : Ob} → (μ.η X ∘ η.η (F₀ X)) ≡ id

    -- forms a full subcategory of alg for F
    record MonadAlgebra{o ℓ}{𝒞 : Category o ℓ}(M : Monad {o}{ℓ}{𝒞}) : Set (levelOfTerm 𝒞) where
        open Category 𝒞
        open Monad M
        field 
            alg : F-Algebra F

        open F-Algebra alg

        open Functor F
        field
            ret-alg : (θ ∘ η.η _) ≡ id 
            bind-alg : (θ ∘ F₁ θ) ≡ (θ ∘ μ.η _)


            
                
                 