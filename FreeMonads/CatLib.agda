{-# OPTIONS --allow-unsolved-metas #-}

-- Partially from https://github.com/agda/agda-categories
-- using Cubical Agda for enhanced equality type
module CatLib where 
    open import Cubical.Core.Everything using (_≡_)
    open import Cubical.Foundations.Prelude hiding (_∙_)

    open import Data.Nat using (ℕ;suc)
    open import Agda.Primitive using (Level; lsuc ; _⊔_)


    record is-contr {ℓ} (A : Set ℓ) : Set ℓ where
        constructor contr 
        field 
            centre : A 
            paths : (x : A) → centre ≡ x
    open is-contr public

    is-prop : ∀{ℓ} → Set ℓ → Set _ 
    is-prop A = (x y : A) → x ≡ y  

    is-hlevel : ∀{ℓ} → Set ℓ → ℕ → Set _ 
    is-hlevel A 0 = is-contr A
    is-hlevel A 1 = is-prop A
    is-hlevel A (suc n) = (x y : A) → is-hlevel (x ≡ y) n

    is-set : ∀{ℓ} → Set ℓ → Set ℓ 
    is-set A = is-hlevel A 2

    coe0→1 : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1
    coe0→1 A a = transp (λ i → A i) i0 a

    coe0→i : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i0 → A i
    coe0→i A i a = transp (λ j → A (i ∧ j)) (~ i) a
    
    to-pathp : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1}
         → coe0→1 A x ≡ y
         → PathP A x y
    to-pathp {A = A} {x} p i =
        hcomp (λ j → λ { (i = i0) → x
                        ; (i = i1) → p j })
                (coe0→i A i x)

    is-prop→pathp : ∀ {ℓ} {B : I → Type ℓ} → ((i : I) → is-prop (B i))
              → (b0 : B i0) (b1 : B i1)
              → PathP (λ i → B i) b0 b1
    is-prop→pathp {B = B} hB b0 b1 = to-pathp (hB _ _ _)

    record Category (o h : Level) : Set (lsuc (o ⊔ h)) where 
        field 
            Ob : Set o
            _⇒_ : Ob → Ob → Set h
            id : ∀ {x} → x ⇒ x
            _∘_ : ∀{x y z} → y ⇒ z → x ⇒ y → x ⇒ z

            idr : ∀{x y}{f : x ⇒ y} → (f ∘ id) ≡ f 
            idl : ∀{x y}{f : x ⇒ y} → id ∘ f ≡ f
            assoc : ∀{w x y z} {f : y ⇒ z}{g : x ⇒ y}{h : w ⇒ x} → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h


        infixr 40 _∘_


    module Hom-Set {o ℓ} (C : Category o ℓ) where 
        open Category C

        hom-set-cond : Set (o ⊔ ℓ)
        hom-set-cond = ∀ (x y : Ob) → is-set (x ⇒ y)

    module ObjectProduct{o ℓ : Level} (𝒞 : Category o ℓ) where
        open Category 𝒞

        private 
            variable
                A B C D : Ob 
                h i j : A ⇒ B

        record Product (A B : Ob) : Set (o ⊔ ℓ) where
            infix 10 ⟨_,_⟩

            field
                A×B   : Ob
                π₁    : A×B ⇒ A
                π₂    : A×B ⇒ B
                ⟨_,_⟩ : C ⇒ A → C ⇒ B → C ⇒ A×B

                project₁ : π₁ ∘ ⟨ h , i ⟩ ≡ h
                project₂ : π₂ ∘ ⟨ h , i ⟩ ≡ i
                unique   : π₁ ∘ h ≡ i → π₂ ∘ h ≡ j → ⟨ i , j ⟩ ≡ h 

        
        module Morphisms where 

            open Product
            infix 10 [_]⟨_,_⟩ [_⇒_]_×_
            infix 12 [[_]] [_]π₁ [_]π₂

            [[_]] : Product A B → Ob 
            [[ p ]] = p .A×B

            [_]⟨_,_⟩ : ∀(p : Product B C) → A ⇒ B → A ⇒ C → A ⇒ [[ p ]]
            [ p ]⟨ f , g ⟩ = ⟨_,_⟩ p f g

            [_]π₁ : ∀(p : Product A B) → [[ p ]] ⇒ A 
            [ p ]π₁ = π₁ p

            [_]π₂ : ∀(p : Product A B) → [[ p ]] ⇒ B
            [ p ]π₂ = π₂ p

            [_⇒_]_×_ : ∀(p₁ : Product A C)(p₂ : Product B D) → (A ⇒ B) → (C ⇒ D) → ([[ p₁ ]] ⇒ [[ p₂ ]])
            [ p₁ ⇒ p₂ ] f × g = [ p₂ ]⟨ f ∘ [ p₁ ]π₁ , g ∘ [ p₁ ]π₂ ⟩ 



    module ObjectCoproduct{o ℓ : Level} (𝒞 : Category o ℓ) where
        open Category 𝒞

        private 
            variable
                A B C D : Ob 
                h f g : A ⇒ B

        record Coproduct (A B : Ob) : Set (o ⊔ ℓ) where
            infix 10 ⟨_+_⟩

            field
                A+B   : Ob
                inj₁  : A ⇒ A+B 
                inj₂  : B ⇒ A+B
                ⟨_+_⟩ : A ⇒ C → B ⇒ C → A+B ⇒ C

                inject₁ : ⟨ f + g ⟩ ∘ inj₁ ≡ f
                inject₂ : ⟨ f + g ⟩ ∘ inj₂ ≡ g
                unique  : h ∘ inj₁ ≡ f → h ∘ inj₂ ≡ g → ⟨ f + g ⟩ ≡ h 
                

    module BinaryProducts {o h} (𝒞 : Category o h) where
        open ObjectProduct 𝒞
        open Category 𝒞
        open import Level using (levelOfTerm)
        private 
            variable
                A B C D : Ob 

        record BinaryProductsT : Set (levelOfTerm 𝒞) where
            infixr 7 _×_

            field
                product : ∀ {A B : Ob} → Product A B

            _×_ : Ob → Ob → Ob
            A × B = Product.A×B (product {A} {B})


            
            --_⁂_ : A ⇒ B → C ⇒ D → A × C ⇒ B × D
            --f ⁂ g = [ product ⇒ product ] f × g

    module BinaryCoproducts {o h} (𝒞 : Category o h) where
        open ObjectCoproduct 𝒞
        open Category 𝒞
        open import Level using (levelOfTerm)
        private 
            variable
                A B C D : Ob 

        record BinaryCoproductsT : Set (levelOfTerm 𝒞) where
            infixr 7 _+_
            field 
                coproduct : ∀{A B : Ob} → Coproduct A B

            _+_ : Ob → Ob → Ob 
            A + B = Coproduct.A+B (coproduct {A} {B})

    module Terminal {o h} (𝒞 : Category o h) where
        open Category 𝒞
        
        record IsTerminal(⊤ : Ob) : Set (o ⊔ h) where
            field
                ! : {A : Ob} → (A ⇒ ⊤)
                !-unique : ∀{A : Ob} → (f : A ⇒ ⊤) → ! ≡ f

        record TerminalT : Set (o ⊔ h) where 
            field 
                ⊤ : Ob 
                ⊤-is-terminal : IsTerminal ⊤

    module Cartesian {o h} (𝒞 : Category o h) where 
        open import Level using (levelOfTerm)
        open Terminal 𝒞 using (TerminalT)
        open BinaryProducts 𝒞 using (BinaryProductsT)

        record CartesianT : Set (levelOfTerm 𝒞) where 
            field 
                terminal : TerminalT
                products : BinaryProductsT
                

    module Equalizer {o ℓ} (𝒞 : Category o ℓ) where 
        open Category 𝒞

        private 
            variable
                A B X : Ob 
                h i l : A ⇒ B

        record IsEqualizer {E : Ob} (arr : E ⇒ A) (f g : A ⇒ B) : Set (o ⊔ ℓ) where  
            field 
                equality : f ∘ arr ≡ g ∘ arr 
                equalize : ∀{h : X ⇒ A} → f ∘ h ≡ g ∘ h → X ⇒ E
                universal : ∀{eq : f ∘ h ≡ g ∘ h} → h ≡ arr ∘ equalize eq
                unique : ∀{eq : f ∘ h ≡ g ∘ h} → h ≡ arr ∘ i → i ≡ equalize eq

        record EqualizerT (f g : A ⇒ B) : Set (o ⊔ ℓ) where 
            field 
                {obj} : Ob 
                arr : obj ⇒ A 
                isEqualizer : IsEqualizer arr f g

    module Pullback {o ℓ}(𝒞 : Category o ℓ) where
        open Category 𝒞 
        private
            variable
                A B X Y Z  : Ob
                h₁ h₂ i f g : A ⇒ B 

        record IsPullback {P : Ob} (p₁ : P ⇒ X) (p₂ : P ⇒ Y)(f : X ⇒ Z)(g : Y ⇒ Z) : Set (o ⊔ ℓ) where 
            field
                commute : f ∘ p₁ ≡ g ∘ p₂
                universal : ∀{h₁ : A ⇒ X}{h₂ : A ⇒ Y} → f ∘ h₁ ≡ g ∘ h₂ → A ⇒ P 
                unique : ∀{eq : f ∘ h₁ ≡ g ∘ h₂} → 
                            p₁ ∘ i ≡ h₁ → p₂ ∘ i ≡ h₂ → 
                            i ≡ universal eq
                p₁∘universal≈h₁  : ∀ {eq : f ∘ h₁ ≡ g ∘ h₂} →
                         p₁ ∘ universal eq ≡ h₁
                p₂∘universal≈h₂  : ∀ {eq : f ∘ h₁ ≡ g ∘ h₂} →
                         p₂ ∘ universal eq ≡ h₂

        record PullbackT (f : X ⇒ Z) (g : Y ⇒ Z) : Set (o ⊔ ℓ) where 
            field 
                {P} : Ob 
                p₁ : P ⇒ X 
                p₂ : P ⇒ Y 
                isPullback : IsPullback p₁ p₂ f g 



        open ObjectProduct 𝒞 
        open Equalizer 𝒞 
        -- do this proof later
        Product×Equalizer⇒Pullback : (p : Product A B) → EqualizerT (f ∘ Product.π₁ p) (g ∘ Product.π₂ p) → PullbackT f g
        Product×Equalizer⇒Pullback = {!   !}

    module Finitely {o ℓ} (𝒞 : Category o ℓ) where 
        open import Level using (levelOfTerm)

        open Category 𝒞 
        open BinaryProducts 𝒞 using (BinaryProductsT)
        open Cartesian 𝒞 using (CartesianT)
        open Equalizer 𝒞 using (EqualizerT)
        open Pullback 𝒞 using (PullbackT; Product×Equalizer⇒Pullback)

        record FinitelyComplete : Set (levelOfTerm 𝒞) where 
            field 
                cartesian : CartesianT
                equalizer : ∀ {A B : Ob} → (f g : A ⇒ B) → EqualizerT f g

            pullback : ∀{X Y Z : Ob} → (f : X ⇒ Z) → (g : Y ⇒ Z) → PullbackT f g  
            pullback f g = Product×Equalizer⇒Pullback (BinaryProductsT.product (CartesianT.products cartesian)) (equalizer _ _)

    module Functor {o ℓ}(𝒞 𝒟 : Category o ℓ) where
        open import Level using (levelOfTerm)

        open Category 𝒞 renaming (Ob to Obᶜ; _⇒_ to _⇒ᶜ_; id to idᶜ; _∘_ to _∘ᶜ_)
        open Category 𝒟 renaming (Ob to Obᵈ; _⇒_ to _⇒ᵈ_; id to idᵈ; _∘_ to _∘ᵈ_)

        record FunctorT : Set (levelOfTerm 𝒞) where 
            field
                F₀ : Obᶜ → Obᵈ
                F₁ : {A B : Obᶜ} → (f : A ⇒ᶜ B) → F₀ A ⇒ᵈ F₀ B

                Fid : {A : Obᶜ} → F₁ (idᶜ {A}) ≡ idᵈ { F₀ A }
                Fcomp : {A B C : Obᶜ}{f : A ⇒ᶜ B}{g : B ⇒ᶜ C} → F₁ (g ∘ᶜ f) ≡ (F₁ g ∘ᵈ F₁ f)

    module NaturalTransformation where 
        open Functor
        record NaturalTransformationT {o ℓ : Level}{C : Category o ℓ}
                             {D : Category o ℓ}
                             (F G : FunctorT C D) : Set (o ⊔ ℓ ) where
            eta-equality
            open FunctorT F using (F₀; F₁)
            open FunctorT G renaming (F₀ to G₀; F₁ to G₁)
            open Category C renaming (_⇒_ to _⇒C_)
            open Category D renaming (_⇒_ to _⇒D_; _∘_ to _∘D_)

            field
                η           : ∀ X → F₀ X ⇒D G₀ X 
                commute     : ∀{X Y} → (f : X ⇒C Y) → (η Y ∘D F₁ f) ≡ (G₁ f ∘D η X) 

        _~>_ : {o ℓ : Level}{C : Category o ℓ} {D : Category o ℓ}(F G : FunctorT C D) → Set (o ⊔ ℓ )
        F ~> G = NaturalTransformationT F G

    module BiFunctor {o ℓ}(𝒞 𝒟 ℬ : Category o ℓ) where
        open import Level using (levelOfTerm)

        open Category ℬ renaming (Ob to Obᵇ; _⇒_ to _⇒ᵇ_; id to idᵇ; _∘_ to _∘ᵇ_)
        open Category 𝒞 renaming (Ob to Obᶜ; _⇒_ to _⇒ᶜ_; id to idᶜ; _∘_ to _∘ᶜ_)
        open Category 𝒟 renaming (Ob to Obᵈ; _⇒_ to _⇒ᵈ_; id to idᵈ; _∘_ to _∘ᵈ_)

        record BiFunctorT : Set (levelOfTerm 𝒞) where 
            field
                F₀ : Obᵇ → Obᶜ → Obᵈ
                F₁ : {A A' : Obᵇ}{B B' : Obᶜ} → (f : A ⇒ᵇ A')(g : B ⇒ᶜ B') → F₀ A B ⇒ᵈ F₀ A' B'

                Fid : {A : Obᵇ}{B : Obᶜ} → F₁ (idᵇ {A}) (idᶜ {B}) ≡ idᵈ { F₀ A B }
                Fcomp : {A B C : Obᵇ}{f  : A ⇒ᵇ B}{g  : B ⇒ᵇ C}
                        {X Y Z : Obᶜ}{f' : X ⇒ᶜ Y}{g' : Y ⇒ᶜ Z}
                    → F₁ (g ∘ᵇ f) (g' ∘ᶜ f') ≡ (F₁ g  g' ∘ᵈ F₁ f f')

    module Iso{o ℓ} (𝒞 : Category o ℓ) where 
        open Category 𝒞

        infix 4 _≅_
        record _≅_ (A B : Ob) : Set (ℓ ⊔ o) where
            field
                from : A ⇒ B
                to   : B ⇒ A
                isoˡ : to ∘ from ≡ id
                isoʳ : from ∘ to ≡ id


    module Commutation {o ℓ}(𝓒 : Category o ℓ) where
        open Category 𝓒

        infix 1 [_⇒_]⟨_≡_⟩
        [_⇒_]⟨_≡_⟩ : ∀ (A B : Ob) → A ⇒ B → A ⇒ B → Set _
        [ A ⇒ B ]⟨ f ≡ g ⟩ = f ≡ g

        infixl 2 connect
        connect : ∀ {A C : Ob} (B : Ob) → A ⇒ B → B ⇒ C → A ⇒ C
        connect B f g = g ∘ f

        syntax connect B f g = f ⇒⟨ B ⟩ g
        
    module Monoidal {o ℓ}(𝒞 : Category o ℓ) where
        open import Level using (levelOfTerm)
        open BiFunctor using (BiFunctorT)
        open Iso 𝒞 
        open _≅_

        open Category 𝒞
        open Commutation 𝒞
        
        record MonoidalT : Set (levelOfTerm 𝒞) where 
            field 
                ⊗ : BiFunctorT 𝒞 𝒞 𝒞
                unit : Ob
                

            open BiFunctorT ⊗ 
            infixr 10 _⊗₀_ _⊗₁_ 

            _⊗₀_ : Ob → Ob → Ob
            _⊗₀_ = F₀

            _⊗₁_ : {X Y Z W : Ob} → X ⇒ Y → Z ⇒ W → (X ⊗₀ Z) ⇒ (Y ⊗₀ W)
            _⊗₁_ = F₁          

            field 
                unitorˡ : {X : Ob} → unit ⊗₀ X ≅ X
                unitorʳ : {X : Ob} → X ⊗₀ unit ≅ X
                associator : {X Y Z : Ob} → (X ⊗₀ Y) ⊗₀ Z ≅ X ⊗₀ (Y ⊗₀ Z)

            private 
                λ⇒ : {X : Ob} → (unit ⊗₀ X) ⇒ X
                λ⇒ {X} = (unitorˡ {X}) .from  

                λ⇐ : {X : Ob} →  X ⇒ (unit ⊗₀ X)
                λ⇐ {X} = (unitorˡ {X}) .to

                ρ⇒ : {X : Ob} → (X ⊗₀ unit) ⇒ X
                ρ⇒ {X} = (unitorʳ {X}) .from  
                 
                ρ⇐ : {X : Ob} →  X ⇒ (X ⊗₀ unit)
                ρ⇐ {X} = (unitorʳ {X}) .to

                α⇒ : {X Y Z : Ob} → ((X ⊗₀ Y) ⊗₀ Z) ⇒ (X ⊗₀ (Y ⊗₀ Z))
                α⇒ {X}{Y}{Z} = associator {X} {Y} {Z} .from

                α⇐ : {X Y Z : Ob} → (X ⊗₀ (Y ⊗₀ Z)) ⇒ (((X ⊗₀ Y) ⊗₀ Z))
                α⇐ {X}{Y}{Z} = associator {X} {Y} {Z} .to
            field
                pentagon : { X Y Z W : Ob } → [ (((X ⊗₀ Y) ⊗₀ Z) ⊗₀ W) ⇒ (X ⊗₀ Y ⊗₀ Z ⊗₀ W) ]⟨
                                                    α⇒ ⊗₁ id ⇒⟨ ((X ⊗₀ Y ⊗₀ Z) ⊗₀ W) ⟩ 
                                                    α⇒       ⇒⟨ (X ⊗₀ (Y ⊗₀ Z) ⊗₀ W) ⟩ 
                                                    id ⊗₁ α⇒ 
                                                ≡ 
                                                    α⇒ ⇒⟨ ((X ⊗₀ Y) ⊗₀ Z ⊗₀ W) ⟩ 
                                                    α⇒ ⟩

    module Reasonging {o h}(C : Category o h) where 
        open import Cubical.Foundations.Prelude
        open Category C
        private
            variable
                X Y : Ob
                a b c d f : X ⇒ Y

        module Pre (ab≡cd : a ∘ b ≡ c ∘ d) where
            pre : f ∘ (a ∘ b) ≡ f ∘ (c ∘ d) 
            pre {f = f} = cong₂ _∘_ refl ab≡cd
        
        module Pulls (ab≡c : a ∘ b ≡ c) where

            pullʳ : (f ∘ a) ∘ b ≡ f ∘ c
            pullʳ {f = f} = 
                (f ∘ a) ∘ b  ≡⟨ sym assoc ⟩ 
                f ∘ (a ∘ b)  ≡⟨ cong₂ _∘_  refl ab≡c ⟩ 
                f ∘ c        ∎
            
            pullˡ : a ∘ b ∘ f ≡ c ∘ f 
            pullˡ {f = f} = 
                a ∘ b ∘ f   ≡⟨ assoc ⟩ 
                (a ∘ b) ∘ f ≡⟨ cong₂ _∘_ ab≡c refl ⟩ 
                c ∘ f ∎

        open Pulls public

        module Pushes (c≡ab : c ≡ a ∘ b) where
            pushʳ : f ∘ c ≡ (f ∘ a) ∘ b
            pushʳ {f = f} = 
                f ∘ c       ≡⟨ cong₂ _∘_ refl c≡ab ⟩ 
                f ∘ (a ∘ b) ≡⟨ assoc ⟩ 
                (f ∘ a) ∘ b ∎


            pushˡ : c ∘ f ≡ a ∘ (b ∘ f)
            pushˡ {f = f} = 
                c ∘ f       ≡⟨ cong₂ _∘_ c≡ab refl ⟩ 
                (a ∘ b) ∘ f ≡⟨ sym assoc ⟩ 
                a ∘ (b ∘ f) ∎


        open Pushes public
            

    -- Displayed Categories
    -- https://arxiv.org/pdf/1705.04296.pdf
    -- https://1lab.dev/Cat.Displayed.Base.html#682

    -- idea, add structure to some base category
    -- example: Sets & functions -> monoids & monoid homs
    open import Cubical.Core.Everything using (_≡_; PathP)
    record Displayed {o ℓ} (B : Category o ℓ) (o' ℓ' : Level) : Set (o ⊔ ℓ ⊔ lsuc o' ⊔ lsuc ℓ') where 
        open Category B
        -- data 
        field 
            Ob[_] : Ob → Set o'
            Hom[_] : ∀{x y : Ob} → x ⇒ y → Ob[ x ] → Ob[ y ] → Set ℓ'
            id' : ∀ {a : Ob} {x : Ob[ a ]} → Hom[ id ] x x  
            _∘'_ : ∀ {a b c x y z}{f : b ⇒ c}{g : a ⇒ b} → 
                Hom[ f ] y z → Hom[ g ] x y → Hom[ f ∘ g ] x z

        infixr 40 _∘'_

        -- equalities in the displayed category should respect equalities in the base?
        -- not quite what this is
        _≡[_]_ : ∀ {a b x y}{f g : a ⇒ b} → Hom[ f ] x y → f ≡ g → Hom[ g ] x y → Set ℓ'
        _≡[_]_ {a} {b} {x} {y} f' p g' = PathP (λ i → Hom[ p i ] x y) f' g'

        infix 30 _≡[_]_

        -- laws 
        field 
         --   Hom[_]-set : ∀{a b : Ob} (f : a ⇒ b) → (x : Ob[ a ]) → (y : Ob[ b ]) → is-set (Hom[ f ] x y)
            idr' : ∀ {a b x y}{f : a ⇒ b} → (f' : Hom[ f ] x y) → (f' ∘' id') ≡[ idr  ] f'
            idl' : ∀ {a b x y}{f : a ⇒ b} → (f' : Hom[ f ] x y) → (id' ∘' f') ≡[ idl  ] f'
            assoc' : ∀ {a b c d w x y z}{f : c ⇒ d} {g : b ⇒ c}{h : a ⇒ b} → 
                (f' : Hom[ f ] y z) → (g' : Hom[ g ] x y) → (h' : Hom[ h ] w x) → 
                f' ∘' (g' ∘' h') ≡[ assoc ] ((f' ∘' g') ∘' h' )

    module F-alg {o ℓ} (𝒞 : Category o ℓ) where 
        open Functor
    
        record F-Algebra (F : FunctorT 𝒞 𝒞) : Set (o ⊔ ℓ) where 
            open Category 𝒞
            open FunctorT F
            field 
                carrier : Ob
                alg : F₀ carrier ⇒ carrier
            
        
        iterate : {F : FunctorT 𝒞 𝒞} → F-Algebra F → F-Algebra F
        iterate {F} Falg = record { 
                            carrier = F₀ carrier ; 
                            alg = F₁ alg
                            }
            where 
                open FunctorT F 
                open F-Algebra Falg


        record F-Alg-Mor {F : FunctorT 𝒞 𝒞} (Falg Galg : F-Algebra F) : Set (o ⊔ ℓ) where
            open Category 𝒞
            open FunctorT F 
            module X = F-Algebra Falg 
            module Y = F-Algebra Galg 
            field 
                alg-map : X.carrier ⇒ Y.carrier
                commutes : (alg-map ∘ X.alg) ≡ (Y.alg ∘ F₁ alg-map)

        Eq-F-Alg-Mor : {F : FunctorT 𝒞 𝒞}{F G : F-Algebra F}{ϕ ψ : F-Alg-Mor F G}
            → F-Alg-Mor.alg-map ϕ ≡ F-Alg-Mor.alg-map ψ →  ϕ ≡ ψ
        Eq-F-Alg-Mor = {!   !}
            
        open Category
        F-Algebras : (F : FunctorT 𝒞 𝒞) → Category (o ⊔ ℓ) (o ⊔ ℓ) 
        F-Algebras F .Ob    = F-Algebra F
        F-Algebras F ._⇒_   = F-Alg-Mor
        F-Algebras F .id {x} = record { alg-map = 𝒞 .id ; commutes = 
            (𝒞 ∘ 𝒞 .id) alg         ≡⟨ 𝒞 .idl ⟩ 
            alg                      ≡⟨ sym (𝒞 .idr) ⟩ 
            (𝒞 ∘ alg) (𝒞 .id)       ≡⟨ cong₂ (𝒞 ._∘_) refl (sym Fid) ⟩ 
            (𝒞 ∘ alg) (F₁ (𝒞 .id))  ∎ }
            where 
                open F-Algebra x
                open FunctorT F

        F-Algebras F ._∘_ {x}{y}{z} ϕ ψ  = new
            where 
                open F-Alg-Mor ϕ renaming (alg-map to alg-map₂; commutes to commutes₂)
                open F-Alg-Mor ψ renaming (alg-map to alg-map₁; commutes to commutes₁)
                open F-Algebra x renaming (carrier to carrier₁; alg to alg₁)
                open F-Algebra y renaming (carrier to carrier₂; alg to alg₂)
                open F-Algebra z renaming (carrier to carrier₃; alg to alg₃)

                open F-Alg-Mor
                open FunctorT F

                open Category 𝒞 renaming (_∘_ to _∙_; assoc to assoc')
                new : F-Alg-Mor x z 
                new .alg-map = alg-map₂ ∙ alg-map₁
                new .commutes = 
                    (alg-map₂ ∙ alg-map₁) ∙ alg₁ ≡⟨ sym assoc' ⟩ 
                    alg-map₂ ∙ (alg-map₁ ∙ alg₁) ≡⟨ cong₂ _∙_ refl commutes₁ ⟩
                    alg-map₂ ∙ (alg₂ ∙ F₁ alg-map₁) ≡⟨ assoc' ⟩ 
                    (alg-map₂ ∙ alg₂) ∙ F₁ alg-map₁ ≡⟨ cong₂ _∙_ commutes₂ refl ⟩
                    (alg₃ ∙ F₁ alg-map₂) ∙ F₁ alg-map₁ ≡⟨ sym assoc' ⟩
                    alg₃ ∙ (F₁ alg-map₂ ∙ F₁ alg-map₁) ≡⟨ cong₂ _∙_ refl (sym Fcomp) ⟩ 
                    alg₃ ∙ (F₁ (alg-map₂ ∙ alg-map₁)) ∎
                
                
        F-Algebras F .idl   = Eq-F-Alg-Mor (𝒞 .idl)
        F-Algebras F .idr   = Eq-F-Alg-Mor (𝒞 .idr)
        F-Algebras F .assoc = Eq-F-Alg-Mor (𝒞 .assoc)

        
  