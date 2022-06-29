{-# OPTIONS --type-in-type #-}
module ex where 
    open import Data.Sum

    data T₁ : Set where
            s₁ : T₁  

    data T₂ : Set where
            s₂ : T₂ 


    open import Data.Product
    T₃ : Set 
    T₃ = T₁ ⊎ T₂

    T₃' : Set 
    T₃' = Σ T₁ (λ _ → T₂)

    module console where
 
        -- 
        data ConsoleF (El₁ : T₃ → Set) (X : Set) : Set where 
            PutStrLn : El₁ (inj₁ s₁) → X → ConsoleF El₁ X 
            GetLine  : (El₁ (inj₁ s₁) → X) → ConsoleF El₁ X

    module keyvalue where

        open import Data.Maybe

        data KeyValF (El₂ : T₃ → Set) (A : Set)(X : Set) : Set where 
            GetKey : El₂ (inj₂ s₂) → (Maybe A → X) → KeyValF El₂ A X 
            PutKey : El₂ (inj₂ s₂) → A → X → KeyValF El₂ A X

    data _⊹_ (F G : Set → Set)(E : Set): Set where 
        InL : F E → (F ⊹ G) E 
        InR : G E → (F ⊹ G) E

    module combindthings 
        {Ty₁ Ty₂ : Set} 
        (El₁ : Ty₁ → Set)
        (El₂ : Ty₂ → Set)
        (F : (Ty₁ → Set) → Set → Set)
        (G : (Ty₂ → Set) → Set → Set)
        (E : Set)  where 

        open import Data.String
        
        --El₃ : Ty₁ ⊎ Ty₂ → Set 
        --El₃ (inj₁ s₁) = String
        --El₃ (inj₂ s₁) = String

        data _⊹'_ (E : Set) : Set where 
            InL' : {!   !}
            InR' : {!   !} 

    module combindthings'
        --{Ty₁ Ty₂ : Set} 
        (El₁ : T₃ → Set)
        (El₂ : T₃ → Set)
        (F : (T₃ → Set) →  Set → Set)
        (G : (T₃ → Set) →  Set → Set)
        (E : Set)  where 

        open import Data.Sum
        open import Data.Nat
        open import Data.String
        
        -- lift
        -- C Struct --> Coq/Agda      (easy proof, hard lift)
        --          --> Scala/Haskell (easy lift, limited proving capabilities)

        {-
            lifting C -> Coq
                Autocorres "like" tecsalkdjfa

            Coq -> C...
                Code Extractions -> Ocaml
        -}
        El₃ : T₃ → Set 
        El₃ (inj₁ s₁) = String
        El₃ (inj₂ s₂) = String




        data ⊹' (E : Set) : Set where 
            InL' : {! (F El₃ E) → ⊹' E !}
            InR' : {! (G El₃ E) !} 
            --InC : {!   !}
        

        
       

    

    open console 
    open keyvalue

    postulate 
        El₁ : T₁ → Set 
        El₂ : T₂ → Set
        V : Set  

    --combined = ConsoleF El₁ ⊹ KeyValF El₂ V

    open import FreeMonad

   -- free = Free combined

   

    
        