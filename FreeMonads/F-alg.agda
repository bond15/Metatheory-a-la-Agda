{-# OPTIONS --allow-unsolved-metas #-}
module F-alg where 
    open import CatLib
    open import FreeMonadCat
    open import Cubical.Foundations.Prelude using (refl;funExt)
    open import Level 
    open Level renaming (suc to ℓ-suc; zero to ℓ-zero)
    module Example where 
        open Category
        open Functor
        open AgdaCat
        open F-alg Agda
        open import Data.Unit
        open import Data.Sum
        open import Data.Product
        open import Data.Nat
        
       -- {-# NO_POSITIVITY_CHECK #-}
       -- data Fix (F : Set → Set) : Set where 
        --    In : F (Fix F) → Fix F

        -- BinTreeF' (A) (X) = ⊤ ⊎ (X × A × X)
        data BinTreeF' (A : Set) (X : Set) : Set where 
            Leaf : BinTreeF' A X
            Node : X → A → X → BinTreeF' A X
        
        open FunctorT
        BinTreeF : {A : Set} → FunctorT Agda Agda 
        BinTreeF {A} .F₀ = BinTreeF' A
        BinTreeF .F₁ f Leaf = Leaf
        BinTreeF .F₁ f (Node x₁ a x₂) = Node (f x₁) a (f x₂)
        BinTreeF .Fid = funExt λ { Leaf → refl
                                 ; (Node x x₁ x₂) → refl }
        BinTreeF .Fcomp = funExt λ { Leaf → refl
                                   ; (Node x x₁ x₂) → refl}


        natTrees : Category (ℓ-suc ℓ-zero) (ℓ-suc ℓ-zero)
        natTrees = F-Algebras (BinTreeF {ℕ})
        
        module ex1 where 
            t : Ob natTrees
            t = record { carrier = ⊤ ; alg = λ x → tt }

            -- trees of depth 3
            t' : Ob natTrees
            t' = iterate-n t 3
            open F-Algebra t'
            
            {- ex
                    4
                   / \
                  3   0
                 / \  / \
                5  9  1  8
            -}

            ex : carrier  -- carrier := BinTreeF (BinTreeF (BinTreeF ⊤))
            ex = Node (Node (Node tt 5 tt) 3 (Node tt 9 tt)) 4 (Node (Node tt 1 tt) 0 (Node tt 8 tt))

        module ex2 where    
            -- want to sum over the whole tree

            sum : BinTreeF' ℕ ℕ → ℕ 
            sum Leaf = 0
            sum (Node x y z) = x + y + z
            
            sumalg : Ob natTrees 
            sumalg = record { carrier = ℕ ; 
                              alg = sum}

            sumalg-2 : Ob natTrees
            sumalg-2 = iterate-n sumalg 2

            open F-Algebra sumalg-2 renaming(carrier to s2carrier; alg to s2alg)

            -- max tree depth of 2
            ex : s2carrier 
            ex = Node (Node 1 3 5) 7 (Node 9 10 2)

            also : BinTreeF' ℕ (BinTreeF' ℕ ℕ)
            also = ex

            open FunctorT (BinTreeF {ℕ}) renaming (F₁ to fmap)
            -- how to recursivly apply `alg`?
            -- repeatedly apply (sum/alg) at each level using fmap to change levels?
            eval : ℕ
            eval = sum (fmap sum ex)


            s4 = iterate-n sumalg 4
            open F-Algebra s4 renaming (carrier to s4carrier; alg to s4alg)

            --t4 : s4carrier 
            t4 :  BinTreeF' ℕ (BinTreeF' ℕ (BinTreeF' ℕ (BinTreeF' ℕ ℕ)))
            t4 = Leaf
        
            eval4 : ℕ 
            eval4 = {! s4alg  !}