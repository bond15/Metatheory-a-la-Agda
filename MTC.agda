{-# OPTIONS --overlapping-instances #-}
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --guardedness #-}
module MTC where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂ ; cong-app; subst)


_∘_ : {X Y Z : Set} → (f : Y → Z) → (g : X → Y) → X → Z
f ∘ g = λ x → f(g x)

id : {A : Set} → A → A 
id a = a 


record Functor(F : Set → Set): Set where
    field
        fmap : {X Y : Set} → (f : X → Y) → F X → F Y
        -- laws

open Functor {{...}} 

record Monad (F : Set → Set){{_ : Functor F}} : Set where
    field 
        return : {A : Set} → A → F A 
        _>>=_ : {A B : Set}→ F A → (A → F B) → F B
    
    _>>_ : {A B : Set} → F A → F B → F B 
    x >> y = y
        -- laws
open Monad {{...}}

data Option (A : Set) : Set where 
    None : Option A 
    Some : A → Option A


opt-fmap : {X Y : Set} → (X → Y) → Option X → Option Y 
opt-fmap f None = None
opt-fmap f (Some x) = Some (f x)

OptionFunc : Functor Option
OptionFunc = record { 
                fmap = opt-fmap 
            }


open import Data.Nat
open import Data.Bool
 
isSeven : ℕ → Bool 
isSeven 7 = true
isSeven _ = false

_ : {{_ : Functor Option}} → Option ℕ → Option Bool 
_ = fmap isSeven 

Algebra : (Set → Set) → Set → Set 
Algebra F A = F A → A

{-# NO_POSITIVITY_CHECK #-}
data Fix (F : Set → Set) : Set where
    In : F (Fix F) → Fix F
open Fix

out : {F : Set → Set} → Fix F → F (Fix F)
out (In x) = x

lemma-out-in-iso-l : {F : Set → Set} → out{F} ∘ In ≡ id
lemma-out-in-iso-l = refl

{-
data Nat : Set where
    Z : Nat 
    S : Nat → Nat
-}


data NatF (A : Set) : Set where 
    Z : NatF A
    S : A → NatF A


Nat : Set 
Nat = Fix NatF


z : Nat 
z = In Z

s : Nat → Nat 
s n = In (S n)


three : Nat 
three = s (s (s z))

instance
    NatF-Functor : Functor NatF
    NatF-Functor = record {
                        fmap = λ{f Z → Z
                               ; f (S x) → S (f x) }
                    }




{-
data Exp : Set where 
    Val : ℕ → Exp 
    Add : Exp → Exp → Exp
-}
data ExpF (A : Set): Set where 
    Val : ℕ → ExpF A 
    Add : A → A → ExpF A

Exp : Set 
Exp = Fix ExpF

val : ℕ → Exp
val x = In (Val x)

add : Exp → Exp → Exp
add e₁ e₂ = In (Add e₁ e₂)

instance
    ExpF-Functor : Functor ExpF
    ExpF-Functor = record { fmap = λ{f (Val x) → Val x
                                   ; f (Add x y) → Add (f x) (f y) }}

eval-exp-alg : Algebra ExpF ℕ
eval-exp-alg (Val x) = x
eval-exp-alg (Add x y) = x + y



{-# TERMINATING #-}
cata : {F : Set → Set}{A : Set}{{_ : Functor F}} → Algebra F A → Fix F → A
cata alg = alg ∘ (fmap (cata alg) ∘ out)

eval : Exp → ℕ 
eval = cata eval-exp-alg

-- paramorphism (package result with original term)
open import Data.Product
RAlgebra : (Set → Set) → Set → Set 
RAlgebra F A = F (Fix F × A) → A

{-# TERMINATING #-}
para : {F : Set → Set}{A : Set}{{_ : Functor F}} → RAlgebra F A → Fix F → A 
para ralg = ralg ∘ (fmap < id , para ralg > ∘ out) 

{-
does not do what "expected"
it looks like pattern matching n layers deep... but it only processes one layer at a time
.... but if you use a mendler style algebra with an explicit recursor.. you could make this correct

even-alg : RAlgebra NatF Bool
even-alg Z = true
even-alg (S (In Z , _)) = false
even-alg (S (In (S _) , b)) = b

even : Nat → Bool 
even = para even-alg 
-}

even-alg : Algebra NatF Bool
even-alg Z = true
even-alg (S b) = not b

even : Nat → Bool 
even = cata even-alg


-- histomorphism (dynamic programming)

-- church encoded

MAlgebra : (Set → Set) → Set → Set
MAlgebra F A = ∀ {R : Set} → (R → A) → F R → A

FixM : (Set → Set) → Set 
FixM F = ∀ {A : Set} → MAlgebra F A → A

cataM : {F : Set → Set}{A : Set}{{_ : Functor F}} → MAlgebra F A → FixM F → A 
cataM malg fa = fa malg

eval-left : MAlgebra ExpF ℕ
eval-left ⟦_⟧ (Val x) = x
eval-left ⟦_⟧ (Add x y) = ⟦ x ⟧

Nat-ind :   (P : Nat → Set)
            (Hz : P z)
            (Hs : ∀ (n : Nat) → P n → P (s n)) 
            → Algebra NatF (Σ[ e ∈ Nat ] P e)
Nat-ind P hz hs Z = z , hz
Nat-ind P hz hs (S x) = s (proj₁ x) , hs (proj₁ x) (proj₂ x)

-- ensure that the built up terms are equivalent to the previous terms
WF-proof-alg : {F : Set → Set}{{_ : Functor F}}{P : Fix F → Set}
                → (alg : Algebra F (Σ[ e ∈ Fix F ] P e)) 
                → Set
WF-proof-alg alg = (proj₁ ∘ alg) ≡ (In ∘ fmap proj₁)


Nat-ind-WF : ∀(P : Nat → Set)(Hz : P z)(Hs : ∀ (n : Nat) → P n → P (s n))
    → WF-proof-alg (Nat-ind P Hz Hs)
Nat-ind-WF P Hz Hs = {!   !}


-- mendler algebra with a
{-
get stuck, can't unpack past the first layer because the ntested term is R

RMAlgebra : (Set → Set) → Set → Set
RMAlgebra F A = ∀ {R : Set} → (R → A) → F (R × A) → A

FixRM : (Set → Set) → Set 
FixRM F = ∀ {A : Set} → RMAlgebra F A → A

even-alg' : RMAlgebra NatF Bool
even-alg' ⟦_⟧ Z = true
even-alg' ⟦_⟧ (S (fst , snd)) with ⟦ fst ⟧
... | false = {!   !}
... | true = {!   !} 
-}


-- induction for natF
{-
NatF-ind : ∀(P : FixM NatF → Set)
            (Hz : ∀ (n : ℕ) → P ?)
            (Hs : ∀ (a : Nat) → P a → P (s a) )
            → Algebra NatF (Σ ? ? )

NatF-ind = {!   !}

-}


module Inj where

    data _⊹_ (F G : Set → Set) (E : Set) : Set where 
        Inl : F E → _⊹_ F G E 
        Inr : G E → _⊹_ F G E
    open _⊹_

    instance
        _ : {F G : Set → Set}{{_ : Functor F}}{{_ : Functor G}}→ Functor (F ⊹ G)
        _ = record { fmap = λ{ f (Inl x) → Inl (fmap f x)
                             ; f (Inr x) → Inr (fmap f x) } }

    record _<:_ (sub sup : Set → Set) {{_ : Functor sub}} {{_ : Functor sup}}: Set where
        field
            inj : {A : Set} → sub A → sup A
    open _<:_ {{...}}

    instance
        _ : {F : Set → Set}{{_ : Functor F}} → F <: F 
        _ = record { inj = id }

    instance 
        _ : {F G : Set → Set}{{_ : Functor F}}{{_ : Functor G}} → F <: (F ⊹ G)
        _ = record { inj = Inl}

    instance 
        _ : {F G H : Set → Set}{{_ : Functor F}}{{_ : Functor G}}{{_ : Functor H}}{{_ : F <: G}} → F <: (H ⊹ G)
        _ = record { inj = Inr ∘ inj }


    inject : {F G : Set → Set}{{_ : Functor F}}{{_ : Functor G}}{{_ : G <: F}} → G (Fix F) → Fix F
    inject = In ∘ inj

    data ValF (E : Set) : Set where 
        Val' : ℕ → ValF E

    instance
        _ : Functor ValF
        _ = record { fmap = λ{ f (Val' x) → Val' x } }

    val' : {F : Set → Set}{{_ : Functor F}}{{_ : ValF <: F}} → ℕ → Fix F 
    val' n = inject (Val' n)

    data AddF (E : Set) : Set where
        Add' : E → E → AddF E

    instance
        _ : Functor AddF 
        _ = record { fmap = λ {f (Add' x y) → Add' (f x) (f y)} }

    add' : {F : Set → Set}{{_ : Functor F}}{{_ : AddF <: F}}→ Fix F → Fix F → Fix F 
    add' x y = inject (Add' x y)


    data MultF (E : Set) : Set where 
        Mult : E → E → MultF E
    
    instance
        _ : Functor MultF 
        _ = record { fmap = λ{ f (Mult x y) → Mult (f x) (f y)} }

    mult : {F : Set → Set}{{_ : Functor F}}{{_ : MultF <: F}} → Fix F → Fix F → Fix F 
    mult x y =  inject (Mult x y) 

    AVF : Set → Set 
    AVF = ValF ⊹ AddF

    AV : Set 
    AV = Fix AVF

    baz : AV 
    baz = add' (add' (val' 3) (val' 5)) (val' 5)

    AVMF : Set → Set 
    AVMF = ValF ⊹ (AddF ⊹ MultF)

    AVM : Set 
    AVM = Fix AVMF

    foo : AVM
    foo = mult (add' (val' 5) (val' 3)) (val' 9)

    bar : AVM -- or AV
    bar = add' (add' (val' 3) (val' 5)) (val' 5)


    -- modular evaluation
    record EvalAlg (F : Set → Set): Set where
        field 
            evalAlg : Algebra F ℕ
    open EvalAlg{{...}}

    instance
        _ : {F G : Set → Set}{{_ : EvalAlg F}}{{_ : EvalAlg G}} → EvalAlg (F ⊹ G)
        _ = record { evalAlg = λ{(Inl x) → evalAlg x
                               ; (Inr x) → evalAlg x} } 

    instance 
        
        _ : EvalAlg ValF
        _ = record { evalAlg = λ{ (Val' x) → x }}

        _ : EvalAlg AddF
        _ = record { evalAlg = λ{ (Add' x y) → x + y } }

    eval' : {F : Set → Set}{{_ : Functor F}}{{_ : EvalAlg F}} → Fix F → ℕ
    eval' = cata evalAlg

    _ : ℕ 
    _ = eval' baz

    _ : eval' baz ≡ 13
    _ = refl



    {-# NO_POSITIVITY_CHECK #-}
    data Free (F : Set → Set) (A : Set) : Set where 
        pure : A → Free F A
        free : F (Free F A) → Free F A

    swaparg : {A B C : Set} → (A → B → C) → (B → A → C)
    swaparg f b a = f a b


    instance 
        {-# TERMINATING #-}
        _ : {F : Set → Set}{{_ : Functor F}} → Functor (Free F)
        _ = record { fmap = λ{ f (pure x) → pure (f x)
                             ; f (free x) → free (fmap (fmap f) x)} }

        {-# TERMINATING #-}
        _ : {F : Set → Set}{{_ : Functor F}} → Monad (Free F)
        _ = record { 
                return = pure ; 
                _>>=_ = λ{ (pure x) f → f x
                         ; (free x) f → free (fmap (swaparg _>>=_  f ) x) }}
        

    injectM : {A : Set}{F G : Set → Set}{{_ : Functor F}}{{_ : Functor G}}{{_ : G <: F}} → G (Free F A) → Free F A 
    injectM = free ∘ inj    

    data Unit : Set where 
        unit : Unit 
 
    -- claculator example
    data IncrF (T : Set) : Set where 
        Incr : ℕ → T → IncrF T

    instance
        _ : Functor IncrF
        _ = record { fmap = λ{ f (Incr x y) → Incr x (f y) } }

    incr : {F : Set → Set}{{_ : Functor F}}{{_ : IncrF <: F}} → ℕ → Free F Unit 
    incr i = injectM (Incr i (pure unit))

    data RecallF (T : Set) : Set where 
        Recall : (ℕ → T) → RecallF T

    instance
        _ : Functor RecallF
        _ = record { fmap = λ{ f (Recall x) → Recall (f ∘ x) } }

    recall : {F : Set → Set}{{_ : Functor F}}{{_ : RecallF <: F}} → Free F ℕ 
    recall = injectM (Recall pure)

    tick : Free (RecallF ⊹ IncrF) ℕ
    tick = {!   !}
            {- Type checker instances resolver loops
              do 
                y ← recall
                incr 1
                return y 
            -}
    
    {-# TERMINATING #-}
    foldFree : {A B : Set}{F : Set → Set}{{_ : Functor F}} → (A → B) → (F B → B) → Free F A → B 
    foldFree f imp (pure x) = f x
    foldFree f imp (free x) = imp (fmap (foldFree f imp) x)

    data Mem : Set where 
        Mem' : ℕ → Mem
    
    record Run (F : Set → Set) {{_ : Functor F}} : Set where 
        field 
            runAlg : {A : Set} → Algebra F (Mem → (A × Mem))
    open Run {{...}}

    instance
        _ : Run IncrF
        _ = record { runAlg = λ{(Incr k r) (Mem' i) → r (Mem' (i + k))} }

        _ : Run RecallF
        _ = record { runAlg = λ{(Recall r) (Mem' i) → r i (Mem' i)} }

        _ : {F G : Set → Set}{{_ : Functor F}}{{_ : Functor G}}{{_ : Run F}}{{_ : Run G}} → Run (F ⊹ G)
        _ = record { runAlg = λ{(Inl x) → runAlg x
                              ; (Inr x) → runAlg x} }

    run : {A : Set}{F : Set → Set}{{_ : Functor F}}{{_ : Run F}} → Free F A → Mem → (A × Mem)
    run = foldFree _,_ runAlg


    -- Terminal Example
    open import Data.Char
    open import Data.String
    open import IO using (putStrLn ; IO)

    FilePath : Set 
    FilePath = String

    data TeleType (A : Set) : Set where 
        GetString : (String → A) → TeleType A   
        PutString : String → A → TeleType A

    instance
        _ : Functor TeleType
        _ = record { fmap = λ{ f (GetString x) → GetString (f ∘ x)
                             ; f (PutString x y) → PutString x (f y) } }

{-  ?? 
    getString : {A : Set}{F : Set → Set}{{_ : Functor F}}{{_ : TeleType <: F}} → Free F (IO A)
    getString = {!   !}
-} 
    

    data FileSystem (A : Set) : Set where 
        ReadFile : FilePath → (String → A) → FileSystem A 
        WriteFile : FilePath → String → A → FileSystem A

    record Exec (F : Set → Set){{_ : Functor F}} : Set where
        field
            execAlg : {A : Set} → Algebra F (IO A)
    open Exec{{...}}


    -- example program
    cat : FilePath → Free (TeleType ⊹ FileSystem) Unit 
    cat fp = {! do 
                    contents ← readFile fp
                    putString contents
                    return unit  !}


    getStrLn : IO String
    getStrLn = {!   !}
    instance
        _ : {F G : Set → Set}{{_ : Functor F}}{{_ : Functor G}}{{_ : Exec F}}{{_ : Exec G}} → Exec (F ⊹ G)
        _ = record { execAlg = λ{ (Inl x) → execAlg x
                                ; (Inr x) → execAlg x} }
                        
        _ : Exec TeleType
        _ = record { execAlg = λ{  (GetString io) → getStrLn IO.>>= io
                                 ; (PutString c io) → putStrLn c IO.>> io} }
    