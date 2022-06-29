module DSLs where 
open import FreeMonad

module IncRecDSL where 
    open import Data.Nat 
    open import Data.Unit
    
    -- The DSL
    data Cmds (X : Set) : Set where 
        Incr : ℕ → X → Cmds X
        Recall : (ℕ → X) → Cmds X

    -- The DSL language requires a Functor instance. 
    -- This restriction is no longer needed in Freer Monads
    instance
        -- automaticaly deduced by Agsy
        Cmds-F : Functor Cmds
        Cmds-F = record { fmap = λ{ x (Incr x₁ x₂) → Incr x₁ (x x₂)
                            ; x (Recall x₁) → Recall (λ z → x (x₁ z)) }}


    -- The monad to program in
    M = Free Cmds

    -- smart constructors, one for each DSL construct
    incr : ℕ → M ⊤
    incr i = liftF  (Incr i tt)

    recall : M ℕ 
    recall = liftF (Recall λ x → x)


module KeyValDSL where 
    open import Data.String 
    open import Function
    open import Data.Maybe
    open import Data.Unit

    data KeyValF (A : Set)(X : Set) : Set where 
        GetKey : String → (Maybe A → X) → KeyValF A X 
        PutKey : String → A → X → KeyValF A X
        -- id : Get ∘ Put ≡ id 
        -- How to add Proof obligations?
        -- Try localization challenge problem (key valu store)
        -- Do proof algebras lift to monad algebras?
        -- bidirectional interp <-> abstract? in the case of deep embedding this might be possible?

    instance
        kv-F : {A : Set} → Functor (KeyValF A)
        kv-F = record { fmap = λ{ f (GetKey s m) → GetKey s (f ∘ m)
                                ; f (PutKey s₁ s₂ a) → PutKey s₁ s₂ (f a)}}

    KeyVal : {Set} → Set → Set
    KeyVal {A} = Free (KeyValF A)

    -- smart constructors
    getKey : {A : Set} → String → KeyVal (Maybe A)
    getKey s = liftF (GetKey s id)

    putKey : String → String → KeyVal ⊤
    putKey k v = liftF (PutKey k v tt)



module ConsoleDSL where 
    open import Data.String
    open import Data.Unit 
    open import Function

    data ConsoleF (X : Set) : Set where 
        PutStrLn : String → X → ConsoleF X 
        GetLine  : (String → X) → ConsoleF X

    instance
        con-F : Functor ConsoleF
        con-F = record { fmap = λ{ f (PutStrLn s a) → PutStrLn s (f a)
                                 ; f (GetLine m) → GetLine (f ∘ m) }}
    
    Console = Free ConsoleF

    putStrLn : String → Console ⊤
    putStrLn s = liftF (PutStrLn s tt)

    getLine : Console String 
    getLine = liftF (GetLine id)



module ClubDSL where 
    open import Data.String 
    open import Data.Maybe
    open import Data.Unit
    open import Function
    
    data ClubF (X : Set): Set where 
        GetClubMembers : String → (Maybe String → X) → ClubF X
        GetMemberClubs : String → (Maybe String → X) → ClubF X 
        GetInput       : (String → X) → ClubF X 
        Display        : String → X → ClubF X

    instance
        clubF-F : Functor ClubF 
        clubF-F = record { fmap = λ {f (GetClubMembers s m) → GetClubMembers s (f ∘ m)
                                   ; f (GetMemberClubs s m) → GetMemberClubs s (f ∘ m)
                                   ; f (GetInput m) → GetInput (f ∘ m)
                                   ; f (Display s a) → Display s (f a) }}

    -- Monad to program in
    Club = Free ClubF

    -- smart constructors
    getClubMembers : String → Club (Maybe String)
    getClubMembers s = liftF (GetClubMembers s id)

    getMemberClubs : String → Club (Maybe String) 
    getMemberClubs s = liftF (GetMemberClubs s id)

    getInput : Club String 
    getInput = liftF (GetInput id)

    display : String → Club ⊤ 
    display s = liftF (Display s tt)


 
 
module foo where 
    