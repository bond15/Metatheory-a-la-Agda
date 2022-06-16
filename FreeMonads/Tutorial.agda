{-# OPTIONS --guardedness #-}
{-# OPTIONS --type-in-type #-} -- These two flags are just needed for the IO monad
module Tutorial where 


-- This modules contains 3 DSLs
-- One describing a Console with read and write actions
-- One describing a KeyValue store with get and put actions
-- One describing a LoginServer
module DSLs where 

    open import FreeMonad using (Functor; Free; liftF; Monad)
    open Monad{{...}}

    
    module ConsoleDSL where 
        open import Data.String
        open import Data.Unit
        open import Function using (id;_∘_)

        -- A datatype describing the API for a console
        data ConsoleF (X : Set) : Set where 
            -- PutStrLn takes a string to output
            PutStrLn : String → X → ConsoleF X 
            -- GetLine takes a continuation which is feed a String
            GetLine  : (String → X) → ConsoleF X

        -- This can be ignored :) 
        instance
            con-F : Functor ConsoleF
            con-F = record { fmap = λ{ f (PutStrLn s a) → PutStrLn s (f a)
                                     ; f (GetLine m)    → GetLine (f ∘ m) }}
        
        -- ConsoleF describes the Console API
        -- Console is the monad we can program in using our API
        Console = Free ConsoleF

        -- Smart constructors
        -- These are what you actually use to program with.
        putStrLn : String → Console ⊤
        putStrLn s = liftF (PutStrLn s tt)

        getLine : Console String 
        getLine = liftF (GetLine id)


        -- An example program in this DSL.
        -- This is a Console program that returns a String
        prog : Console String 
        prog = do 
                putStrLn "Input your user ID"
                uid ← getLine
                return uid
        -- This program has no interpretation. Think "programming against an interface"
        -- `putStrLn` and `getLine` are commands that have no concrete implementation.
        -- We can give them implementations later. 

    
    -- Next a Key Value Store DSL
    module KeyValDSL where 
        open import Data.String 
        open import Function
        open import Data.Maybe hiding (_>>=_)
        open import Data.Unit
        open import Data.Nat

        -- A key value store API with String keys and values of type A.
        data KeyValF (A : Set)(X : Set) : Set where 
            -- Gey Key takes a String key used to look up a value
            -- And a "continuation" (Maybe A → X) to run once a value has been found or not
            GetKey : String → (Maybe A → X) → KeyValF A X 
            PutKey : String → A → X → KeyValF A X

        -- you can ignore this :)
        instance
            kv-F : {A : Set} → Functor (KeyValF A)
            kv-F = record { fmap = λ{ f (GetKey s m) → GetKey s (f ∘ m)
                                    ; f (PutKey s₁ s₂ a) → PutKey s₁ s₂ (f a)}}

        -- Like Console, KeyValue is the monad we can program in
        KeyVal : {Set} → Set → Set
        KeyVal {A} = Free (KeyValF A)

        -- smart constructors
        getKey : {A : Set} → String → KeyVal (Maybe A)
        getKey s = liftF (GetKey s id)

        putKey : {A : Set} → String → A → KeyVal ⊤
        putKey k v = liftF (PutKey k v tt)

        -- an example program using the Key Value API
        prog : KeyVal {ℕ} ⊤
        prog = do 
                v ← getKey "x"
                v' ← case v of λ { (just x) → return (x + x + 4)
                                  ; nothing → return 0}
                putKey "x" v' 
        -- again getKey and putKey have no concrete implementation



    -- one last DSL
    module LoginServerDSL where 
        open import Function
        open import Data.String
        open import Data.Nat
        open import Data.Unit
        open import Data.Bool
        open import Data.Maybe hiding(_>>=_)
        open Functor

        data LoginServerF (X : Set) : Set where 
            Input   : (String → X) → LoginServerF X
            Output  : String → X → LoginServerF X
            NewUser : String → String → X → LoginServerF X
            LookupUser : String → (Maybe String → X) → LoginServerF X
            ValidateUser : String → (Bool → X) → LoginServerF X

        -- you can ignore this :)
        instance 
            LS-F : Functor LoginServerF
            LS-F .fmap f (Input x) = Input (f ∘ x)
            LS-F .fmap f (Output x x₁) = Output x (f x₁)
            LS-F .fmap f (NewUser x x₁ x₂) = NewUser x x₁ (f x₂)
            LS-F .fmap f (LookupUser x x₁) = LookupUser x (f ∘ x₁)
            LS-F .fmap f (ValidateUser x x₁) = ValidateUser x (f ∘ x₁)

        LoginServer = Free LoginServerF

        -- smart constructors
        input : LoginServer String 
        input = liftF (Input id)

        output : String → LoginServer ⊤ 
        output s = liftF (Output s tt)

        newUser : String → String → LoginServer ⊤ 
        newUser s s' = liftF (NewUser s s' tt)

        lookupUser : String → LoginServer (Maybe String) 
        lookupUser s = liftF (LookupUser s id)

        validate : String → LoginServer Bool
        validate s = liftF (ValidateUser s id)

        -- A login server program that returns a Bool
        -- again, output, input, validate, lookupUser, newUser have no concrete implementation
        -- the implementation can be chosen later
        prog : LoginServer Bool 
        prog = do
                output "Enter user id"
                uid ← input
                maybeuser ← lookupUser uid
                res ← case maybeuser of λ{(just user) → validate user
                                         ; nothing → do 
                                                        output "user not found"
                                                        return false}
                return res




-- So far 3 DSLs have been defined and 3 example programs written in those DSLs
-- The programs are just syntax and they have no concrete implementation.
-- Now its time to show how to give a DSL an implementation

module Implementation where

    -- 1st step in choosing an implementation is choosing a sufficient monad.
    -- The monad of should be able to support the operations the DSL is modeling.
    -- The Console DSL handles basic input output with a terminal, So our choice of Monad should also be able to do that.
    -- Here we provide an implementation of the Console DSL via the IO monad.
    module ConsoleIOImplementation where
        open import Function
        open DSLs.ConsoleDSL
        open import Data.String
        open import Data.List using (map)
        open import FreeMonad
        open import IO
        open import TypeClassInstances
        open _~>_ -- NaturalTransformation
        
        -- To provide an interpretation of a DSl we must say what each action in that DSL is mapped to
        -- This is a very straight forward interpretation where we map `PutStrLn` exactly to the IO monad's `putStrLn`
        Con~>IO : ConsoleF ~> IO 
        Con~>IO .α (PutStrLn s a) = IO.putStrLn s >> return a
        Con~>IO .α (GetLine cont) = IO.getLine >>= λ s → return (cont s)

        -- We don't have to be this restrictive though.. we are free to have interpretations like this..
        filter : String → String 
        filter "PBJ" = "Reuban"
        filter "Ranch" = "Caesar"
        filter "user" = "POWER USER"
        filter s = s
        
        Con~>IO` : ConsoleF ~> IO
        Con~>IO` .α (PutStrLn s a) = -- instead of simply printing the string `s`, 
                                    -- this interpretation warns that its output is filtered
                                    -- and then prints the filtered `s`
                                    do 
                                        IO.putStrLn "Warning: this output is censored"
                                        IO.putStrLn (unwords (map filter (words s)))
                                        return a
        Con~>IO` .α (GetLine cont) = IO.getLine >>= λ s → return (cont s)

        {-  
            Now that we have interpretations of the Console DSL,
            we can "compile" a concrete program from our original program
            recall our example program..
            
                prog : Console String 
                prog = do 
                        putStrLn "Input your user ID"
                        uid ← getLine
                        return uid    

            let's compile this program using each of our interpretations
        -}
        
        -- This "compiler" takes any Console program. 
        -- It returns a program in the IO monad, which can be run!
        compiler₁ : {A : Set} → Console A → IO A
        compiler₁ = foldFree Con~>IO

        -- given the compiler using the Con~>IO interpretation, lets compile `prog`
        compiledprog₁ : IO String 
        compiledprog₁ = compiler₁ prog

        {- 
            this is the resulting program:

            compiledprog₁ : IO String 
            compiledprog₁ = do 
                                IO.putStrLn "Input your user ID"
                                uid ← IO.getLine
                                return uid 

            now for the other interpretation
        
        -}

        compiler₂ : {A : Set} → Console A → IO A 
        compiler₂ = foldFree Con~>IO`

        compiledprog₂ : IO String 
        compiledprog₂ = compiler₂ prog
        {-
            this is the resulting program:

            compiledprog₂ : IO String
            compiledprog₂ = do 
                                IO.putStrLn "Warning: this output is censored"
                                IO.putStrLn (unwords (map filter (words "Input your user ID")))
                                uid ← IO.getLine
                                return uid 

            so instead of prompting 
                "Input your user ID"

            this compiled program prompts
                "Warning: this output is censord"
                "Input your POWER USER ID"
        
        -}


        -- Note: those two interpretations both used the IO monad. 
        -- We can provide an interpretation via other monads as well
        -- This next interpretation is using a monad transformer stack consisting of State stacked on top of IO
        -- No worries is this is new terminology... Just think a Monad with IO and stateful computations

    module ConsolMImplementation where 
        open DSLs.ConsoleDSL
        open import FreeMonad
        open import Store
        open import TypeClassInstances
        open _~>_
        open Monad{{...}}

        -- M = StateT Store IO 
        --  where 
        --      Store = List (String × String)
        -- So a monad with a key value store represented by a List of pairs of Strings, 
        -- and the monad also has IO capabilities
        Con~>M : ConsoleF ~> M 
        Con~>M .α (PutStrLn s a) = print s >> return a
        Con~>M .α (GetLine cont) = read >>= λ s → return (cont s)

    -- Now an implementation for the KeyValue DSl
    module KeyValMImplementation where 
        open import Data.String
        open DSLs.KeyValDSL
        open import FreeMonad
        open import Store
        open import TypeClassInstances
        open _~>_
        open Monad{{...}}

        KV~>M : KeyValF String ~> M 
        KV~>M .α (GetKey k cont) = do 
                                    v ← find k
                                    return (cont v)
        KV~>M .α (PutKey k v a) = do 
                                    put k v 
                                    return a


    -- Now instead of providing a direct implementation for the LoginServer DSL.. 
    -- we can instead say that the KeyValue DSL and Console DSL are sufficient to implement the Login Server DSL
    -- for whatever choice of implementation the KeyValue or Console DSls chose!
    module LoginServerMImplementation where 
        open DSLs
        open ConsoleDSL hiding (prog)
        open KeyValDSL hiding (prog)
        open LoginServerDSL
        
        open import FreeMonad
        open import Store 
        open import TypeClassInstances
        open _~>_
        open Monad{{...}}

        open import Data.String
        open import Data.Bool
        open import Data.Maybe hiding (_>>=_)
        open import Function

        -- This give a concrete interpretation of the LoginServer DSL.
        -- we could do this... but instead lets take a different path!
        direct : LoginServerF ~> M 
        direct .α (Input x) = {!  !}
        direct .α (Output x x₁) = {!   !}
        direct .α (NewUser x x₁ x₂) = {!   !}
        direct .α (LookupUser x x₁) = {!   !}
        direct .α (ValidateUser x x₁) = {!   !}

        -- Lets use ConsoleDSL and KeyValueDSl to provide meaning to the LoginServer DSL

        -- combining the Console and Keyvalue DLSs
        KVConsole = Free (ConsoleF ⊹ KeyValF String)

        -- this injects our KeyVal constructors into our new combined monad
        kv : {A : Set} → KeyVal A → KVConsole A
        kv = right .α

        -- this injects our Console constructors into our new combined monad
        con : {A : Set} → Console A → KVConsole A 
        con = left .α

        -- This gives an abstract interpretation of the LoginServer DSL.
        -- here we are programming "against an interface" instead of "against concrete instances of an interface"

        
        userValidate : String → Bool 
        -- Pretend the user is represented by a String and this function does some validation logic
        userValidate s = true

        -- Here we say how to implement LoginServer via any possible implementations of KeyValue DSl and Console DSL
        LS~>Con+KV : LoginServerF ~> KVConsole
        LS~>Con+KV .α (Input cont)          = do 
                                                input ← con( getLine )
                                                return (cont input)
        LS~>Con+KV .α (Output s a)          = do 
                                                con( putStrLn s )
                                                return a
        LS~>Con+KV .α (NewUser k v a)       = do 
                                                kv( putKey ("User:" ++ k) v )
                                                return a
        LS~>Con+KV .α (LookupUser k cont)   = do 
                                                v ← kv( getKey ("User:" ++ k))
                                                return (cont v)
        LS~>Con+KV .α (ValidateUser k cont) = do 
                                                maybeuser ← kv( getKey ("User:" ++ k))
                                                res ← case maybeuser of λ { (just user) → return (userValidate user)
                                                                           ; nothing → return false }
                                                return (cont res)

        

        -- So given a concrete implementation of the Console and Keyvalue DSL (KV~>M and Con~>M),
        -- we get a concrete implementation of the LoginServer DSL (LoginServer~>M)
        open KeyValMImplementation using (KV~>M)
        open ConsolMImplementation using (Con~>M)


        compiler : LoginServer ~> M
        compiler = (Con~>M ⊞ KV~>M) ⊙ LS~>Con+KV

        {-
            now we can compile our original Login Server program
            
            prog : LoginServer Bool 
            prog = do
                    output "Enter user id"
                    uid ← input
                    maybeuser ← lookupUser uid
                    res ← case maybeuser of λ{(just user) → validate user
                                            ; nothing → do 
                                                            output "user not found"
                                                            return false}
                    return res
        
        -}

        compiled-prog : M Bool 
        compiled-prog = (compiler .α) prog




    
           