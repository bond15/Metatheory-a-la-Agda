module ClubEx where
open import Data.Unit
open import Data.Maybe hiding (_>>=_)
open import Function

open import FreeMonad
open Monad{{...}}

open import DSLs
open ClubDSL

showClubSiblings : Club ⊤
showClubSiblings = do 
                    display "Enter club id"
                    clubId ← getInput
                    members ← getClubMembers clubId 
                    case members of λ{ nothing → display "Sorry, club does not exist"
                                     ; (just x) → do -- more complicated logic here, but ignore for now
                                                    return tt
                                    }
                    return tt



module interp where 

    
    