{-# OPTIONS --rewriting #-}

module Complete where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import SeqCalc
open import Fsk
--open import MulticatLaws

-- ====================================================================

-- completeness

-- (a more general function typed 〈 S ∣ Γ 〉 ⇒ C → S ∣ Γ ⊢ C is
-- constructed in the end of the file StrongComplete.agda)

cmplt : {A B : Fma} → A ⇒ B → just A ∣ [] ⊢ B
cmplt id = ax
cmplt (f ∘ g) = scut (cmplt g) (cmplt f)
cmplt (f ⊗ g) = ⊗l (⊗r (cmplt f) (uf (cmplt g)))
cmplt l = ⊗l (Il (uf ax))
cmplt ρ = ⊗r ax Ir
cmplt α = ⊗l (⊗l (⊗r ax (uf (⊗r ax (uf ax)))))
cmplt (s b) = ⊗l (⊗l (ex {Γ = []} b (⊗r (⊗r ax (uf ax)) (uf ax))))
