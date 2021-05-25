{-# OPTIONS --rewriting #-}

module EqComplete where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import SeqCalc
open import CutEqs
open import Fsk
open import Complete

-- ====================================================================

-- the "cmplt" function is well-defined, since it sends ≐-related
-- derivations to ≗-related derivations.

eq-cmplt : ∀{A C} {f g : A ⇒ C} → f ≐ g → cmplt f ≗ cmplt g
eq-cmplt refl = refl
eq-cmplt (~ p) = ~ eq-cmplt p
eq-cmplt (p ∙ p₁) = eq-cmplt p ∙ eq-cmplt p₁
eq-cmplt (p ∘ p₁) = cong-scut (eq-cmplt p₁) (eq-cmplt p)
eq-cmplt (p ⊗ p₁) = ⊗l (⊗r (eq-cmplt p) (uf (eq-cmplt p₁)))
eq-cmplt lid = ≡-to-≗ (scut-unit _)
eq-cmplt rid = refl
eq-cmplt (ass {h = h}) = scutscut-vass (cmplt h) _ _
eq-cmplt f⊗id = ~ ax⊗
eq-cmplt (f⊗∘ {f = f}) = ⊗l (~ scut⊗r (cmplt f) _ _)
eq-cmplt nl = ⊗l (Il (uf (≡-to-≗ (scut-unit _))))
eq-cmplt (nρ {f = f}) = scut⊗r (cmplt f) _ _ ∙ ⊗r (≡-to-≗ (scut-unit _)) refl
eq-cmplt (nα {f = f}{g}) =
  ⊗l (⊗l (scut⊗r (cmplt f) _ _
          ∙ ⊗r (≡-to-≗ (scut-unit _))
               (uf (scut⊗r (cmplt g) _ _
                   ∙ ⊗r (≡-to-≗ (scut-unit _)) (uf (≡-to-≗ (scut-unit _)))))))
eq-cmplt (ns {f = f} {h = h}) =
  ⊗l (⊗l (scut-ex (cmplt f)
          ∙ ex (scut⊗r (cmplt f) _ _
               ∙ ⊗r (scut⊗r (cmplt f) _ _
                    ∙ ⊗r (≡-to-≗ (scut-unit _)) (uf (≡-to-≗ (scut-unit _))))
                    (uf (≡-to-≗ (scut-unit _))))))
eq-cmplt lρ = ~ axI
eq-cmplt lαρ = ax⊗
eq-cmplt lα = ⊗l (⊗l (Il (~ ⊗ruf) ∙ (~ ⊗rIl)) ∙ (~ ⊗r⊗l))
eq-cmplt αρ = refl
eq-cmplt ααα = refl
eq-cmplt (sss {A} {B} {C} {D}) = 
  ⊗l (⊗l (⊗l (ex (ex (~ ex⊗r₁)) ∙ ex-braid) ∙ ~ ex⊗l))
eq-cmplt sα1 = refl
eq-cmplt sα2 = ⊗l (⊗l (~ ex⊗l))
eq-cmplt sα3 = ⊗l (⊗l (ex⊗l ∙ ⊗l (ex⊗r₂ ∙ ⊗r refl exuf)))
eq-cmplt ss = ⊗l (⊗l ex-iso ∙ (~ ⊗r⊗l) ∙ ⊗r (~ ax⊗) refl) ∙ (~ ax⊗)


-- ====================================================================

-- the 4th coherence equation of operadic trees in:
-- Curien, Obradović, Ivanović:
-- "Syntactic aspects of hypergraph polytopes"

eq4-operadic-trees : ∀{A B C D} →
  cmplt (s ∘ α ∘ s {A}{B}{C} ⊗ id {D}) ≗ cmplt (α ⊗ id ∘ s)
eq4-operadic-trees {A}{B}{C}{D} =
  ⊗l (⊗l
    (proof≗
       ⊗l (ex {Γ = []} (ex {Γ = []} (ex {Γ = B ∷ []} (⊗r (⊗r ax (uf (⊗r ax (uf ax)))) (uf ax)))))
     ≗〈 ⊗l ex-iso 〉
       ⊗l (ex {Γ = B ∷ []} (⊗r (⊗r ax (uf (⊗r ax (uf ax)))) (uf ax)))
     ≗〈 ~ ex⊗l 〉
       ex {Γ = []} (⊗l (⊗r (⊗r ax (uf (⊗r ax (uf ax)))) (uf ax)))
     ≗〈 ex (~ ⊗r⊗l) 〉
       ex {Γ = []}  (⊗r (⊗l (⊗r ax (uf (⊗r ax (uf ax))))) (uf ax))
     qed≗))
