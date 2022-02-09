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
open import CutEqs
--open import MulticatLaws

-- ====================================================================

-- completeness

cmplt : {A B : Fma} → A ⇒ B → just A ∣ [] ⊢ B
cmplt id = ax
cmplt (f ∘ g) = scut (cmplt g) (cmplt f)
cmplt (f ⊸ g) = ⊸r (⊸l (uf (cmplt f)) (cmplt g))
cmplt i = ⊸l Ir ax
cmplt j = ⊸r (Il (uf ax))
cmplt L = ⊸r (⊸r (⊸l (uf (⊸l (uf ax) ax)) ax))
cmplt s = ⊸r (⊸r (ex {Γ = []} (⊸l (uf ax) (⊸l (uf ax) ax))))

-- ====================================================================

-- the "cmplt" function is well-defined, since it sends ≐-related
-- derivations to ≗-related derivations.

≐cmplt≗ : {A B : Fma} {f g : A ⇒ B} → f ≐ g → cmplt f ≗ cmplt g
≐cmplt≗ refl = refl
≐cmplt≗ (~ p) = ~ (≐cmplt≗ p)
≐cmplt≗ (p ∙ q) = (≐cmplt≗ p) ∙ (≐cmplt≗ q)
≐cmplt≗ (p ∘ q) = cong-scut (≐cmplt≗ q) (≐cmplt≗ p)
≐cmplt≗ (p ⊸ q) = ⊸r (⊸l (uf (≐cmplt≗ p)) (≐cmplt≗ q))
≐cmplt≗ lid = ≡-to-≗ (scut-unit _)
≐cmplt≗ rid = refl
≐cmplt≗ (ass {h = h}) = scutscut-vass (cmplt h) _ _ 
≐cmplt≗ f⊸id = ~ ax⊸
≐cmplt≗ f⊸∘ = refl
≐cmplt≗ (ni {f = f}) = ⊸l refl (~ ≡-to-≗ (scut-unit _)) 
≐cmplt≗ (nj {f = f}) =
  proof≗
    ⊸r (Il (uf (scut (scut (cmplt f) ax) ax)))
  ≗〈 ⊸r (Il (uf (≡-to-≗ (scut-unit _)))) 〉 
    ⊸r (Il (uf (scut (cmplt f) ax)))
  ≗〈 ⊸r (Il (uf (≡-to-≗ (scut-unit _)))) 〉
    ⊸r (Il (uf (cmplt f)))
  qed≗
≐cmplt≗ (nL {f = f}{g}{h}) =
  proof≗
    ⊸r (⊸r (⊸l (uf (⊸l (uf (cmplt f)) (scut (cmplt g) ax))) (cmplt h)))
  ≗〈 ⊸r (⊸r (⊸l (uf (⊸l refl (≡-to-≗ (scut-unit _)))) refl)) 〉 
    ⊸r (⊸r (⊸l (uf (⊸l (uf (cmplt f)) (cmplt g))) (cmplt h)))
  ≗〈 ⊸r (⊸r (⊸l (uf (⊸l (uf (~ ≡-to-≗ (scut-unit _))) refl)) (~ ≡-to-≗ (scut-unit _)))) 〉
    ⊸r (⊸r (⊸l (uf (⊸l (uf (scut (cmplt f) ax)) (cmplt g))) (scut (cmplt h) ax)))
  qed≗
≐cmplt≗ LLL = refl
≐cmplt≗ ijL = ~ ax⊸
≐cmplt≗ Lj =
  proof≗
    ⊸r (⊸r (Il (uf (⊸l (uf ax) ax))))
  ≗〈 ⊸r ⊸rIl 〉
    ⊸r (Il (⊸r (uf (⊸l (uf ax) ax))))
  ≗〈 ⊸r (Il ⊸ruf) 〉
    ⊸r (Il (uf (⊸r (⊸l (uf ax) ax))))
  ≗〈 ~ (⊸r (Il (uf ax⊸))) 〉
    ⊸r (Il (uf ax))
  qed≗
≐cmplt≗ iL = refl
≐cmplt≗ ij = ~ axI
≐cmplt≗ ns =
  ⊸r (⊸r (ex (⊸l (uf (≡-to-≗ (scut-unit _)))
                   (⊸l (uf (≡-to-≗ (scut-unit _)))
                        (~ (≡-to-≗ (scut-unit _)))))))
≐cmplt≗ sss = ⊸r (⊸r (ex⊸r ∙ ⊸r (ex-braid ∙ ex (ex (ex⊸l₂)))))
≐cmplt≗ sL1 = ⊸r (⊸r (~ ex⊸r))
≐cmplt≗ sL2 = refl
≐cmplt≗ sL3 = ⊸r (⊸r (⊸r (ex⊸l₁ ∙ ⊸l exuf refl)))
≐cmplt≗ ss = ⊸r (⊸r ex-iso ∙ ⊸r⊸l ∙ ⊸l refl (~ ax⊸)) ∙ (~ ax⊸)
