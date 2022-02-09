{-# OPTIONS --rewriting #-}

module CompleteSound where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import SeqCalc
open import Fsk
open import CutEqs
open import Complete
open import StrongComplete
open import Sound
open import EqComplete
open import SoundComplete

-- ====================================================================

-- Proof that ∀ f. strcmplt (sound f) ≐ f

cmpltsound' : {S : Stp} → {Γ : Cxt} → {C : Fma} → (f : S ∣ Γ ⊢ C) → cmplt (sound f) ≗ ⊗l⋆ S Γ f
cmpltsound' ax = refl
cmpltsound' (uf {Γ}{A} f) =
  proof≗
  scut (cmplt [ l ∣ Γ ]f) (cmplt (sound f))
  ≗〈 cong-scut2 (cmplt [ l ∣ Γ ]f) (cmpltsound' f) 〉
  scut (cmplt [ l ∣ Γ ]f) (⊗l⋆ (just A) Γ f)
  ≗〈 cong-scut1 (cmplt-uf-lemma Γ l) 〉
  scut (⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (⊗l-1⋆ (just A) Γ ax))))) (⊗l⋆ (just A) Γ f)
  ≗〈 ≡-to-≗ (scut⊗l⋆ {just (I ⊗ A)}{Γ})  〉
  ⊗l⋆ (just (I ⊗ A)) Γ (scut (⊗l (Il (uf (⊗l-1⋆ (just A) Γ ax)))) (⊗l⋆ (just A) Γ {[]} f))
  ≗〈 refl 〉
  ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (scut (⊗l-1⋆ (just A) Γ ax) (⊗l⋆ (just A) Γ {[]} f)))))
  ≗〈 ≡-to-≗ (cong (⊗l⋆ (just (I ⊗ A)) Γ) (cong ⊗l (cong Il (cong uf (scut⊗l-1⋆ {just A}{Γ}))))) 〉
  ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (⊗l-1⋆ (just A) Γ (scut ax (⊗l⋆ (just A) Γ {[]} f))))))
  ≗〈 refl 〉
  ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (⊗l-1⋆ (just A) Γ (⊗l⋆ (just A) Γ {[]} f)))))
  ≗〈 ≡-to-≗ (cong (⊗l⋆ (just (I ⊗ A)) Γ) (cong ⊗l (cong Il (cong uf (⊗l⋆-iso {just A}{Γ}))))) 〉
  ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf f)))
  qed≗
cmpltsound' Ir = axI
cmpltsound' (⊗r {S}{Γ}{Δ} f f') = 
  proof≗
  scut (cmplt (φ S Γ Δ)) (⊗l (⊗r (cmplt (sound f)) (uf (cmplt (sound f')))))
  ≗〈 cong-scut2 (cmplt (φ S Γ Δ)) (⊗l (⊗r (cmpltsound' f) (uf (cmpltsound' f')))) 〉
  scut (cmplt (φ S Γ Δ)) (⊗l (⊗r (⊗l⋆ S Γ {[]} f) (uf (⊗l⋆ nothing Δ {[]} f'))))
  ≗〈 cong-scut1 (cmplt-⊗r-lemma {S}{Γ}{Δ}) 〉
  scut (⊗l⋆ S (Γ ++ Δ) (⊗r (⊗l-1⋆ S Γ ax) (⊗l-1⋆ nothing Δ ax))) (⊗l (⊗r (⊗l⋆ S Γ {[]} f) (uf (⊗l⋆ nothing Δ {[]} f'))))
  ≗〈 ≡-to-≗ (scut⊗l⋆ {S}{Γ ++ Δ}) 〉
  ⊗l⋆ S (Γ ++ Δ) (scut (⊗l-1⋆ S Γ ax) (⊗r (⊗l⋆ S Γ {[]} f) (scut (⊗l-1⋆ nothing Δ ax) (⊗l⋆ nothing Δ {[]} f')))) 
  ≗〈 cong⊗l⋆ {S} {Γ ++ Δ} (cong-scut2 (⊗l-1⋆ S Γ ax) (⊗r refl (≡-to-≗ (scut⊗l-1⋆ {nothing}{Δ})))) 〉
  ⊗l⋆ S (Γ ++ Δ) (scut (⊗l-1⋆ S Γ ax) (⊗r (⊗l⋆ S Γ {[]} f) (⊗l-1⋆ nothing Δ (⊗l⋆ nothing Δ {[]} f'))))
  ≗〈 cong⊗l⋆ {S} {Γ ++ Δ} (cong-scut2 (⊗l-1⋆ S Γ ax) (⊗r refl (≡-to-≗ (⊗l⋆-iso {nothing}{Δ})))) 〉
  ⊗l⋆ S (Γ ++ Δ) (scut (⊗l-1⋆ S Γ ax) (⊗r (⊗l⋆ S Γ {[]} f) f'))
  ≗〈 cong⊗l⋆ {S} {Γ ++ Δ} (≡-to-≗ (scut⊗l-1⋆ {S}{Γ})) 〉
  ⊗l⋆ S (Γ ++ Δ) (⊗l-1⋆ S Γ (⊗r (⊗l⋆ S Γ {[]} f) f'))
  ≗〈 cong⊗l⋆ {S} {Γ ++ Δ} (cong⊗l-1⋆ {S} {Γ} (⊗r⊗l⋆ {S}{Γ})) 〉
  ⊗l⋆ S (Γ ++ Δ) (⊗l-1⋆ S Γ (⊗l⋆ S Γ {Δ} (⊗r f f')))
  ≗〈 cong⊗l⋆ {S} {Γ ++ Δ} (≡-to-≗ (⊗l⋆-iso {S}{Γ})) 〉
  ⊗l⋆ S (Γ ++ Δ) {[]} (⊗r f f')
  qed≗
cmpltsound' (Il {Γ = []} f) = cmpltsound' f
cmpltsound' (Il {Γ = _ ∷ _} f) = cmpltsound' f
cmpltsound' (⊗l f) = cmpltsound' f
cmpltsound' (ex {S}{Γ} {Δ} b f) =
  proof≗
    scut (cmplt [ s b ∣ Δ ]f) (cmplt (sound f))
  ≗〈 cong-scut2 (cmplt [ s b ∣ Δ ]f) (cmpltsound' f) 〉 
    scut (cmplt [ s b ∣ Δ ]f) (⊗l⋆ _ (Γ ++ _ ∷ _ ∷ Δ) f)
  ≗〈 cong-scut1 {h = ⊗l⋆ _ (Γ ++ _ ∷ _ ∷ Δ) f} (cmplt-uf-lemma Δ (s b))  〉 
    scut (⊗l⋆ _ Δ {[]} (⊗l (⊗l (ex {Γ = []} b (scut (⊗r (⊗r ax (uf ax)) (uf ax)) (⊗l-1⋆ _ Δ ax)))))) (⊗l⋆ _ (Γ ++ _ ∷ _ ∷ Δ) f) 
  ≗〈 ≡-to-≗ (scut⊗l⋆ {just (_ ⊗ _)}{Γ = Δ}) 〉 
    ⊗l⋆ _ Δ (⊗l (⊗l (ex {Γ = []} b (scut (scut (⊗r (⊗r ax (uf ax)) (uf ax)) (⊗l-1⋆ _ Δ ax)) (⊗l⋆ _ (Γ ++ _ ∷ _ ∷ Δ) {[]} f)))))
  ≗〈 cong⊗l⋆ {just (_ ⊗ _)} {Δ} (⊗l (⊗l (ex {Γ = []} b (~ scutscut-vass ((⊗r (⊗r ax (uf ax)) (uf ax))) (⊗l-1⋆ _ Δ ax) _)))) 〉 
    ⊗l⋆ _ Δ (⊗l (⊗l (ex {Γ = []} b (scut {Γ = _ ∷ _ ∷ []} (⊗r (⊗r ax (uf ax)) (uf ax)) (scut (⊗l-1⋆ _ Δ ax) (⊗l⋆ _ (Γ ++ _ ∷ _ ∷ Δ) {[]} f))))))
  ≗〈 cong⊗l⋆ {just (_ ⊗ _)} {Δ} (⊗l (⊗l (ex b (cong-scut2 (⊗r (⊗r ax (uf ax)) (uf ax)) (≡-to-≗ (scut⊗l-1⋆ {just (_ ⊗ _)}{Δ}{[]}{f = ax})))))) 〉 
    ⊗l⋆ _ Δ (⊗l (⊗l (ex {Γ = []} b (scut {Γ = _ ∷ _ ∷ []} (⊗r (⊗r ax (uf ax)) (uf ax)) (⊗l-1⋆ _ Δ (⊗l⋆ _ (Γ ++ _ ∷ _ ∷ Δ) {[]} f))))))
  ≗〈 cong⊗l⋆ {just (_ ⊗ _)} {Δ} (⊗l (⊗l (ex b (≡-to-≗ (cong (scut (⊗r (⊗r ax (uf ax)) (uf ax))) (cong (⊗l-1⋆ _ Δ) (⊗l⋆++ S Γ (_ ∷ _ ∷ Δ)))))))) 〉 
    ⊗l⋆ _ Δ (⊗l (⊗l (ex {Γ = []} b (scut {Γ = _ ∷ _ ∷ []} (⊗r (⊗r ax (uf ax)) (uf ax)) (⊗l-1⋆ _ Δ {[]} (⊗l⋆ _ Δ (⊗l (⊗l (⊗l⋆ S Γ f)))))))))
  ≗〈 cong⊗l⋆ {just (_ ⊗ _)} {Δ} (⊗l (⊗l (ex b (≡-to-≗ (cong (scut (⊗r (⊗r ax (uf ax)) (uf ax))) (⊗l⋆-iso {Γ = Δ})))))) 〉 
    ⊗l⋆ _ Δ (⊗l (⊗l (ex {Γ = []} b (ccut [] (uf ax) (ccut (_ ∷ []) (uf ax) (⊗l⋆ S Γ f) refl) refl))))
  ≗〈 cong⊗l⋆ {just (_ ⊗ _)} {Δ} (⊗l (⊗l (ex b (≡-to-≗ (ccut-unit [] (ccut (_ ∷ []) (uf ax) (⊗l⋆ S Γ f) refl) refl))))) 〉 
    ⊗l⋆ _ Δ (⊗l (⊗l (ex {Γ = []} b (ccut (_ ∷ []) (uf ax) (⊗l⋆ S Γ f) refl))))
  ≗〈 cong⊗l⋆ {just (_ ⊗ _)} {Δ} (⊗l (⊗l (ex b (≡-to-≗ (ccut-unit (_ ∷ []) (⊗l⋆ S Γ f) refl))))) 〉 
    ⊗l⋆ _ Δ (⊗l (⊗l (ex {Γ = []} b (⊗l⋆ _ Γ f))))
  ≗〈 cong⊗l⋆ {just (_ ⊗ _)} {Δ} (⊗l (⊗l (ex⊗l⋆ S Γ b f))) 〉 
    ⊗l⋆ _ Δ (⊗l (⊗l (⊗l⋆ _ Γ (ex b f))))
  ≗〈 ≡-to-≗ (sym (⊗l⋆++ S Γ (_ ∷ _ ∷ Δ))) 〉 
    ⊗l⋆ _ (Γ ++ _ ∷ _ ∷ Δ) (ex b f)
  qed≗


cmpltsound : {A B : Fma} → (f : just A ∣ [] ⊢ B) → cmplt (sound f) ≗ f
cmpltsound = cmpltsound'
