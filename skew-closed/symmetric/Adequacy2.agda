{-# OPTIONS --rewriting #-}

module Adequacy2 where

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
--open import StrongComplete
open import Sound
--open import EqComplete
--open import SoundComplete

-- ====================================================================

-- Proof that ∀ f. sound (cmplt f) ≐ f

sound-Il-1 : {Γ : Cxt} → {C : Fma} → 
              (f : just I ∣ Γ ⊢ C) → sound (Il-1 f) ≐ sound f
sound-Il-1 ax = refl
sound-Il-1 (⊸r f) = sound-Il-1 f
sound-Il-1 (Il f) = refl
sound-Il-1 (ex f) = refl ∘ sound-Il-1 f

sem-scut : {S : Stp} → {Γ Δ : Cxt} → {A C : Fma} → 
           t S ⇒ [ Γ ∣ A ] → A ⇒ [ Δ ∣ C ] → t S ⇒ [ Γ ++ Δ ∣ C ]
sem-scut {Γ = Γ} f g = [ Γ ∣ g ]f ∘ f

sem-ccut : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
           I ⇒ [ Γ ∣ A ]  →  t T ⇒ [ Δ ∣ C ] → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                      t T ⇒ [ Δ₀ ++ Γ ++ Δ' ∣ C ]
sem-ccut {Γ = Γ} Δ₀ f g refl = [ Δ₀ ∣ i ∘ f ⊸ id ∘ L⋆ Γ ]f ∘ g 

[ex-fma-cxt] : (Λ : Cxt) → {A C : Fma} → 
              A ⊸ [ Λ ∣ C ] ⇒ [ Λ ∣ A ⊸ C ]
[ex-fma-cxt] [] = id
[ex-fma-cxt] (B ∷ Λ) = id ⊸ [ex-fma-cxt] Λ ∘ s

[ex-cxt-fma] : (Λ : Cxt) → {A C : Fma} → 
              [ Λ ∣ A ⊸ C ] ⇒ A ⊸ [ Λ ∣ C ]
[ex-cxt-fma] [] = id
[ex-cxt-fma] (B ∷ Λ) = s ∘ id ⊸ [ex-cxt-fma] Λ

i[ex-fma-cxt] : (Λ : Cxt) → {A : Fma} → 
              i ≐ [ Λ ∣ i ]f ∘ [ex-fma-cxt] Λ {I}{A}
i[ex-fma-cxt] [] = rid
i[ex-fma-cxt] (B ∷ Λ) =
  is1
  ∙ (refl ⊸ i[ex-fma-cxt] Λ ∘ refl)
  ∙ (id⊸∘ ∘ refl)
  ∙ ass

sL⋆1 : (Γ : Cxt) {A B C : Fma}
  → L⋆ Γ {A}{B ⊸ C} ∘ s ≐ id ⊸ [ex-fma-cxt] Γ ∘ s ∘ id ⊸ L⋆ Γ
sL⋆1 [] = rid ∙ ((~ f⊸id) ∘ refl ∘ (~ f⊸id))
sL⋆1 (_ ∷ Γ) =
  ass
  ∙ (refl ∘ sL⋆1 Γ)
  ∙ ~ ass
  ∙ (((~ ass)
      ∙ ((~ lid ∙ ((~ f⊸id ∙ refl ⊸ (~ f⊸id)) ∘ refl) ∙ (~ ass ∙ (~ nL))) ∘ refl)
      ∙ ass 
      ∙ (f⊸id ⊸ refl ∘ (sL2 ∙ ass))
      ∙ ~ ass ∙ ~ ass
      ∙ ((~ id⊸∘) ∘ refl ∘ refl))
    ∘ refl)
  ∙ ass
  ∙ (refl ∘ (~ id⊸∘))

sL⋆2 : (Γ : Cxt) {A B C : Fma}
  → id {A} ⊸ L⋆ Γ {B}{C} ∘ s ≐ s ∘ id ⊸ [ex-cxt-fma] Γ ∘ L⋆ Γ
sL⋆2 [] = f⊸id ∘ refl ∙ lid ∙ (rid ∙ (refl ∘ ~ f⊸id)) ∙ rid
sL⋆2 (_ ∷ Γ) =
  id⊸∘ ∘ refl
  ∙ ass
  ∙ (refl ∘ sL⋆2 Γ)
  ∙ ~ ass
  ∙ ((~ ass
      ∙ ((sL1 ∙ ((refl ∘ (rid ∙ (refl ∘ (~ (refl ⊸ f⊸id ∙ f⊸id)))) ∙ ~ ass) ∘ refl ∙ ass)) ∘ refl)
      ∙ ass ∙ ass
      ∙ (refl ∘ (refl ∘ (~ ((~ f⊸id) ⊸ refl ∘ refl ∙ nL)) ∙ ~ ass) ∙ ~ ass)
      ∙ (refl ∘ (~ id⊸∘) ∘ refl))
     ∘ refl)
  ∙ ass

soundex-fma-cxt : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma} → 
              (f : S ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C) →
                sound (ex-fma-cxt {S}{Γ}{Δ} Λ f) ≐
                  [ Γ ∣ [ex-fma-cxt] Λ ]f ∘ sound f
soundex-fma-cxt [] f = ~ lid ∙ ((~ [ _ ∣id]f) ∘ refl)
soundex-fma-cxt {Γ = Γ} (B ∷ Λ) f =
  soundex-fma-cxt {Γ = Γ ∷ʳ _} Λ (ex f)
  ∙ (≡-to-≐ (sym [ Γ ∣ _ ∷ [] ∣ass]f) ∘ refl)
  ∙ (~ ass)
  ∙ ((~ [ Γ ∣∘]f) ∘ refl)

soundex-cxt-fma : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma} → 
              (f : S ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C) →
                sound (ex-cxt-fma {S}{Γ}{Δ} Λ f) ≐
                  [ Γ ∣ [ex-cxt-fma] Λ ]f ∘ sound f
soundex-cxt-fma [] f = ~ lid ∙ ((~ [ _ ∣id]f) ∘ refl)
soundex-cxt-fma {Γ = Γ} (B ∷ Λ) f =
  refl ∘ soundex-cxt-fma {Γ = Γ ∷ʳ _} Λ f
  ∙ ~ ass
  ∙ ((refl ∘ ≡-to-≐ (sym [ Γ ∣ _ ∷ [] ∣ass]f) ∙ (~ [ Γ ∣∘]f)) ∘ refl)

sound-scut : {S : Stp} → {Γ Δ : Cxt} → {A C : Fma} →
             (f : S ∣ Γ ⊢ A) (g : just A ∣ Δ ⊢ C) →
             sound (scut f g) ≐ sem-scut {S}{Γ}{Δ} (sound f) (sound g)
sound-ccut : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
               (f : nothing ∣ Γ ⊢ A)  → (g : T ∣ Δ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
                sound (ccut Δ₀ f g r) ≐ sem-ccut {T}{Γ} Δ₀ (sound f) (sound g) r              

sound-scut ax g = rid
sound-scut (uf {Γ} f) g =
  proof≐
    id ⊸ sound (scut f g) ∘ j
  ≐⟨ refl ⊸ sound-scut f g ∘ refl ⟩ 
    id ⊸ ([ Γ ∣ sound g ]f ∘ sound f) ∘ j
  ≐⟨ id⊸∘ ∘ refl ⟩ 
    id ⊸ [ Γ ∣ sound g ]f ∘ id ⊸ sound f ∘ j
  ≐⟨ ass ⟩ 
    id ⊸ [ Γ ∣ sound g ]f ∘ (id ⊸ sound f ∘ j)
  qed≐
sound-scut Ir ax = rid
sound-scut Ir (ex g) = refl ∘ sound-scut Ir g ∙ (~ ass)
sound-scut Ir (Il g) = rid
sound-scut Ir (⊸r g) = sound-scut Ir g 
sound-scut {Γ = Γ} (⊸r f) ax = (~ lid) ∙ (~ [ Γ ∣id]f ∘ refl)
sound-scut (⊸r f) (⊸r g) = sound-scut (⊸r f) g
sound-scut (⊸r {Γ = Γ} f) (ex {Γ = Γ'} g) =
  ≡-to-≐ (sym [ Γ ∣ Γ' ∣ass]f) ∘ sound-scut (⊸r f) g
  ∙ ~ ass
  ∙ ((~ [ Γ ∣∘]f) ∘ refl)
sound-scut {Γ = Γ} (⊸r f) (⊸l {Γ₁} g g') =
  proof≐
    sound (scut (ccut Γ g f refl) g')
  ≐⟨ sound-scut (ccut Γ g f refl) g' ⟩ 
    [ Γ ++ Γ₁ ∣ sound g' ]f ∘ sound (ccut Γ g f refl)
  ≐⟨ refl ∘ sound-ccut Γ g f refl ⟩ 
    [ Γ ++ Γ₁ ∣ sound g' ]f ∘ ([ Γ ∣ i ∘ sound g ⊸ id ∘ L⋆ Γ₁ ]f ∘ sound f)
  ≐⟨ ≡-to-≐ (sym [ Γ ∣ Γ₁ ∣ass]f) ∘ refl ⟩ 
    [ Γ ∣ [ Γ₁ ∣ sound g' ]f ]f ∘ ([ Γ ∣ i ∘ sound g ⊸ id ∘ L⋆ Γ₁ ]f ∘ sound f)
  ≐⟨ ~ ass ⟩ 
    [ Γ ∣ [ Γ₁ ∣ sound g' ]f ]f ∘ [ Γ ∣ i ∘ sound g ⊸ id ∘ L⋆ Γ₁ ]f ∘ sound f
  ≐⟨ ~ [ Γ ∣∘]f ∘ refl ⟩ 
    [ Γ ∣ [ Γ₁ ∣ sound g' ]f ∘ (i ∘ sound g ⊸ id ∘ L⋆ Γ₁) ]f ∘ sound f
  ≐⟨ [ Γ ∣≐]f ((~ ass) ∙ (~ ass ∘ refl)) ∘ refl ⟩ 
    [ Γ ∣ [ Γ₁ ∣ sound g' ]f ∘ i ∘ sound g ⊸ id ∘ L⋆ Γ₁ ]f ∘ sound f
  ≐⟨ [ Γ ∣≐]f (ni ∘ refl ∘ refl) ∘ refl ⟩ 
    [ Γ ∣ i ∘ id ⊸ [ Γ₁ ∣ sound g' ]f ∘ sound g ⊸ id ∘ L⋆ Γ₁ ]f ∘ sound f
  ≐⟨ [ Γ ∣≐]f (ass ∘ refl) ∘ refl ⟩ 
    [ Γ ∣ i ∘ (id ⊸ [ Γ₁ ∣ sound g' ]f ∘ sound g ⊸ id) ∘ L⋆ Γ₁ ]f ∘ sound f
  ≐⟨ [ Γ ∣≐]f (refl ∘ ~ swap⊸ ∘ refl ) ∘ refl ⟩ 
    [ Γ ∣ i ∘ (sound g ⊸ id ∘ id ⊸ [ Γ₁ ∣ sound g' ]f) ∘ L⋆ Γ₁ ]f ∘ sound f
  ≐⟨ [ Γ ∣≐]f ((~ ass ∘ refl) ∙ ass) ∘ refl ⟩ 
    [ Γ ∣ i ∘ sound g ⊸ id ∘ (id ⊸ [ Γ₁ ∣ sound g' ]f ∘ L⋆ Γ₁) ]f ∘ sound f
  ≐⟨ [ Γ ∣≐]f (refl ∘ ~ (nL⋆2 Γ₁ (sound g'))) ∘ refl ⟩ 
    [ Γ ∣ i ∘ sound g ⊸ id ∘ (L⋆ Γ₁ ∘ id ⊸ sound g') ]f ∘ sound f
  ≐⟨ [ Γ ∣≐]f (~ ass) ∘ refl ⟩ 
    [ Γ ∣ i ∘ sound g ⊸ id ∘ L⋆ Γ₁ ∘ id ⊸ sound g' ]f ∘ sound f
  qed≐
sound-scut (Il f) g = sound-scut f g
sound-scut (⊸l {Γ} {Δ} f f') g =
  proof≐
    i ∘ sound f ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound (scut f' g)
  ≐⟨ refl ∘ refl ⊸ sound-scut f' g ⟩ 
    i ∘ sound f ⊸ id ∘ L⋆ Γ ∘ id ⊸ ([ Δ ∣ sound g ]f ∘ sound f')
  ≐⟨ refl ∘ id⊸∘ ⟩ 
    i ∘ sound f ⊸ id ∘ L⋆ Γ ∘ (id ⊸ [ Δ ∣ sound g ]f ∘ id ⊸ sound f')
  ≐⟨ (~ ass) ∙ (ass ∘ refl) ⟩ 
    i ∘ sound f ⊸ id ∘ (L⋆ Γ ∘ id ⊸ [ Δ ∣ sound g ]f) ∘ id ⊸ sound f'
  ≐⟨ refl ∘ nL⋆2 Γ [ Δ ∣ sound g ]f ∘ refl ⟩ 
    i ∘ sound f ⊸ id ∘ (id ⊸ [ Γ ∣ [ Δ ∣ sound g ]f ]f ∘ L⋆ Γ) ∘ id ⊸ sound f'
  ≐⟨ refl ∘ (refl ⊸ ≡-to-≐ [ Γ ∣ Δ ∣ass]f  ∘ refl) ∘ refl ⟩ 
    i ∘ sound f ⊸ id ∘ (id ⊸ [ Γ ++ Δ ∣ sound g ]f ∘ L⋆ Γ) ∘ id ⊸ sound f'
  ≐⟨ (~ ass) ∙ (ass ∘ refl) ∘ refl ⟩ 
    i ∘ (sound f ⊸ id ∘ id ⊸ [ Γ ++ Δ ∣ sound g ]f) ∘ L⋆ Γ ∘ id ⊸ sound f'
  ≐⟨ refl ∘ swap⊸ ∘ refl ∘ refl ⟩ 
    i ∘ (id ⊸ [ Γ ++ Δ ∣ sound g ]f ∘ sound f ⊸ id) ∘ L⋆ Γ ∘ id ⊸ sound f'
  ≐⟨ ~ ass ∘ refl ∘ refl ⟩ 
    i ∘ id ⊸ [ Γ ++ Δ ∣ sound g ]f ∘ sound f ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound f'
  ≐⟨ ~ ni ∘ refl ∘ refl ∘ refl ⟩ 
    [ Γ ++ Δ ∣ sound g ]f ∘ i ∘ sound f ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound f'
  ≐⟨ ((ass ∘ refl) ∙ ass ∘ refl ) ∙ ass ⟩ 
    [ Γ ++ Δ ∣ sound g ]f ∘ (i ∘ sound f ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound f')
  qed≐
sound-scut (ex {Γ = Γ} {Δ} f) g =
  refl ∘ sound-scut f g
  ∙ (~ ass)
  ∙ ((refl ∘ ≡-to-≐ (sym [ Γ ∣ _ ∷ _ ∷ Δ ∣ass]f)
      ∙ (~ [ Γ ∣∘]f)
      ∙ [ Γ ∣≐]f (~ ns)
      ∙ [ Γ ∣∘]f
      ∙ (≡-to-≐ [ Γ ∣ _ ∷ _ ∷ Δ ∣ass]f ∘ refl))
     ∘ refl)
  ∙ ass

sound-ccut Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
sound-ccut Δ₀ f (uf g) r with cases∷ Δ₀ r
sound-ccut {Γ = Γ} .[] f (uf g) refl | inj₁ (refl , refl , refl) =
  proof≐
    sound (scut f g)
  ≐⟨ sound-scut f g ⟩
    [ Γ ∣ sound g ]f ∘ sound f
  ≐⟨ rid ⟩ 
    [ Γ ∣ sound g ]f ∘ sound f ∘ id
  ≐⟨ refl ∘ ~ ij ⟩ 
    [ Γ ∣ sound g ]f ∘ sound f ∘ (i ∘ j)
  ≐⟨ (~ ass) ∙ (ass ∘ refl) ⟩ 
    [ Γ ∣ sound g ]f ∘ (sound f ∘ i) ∘ j
  ≐⟨ refl ∘ ni ∘ refl ⟩ 
    [ Γ ∣ sound g ]f ∘ (i ∘ id ⊸ sound f) ∘ j
  ≐⟨ (~ ass ∘ refl) ∙ ass ⟩ 
    [ Γ ∣ sound g ]f ∘ i ∘ (id ⊸ sound f ∘ j)
  ≐⟨ ni ∘ ~ nj ⟩ 
    i ∘ id ⊸ [ Γ ∣ sound g ]f ∘ (sound f ⊸ id ∘ j)
  ≐⟨ (~ ass) ∙ (ass ∘ refl) ⟩ 
    i ∘ (id ⊸ [ Γ ∣ sound g ]f ∘ sound f ⊸ id) ∘ j
  ≐⟨ refl ∘ ~ swap⊸ ∘ ~ (L⋆-j Γ) ⟩ 
    i ∘ (sound f ⊸ id ∘ id ⊸ [ Γ ∣ sound g ]f) ∘ (L⋆ Γ ∘ j)
  ≐⟨ (~ ass) ∙ ((~ ass ∘ refl) ∙ ass ∘ refl) ⟩ 
    i ∘ sound f ⊸ id ∘ (id ⊸ [ Γ ∣ sound g ]f ∘ L⋆ Γ) ∘ j
  ≐⟨ refl ∘ ~ (nL⋆2 Γ (sound g))  ∘ refl ⟩ 
    i ∘ sound f ⊸ id ∘ (L⋆ Γ ∘ id ⊸ sound g) ∘ j
  ≐⟨ (~ ass ∘ refl) ∙ ass ⟩ 
    i ∘ sound f ⊸ id ∘ L⋆ Γ ∘ (id ⊸ sound g ∘ j)
  qed≐
sound-ccut {Γ = Γ} .(_ ∷ Γ₀) f (uf g) refl | inj₂ (Γ₀ , refl , refl) =
  proof≐
    id ⊸ sound (ccut Γ₀ f g refl) ∘ j
  ≐⟨ refl ⊸ sound-ccut Γ₀ f g refl ∘ refl ⟩ 
    id ⊸ ([ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ sound g) ∘ j
  ≐⟨ (id⊸∘ ∘ refl) ∙ ass ⟩ 
    id ⊸ [ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ (id ⊸ sound g ∘ j)
  qed≐
sound-ccut Δ₀ f Ir r = ⊥-elim ([]disj∷ Δ₀ r)
sound-ccut Δ₀ f (⊸r g) refl = sound-ccut Δ₀ f g refl
sound-ccut Δ₀ f (Il g) refl = sound-ccut Δ₀ f g refl
sound-ccut Δ₀ {Δ'} f (⊸l {Γ} {Δ} g g') r with cases++ Δ₀ Γ Δ' Δ r
sound-ccut {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} {A} {C} f (⊸l {.(Δ₀ ++ A ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) =
  proof≐
    i ∘ sound (ccut Δ₀ f g refl) ⊸ id ∘ L⋆ (Δ₀ ++ Γ ++ Γ₀) ∘ id ⊸ sound g'
  ≐⟨ refl ∘ sound-ccut Δ₀ f g refl ⊸ refl ∘ refl ∘ refl ⟩ 
    i ∘ ([ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ sound g) ⊸ id ∘ L⋆ (Δ₀ ++ Γ ++ Γ₀) ∘ id ⊸ sound g'
  ≐⟨ refl ∘ ∘⊸id ∘ refl ∘ refl ⟩ 
    i ∘ (sound g ⊸ id ∘ [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ⊸ id) ∘ L⋆ (Δ₀ ++ Γ ++ Γ₀) ∘ id ⊸ sound g'
  ≐⟨ (~ ass ∘ refl) ∙ ass ∘ refl ⟩ 
    i ∘ sound g ⊸ id ∘ ([ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ⊸ id ∘ L⋆ (Δ₀ ++ Γ ++ Γ₀)) ∘ id ⊸ sound g'
  ≐⟨ refl ∘ (refl ∘ L⋆ass Δ₀ (Γ ++ Γ₀)) ∘ refl ⟩  
    i ∘ sound g ⊸ id ∘ ([ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ⊸ id ∘ (L⋆ Δ₀ ∘ L⋆ (Γ ++ Γ₀))) ∘ id ⊸ sound g'
  ≐⟨ refl ∘ (~ ass ∙ (~ (nL⋆ Δ₀ _ ∘ refl))) ∘ refl ⟩ 
    i ∘ sound g ⊸ id ∘ (L⋆ Δ₀ ∘ (i ∘ sound f ⊸ id ∘ L⋆ Γ) ⊸ id ∘ L⋆ (Γ ++ Γ₀)) ∘ id ⊸ sound g'
  ≐⟨ refl ∘ (refl ∘ ∘⊸id ∘ refl) ∘ refl ⟩ 
    i ∘ sound g ⊸ id ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ (i ∘ sound f ⊸ id) ⊸ id) ∘ L⋆ (Γ ++ Γ₀)) ∘ id ⊸ sound g'
  ≐⟨ refl ∘ ass ∘ refl ⟩
    i ∘ sound g ⊸ id ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ (i ∘ sound f ⊸ id) ⊸ id ∘ L⋆ (Γ ++ Γ₀))) ∘ id ⊸ sound g'    
  ≐⟨ refl ∘ (refl ∘ lemma) ∘ refl ⟩
    i ∘ sound g ⊸ id ∘ (L⋆ Δ₀ ∘ (id ⊸ (i ∘ sound f ⊸ id) ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀)) ∘ id ⊸ sound g'
  ≐⟨ refl ∘ ((refl ∘ ass ∙ ~ ass) ∙ (~ ass)) ∘ refl ⟩
    i ∘ sound g ⊸ id ∘ (L⋆ Δ₀ ∘ (id ⊸ (i ∘ sound f ⊸ id) ∘ id ⊸ L⋆ Γ) ∘ L ∘ L⋆ Γ₀) ∘ id ⊸ sound g'
  ≐⟨ refl ∘ (refl ∘ ~ id⊸∘ ∘ refl ∘ refl) ∘ refl ⟩ 
    i ∘ sound g ⊸ id ∘ (L⋆ Δ₀ ∘ id ⊸ (i ∘ sound f ⊸ id ∘ L⋆ Γ) ∘ L ∘ L⋆ Γ₀) ∘ id ⊸ sound g'
  ≐⟨ refl ∘ (nL⋆2 Δ₀ (i ∘ sound f ⊸ id ∘ L⋆ Γ) ∘ refl ∘ refl) ∘ refl ⟩
    i ∘ sound g ⊸ id ∘ (id ⊸ [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ L⋆ Δ₀ ∘ L ∘ L⋆ Γ₀) ∘ id ⊸ sound g'
  ≐⟨ refl ∘ (ass ∙ ass) ∘ refl ⟩ 
    i ∘ sound g ⊸ id ∘ (id ⊸ [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ (L⋆ Δ₀ ∘ (L ∘ L⋆ Γ₀))) ∘ id ⊸ sound g'
  ≐⟨ refl ∘ (refl ∘ ~ (L⋆ass Δ₀ (A ∷ Γ₀))) ∘ refl ⟩ 
    i ∘ sound g ⊸ id ∘ (id ⊸ [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ L⋆ (Δ₀ ++ A ∷ Γ₀)) ∘ id ⊸ sound g'
  ≐⟨ (~ ass) ∙ (ass ∘ refl) ∘ refl ⟩ 
    i ∘ (sound g ⊸ id ∘ id ⊸ [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f) ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g'
  ≐⟨ refl ∘ swap⊸ ∘ refl ∘ refl ⟩ 
    i ∘ (id ⊸ [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ sound g ⊸ id) ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g'
  ≐⟨ ~ ass ∘ refl ∘ refl ⟩ 
    i ∘ id ⊸ [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ sound g ⊸ id ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g'
  ≐⟨ ~ ni ∘ refl ∘ refl ∘ refl ⟩ 
    [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ i ∘ sound g ⊸ id ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g'
  ≐⟨ ((ass ∘ refl) ∙ ass ∘ refl) ∙ ass ⟩ 
    [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ (i ∘ sound g ⊸ id ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g')
  qed≐
  where
    lemma : L⋆ Γ ⊸ id ∘ (i ∘ sound f ⊸ id) ⊸ id ∘ L⋆ (Γ ++ Γ₀) ≐ id ⊸ (i ∘ sound f ⊸ id) ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀
    lemma =
        proof≐
          L⋆ Γ ⊸ id ∘ (i ∘ sound f ⊸ id) ⊸ id ∘ L⋆ (Γ ++ Γ₀)
        ≐⟨ refl ∘ ∘⊸id ∘ refl ⟩
          L⋆ Γ ⊸ id ∘ ((sound f ⊸ id) ⊸ id ∘ i ⊸ id) ∘ L⋆ (Γ ++ Γ₀)
        ≐⟨ refl ∘ (refl ∘ ~ iL)  ∘ refl ⟩ 
          L⋆ Γ ⊸ id ∘ ((sound f ⊸ id) ⊸ id ∘ (id ⊸ i ∘ L)) ∘ L⋆ (Γ ++ Γ₀)
        ≐⟨ (~ ass) ∙ ((~ ass) ∙ (ass ∘ refl)) ∘ refl ⟩ 
          L⋆ Γ ⊸ id ∘ ((sound f ⊸ id) ⊸ id ∘ id ⊸ i) ∘ L ∘ L⋆ (Γ ++ Γ₀)
        ≐⟨ refl ∘ swap⊸ ∘ refl ∘ refl ⟩ 
          L⋆ Γ ⊸ id ∘ (id ⊸ i ∘ (sound f ⊸ id) ⊸ id) ∘ L ∘ L⋆ (Γ ++ Γ₀)
        ≐⟨ (~ ass ∘ refl) ∙ ass ∘ refl ⟩ 
          L⋆ Γ ⊸ id ∘ id ⊸ i ∘ ((sound f ⊸ id) ⊸ id ∘ L) ∘ L⋆ (Γ ++ Γ₀)
        ≐⟨ refl ∘ (refl ⊸ (~ f⊸id) ∘ refl) ∘ refl ⟩ 
          L⋆ Γ ⊸ id ∘ id ⊸ i ∘ ((sound f ⊸ id) ⊸ (id ⊸ id) ∘ L) ∘ L⋆ (Γ ++ Γ₀)
        ≐⟨ refl ∘ nL ∘ refl ⟩ 
          L⋆ Γ ⊸ id ∘ id ⊸ i ∘ (id ⊸ (sound f ⊸ id) ∘ L ∘ id ⊸ id) ∘ L⋆ (Γ ++ Γ₀)
        ≐⟨ refl ∘ (refl ∘ f⊸id) ∘ refl ⟩ 
          L⋆ Γ ⊸ id ∘ id ⊸ i ∘ (id ⊸ (sound f ⊸ id) ∘ L ∘ id) ∘ L⋆ (Γ ++ Γ₀)
        ≐⟨ refl ∘ ~ rid ∘ refl ⟩ 
          L⋆ Γ ⊸ id ∘ id ⊸ i ∘ (id ⊸ (sound f ⊸ id) ∘ L) ∘ L⋆ (Γ ++ Γ₀)
        ≐⟨ (~ ass) ∙ (ass ∘ refl) ∘ refl ⟩ 
          L⋆ Γ ⊸ id ∘ (id ⊸ i ∘ id ⊸ (sound f ⊸ id)) ∘ L ∘ L⋆ (Γ ++ Γ₀)
        ≐⟨ refl ∘ ~ id⊸∘ ∘ refl ∘ refl ⟩ 
          L⋆ Γ ⊸ id ∘ id ⊸ (i ∘ sound f ⊸ id) ∘ L ∘ L⋆ (Γ ++ Γ₀)
        ≐⟨ ((swap⊸ ∘ refl) ∙ ass ∘ refl) ∙ ass ⟩ 
          id ⊸ (i ∘ sound f ⊸ id) ∘ (L⋆ Γ ⊸ id ∘ L ∘ L⋆ (Γ ++ Γ₀))
        ≐⟨ refl ∘ L⋆LL⋆ Γ Δ Γ₀  ⟩ 
          id ⊸ (i ∘ sound f ⊸ id) ∘ (id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀)
        ≐⟨ (~ ass) ∙ ((~ ass ∘ refl) ∙ ass) ⟩ 
          id ⊸ (i ∘ sound f ⊸ id) ∘ id ⊸ L⋆ Γ ∘ (L ∘ L⋆ Γ₀)
        ≐⟨ ~ id⊸∘ ∘ refl ⟩ 
          id ⊸ (i ∘ sound f ⊸ id ∘ L⋆ Γ) ∘ (L ∘ L⋆ Γ₀)
        ≐⟨ (~ ass) ∙ (id⊸∘ ∘ refl ∘ refl) ⟩
          id ⊸ (i ∘ sound f ⊸ id) ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀
        qed≐
sound-ccut {Γ = Γ'} .(Γ ++ Γ₀) {Δ'} f (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) =
  proof≐
    i ∘ sound g ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound (ccut Γ₀ f g' refl)
  ≐⟨ refl ∘ refl ⊸ sound-ccut Γ₀ f g' refl ⟩
    i ∘ sound g ⊸ id ∘ L⋆ Γ ∘ id ⊸ ([ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ sound g')
  ≐⟨ refl ∘ id⊸∘ ⟩
    i ∘ sound g ⊸ id ∘ L⋆ Γ ∘ (id ⊸ [ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ id ⊸ sound g')
  ≐⟨ (~ ass) ∙ (ass ∘ refl) ⟩
    i ∘ sound g ⊸ id ∘ (L⋆ Γ ∘ id ⊸ [ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f) ∘ id ⊸ sound g'
  ≐⟨ refl ∘ nL⋆2 Γ [ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ refl ⟩
    i ∘ sound g ⊸ id ∘ (id ⊸ [ Γ ∣ [ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ]f ∘ L⋆ Γ) ∘ id ⊸ sound g'
  ≐⟨ refl ∘ (refl ⊸ ≡-to-≐ [ Γ ∣ Γ₀ ∣ass]f ∘ refl) ∘ refl ⟩
    i ∘ sound g ⊸ id ∘ (id ⊸ [ Γ ++ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ L⋆ Γ) ∘ id ⊸ sound g'
  ≐⟨  (~ ass) ∙ (ass ∘ refl) ∘ refl ⟩
    i ∘ (sound g ⊸ id ∘ id ⊸ [ Γ ++ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f) ∘ L⋆ Γ ∘ id ⊸ sound g'
  ≐⟨ refl ∘ swap⊸ ∘ refl ∘ refl ⟩
    i ∘ (id ⊸ [ Γ ++ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ sound g ⊸ id) ∘ L⋆ Γ ∘ id ⊸ sound g'
  ≐⟨ ~ ass ∘ refl ∘ refl ⟩
    i ∘ id ⊸ [ Γ ++ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ sound g ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound g'
  ≐⟨ ~ ni ∘ refl ∘ refl ∘ refl ⟩
    [ Γ ++ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ i ∘ sound g ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound g'
  ≐⟨ ((ass ∘ refl) ∙ ass ∘ refl) ∙ ass ⟩
    [ Γ ++ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ (i ∘ sound g ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound g')
  qed≐
sound-ccut Δ₀ {Δ'} f (ex {Γ = Γ} {Δ} g) r with cases++2 Δ₀ Γ Δ' Δ r
sound-ccut {Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ _ ∷ Δ)} f (ex {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g) refl | inj₁ (Γ₀ , refl , refl) =
  refl ∘ sound-ccut Δ₀ f g refl
  ∙ (≡-to-≐ (sym [ Δ₀ ∣ Γ ++ Γ₀ ∣ass]f) ∘ refl)
  ∙ ~ ass
  ∙ (((~ [ Δ₀ ∣∘]f)
      ∙ [ Δ₀ ∣≐]f ((~ ass)
                  ∙ ((~ ass) ∘ refl)
                  ∙ (ni ∘ refl ∘ refl)
                  ∙ ass ∙  ass
                  ∙ (refl ∘ ((~ ass)
                             ∙ (~ swap⊸ ∘ refl)
                             ∙ ass
                             ∙ (refl ∘ (refl ⊸ ≡-to-≐ (sym [ Γ ∣ Γ₀ ∣ass]f) ∘ refl
                                       ∙ (~ (nL⋆2 Γ _))))))
                  ∙ ~ ass ∙ ~ ass)
      ∙ [ Δ₀ ∣∘]f)
     ∘ refl)
  ∙ ass
  ∙ (refl ∘ (≡-to-≐ [ Δ₀ ∣ _ ∷ Γ₀ ∣ass]f ∘ refl))
sound-ccut {Γ = Γ'} .(Γ ++ _ ∷ _ ∷ Γ₀) {Δ'} f (ex {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g) refl | inj₂ (inj₁ (Γ₀ , refl , refl)) =
  refl ∘ sound-ccut (Γ ++ _ ∷ _ ∷ Γ₀) f g refl
  ∙ (refl ∘ ((~ (≡-to-≐ [ Γ ∣ _ ∷ _ ∷ Γ₀ ∣ass]f)) ∘ refl))
  ∙ ~ ass
  ∙ ((~ [ Γ ∣∘]f
      ∙ [ Γ ∣≐]f (~ ns)
      ∙ [ Γ ∣∘]f)
    ∘ refl)
  ∙ ass
  ∙ (≡-to-≐ [ Γ ∣ _ ∷ _ ∷ Γ₀ ∣ass]f ∘ refl)
sound-ccut {Γ = Γ} Δ₀ {.(_ ∷ Δ)} f (ex {Γ = .Δ₀} {Δ} g) refl | inj₂ (inj₂ (inj₁ (refl , refl , refl))) =
  soundex-fma-cxt Γ (ccut (Δ₀ ++ _ ∷ []) f g refl)
  ∙ (refl ∘ sound-ccut (Δ₀ ++ _ ∷ []) f g refl)
  ∙ (refl ∘ (≡-to-≐ (sym [ Δ₀ ∣ _ ∷ [] ∣ass]f) ∘ refl))
  ∙ ~ ass
  ∙ ((~ [ Δ₀ ∣∘]f
      ∙ [ Δ₀ ∣≐]f (refl ∘ id⊸∘
                  ∙ ~ ass
                  ∙ lem)
      ∙ [ Δ₀ ∣∘]f)
    ∘ refl)
  ∙ ass
  where
    lem : [ex-fma-cxt] Γ ∘ id ⊸ (i ∘ sound f ⊸ id) ∘ id ⊸ L⋆ Γ ≐ i ∘ sound f ⊸ id ∘ L⋆ Γ ∘ s
    lem =
      proof≐
        [ex-fma-cxt] Γ ∘ id ⊸ (i ∘ sound f ⊸ id) ∘ id ⊸ L⋆ Γ
      ≐⟨ (refl ∘ id⊸∘ ∙ ~ ass) ∘ refl ⟩ 
        [ex-fma-cxt] Γ ∘ id ⊸ i ∘ id ⊸ (sound f ⊸ id) ∘ id ⊸ L⋆ Γ
      ≐⟨ refl ∘ is2 ∘ refl ∘ refl ⟩ 
        [ex-fma-cxt] Γ ∘ (i ∘ s) ∘ id ⊸ (sound f ⊸ id) ∘ id ⊸ L⋆ Γ
      ≐⟨ (~ ass ∘ refl ∙ ass) ∘ refl ⟩ 
        [ex-fma-cxt] Γ ∘ i ∘ (s ∘ id ⊸ (sound f ⊸ id)) ∘ id ⊸ L⋆ Γ
      ≐⟨ refl ∘ (~ ns) ∘ refl ⟩ 
        [ex-fma-cxt] Γ ∘ i ∘ (sound f ⊸ (id ⊸ id) ∘ s) ∘ id ⊸ L⋆ Γ
      ≐⟨ (refl ∘ (refl ⊸ f⊸id ∘ refl) ∙ ~ ass) ∘ refl ⟩ 
        [ex-fma-cxt] Γ ∘ i ∘ sound f ⊸ id ∘ s ∘ id ⊸ L⋆ Γ
      ≐⟨  ni ∘ refl ∘ refl ∘ refl ⟩ 
        i ∘ id ⊸ [ex-fma-cxt] Γ ∘ sound f ⊸ id ∘ s ∘ id ⊸ L⋆ Γ
      ≐⟨ ass ∘ refl ∘ refl ⟩ 
        i ∘ (id ⊸ [ex-fma-cxt] Γ ∘ sound f ⊸ id) ∘ s ∘ id ⊸ L⋆ Γ
      ≐⟨ refl ∘ (~ swap⊸) ∘ refl ∘ refl ⟩ 
        i ∘ (sound f ⊸ id ∘ id ⊸ [ex-fma-cxt] Γ) ∘ s ∘ id ⊸ L⋆ Γ
      ≐⟨ (~ ass ∘ refl ∙ ass) ∘ refl ∙ ass ⟩ 
        i ∘ sound f ⊸ id ∘ (id ⊸ [ex-fma-cxt] Γ ∘ s ∘ id ⊸ L⋆ Γ)
      ≐⟨ refl ∘ (~ sL⋆1 Γ) ⟩ 
        i ∘ sound f ⊸ id ∘ (L⋆ Γ ∘ s)
      ≐⟨ ~ ass ⟩ 
        i ∘ sound f ⊸ id ∘ L⋆ Γ {_}{_ ⊸ [ Δ ∣ _ ]} ∘ s
      qed≐
sound-ccut {Γ = Γ'} .(Γ ++ _ ∷ []) {Δ'} f (ex {Γ = Γ} {.Δ'} g) refl | inj₂ (inj₂ (inj₂ (refl , refl , refl))) =
  soundex-cxt-fma Γ' (ccut Γ f g refl)
  ∙ (refl ∘ sound-ccut Γ f g refl)
  ∙ (~ ass)
  ∙ ((~ [ Γ ∣∘]f
      ∙ [ Γ ∣≐]f (lem ∙ (~ id⊸∘ ∘ refl))
      ∙ [ Γ ∣∘]f
      ∙ (≡-to-≐ [ Γ ∣ _ ∷ [] ∣ass]f ∘ refl))
     ∘ refl)
  ∙ ass
  where
    lem : [ex-cxt-fma] Γ' ∘ (i ∘ sound f ⊸ id ∘ L⋆ Γ') ≐
                       id ⊸ (i ∘ sound f ⊸ id) ∘ id ⊸ L⋆ Γ' ∘ s
    lem =
      proof≐
        [ex-cxt-fma] Γ' ∘ (i ∘ sound f ⊸ id ∘ L⋆ Γ')
      ≐⟨ ~ ass ∙ (~ ass ∘ refl) ⟩ 
        [ex-cxt-fma] Γ' ∘ i ∘ sound f ⊸ id ∘ L⋆ Γ'
      ≐⟨ ni ∘ refl ∘ refl ⟩ 
        i ∘ id ⊸ [ex-cxt-fma] Γ' ∘ sound f ⊸ id ∘ L⋆ Γ'
      ≐⟨ ass ∘ refl ⟩ 
        i ∘ (id ⊸ [ex-cxt-fma] Γ' ∘ sound f ⊸ id) ∘ L⋆ Γ'
      ≐⟨ is1 ∘ (~ swap⊸) ∘ refl ⟩ 
        id ⊸ i ∘ s ∘ (sound f ⊸ id ∘ id ⊸ [ex-cxt-fma] Γ') ∘ L⋆ Γ'
      ≐⟨ (~ ass ∙ ((refl ∘ refl ⊸ (~ f⊸id) ∙ ass) ∘ refl)) ∘ refl ⟩ 
        id ⊸ i ∘ (s ∘ sound f ⊸ (id ⊸ id)) ∘ id ⊸ [ex-cxt-fma] Γ' ∘ L⋆ Γ'
      ≐⟨ refl ∘ ~ ns ∘ refl ∘ refl ⟩ 
        id ⊸ i ∘ (id ⊸ (sound f ⊸ id) ∘ s) ∘ id ⊸ [ex-cxt-fma] Γ' ∘ L⋆ Γ'
      ≐⟨ (~ ass ∘ refl ∙ ass) ∘ refl ∙ ass ⟩ 
        id ⊸ i ∘ id ⊸ (sound f ⊸ id) ∘ (s ∘ id ⊸ [ex-cxt-fma] Γ' ∘ L⋆ Γ')
      ≐⟨ (~ id⊸∘) ∘ refl ⟩ 
        id ⊸ (i ∘ sound f ⊸ id) ∘ (s ∘ id ⊸ [ex-cxt-fma] Γ' ∘ L⋆ Γ')
      ≐⟨ refl ∘ (~ sL⋆2 Γ') ⟩ 
        id ⊸ (i ∘ sound f ⊸ id) ∘ (id ⊸ L⋆ Γ' ∘ s)
      ≐⟨ ~ ass ⟩ 
        id ⊸ (i ∘ sound f ⊸ id) ∘ id ⊸ L⋆ Γ' ∘ s
      qed≐

soundcmplt : {A C : Fma} → (f : A ⇒ C) → sound (cmplt f) ≐ f
soundcmplt id = refl
soundcmplt (f ∘ g) =
  proof≐
    sound (scut (cmplt g) (cmplt f))
  ≐⟨ sound-scut (cmplt g) (cmplt f) ⟩
    sound (cmplt f) ∘ sound (cmplt g)
  ≐⟨ soundcmplt f ∘ soundcmplt g ⟩
    f ∘ g
  qed≐
soundcmplt (f ⊸ g) = 
  proof≐ 
    i ∘ (id ⊸ sound (cmplt f) ∘ j) ⊸ id ∘ (L ∘ id) ∘ id ⊸ sound (cmplt g)
  ≐⟨ refl ∘ (refl ⊸ soundcmplt f ∘ refl) ⊸ refl ∘ ~ rid ∘ refl ⊸ soundcmplt g ⟩
    i ∘ (id ⊸ f ∘ j) ⊸ id ∘ L ∘ id ⊸ g
  ≐⟨ refl ∘ (~ nj) ⊸ rid ∘ refl ∘ refl ⟩
    i ∘ (f ⊸ id ∘ j) ⊸ (id ∘ id) ∘ L ∘ id ⊸ g
  ≐⟨ refl ∘ f⊸∘ ∘ refl ∘ refl ⟩
    i ∘ (j ⊸ id ∘ (f ⊸ id) ⊸ id) ∘ L ∘ id ⊸ g
  ≐⟨ (~ ass ∘ refl) ∙ ass ∘ refl ⟩
    i ∘ j ⊸ id ∘ ((f ⊸ id) ⊸ id ∘ L) ∘ id ⊸ g
  ≐⟨ refl ∘ (~ (refl ⊸ f⊸id) ∘ refl) ∘ refl  ⟩
    i ∘ j ⊸ id ∘ ((f ⊸ id) ⊸ (id ⊸ id) ∘ L) ∘ id ⊸ g
  ≐⟨ refl ∘ nL ∘ refl ⟩
    i ∘ j ⊸ id ∘ (id ⊸ (f ⊸ id) ∘ L ∘ id ⊸ id) ∘ id ⊸ g
  ≐⟨ refl ∘ (refl ∘ f⊸id) ∘ refl ⟩
    i ∘ j ⊸ id ∘ (id ⊸ (f ⊸ id) ∘ L ∘ id) ∘ id ⊸ g
  ≐⟨ (~ ass) ∙ ((~ ass) ∙ (ass ∘ refl) ∘ refl) ∘ refl ⟩
    i ∘ (j ⊸ id ∘ id ⊸ (f ⊸ id)) ∘ L ∘ id ∘ id ⊸ g
  ≐⟨ ~ rid ∘ refl ⟩
    i ∘ (j ⊸ id ∘ id ⊸ (f ⊸ id)) ∘ L ∘ id ⊸ g
  ≐⟨ refl ∘ ~ f⊸∘ ∘ refl ∘ refl ⟩
    i ∘ (id ∘ j) ⊸ (id ∘ f ⊸ id) ∘ L ∘ id ⊸ g
  ≐⟨ refl ∘ (lid ∙ rid) ⊸ (lid ∙ rid) ∘ refl ∘ refl  ⟩
    i ∘ (j ∘ id) ⊸ (f ⊸ id ∘ id) ∘ L ∘ id ⊸ g
  ≐⟨ refl ∘ f⊸∘ ∘ refl ∘ refl  ⟩
    i ∘ (id ⊸ (f ⊸ id) ∘ j ⊸ id) ∘ L ∘ id ⊸ g
  ≐⟨ ~ ass ∘ refl ∘ refl ⟩
    i ∘ id ⊸ (f ⊸ id) ∘ j ⊸ id ∘ L ∘ id ⊸ g
  ≐⟨ ~ ni ∘ refl ∘ refl ∘ refl ⟩
    f ⊸ id ∘ i ∘ j ⊸ id ∘ L ∘ id ⊸ g
  ≐⟨ (ass ∘ refl) ∙ ass ∘ refl ⟩
    f ⊸ id ∘ (i ∘ j ⊸ id ∘ L) ∘ id ⊸ g
  ≐⟨ refl ∘ ijL ∘ refl ⟩
    f ⊸ id ∘ id ∘ id ⊸ g
  ≐⟨ ~ (rid ∘ refl) ⟩
    f ⊸ id ∘ id ⊸ g
  ≐⟨ ~ f⊸∘ ⟩
    (id ∘ f) ⊸ (id ∘ g)
  ≐⟨ lid ⊸ lid ⟩
    f ⊸ g
  qed≐
soundcmplt i =
  proof≐
    i ∘ id ⊸ id ∘ id ∘ id ⊸ id
  ≐⟨ refl ∘ f⊸id ∘ refl ∘ f⊸id ⟩
    i ∘ id ∘ id ∘ id
  ≐⟨ ~ (rid ∙ (rid ∙ rid)) ⟩
    i
  qed≐
soundcmplt j = (f⊸id ∘ refl) ∙ lid
soundcmplt L =
  proof≐
    i ∘ (id ⊸ (i ∘ (id ⊸ id ∘ j) ⊸ id ∘ (L ∘ id) ∘ id ⊸ id) ∘ j) ⊸ id ∘ (L ∘ (L ∘ id)) ∘ id ⊸ id
  ≐⟨ refl ∘ (refl ⊸ (refl ∘ (f⊸id ∘ refl) ⊸ refl  ∘ ~ rid ∘ f⊸id) ∘ refl) ⊸ refl  ∘ (refl ∘ ~ rid) ∘ f⊸id ⟩
    i ∘ (id ⊸ (i ∘ (id ∘ j) ⊸ id ∘ L ∘ id) ∘ j) ⊸ id ∘ (L ∘ L) ∘ id
  ≐⟨ ~ rid ⟩
    i ∘ (id ⊸ (i ∘ (id ∘ j) ⊸ id ∘ L ∘ id) ∘ j) ⊸ id ∘ (L ∘ L)
  ≐⟨ refl ∘ (refl ⊸ (~ rid) ∙ refl ⊸ (refl ∘ lid ⊸ refl ∘ refl) ∘ refl) ⊸ refl ∘ refl ⟩
    i ∘ (id ⊸ (i ∘ j ⊸ id ∘ L) ∘ j) ⊸ id ∘ (L ∘ L)
  ≐⟨ refl ∘ (refl ⊸ ijL ∘ refl) ⊸ refl ∘ refl ⟩
    i ∘ (id ⊸ id ∘ j) ⊸ id ∘ (L ∘ L)
  ≐⟨ refl ∘ ((f⊸id ∘ refl) ∙ lid) ⊸ refl ∘ refl ⟩
    i ∘ j ⊸ id ∘ (L ∘ L)
  ≐⟨ ~ ass ⟩
    i ∘ j ⊸ id ∘ L ∘ L
  ≐⟨ ijL ∘ refl ⟩
    id ∘ L
  ≐⟨ lid ⟩
    L
  qed≐
soundcmplt s =
  proof≐
    s ∘ (i ∘ (id ⊸ id ∘ j) ⊸ id ∘ (L ∘ id) ∘ id ⊸ (i ∘ (id ⊸ id ∘ j) ⊸ id ∘ (L ∘ id) ∘ id ⊸ id))
  ≐⟨ refl ∘ (refl ∘ ((f⊸id ∘ refl) ∙ lid) ⊸ refl ∘ refl ∘ refl) ⟩
    s ∘ (i ∘ j ⊸ id ∘ (L ∘ id) ∘ id ⊸ (i ∘ (id ⊸ id ∘ j) ⊸ id ∘ (L ∘ id) ∘ id ⊸ id))
  ≐⟨ refl ∘ (refl ∘ ~ rid ∘ refl ⊸ (refl ∘ ((f⊸id ∘ refl) ∙ lid) ⊸ refl ∘ (~ rid) ∘ f⊸id ∙ ~ rid)) ⟩
    s ∘ (i ∘ j ⊸ id ∘ L ∘ id ⊸ (i ∘ j ⊸ id ∘ L))
  ≐⟨ refl ∘ (refl ∘ (refl ⊸ ijL ∙ f⊸id)) ⟩
    s ∘ (i ∘ j ⊸ id ∘ L ∘ id)
  ≐⟨ refl ∘ ~ rid ⟩
    s ∘ (i ∘ j ⊸ id ∘ L)
  ≐⟨ refl ∘ ijL ⟩
    s ∘ id
  ≐⟨ ~ rid ⟩
    s
  qed≐

