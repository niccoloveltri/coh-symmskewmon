{-# OPTIONS --rewriting #-}

module EqSound where

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
open import Sound

-- ====================================================================

-- the "sound" function is well-defined, since it sends ≗-related
-- derivations to ≐-related derivations.

eq-sound : ∀{S Γ C} {f g : S ∣ Γ ⊢ C} → f ≗ g → sound f ≐ sound g
eq-sound refl = refl
eq-sound (~ p) = ~ eq-sound p
eq-sound (p ∙ p₁) = eq-sound p ∙ eq-sound p₁
eq-sound (uf p) = eq-sound p ∘ refl
eq-sound (⊗l p) = eq-sound p
eq-sound (Il p) = eq-sound p
eq-sound (⊗r p p₁) = eq-sound p ⊗ eq-sound p₁ ∘ refl
eq-sound axI = refl
eq-sound ax⊗ = lαρ ∙ ~ (refl ⊗ lid ∘ lid ∘ refl) ∙ ass
eq-sound (⊗ruf {Γ}{Δ}{A}{A'}{B}{f}{g}) =
  proof≐
    ((sound f ∘ [ l ∣ Γ ]f) ⊗ sound g) ∘ φ' (I ⊗ A') Γ Δ
  ≐⟨ refl ⊗ rid ∘ refl ⟩
    ((sound f ∘ [ l ∣ Γ ]f) ⊗ (sound g ∘ id)) ∘ φ' (I ⊗ A') Γ Δ
  ≐⟨ f⊗∘ ∘ refl ⟩
    (sound f ⊗ sound g) ∘ ([ l ∣ Γ ]f ⊗ id) ∘ φ' (I ⊗ A') Γ Δ
  ≐⟨ ass ⟩
    (sound f ⊗ sound g) ∘ (([ l ∣ Γ ]f ⊗ id) ∘ φ' (I ⊗ A') Γ Δ)
  ≐⟨ refl ∘ nφ' Γ Δ l ⟩ 
    (sound f ⊗ sound g) ∘ (φ' A' Γ Δ ∘ [ l ∣ Γ ++ Δ ]f)
  ≐⟨ ~ ass ⟩
    (sound f ⊗ sound g) ∘ φ' A' Γ Δ ∘ [ l ∣ Γ ++ Δ ]f
  qed≐
eq-sound ⊗rIl = refl
eq-sound ⊗r⊗l = refl
eq-sound (ex p) = eq-sound p ∘ refl
eq-sound (exex {Γ₂ = Γ₂} {Γ₃} {f = f}) =
  proof≐
    sound f ∘ [ [ s ∣ Γ₂ ]f ⊗ id ⊗ id ∣ Γ₃ ]f ∘ [ s ∣ Γ₃ ]f
  ≐⟨ ass ⟩ 
    sound f ∘ ([ [ s ∣ Γ₂ ]f ⊗ id ⊗ id ∣ Γ₃ ]f ∘ [ s ∣ Γ₃ ]f)
  ≐⟨ refl ∘ (~ [∘∣ Γ₃ ] _ _) ⟩ 
    sound f ∘ [ [ s ∣ Γ₂ ]f ⊗ id ⊗ id ∘ s ∣ Γ₃ ]f
  ≐⟨ refl ∘ [≐∣ Γ₃ ] (~ ns) ⟩ 
    sound f ∘ [ s ∘ [ s ∣ Γ₂ ]f ⊗ id ⊗ id ∣ Γ₃ ]f
  ≐⟨ refl ∘ [∘∣ Γ₃ ] _ _ ⟩ 
    sound f ∘ ([ s ∣ Γ₃ ]f ∘ [ [ s ∣ Γ₂ ]f ⊗ id ⊗ id ∣ Γ₃ ]f)
  ≐⟨ ~ ass ⟩ 
    sound f ∘ [ s ∣ Γ₃ ]f ∘ [ [ s ∣ Γ₂ ]f ⊗ id ⊗ id ∣ Γ₃ ]f
  qed≐
eq-sound (exuf {Γ} {Δ} {f = f}) =
  proof≐
    sound f ∘ [ [ l ∣ Γ ]f ⊗ id ⊗ id ∣ Δ ]f ∘ [ s ∣ Δ ]f
  ≐⟨ ass ⟩ 
    sound f ∘ ([ [ l ∣ Γ ]f ⊗ id ⊗ id ∣ Δ ]f ∘ [ s ∣ Δ ]f)
  ≐⟨ refl ∘ (~ [∘∣ Δ ] _ _) ⟩ 
    sound f ∘ [ [ l ∣ Γ ]f ⊗ id ⊗ id ∘ s ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ ns) ⟩ 
    sound f ∘ [ s ∘ [ l ∣ Γ ]f ⊗ id ⊗ id ∣ Δ ]f
  ≐⟨ refl ∘ [∘∣ Δ ] _ _ ⟩ 
    sound f ∘ ([ s ∣ Δ ]f ∘ [ [ l ∣ Γ ]f ⊗ id ⊗ id ∣ Δ ]f)
  ≐⟨ ~ ass ⟩ 
    sound f ∘ [ s ∣ Δ ]f ∘ [ [ l ∣ Γ ]f ⊗ id ⊗ id ∣ Δ ]f
  qed≐
eq-sound exIl = refl
eq-sound ex⊗l = refl
eq-sound (ex⊗r₁ {Γ₁ = Γ₁} {Γ₂} {Δ} {A} {B} {f = f} {g}) =
  proof≐
    sound f ⊗ sound g ∘ φ' _ (Γ₁ ++ A ∷ B ∷ Γ₂) Δ ∘ [ [ s ∣ Γ₂ ]f ∣ Δ ]f
  ≐⟨ ass ⟩
    sound f ⊗ sound g ∘ (φ' _ (Γ₁ ++ A ∷ B ∷ Γ₂) Δ ∘ [ [ s ∣ Γ₂ ]f ∣ Δ ]f)
  ≐⟨ refl ∘ (~ nφ' Γ₂ Δ _) ⟩
    sound f ⊗ sound g ∘ ([ s ∣ Γ₂ ]f ⊗ id ∘ φ' _ (Γ₁ ++ B ∷ A ∷ Γ₂) Δ)
  ≐⟨ ~ ass ⟩
    sound f ⊗ sound g ∘ [ s ∣ Γ₂ ]f ⊗ id ∘ φ' _ (Γ₁ ++ B ∷ A ∷ Γ₂) Δ
  ≐⟨ (~ f⊗∘) ∘ refl ⟩
    (sound f ∘ [ s ∣ Γ₂ ]f) ⊗ (sound g ∘ id) ∘ φ' _ (Γ₁ ++ B ∷ A ∷ Γ₂) Δ
  ≐⟨ refl ⊗ (~ rid) ∘ refl ⟩
    (sound f ∘ [ s ∣ Γ₂ ]f) ⊗ sound g ∘ φ' _ (Γ₁ ++ B ∷ A ∷ Γ₂) Δ
  qed≐
eq-sound (ex⊗r₂ {S} {Γ} {Δ₁} {Δ₂} {A} {B} {f = f} {g}) =
  proof≐
    sound f ⊗ sound g ∘ φ' _ Γ (Δ₁ ++ A ∷ B ∷ Δ₂) ∘ [ s ∣ Δ₂ ]f
  ≐⟨ ass ⟩
    sound f ⊗ sound g ∘ (φ' _ Γ (Δ₁ ++ A ∷ B ∷ Δ₂) ∘ [ s ∣ Δ₂ ]f)
  ≐⟨ refl ∘ (φ'++ _ Γ Δ₁ (A ∷ B ∷ Δ₂)  ∘ refl) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ Δ₂ ∘ [ α ∣ Δ₂ ]f ∘ [ α ⊗ id ∣ Δ₂ ]f
      ∘ [ φ' _ Γ Δ₁ ⊗ id ⊗ id ∣ Δ₂ ]f ∘ [ s ∣ Δ₂ ]f)
  ≐⟨ refl ∘ (ass ∙ (refl ∘ (~ [∘∣ Δ₂ ] _ _))) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ Δ₂ ∘ [ α ∣ Δ₂ ]f ∘ [ α ⊗ id ∣ Δ₂ ]f
      ∘ [ φ' _ Γ Δ₁ ⊗ id ⊗ id ∘ s ∣ Δ₂ ]f)
  ≐⟨ refl ∘ (refl ∘ [≐∣ Δ₂ ] (~ ns)) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ Δ₂ ∘ [ α ∣ Δ₂ ]f ∘ [ α ⊗ id ∣ Δ₂ ]f
      ∘ [ s ∘ φ' _ Γ Δ₁ ⊗ id ⊗ id ∣ Δ₂ ]f)
  ≐⟨ refl ∘ (refl ∘ [∘∣ Δ₂ ] _ _ ∙ (~ ass ∙ ((ass ∘ refl ∙ ass) ∘ refl))) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ Δ₂
      ∘ ([ α ∣ Δ₂ ]f ∘ [ α ⊗ id ∣ Δ₂ ]f ∘ [ s ∣ Δ₂ ]f)
      ∘ [ φ' _ Γ Δ₁ ⊗ id ⊗ id ∣ Δ₂ ]f)
  ≐⟨ refl ∘ (refl ∘ ((~ [∘∣ Δ₂ ] _ _) ∘ refl ∙ (~ [∘∣ Δ₂ ] _ _)) ∘ refl) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ Δ₂
      ∘ [ α ∘ α ⊗ id ∘ s ∣ Δ₂ ]f
      ∘ [ φ' _ Γ Δ₁ ⊗ id ⊗ id ∣ Δ₂ ]f)
  ≐⟨ refl ∘ (refl ∘ [≐∣ Δ₂ ] sα3 ∘ refl) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ Δ₂
      ∘ [ id ⊗ s ∘ α ∘ α ⊗ id ∣ Δ₂ ]f
      ∘ [ φ' _ Γ Δ₁ ⊗ id ⊗ id ∣ Δ₂ ]f)
  ≐⟨ refl ∘ (refl ∘ ([∘∣ Δ₂ ] _ _ ∙ ([∘∣ Δ₂ ] _ _ ∘ refl)) ∘ refl) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ Δ₂
      ∘ ([ id ⊗ s ∣ Δ₂ ]f ∘ [ α ∣ Δ₂ ]f ∘ [ α ⊗ id ∣ Δ₂ ]f)
      ∘ [ φ' _ Γ Δ₁ ⊗ id ⊗ id ∣ Δ₂ ]f)
  ≐⟨ refl ∘ ((~ ass ∙ ((~ ass ∙ ((~ nψ2 Δ₂ s) ∘ refl)) ∘ refl)) ∘ refl) ⟩
    sound f ⊗ sound g ∘ (id ⊗ [ s ∣ Δ₂ ]f ∘ ψ _ _ Δ₂
      ∘ [ α ∣ Δ₂ ]f ∘ [ α ⊗ id ∣ Δ₂ ]f ∘ [ φ' _ Γ Δ₁ ∣ B ∷ A ∷ Δ₂ ]f)
  ≐⟨ refl ∘ ((ass ∘ refl ∙ ass) ∘ refl ∙ ass) ⟩
    sound f ⊗ sound g ∘ (id ⊗ [ s ∣ Δ₂ ]f ∘ (ψ _ _ Δ₂
      ∘ [ α ∣ Δ₂ ]f ∘ [ α ⊗ id ∣ Δ₂ ]f ∘ [ φ' _ Γ Δ₁ ∣ B ∷ A ∷ Δ₂ ]f))
  ≐⟨ refl ∘ (refl ∘ (~ (φ'++ _ Γ Δ₁ (B ∷ A ∷ Δ₂)))) ⟩
    sound f ⊗ sound g ∘ (id ⊗ [ s ∣ Δ₂ ]f ∘ φ' _ Γ (Δ₁ ++ B ∷ A ∷ Δ₂))
  ≐⟨ ~ ass ⟩
    sound f ⊗ sound g ∘ id ⊗ [ s ∣ Δ₂ ]f ∘ φ' _ Γ (Δ₁ ++ B ∷ A ∷ Δ₂)
  ≐⟨ (~ f⊗∘) ∘ refl ⟩
    (sound f ∘ id) ⊗ (sound g ∘ [ s ∣ Δ₂ ]f) ∘ φ' _ Γ (Δ₁ ++ B ∷ A ∷ Δ₂)
  ≐⟨ (~ rid) ⊗ refl ∘ refl ⟩
    sound f ⊗ (sound g ∘ [ s ∣ Δ₂ ]f) ∘ φ' _ Γ (Δ₁ ++ B ∷ A ∷ Δ₂)
  qed≐
eq-sound (ex-braid {Δ = Δ} {f = f}) =
  proof≐
    sound f ∘ [ s ⊗ id ∣ Δ ]f ∘ [ s ∣ Δ ]f ∘ [ s ⊗ id ∣ Δ ]f
  ≐⟨ ass ∘ refl ∙ ass ⟩ 
    sound f ∘ ([ s ⊗ id ∣ Δ ]f ∘ [ s ∣ Δ ]f ∘ [ s ⊗ id ∣ Δ ]f)
  ≐⟨ refl ∘ ((~ [∘∣ Δ ] _ _) ∘ refl ∙ (~ [∘∣ Δ ] _ _)) ⟩ 
    sound f ∘ [ s ⊗ id ∘ s ∘ s ⊗ id ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] sss ⟩ 
    sound f ∘ [ s ∘ s ⊗ id ∘ s ∣ Δ ]f
  ≐⟨ refl ∘ ([∘∣ Δ ] _ _ ∙ ([∘∣ Δ ] _ _ ∘ refl)) ⟩ 
    sound f ∘ ([ s ∣ Δ ]f ∘ [ s ⊗ id ∣ Δ ]f ∘ [ s ∣ Δ ]f)
  ≐⟨ ~ (ass ∘ refl ∙ ass) ⟩ 
    sound f ∘ [ s ∣ Δ ]f ∘ [ s ⊗ id ∣ Δ ]f ∘ [ s ∣ Δ ]f
  qed≐
eq-sound {g = g} (ex-iso {Δ = Δ}) =
  proof≐
    sound g ∘ [ s ∣ Δ ]f ∘ [ s ∣ Δ ]f
  ≐⟨ ass ⟩
    sound g ∘ ([ s ∣ Δ ]f ∘ [ s ∣ Δ ]f)
  ≐⟨ refl ∘ (~ [∘∣ Δ ] _ _) ⟩
    sound g ∘ [ s ∘ s ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] ss ⟩
    sound g ∘ [ id ∣ Δ ]f
  ≐⟨ refl ∘ [id∣ Δ ] ⟩
    sound g ∘ id
  ≐⟨ ~ rid ⟩
    sound g
  qed≐
