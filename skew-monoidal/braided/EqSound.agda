{-# OPTIONS --rewriting #-}

module EqSound where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Bool
open import Data.Bool.Properties
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
eq-sound (ex b p) = eq-sound p ∘ refl
eq-sound (exex {Γ₂ = Γ₂} {Γ₃} {f = f}) =
  proof≐
    sound f ∘ [ [ s _ ∣ Γ₂ ]f ⊗ id ⊗ id ∣ Γ₃ ]f ∘ [ s _ ∣ Γ₃ ]f
  ≐⟨ ass ⟩ 
    sound f ∘ ([ [ s _ ∣ Γ₂ ]f ⊗ id ⊗ id ∣ Γ₃ ]f ∘ [ s _ ∣ Γ₃ ]f)
  ≐⟨ refl ∘ (~ [∘∣ Γ₃ ] _ _) ⟩ 
    sound f ∘ [ [ s _ ∣ Γ₂ ]f ⊗ id ⊗ id ∘ s _ ∣ Γ₃ ]f
  ≐⟨ refl ∘ [≐∣ Γ₃ ] (~ ns) ⟩ 
    sound f ∘ [ s _ ∘ [ s _ ∣ Γ₂ ]f ⊗ id ⊗ id ∣ Γ₃ ]f
  ≐⟨ refl ∘ [∘∣ Γ₃ ] _ _ ⟩ 
    sound f ∘ ([ s _ ∣ Γ₃ ]f ∘ [ [ s _ ∣ Γ₂ ]f ⊗ id ⊗ id ∣ Γ₃ ]f)
  ≐⟨ ~ ass ⟩ 
    sound f ∘ [ s _ ∣ Γ₃ ]f ∘ [ [ s _ ∣ Γ₂ ]f ⊗ id ⊗ id ∣ Γ₃ ]f
  qed≐
eq-sound (exuf {Γ} {Δ} {f = f}) =
  proof≐
    sound f ∘ [ [ l ∣ Γ ]f ⊗ id ⊗ id ∣ Δ ]f ∘ [ s true ∣ Δ ]f
  ≐⟨ ass ⟩ 
    sound f ∘ ([ [ l ∣ Γ ]f ⊗ id ⊗ id ∣ Δ ]f ∘ [ s true ∣ Δ ]f)
  ≐⟨ refl ∘ (~ [∘∣ Δ ] _ _) ⟩ 
    sound f ∘ [ [ l ∣ Γ ]f ⊗ id ⊗ id ∘ s true ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ ns) ⟩ 
    sound f ∘ [ s true ∘ [ l ∣ Γ ]f ⊗ id ⊗ id ∣ Δ ]f
  ≐⟨ refl ∘ [∘∣ Δ ] _ _ ⟩ 
    sound f ∘ ([ s true ∣ Δ ]f ∘ [ [ l ∣ Γ ]f ⊗ id ⊗ id ∣ Δ ]f)
  ≐⟨ ~ ass ⟩ 
    sound f ∘ [ s true ∣ Δ ]f ∘ [ [ l ∣ Γ ]f ⊗ id ⊗ id ∣ Δ ]f
  qed≐
eq-sound exIl = refl
eq-sound ex⊗l = refl
eq-sound (ex⊗r₁ {Γ₁ = Γ₁} {Γ₂} {Δ} {A} {B} {f = f} {g}) =
  proof≐
    sound f ⊗ sound g ∘ φ' _ (Γ₁ ++ A ∷ B ∷ Γ₂) Δ ∘ [ [ s true ∣ Γ₂ ]f ∣ Δ ]f
  ≐⟨ ass ⟩
    sound f ⊗ sound g ∘ (φ' _ (Γ₁ ++ A ∷ B ∷ Γ₂) Δ ∘ [ [ s true ∣ Γ₂ ]f ∣ Δ ]f)
  ≐⟨ refl ∘ (~ nφ' Γ₂ Δ _) ⟩
    sound f ⊗ sound g ∘ ([ s true ∣ Γ₂ ]f ⊗ id ∘ φ' _ (Γ₁ ++ B ∷ A ∷ Γ₂) Δ)
  ≐⟨ ~ ass ⟩
    sound f ⊗ sound g ∘ [ s true ∣ Γ₂ ]f ⊗ id ∘ φ' _ (Γ₁ ++ B ∷ A ∷ Γ₂) Δ
  ≐⟨ (~ f⊗∘) ∘ refl ⟩
    (sound f ∘ [ s true ∣ Γ₂ ]f) ⊗ (sound g ∘ id) ∘ φ' _ (Γ₁ ++ B ∷ A ∷ Γ₂) Δ
  ≐⟨ refl ⊗ (~ rid) ∘ refl ⟩
    (sound f ∘ [ s true ∣ Γ₂ ]f) ⊗ sound g ∘ φ' _ (Γ₁ ++ B ∷ A ∷ Γ₂) Δ
  qed≐
eq-sound (ex⊗r₂ {S} {Γ} {Δ₁} {Δ₂} {A} {B} {f = f} {g}) =
  proof≐
    sound f ⊗ sound g ∘ φ' _ Γ (Δ₁ ++ A ∷ B ∷ Δ₂) ∘ [ s true ∣ Δ₂ ]f
  ≐⟨ ass ⟩
    sound f ⊗ sound g ∘ (φ' _ Γ (Δ₁ ++ A ∷ B ∷ Δ₂) ∘ [ s true ∣ Δ₂ ]f)
  ≐⟨ refl ∘ (φ'++ _ Γ Δ₁ (A ∷ B ∷ Δ₂)  ∘ refl) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ Δ₂ ∘ [ α ∣ Δ₂ ]f ∘ [ α ⊗ id ∣ Δ₂ ]f
      ∘ [ φ' _ Γ Δ₁ ⊗ id ⊗ id ∣ Δ₂ ]f ∘ [ s true ∣ Δ₂ ]f)
  ≐⟨ refl ∘ (ass ∙ (refl ∘ (~ [∘∣ Δ₂ ] _ _))) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ Δ₂ ∘ [ α ∣ Δ₂ ]f ∘ [ α ⊗ id ∣ Δ₂ ]f
      ∘ [ φ' _ Γ Δ₁ ⊗ id ⊗ id ∘ s true ∣ Δ₂ ]f)
  ≐⟨ refl ∘ (refl ∘ [≐∣ Δ₂ ] (~ ns)) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ Δ₂ ∘ [ α ∣ Δ₂ ]f ∘ [ α ⊗ id ∣ Δ₂ ]f
      ∘ [ s true ∘ φ' _ Γ Δ₁ ⊗ id ⊗ id ∣ Δ₂ ]f)
  ≐⟨ refl ∘ (refl ∘ [∘∣ Δ₂ ] _ _ ∙ (~ ass ∙ ((ass ∘ refl ∙ ass) ∘ refl))) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ Δ₂
      ∘ ([ α ∣ Δ₂ ]f ∘ [ α ⊗ id ∣ Δ₂ ]f ∘ [ s true ∣ Δ₂ ]f)
      ∘ [ φ' _ Γ Δ₁ ⊗ id ⊗ id ∣ Δ₂ ]f)
  ≐⟨ refl ∘ (refl ∘ ((~ [∘∣ Δ₂ ] _ _) ∘ refl ∙ (~ [∘∣ Δ₂ ] _ _)) ∘ refl) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ Δ₂
      ∘ [ α ∘ α ⊗ id ∘ s true ∣ Δ₂ ]f
      ∘ [ φ' _ Γ Δ₁ ⊗ id ⊗ id ∣ Δ₂ ]f)
  ≐⟨ refl ∘ (refl ∘ [≐∣ Δ₂ ] sα3 ∘ refl) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ Δ₂
      ∘ [ id ⊗ s true ∘ α ∘ α ⊗ id ∣ Δ₂ ]f
      ∘ [ φ' _ Γ Δ₁ ⊗ id ⊗ id ∣ Δ₂ ]f)
  ≐⟨ refl ∘ (refl ∘ ([∘∣ Δ₂ ] _ _ ∙ ([∘∣ Δ₂ ] _ _ ∘ refl)) ∘ refl) ⟩
    sound f ⊗ sound g ∘ (ψ _ _ Δ₂
      ∘ ([ id ⊗ s true ∣ Δ₂ ]f ∘ [ α ∣ Δ₂ ]f ∘ [ α ⊗ id ∣ Δ₂ ]f)
      ∘ [ φ' _ Γ Δ₁ ⊗ id ⊗ id ∣ Δ₂ ]f)
  ≐⟨ refl ∘ ((~ ass ∙ ((~ ass ∙ ((~ nψ2 Δ₂ (s _)) ∘ refl)) ∘ refl)) ∘ refl) ⟩
    sound f ⊗ sound g ∘ (id ⊗ [ s true ∣ Δ₂ ]f ∘ ψ _ _ Δ₂
      ∘ [ α ∣ Δ₂ ]f ∘ [ α ⊗ id ∣ Δ₂ ]f ∘ [ φ' _ Γ Δ₁ ∣ B ∷ A ∷ Δ₂ ]f)
  ≐⟨ refl ∘ ((ass ∘ refl ∙ ass) ∘ refl ∙ ass) ⟩
    sound f ⊗ sound g ∘ (id ⊗ [ s true ∣ Δ₂ ]f ∘ (ψ _ _ Δ₂
      ∘ [ α ∣ Δ₂ ]f ∘ [ α ⊗ id ∣ Δ₂ ]f ∘ [ φ' _ Γ Δ₁ ∣ B ∷ A ∷ Δ₂ ]f))
  ≐⟨ refl ∘ (refl ∘ (~ (φ'++ _ Γ Δ₁ (B ∷ A ∷ Δ₂)))) ⟩
    sound f ⊗ sound g ∘ (id ⊗ [ s true ∣ Δ₂ ]f ∘ φ' _ Γ (Δ₁ ++ B ∷ A ∷ Δ₂))
  ≐⟨ ~ ass ⟩
    sound f ⊗ sound g ∘ id ⊗ [ s true ∣ Δ₂ ]f ∘ φ' _ Γ (Δ₁ ++ B ∷ A ∷ Δ₂)
  ≐⟨ (~ f⊗∘) ∘ refl ⟩
    (sound f ∘ id) ⊗ (sound g ∘ [ s true ∣ Δ₂ ]f) ∘ φ' _ Γ (Δ₁ ++ B ∷ A ∷ Δ₂)
  ≐⟨ (~ rid) ⊗ refl ∘ refl ⟩
    sound f ⊗ (sound g ∘ [ s true ∣ Δ₂ ]f) ∘ φ' _ Γ (Δ₁ ++ B ∷ A ∷ Δ₂)
  qed≐
eq-sound (ex-braid {Δ = Δ} {f = f}) =
  proof≐
    sound f ∘ [ s true ⊗ id ∣ Δ ]f ∘ [ s true ∣ Δ ]f ∘ [ s true ⊗ id ∣ Δ ]f
  ≐⟨ ass ∘ refl ∙ ass ⟩ 
    sound f ∘ ([ s true ⊗ id ∣ Δ ]f ∘ [ s true ∣ Δ ]f ∘ [ s true ⊗ id ∣ Δ ]f)
  ≐⟨ refl ∘ ((~ [∘∣ Δ ] _ _) ∘ refl ∙ (~ [∘∣ Δ ] _ _)) ⟩ 
    sound f ∘ [ s true ⊗ id ∘ s true ∘ s true ⊗ id ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] sss ⟩ 
    sound f ∘ [ s true ∘ s true ⊗ id ∘ s true ∣ Δ ]f
  ≐⟨ refl ∘ ([∘∣ Δ ] _ _ ∙ ([∘∣ Δ ] _ _ ∘ refl)) ⟩ 
    sound f ∘ ([ s true ∣ Δ ]f ∘ [ s true ⊗ id ∣ Δ ]f ∘ [ s true ∣ Δ ]f)
  ≐⟨ ~ (ass ∘ refl ∙ ass) ⟩ 
    sound f ∘ [ s true ∣ Δ ]f ∘ [ s true ⊗ id ∣ Δ ]f ∘ [ s true ∣ Δ ]f
  qed≐
eq-sound {g = g} (ex-iso {Δ = Δ} b) =
  proof≐
    sound g ∘ [ s _ ∣ Δ ]f ∘ [ s _ ∣ Δ ]f
  ≐⟨ ass ⟩
    sound g ∘ ([ s _ ∣ Δ ]f ∘ [ s _ ∣ Δ ]f)
  ≐⟨ refl ∘ (~ [∘∣ Δ ] _ _) ⟩
    sound g ∘ [ s _ ∘ s _ ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ refl≐' (cong s (sym (not-involutive b)))) ⟩
    sound g ∘ [ s _ ∘ s (not (not b)) ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (ss (not b)) ⟩
    sound g ∘ [ id ∣ Δ ]f
  ≐⟨ refl ∘ [id∣ Δ ] ⟩
    sound g ∘ id
  ≐⟨ ~ rid ⟩
    sound g
  qed≐
