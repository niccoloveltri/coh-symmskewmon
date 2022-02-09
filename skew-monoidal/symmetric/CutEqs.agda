{-# OPTIONS --rewriting #-}

module CutEqs where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import Fsk
open import SeqCalc

-- cut and exchange

scut-ex-fma-cxt : ∀{S Γ Δ₁ Δ₂} Λ {A' A C}
  → (f : S ∣ Δ₁ ++ A ∷ Λ ++ Δ₂ ⊢ A') (g : just A' ∣ Γ ⊢ C)
  → scut (ex-fma-cxt {Γ = Δ₁}{Δ₂} Λ f) g ≡ ex-fma-cxt {Γ = Δ₁} Λ (scut f g)
scut-ex-fma-cxt [] f g = refl
scut-ex-fma-cxt {Δ₁ = Δ₁} (x ∷ Λ) f g =
  scut-ex-fma-cxt {Δ₁ = Δ₁ ++ x ∷ []} Λ (ex f) g
  
scut-ex-cxt-fma : ∀{S Γ Δ₁ Δ₂} Λ {A' A C}
  → (f : S ∣ Δ₁ ++ Λ ++ A ∷ Δ₂ ⊢ A') (g : just A' ∣ Γ ⊢ C)
  → scut (ex-cxt-fma {Γ = Δ₁}{Δ₂} Λ f) g ≡ ex-cxt-fma {Γ = Δ₁} Λ (scut f g)
scut-ex-cxt-fma [] f g = refl
scut-ex-cxt-fma {Δ₁ = Δ₁} (x ∷ Λ) f g =
  cong ex (scut-ex-cxt-fma {Δ₁ = Δ₁ ++ x ∷ []} Λ f g)

scut-ex : ∀{S Γ Δ₁ Δ₂ A' A B C}
  → (f : S ∣ Γ ⊢ A') {g : just A' ∣ Δ₁ ++ A ∷ B ∷ Δ₂ ⊢ C}
  → scut f (ex g) ≗ ex {Γ = Γ ++ Δ₁} (scut f g)
scut-ex ax = refl
scut-ex {Δ₁ = Δ} (uf {Γ} f) =
  uf (scut-ex f) ∙ ~ exuf {Γ = Γ ++ Δ} 
scut-ex {Δ₁ = Δ} (ex {Δ = Γ} f) =
  ex (scut-ex f) ∙ ~ exex {Γ₂ = Γ ++ Δ} 
scut-ex Ir = refl
scut-ex (⊗r f f') = refl
scut-ex {Γ = Γ} {Δ} (Il f) = 
  Il (scut-ex f) ∙ ~ exIl {Γ = Γ ++ Δ} 
scut-ex {Γ = Γ} {Δ} (⊗l f) =
  ⊗l (scut-ex f) ∙ ~ ex⊗l {Γ = Γ ++ Δ} 

scut-ex-fma-cxt2 : ∀{S Γ Δ₁ Δ₂} Λ {A' A C}
  → (f : S ∣ Γ ⊢ A') (g : just A' ∣ Δ₁ ++ A ∷ Λ ++ Δ₂ ⊢ C)
  → scut f (ex-fma-cxt {Γ = Δ₁}{Δ₂} Λ g) ≗ ex-fma-cxt {Γ = Γ ++ Δ₁} Λ (scut f g)
scut-ex-fma-cxt2 [] f g = refl
scut-ex-fma-cxt2 {Γ = Γ} {Δ₁}{Δ₂} (x ∷ Λ) f g =
  scut-ex-fma-cxt2 {Δ₁ = Δ₁ ++ x ∷ []}{Δ₂} Λ f (ex g)
  ∙ cong-ex-fma-cxt Λ (scut-ex f)

scut-ex-cxt-fma2 : ∀{S Γ Δ₁ Δ₂} Λ {A' A C}
  → (f : S ∣ Γ ⊢ A') (g : just A' ∣ Δ₁ ++ Λ ++ A ∷ Δ₂ ⊢ C)
  → scut f (ex-cxt-fma {Γ = Δ₁} Λ g) ≗ ex-cxt-fma {Γ = Γ ++ Δ₁} Λ (scut f g)
scut-ex-cxt-fma2 [] f g = refl
scut-ex-cxt-fma2 {Γ = Γ}{Δ₁} (x ∷ Λ) f g =
  scut-ex f ∙ ex {Γ = Γ ++ Δ₁} (scut-ex-cxt-fma2 {Δ₁ = Δ₁ ++ _ ∷ []} Λ f g)

scut⊗r-ex-fma-cxt : ∀{S Γ₁ Γ₂ Δ₁ Δ₂} Λ {A' B' A C}
  → (f : S ∣ Γ₁ ⊢ A') (f' : nothing ∣ Γ₂ ⊢ B') (g : just (A' ⊗ B') ∣ Δ₁ ++ A ∷ Λ ++ Δ₂ ⊢ C)
  → scut (⊗r f f') (ex-fma-cxt {Γ = Δ₁}{Δ₂} Λ g) ≡ ex-fma-cxt {Γ = Γ₁ ++ Γ₂ ++ Δ₁} Λ (scut (⊗r f f') g)
scut⊗r-ex-fma-cxt [] f f' g = refl
scut⊗r-ex-fma-cxt {Δ₁ = Δ₁} (x ∷ Λ) f f' g =
  scut⊗r-ex-fma-cxt {Δ₁ = Δ₁ ++ x ∷ []} Λ f f' (ex g)

scut⊗r-ex-cxt-fma : ∀{S Γ₁ Γ₂ Δ₁ Δ₂} Λ {A' B' A C}
  → (f : S ∣ Γ₁ ⊢ A') (f' : nothing ∣ Γ₂ ⊢ B') (g : just (A' ⊗ B') ∣ Δ₁ ++ Λ ++ A ∷ Δ₂ ⊢ C)
  → scut (⊗r f f') (ex-cxt-fma {Γ = Δ₁}{Δ₂} Λ g) ≡ ex-cxt-fma {Γ = Γ₁ ++ Γ₂ ++ Δ₁} Λ (scut (⊗r f f') g)
scut⊗r-ex-cxt-fma [] f f' g = refl
scut⊗r-ex-cxt-fma {Γ₁ = Γ₁}{Γ₂}{Δ₁} (x ∷ Λ) f f' g =
  cong (ex {Γ = Γ₁ ++ Γ₂ ++ Δ₁}) (scut⊗r-ex-cxt-fma {Δ₁ = Δ₁ ++ x ∷ []} Λ f f' g)

ccut-ex : ∀{T Γ₁ Γ₂ Δ} Δ₀ {Δ' A B A' C}
  → (f : nothing ∣ Γ₁ ++ A ∷ B ∷ Γ₂ ⊢ A') (g : T ∣ Δ ⊢ C)
  → (eq : Δ ≡ Δ₀ ++ A' ∷ Δ')
  → ccut Δ₀ (ex f) g eq ≗ ex {Γ = Δ₀ ++ Γ₁} (ccut Δ₀ f g eq)
ccut-ex Δ₀ f ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
ccut-ex Δ₀ f (uf g) eq with cases∷ Δ₀ eq
... | inj₁ (refl , refl , refl) = refl
ccut-ex {Γ₁ = Γ₁} _ f (uf g) eq | inj₂ (Γ₀ , refl , refl) =
  uf (ccut-ex Γ₀ f g refl) ∙ ~ (exuf {Γ₀ ++ Γ₁})
ccut-ex {Γ₁ = Γ₁}{Γ₂} Δ₀ {Δ'} f (ex {Γ = Γ} {Δ} g) eq with cases++2 Δ₀ Γ Δ' Δ eq
... | inj₁ (Γ₀ , refl , refl) =
  ex {Γ = Δ₀ ++ Γ₁ ++ _ ∷ _ ∷ Γ₂ ++ Γ₀} (ccut-ex Δ₀ f g refl)
  ∙ exex {Γ₁ = Δ₀ ++ Γ₁}{Γ₂ ++ Γ₀}
... | inj₂ (inj₁ (Γ₀ , refl , refl)) =
  ex (ccut-ex (Γ ++ _ ∷ _ ∷ Γ₀) f g refl) ∙ ~ exex {Γ₁ = Γ}{Γ₀ ++ Γ₁}
... | inj₂ (inj₂ (inj₁ (refl , refl , refl))) =
  cong-ex-fma-cxt (Γ₁ ++ _ ∷ _ ∷ Γ₂) (ccut-ex (Δ₀ ++ _ ∷ []) f g refl)
  ∙ ex-fma-cxt-ex-braid Γ₁
... | inj₂ (inj₂ (inj₂ (refl , refl , refl))) =
  cong-ex-cxt-fma (Γ₁ ++ _ ∷ _ ∷ Γ₂) (ccut-ex Γ f g refl)
  ∙ ex-cxt-fma-ex-braid Γ₁
ccut-ex Δ₀ f Ir eq = ⊥-elim ([]disj∷ Δ₀ eq)
ccut-ex {Γ₁ = Γ₁} Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g₁) eq with cases++ Δ₀ Γ Δ' Δ eq
... | inj₁ (Γ₀ , refl , refl) =
  ⊗r (ccut-ex Δ₀ f g refl) refl ∙ ~ ex⊗r₁ {Γ₁ = Δ₀ ++ Γ₁}
... | inj₂ (Γ₀ , refl , refl) =
  ⊗r refl (ccut-ex Γ₀ f g₁ refl) ∙ ~ (ex⊗r₂ {Δ₁ = Γ₀ ++ Γ₁})
ccut-ex {Γ₁ = Γ₁} Δ₀ f (Il g) eq =
  Il (ccut-ex Δ₀ f g eq) ∙ ~ exIl {Γ = Δ₀ ++ Γ₁}
ccut-ex {Γ₁ = Γ₁} Δ₀ f (⊗l g) refl = 
  ⊗l (ccut-ex (_ ∷ Δ₀) f g refl) ∙ ~ ex⊗l {Γ = Δ₀ ++ Γ₁}

ccut-ex-fma-cxt1 : ∀{T Γ₁ Γ₂ Δ} Δ₀ Λ {Δ' A A' C}
  → (f : nothing ∣ Γ₁ ++ A ∷ Λ ++ Γ₂ ⊢ A') (g : T ∣ Δ ⊢ C)
  → (eq : Δ ≡ Δ₀ ++ A' ∷ Δ')
  → ccut Δ₀ (ex-fma-cxt Λ f) g eq ≗ ex-fma-cxt {Γ = Δ₀ ++ Γ₁}{Γ₂ ++ Δ'} Λ (ccut Δ₀ f g eq)
ccut-ex-fma-cxt1 Δ₀ [] f g eq = refl
ccut-ex-fma-cxt1 {Γ₁ = Γ₁} {Γ₂} Δ₀ (x ∷ Λ) {Δ'} f g refl =
  ccut-ex-fma-cxt1 {Γ₁ = Γ₁ ++ x ∷ []} Δ₀ Λ (ex f) g refl
  ∙ cong-ex-fma-cxt Λ (ccut-ex Δ₀ f g refl)

ccut-ex-fma-cxt2 : ∀{T Γ} Δ₀ Λ {Δ₁ Δ₂ A A' C}
  → (f : nothing ∣ Γ ⊢ A') (g : T ∣ Δ₀ ++ A' ∷ Δ₁ ++ A ∷ Λ ++ Δ₂ ⊢ C)
  → ccut Δ₀ f (ex-fma-cxt {Γ = Δ₀ ++ A' ∷ Δ₁}{Δ₂} Λ g) refl
    ≡ ex-fma-cxt {Γ = Δ₀ ++ Γ ++ Δ₁} Λ (ccut Δ₀ f g refl)
ccut-ex-fma-cxt2 Δ₀ [] f g = refl
ccut-ex-fma-cxt2 Δ₀ (x ∷ Λ) {Δ₁}{Δ₂} f g with ccut-ex-fma-cxt2 Δ₀ Λ {Δ₁ ++ x ∷ []}{Δ₂} f (ex {Γ = Δ₀ ++ _ ∷ Δ₁}{Λ ++ Δ₂} g)
ccut-ex-fma-cxt2 Δ₀ (x ∷ Λ) {Δ₁} {Δ₂} {A}{A'} f g | ih
  rewrite cases++-inj₁ Δ₀ Δ₁ (x ∷ A ∷ Λ ++ Δ₂) A' = ih

ccut-ex-fma-cxt2' : ∀{T Γ} Δ₀ Λ {Δ₁ Δ₂ A A' C}
  → (f : nothing ∣ Γ ⊢ A') (g : T ∣ Δ₀ ++ A ∷ Λ ++ Δ₁ ++ A' ∷ Δ₂ ⊢ C)
  → ccut (Δ₀ ++ Λ ++ A ∷ Δ₁) f (ex-fma-cxt {Γ = Δ₀}{Δ₁ ++ A' ∷ Δ₂} Λ g) refl
    ≡ ex-fma-cxt {Γ = Δ₀} Λ (ccut (Δ₀ ++ A ∷ Λ ++ Δ₁) f g refl)
ccut-ex-fma-cxt2' Δ₀ [] f g = refl
ccut-ex-fma-cxt2' {Γ = Γ} Δ₀ (x ∷ Λ) {Δ₁} {Δ₂} {A}{A'} f g with ccut-ex-fma-cxt2' {Γ = Γ} (Δ₀ ++ x ∷ []) Λ {Δ₁}{Δ₂} f (ex g)
... | ih rewrite cases++-inj₂ (x ∷ A ∷ Λ ++ Δ₁) Δ₀ Δ₂ A' = ih

ccut-ex-cxt-fma : ∀{T Γ₁ Γ₂ Δ} Δ₀ Λ {Δ' A A' C}
  → (f : nothing ∣ Γ₁ ++ Λ ++ A ∷ Γ₂ ⊢ A') (g : T ∣ Δ ⊢ C)
  → (eq : Δ ≡ Δ₀ ++ A' ∷ Δ')
  → ccut Δ₀ (ex-cxt-fma {Γ = Γ₁} Λ f) g eq ≗ ex-cxt-fma {Γ = Δ₀ ++ Γ₁} Λ (ccut Δ₀ f g eq)
ccut-ex-cxt-fma Δ₀ [] f g eq = refl
ccut-ex-cxt-fma {Γ₁ = Γ₁} {Γ₂} Δ₀ (x ∷ Λ) f g refl =
  ccut-ex Δ₀ (ex-cxt-fma {Γ = Γ₁ ++ _ ∷ []} Λ f) g refl
  ∙ ex {Γ = Δ₀ ++ Γ₁} (ccut-ex-cxt-fma {Γ₁ = Γ₁ ++ x ∷ []} Δ₀ Λ f g refl)

ccut-ex-cxt-fma2 : ∀{T Γ} Δ₀ Λ {Δ₁ Δ₂ A A' C}
  → (f : nothing ∣ Γ ⊢ A') (g : T ∣ Δ₀ ++ A' ∷ Δ₁ ++ Λ ++ A ∷ Δ₂ ⊢ C)
  → ccut Δ₀ f (ex-cxt-fma {Γ = Δ₀ ++ A' ∷ Δ₁}{Δ₂} Λ g) refl
    ≡ ex-cxt-fma {Γ = Δ₀ ++ Γ ++ Δ₁} Λ (ccut Δ₀ f g refl)
ccut-ex-cxt-fma2 Δ₀ [] f g = refl
ccut-ex-cxt-fma2 {Γ = Γ} Δ₀ (x ∷ Λ) {Δ₁} {Δ₂} {A}{A'} f g
  rewrite cases++-inj₁ Δ₀ Δ₁ (A ∷ x ∷ Λ ++ Δ₂) A' =
  cong (ex {Γ = Δ₀ ++ Γ ++ Δ₁}) (ccut-ex-cxt-fma2 Δ₀ Λ {Δ₁ ++ x ∷ []} f g )

ccut-ex-cxt-fma2' : ∀{T Γ} Δ₀ Λ {Δ₁ Δ₂ A A' C}
  → (f : nothing ∣ Γ ⊢ A') (g : T ∣ Δ₀ ++ Λ ++ A ∷ Δ₁ ++ A' ∷ Δ₂ ⊢ C)
  → ccut (Δ₀ ++ A ∷ Λ ++ Δ₁) f (ex-cxt-fma {Γ = Δ₀}{Δ₁ ++ A' ∷ Δ₂} Λ g) refl
    ≡ ex-cxt-fma {Γ = Δ₀}{Δ₁ ++ Γ ++ Δ₂} Λ (ccut (Δ₀ ++ Λ ++ A ∷ Δ₁) f g refl)
ccut-ex-cxt-fma2' Δ₀ [] f g = refl
ccut-ex-cxt-fma2' {Γ = Γ} Δ₀ (x ∷ Λ) {Δ₁} {Δ₂} {A} {A'} f g
  rewrite cases++-inj₂ (A ∷ x ∷ Λ ++ Δ₁) Δ₀ Δ₂ A' =
    cong ex (ccut-ex-cxt-fma2' {Γ = Γ} (Δ₀ ++ x ∷ []) Λ {Δ₁} {Δ₂} f g)

ccut-ex-cxt-cxt2 : ∀{T Γ} Δ₀ Λ {Δ₁ A C}
  → (f : nothing ∣ Γ ⊢ A) (g : T ∣ Δ₀ ++ Λ ++ A ∷ Δ₁ ⊢ C)
  → ccut Δ₀ f (ex-cxt-fma {Γ = Δ₀}{Δ₁} Λ g) refl
    ≡ ex-cxt-cxt1 {Γ = Δ₀} {Δ₁} Λ Γ (ccut (Δ₀ ++ Λ) f g refl) 
ccut-ex-cxt-cxt2 Δ₀ [] f g = refl
ccut-ex-cxt-cxt2 {Γ = Γ} Δ₀ (x ∷ Λ) {Δ₁} {A} f g
  rewrite cases++-inj₂ [] Δ₀ (x ∷ Λ ++ Δ₁) A =
  cong (ex-fma-cxt Γ) (ccut-ex-cxt-cxt2 {Γ = Γ} (Δ₀ ++ x ∷ []) Λ {Δ₁} f g)

ccut-ex-cxt-cxt2' : ∀{T Γ} Δ₀ Λ {Δ₁ A C}
  → (f : nothing ∣ Γ ⊢ A) (g : T ∣ Δ₀ ++ A ∷ Λ ++ Δ₁ ⊢ C)
  → ccut (Δ₀ ++ Λ) f (ex-fma-cxt {Γ = Δ₀}{Δ₁} Λ g) refl
    ≡ ex-cxt-cxt2 {Γ = Δ₀} {Δ₁} Γ Λ (ccut Δ₀ f g refl) 
ccut-ex-cxt-cxt2' Δ₀ [] f g = refl
ccut-ex-cxt-cxt2' {Γ = Γ} Δ₀ (x ∷ Λ) {Δ₁} {A} f g with ccut-ex-cxt-cxt2' {Γ = Γ} (Δ₀ ++ x ∷ []) Λ {Δ₁} f (ex g)
... | ih rewrite cases++-inj₂ (x ∷ []) Δ₀ (Λ ++ Δ₁) A = ih

-- ====================================================================

-- unitality of identity wrt. cut

ccut-unit : {T : Stp}{Γ Δ : Cxt}(Δ₀ : Cxt){A C : Fma}
  → (g : T ∣ Δ ⊢ C)(r : Δ ≡ Δ₀ ++ A ∷ Γ)
  → ccut Δ₀ (uf ax) g r ≡ subst-cxt r g 
ccut-unit Δ₀ ax r = ⊥-elim ([]disj∷ Δ₀ r)
ccut-unit Δ₀ (uf g) r with cases∷ Δ₀ r
ccut-unit .[] (uf g) refl | inj₁ (refl , refl , refl) = refl
ccut-unit .(_ ∷ Γ) (uf g) refl | inj₂ (Γ , refl , refl) = cong uf (ccut-unit Γ g refl)
ccut-unit Δ₀ Ir r = ⊥-elim ([]disj∷ Δ₀ r)
ccut-unit {_}{Γ} Δ₀ (⊗r {Γ = Γ'}{Δ} g g') r with cases++ Δ₀ Γ' Γ Δ r
ccut-unit Δ₀ (⊗r {Γ = Γ}{Δ} g g') refl | inj₁ (Γ₀ , refl , refl) = 
  cong₂ (⊗r {Γ = Γ}{Δ}) (ccut-unit Δ₀ g refl) refl
ccut-unit ._ (⊗r {Γ = Γ}{Δ} g g') refl | inj₂ (Δ₀ , refl , refl) =
  cong₂ (⊗r {Γ = Γ}) refl (ccut-unit Δ₀ g' refl)
ccut-unit Δ₀ (Il g) refl = cong Il (ccut-unit Δ₀ g refl)
ccut-unit Δ₀ (⊗l g) refl = cong ⊗l (ccut-unit (_ ∷ Δ₀) g refl)
ccut-unit {Γ = Γ} Δ₀ (ex {Γ = Γ₁} {Δ} g) eq with cases++2 Δ₀ Γ₁ Γ Δ eq
ccut-unit Δ₀ (ex g) refl | inj₁ (Γ₀ , refl , refl) =
  cong (ex {Γ = Δ₀ ++ _ ∷ Γ₀}) (ccut-unit Δ₀ g refl)
ccut-unit _ (ex {Γ = Γ₁} g) refl | inj₂ (inj₁ (Γ₀ , refl , refl)) =
  cong ex (ccut-unit (Γ₁ ++ _ ∷ _ ∷ Γ₀) g refl)
ccut-unit Δ₀ (ex g) refl | inj₂ (inj₂ (inj₁ (refl , refl , refl))) =
  cong ex (ccut-unit (Δ₀ ++ _ ∷ []) g refl)
ccut-unit _ (ex {Γ = Γ} g) refl | inj₂ (inj₂ (inj₂ (refl , refl , refl))) =
  cong ex (ccut-unit Γ g refl)

scut-unit : {S : Stp}{Γ : Cxt}{A : Fma}(f : S ∣ Γ ⊢ A) → scut f ax ≡ f
scut-unit ax = refl
scut-unit (uf f) = cong uf (scut-unit f)
scut-unit Ir = refl
scut-unit (⊗r f f') = refl
scut-unit (Il f) = cong Il (scut-unit f)
scut-unit (⊗l f) = cong ⊗l (scut-unit f)
scut-unit (ex f) = cong ex (scut-unit f)

Il-1-scutIr : {Γ : Cxt} → {C : Fma}
  → (f : just I ∣ Γ ⊢ C)
  → Il-1 f ≡ scut Ir f
Il-1-scutIr ax = refl
Il-1-scutIr (ex f) = cong ex (Il-1-scutIr f)
Il-1-scutIr (⊗r {Γ = Γ}{Δ} f f₁) = cong₂ (⊗r {Γ = Γ}{Δ}) (Il-1-scutIr f) refl
Il-1-scutIr (Il f) = refl

⊗l-1-scut⊗r : {Γ : Cxt} → {A B C : Fma}
  → (f : just (A ⊗ B) ∣ Γ ⊢ C)
  → ⊗l-1 f ≡ scut (⊗r ax (uf ax)) f
⊗l-1-scut⊗r ax = refl
⊗l-1-scut⊗r (⊗r {Γ = Γ} {Δ} f f₁) = cong₂ (⊗r {Γ = _ ∷ Γ}{Δ}) (⊗l-1-scut⊗r f) refl
⊗l-1-scut⊗r (⊗l f) = sym (ccut-unit [] f refl) 
⊗l-1-scut⊗r (ex {Γ = Γ} f) = cong (ex {Γ = _ ∷ Γ}) (⊗l-1-scut⊗r f)

-- an alternative representation of ⊗l-1

⊗l-1-alt : {Γ : Cxt}{A B C : Fma}(f : just (A ⊗ B) ∣ Γ ⊢ C)
  → ⊗l-1 f ≡ scut (⊗r ax (uf ax)) f
⊗l-1-alt ax = refl
⊗l-1-alt (⊗r {Γ = Γ}{Δ} f f') = cong₂ (⊗r {Γ = _ ∷ Γ}{Δ}) (⊗l-1-alt f) refl
⊗l-1-alt (⊗l f) = sym (ccut-unit [] f refl)
⊗l-1-alt (ex {Γ = Γ} f) = cong (ex {Γ = _ ∷ Γ}) (⊗l-1-alt f)

-- ====================================================================

-- the cut rules commute with Il-1 and ⊗-1

scutIl-1 : {Γ Δ : Cxt} → {A C : Fma}
  → (f : just I ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ C)
  → Il-1 (scut f g) ≡ scut (Il-1 f) g
scutIl-1 ax g = Il-1-scutIr g
scutIl-1 (⊗r f f') ax = refl
scutIl-1 (⊗r {Γ = Γ} {Δ} f f') (⊗r {Γ = Γ₁} {Δ₁} g g') =
  cong₂ (⊗r {Γ = Γ ++ Δ ++ Γ₁}{Δ₁}) (scutIl-1 (⊗r f f') g) refl
scutIl-1 (⊗r {Γ = Γ} f f') (⊗l g) = scutIl-1 f (ccut [] f' g refl)
scutIl-1 (⊗r {Γ = Γ} {Δ} f f') (ex {Γ = Γ₁} g) =
  cong (ex {Γ = Γ ++ Δ ++ Γ₁}) (scutIl-1 (⊗r f f') g)
scutIl-1 (Il f) g = refl
scutIl-1 (ex f) g = cong ex (scutIl-1 f g)

ccutIl-1 : ∀{Γ}{Δ}{A}{C} Δ₀ {Δ'}
  → (f : nothing ∣ Γ ⊢ A)(g : just I ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
  → Il-1 (ccut Δ₀ f g r) ≡ ccut Δ₀ f (Il-1 g) r
ccutIl-1 Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
ccutIl-1 {Γ} Δ₀ {Δ'} f (⊗r {Γ = Γ'}{Δ} g g') r with cases++ Δ₀ Γ' Δ' Δ r
ccutIl-1 {Γ} Δ₀ {_} f (⊗r {Γ = _} {Δ} g g') r | inj₁ (Γ₀ , refl , refl) = 
  cong₂ (⊗r {Γ = Δ₀ ++ Γ ++ Γ₀}{Δ}) (ccutIl-1 Δ₀  f g refl) refl
ccutIl-1 ._ f (⊗r g g') r | inj₂ (Γ₀ , refl , refl) = refl
ccutIl-1 Δ₀ f (Il g) r = refl
ccutIl-1 Δ₀ {Δ'} f (ex {Γ = Γ} {Δ} g) r with cases++2 Δ₀ Γ Δ' Δ r
ccutIl-1 {Γ} Δ₀ {.(Γ₀ ++ _ ∷ _ ∷ Δ)} f (ex {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g) r | inj₁ (Γ₀ , refl , refl) =
  cong (ex {Γ = Δ₀ ++ Γ ++ Γ₀}) (ccutIl-1 Δ₀ f g refl)
... | inj₂ (inj₁ (Γ₀ , refl , refl)) = cong ex (ccutIl-1 (Γ ++ _ ∷ _ ∷ Γ₀) f g refl)
ccutIl-1 {Γ} Δ₀ {.(_ ∷ Δ)} f (ex {Γ = .Δ₀} {Δ} g) r | inj₂ (inj₂ (inj₁ (refl , refl , refl))) =
  trans (sym (ex-fma-cxt-Il-1 Δ₀ Γ))
        (cong (ex-fma-cxt Γ) (ccutIl-1 (Δ₀ ++ _ ∷ []) f g refl))
ccutIl-1 {Γ₁} .(Γ ++ _ ∷ []) {Δ'} f (ex {Γ = Γ} {.Δ'} g) r | inj₂ (inj₂ (inj₂ (refl , refl , refl))) =
  trans (sym (ex-cxt-fma-Il-1 Γ Γ₁))
        (cong (ex-cxt-fma Γ₁) (ccutIl-1 Γ f g refl))

scut⊗l-1 : {Γ Δ : Cxt} → {A B C D : Fma}
  → (f : just (A ⊗ B) ∣ Γ ⊢ C)(g : just C ∣ Δ ⊢ D)
  → ⊗l-1 (scut f g) ≡ scut (⊗l-1 f) g
scut⊗l-1 ax g = ⊗l-1-alt g
scut⊗l-1 (⊗r f f') ax = refl
scut⊗l-1 (⊗r {Γ = Γ} {Δ} f f') (⊗r {Γ = Γ₁} {Δ₁} g g') = 
  cong₂ (⊗r {Γ = _ ∷ Γ ++ Δ ++ Γ₁}{Δ₁}) (scut⊗l-1 (⊗r f f') g) refl
scut⊗l-1 {B = B} (⊗r {Γ = Γ} f f') (⊗l g) = scut⊗l-1 f (ccut [] f' g refl)
scut⊗l-1 (⊗r {Γ = Γ} {Δ} f f') (ex {Γ = Γ'} g) =
  cong (ex {Γ = _ ∷ Γ ++ Δ ++ Γ'}) (scut⊗l-1 (⊗r f f') g)
scut⊗l-1 (⊗l f) g = refl
scut⊗l-1 (ex {Γ = Γ} f) g = cong (ex {Γ = _ ∷ Γ}) (scut⊗l-1 f g)

-- some lemmata about scut and ⊗r

scut⊗ruf : {Γ Δ Δ' : Cxt}{A A' B C : Fma}
  → {f : just A' ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
  → (f' : just (A ⊗ B) ∣ Δ' ⊢ C)
  → scut (⊗r (uf f) g) f' ≗ uf (scut (⊗r f g) f')
scut⊗ruf ax = ⊗ruf
scut⊗ruf {f = f}{g} (⊗r h h') =
  proof≗
  ⊗r (scut (⊗r (uf f) g) h) h'
  ≗〈 ⊗r (scut⊗ruf h) refl 〉
  ⊗r (uf (scut (⊗r f g) h)) h'
  ≗〈 ⊗ruf 〉
  uf (⊗r (scut (⊗r f g) h) h')
  qed≗
scut⊗ruf (⊗l h) = refl
scut⊗ruf {Γ} {Δ} {f = f} {g} (ex {Γ = Λ} h) =
  proof≗
    ex (scut (⊗r (uf f) g) h)
  ≗〈 ex (scut⊗ruf h) 〉
    ex (uf (scut (⊗r f g) h))
  ≗〈 exuf {Γ = Γ ++ Δ ++ Λ} 〉
    uf (ex {Γ = Γ ++ Δ ++ Λ} (scut (⊗r f g) h))
  qed≗

scut⊗rIl : {Γ Δ Δ' : Cxt}{A B C : Fma}
  → {f : nothing ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
  → (h : just (A ⊗ B) ∣ Δ' ⊢ C)
  → scut (⊗r (Il f) g) h ≗ Il (scut (⊗r f g) h)
scut⊗rIl ax = ⊗rIl
scut⊗rIl {f = f}{g}(⊗r h h') =
  proof≗
  ⊗r (scut (⊗r (Il f) g) h) h'
  ≗〈 ⊗r (scut⊗rIl h) refl 〉
  ⊗r (Il (scut (⊗r f g) h)) h'
  ≗〈 ⊗rIl 〉
  Il (⊗r (scut (⊗r f g) h) h')
  qed≗
scut⊗rIl (⊗l h) = refl
scut⊗rIl {Γ} {Δ} {f = f} {g} (ex {Γ = Λ} h) = 
  proof≗
    ex {Γ = Γ ++ Δ ++ Λ} (scut (⊗r (Il f) g) h)
  ≗〈 ex {Γ = Γ ++ Δ ++ Λ} (scut⊗rIl h) 〉
    ex {Γ = Γ ++ Δ ++ Λ} (Il (scut (⊗r f g) h))
  ≗〈 exIl {Γ = Γ ++ Δ ++ Λ} 〉
    Il (ex {Γ = Γ ++ Δ ++ Λ} (scut (⊗r f g) h))
  qed≗

scut⊗r⊗l : {Γ Δ Δ' : Cxt}{A A' B B' C : Fma}
  → {f : just A' ∣ B' ∷ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
  → (h : just (A ⊗ B) ∣ Δ' ⊢ C)
  → scut (⊗r (⊗l f) g) h ≗ ⊗l (scut (⊗r f g) h)
scut⊗r⊗l ax = ⊗r⊗l
scut⊗r⊗l {f = f}{g} (⊗r h h') =
  proof≗
  ⊗r (scut (⊗r (⊗l f) g) h) h'
  ≗〈 ⊗r (scut⊗r⊗l h) refl 〉
  ⊗r (⊗l (scut (⊗r f g) h)) h'
  ≗〈 ⊗r⊗l 〉
  ⊗l (⊗r (scut (⊗r f g) h) h')
  qed≗
scut⊗r⊗l (⊗l h) = refl
scut⊗r⊗l {Γ} {Δ} {f = f} {g} (ex {Γ = Λ} h) = 
  proof≗
    ex {Γ = Γ ++ Δ ++ Λ} (scut (⊗r (⊗l f) g) h)
  ≗〈 ex {Γ = Γ ++ Δ ++ Λ} (scut⊗r⊗l h) 〉
    ex {Γ = Γ ++ Δ ++ Λ} (⊗l (scut (⊗r f g) h))
  ≗〈 ex⊗l {Γ = Γ ++ Δ ++ Λ} 〉
    ⊗l (ex {Γ = _ ∷ Γ ++ Δ ++ Λ} (scut (⊗r f g) h))
  qed≗

scut⊗r : ∀{S}{Γ}{Δ}{Δ'}{A}{B}{C}
  → (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(g' : nothing ∣ Δ' ⊢ C)
  → scut f (⊗r g g') ≗ ⊗r (scut f g) g'
scut⊗r ax g g' = refl
scut⊗r (uf f) g g' =
  proof≗
  uf (scut f (⊗r g g'))
  ≗〈 uf (scut⊗r f g g') 〉 
  uf (⊗r (scut f g) g')
  ≗〈 ~ ⊗ruf 〉 
  ⊗r (uf (scut f g)) g'
  qed≗
scut⊗r Ir g g' = refl
scut⊗r (⊗r f f') g g' = refl
scut⊗r (Il f) g g' =
  proof≗
  Il (scut f (⊗r g g'))
  ≗〈 Il (scut⊗r f g g') 〉 
  Il (⊗r (scut f g) g')
  ≗〈 ~ ⊗rIl 〉 
  ⊗r (Il (scut f g)) g'
  qed≗
scut⊗r (⊗l f) g g' =
  proof≗
  ⊗l (scut f (⊗r g g'))
  ≗〈 ⊗l (scut⊗r f g g') 〉 
  ⊗l (⊗r (scut f g) g')
  ≗〈 ~ ⊗r⊗l 〉 
  ⊗r (⊗l (scut f g)) g'
  qed≗
scut⊗r (ex {Γ = Γ} f) g g' =
  proof≗
    ex (scut f (⊗r g g'))
  ≗〈 ex (scut⊗r f g g') 〉
    ex (⊗r (scut f g) g')
  ≗〈 ex⊗r₁ 〉
    ⊗r (ex (scut f g)) g'
  qed≗

-- ====================================================================

-- parallel cuts commute and cut is a congruence (all proved
-- simultaneously)

cong-scut⊗r : ∀{S}{Γ}{Δ}{Δ'}{A}{B}{C}
  → {f g : S ∣ Γ ⊢ A}{f' g' : nothing ∣ Δ ⊢ B}
  → (h : just (A ⊗ B) ∣ Δ' ⊢ C)
  → (p : f ≗ g)(q : f' ≗ g')
  → scut (⊗r f f') h ≗ scut (⊗r g g') h
cong-scut1 : {S : Stp} → {Γ Δ' : Cxt} → {A C : Fma} → 
           {f g : S ∣ Γ ⊢ A}  → {h : just A ∣ Δ' ⊢ C} →
           f ≗ g → scut f h ≗ scut g h
cong-scut2 : {S : Stp} → {Γ Δ' : Cxt} → {A C : Fma} → 
           (h : S ∣ Γ ⊢ A)  → {f g : just A ∣ Δ' ⊢ C} →
           f ≗ g → scut h f ≗ scut h g
cong-ccut1 : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} →  {A C : Fma} → 
           {f f' : nothing ∣ Γ ⊢ A}(g : T ∣ Δ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
           f ≗ f' → ccut Δ₀ f g r ≗ ccut Δ₀ f' g r
cong-ccut2 : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} →  {A C : Fma} → 
           {f : nothing ∣ Γ ⊢ A}{g g' : T ∣ Δ ⊢ C}  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
           g ≗ g' → ccut Δ₀ f g r ≗ ccut Δ₀ f g' r
scut⊗r-hass : {T : Stp}{Γ₁ Γ₁' Γ₂ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A₁ A₁' A₂ C : Fma}
  → (f₁ : T ∣ Γ₁ ⊢ A₁)(f₁' : nothing ∣ Γ₁' ⊢ A₁')(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : just (A₁ ⊗ A₁') ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A₂ ∷ Δ')
  → scut (⊗r f₁ f₁') (ccut Δ₀ f₂ g r) ≗ ccut (Γ₁ ++ Γ₁' ++ Δ₀) f₂ (scut (⊗r f₁ f₁') g) (cong (_++_ (Γ₁ ++ Γ₁')) r)
scut-hass : {T : Stp}{Γ₁ Γ₂ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A₁ A₂ C : Fma}
  → (f₁ : T ∣ Γ₁ ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : just A₁ ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A₂ ∷ Δ')
  → scut f₁ (ccut Δ₀ f₂ g r) ≗ ccut (Γ₁ ++ Δ₀) f₂ (scut f₁ g) (cong (_++_ Γ₁) r)
ccut-hass : {T : Stp} → {Γ₁ Γ₂ : Cxt} → (Δ₀ : Cxt) → {Δ Δ₁ Δ₂ : Cxt} → {A₁ A₂ C : Fma}
  → (f₁ : nothing ∣ Γ₁ ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : T ∣ Δ ⊢ C)
  → (r : Δ ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
  → ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) refl ≗ ccut (Δ₀ ++ Γ₁ ++ Δ₁) f₂ (ccut Δ₀ f₁ g r) refl

scut⊗r-hass Δ₀ f₁ f₁' f₂ ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
scut⊗r-hass {Γ₁ = Γ} {Δ} Δ₀ {Δ'} {A₁} {A₂ = A₂} f₁ f₁' f₂ (ex {Γ = Γ₁} {Δ₁} {A} {B} g) eq with cases++2 Δ₀ Γ₁ Δ' Δ₁ eq
scut⊗r-hass {Γ₁ = Γ} {Δ} {Γ₂ = Γ₂} Δ₀ {A₂ = A₂} f₁ f₁' f₂ (ex {Γ = _} {Δ₁} {A} {B} g) refl | inj₁ (Γ₀ , refl , refl)
   rewrite cases++-inj₁ (Γ ++ Δ ++ Δ₀) Γ₀ (B ∷ A ∷ Δ₁) A₂ =
   ex {Γ = Γ ++ Δ ++ Δ₀ ++ Γ₂ ++ Γ₀} (scut⊗r-hass Δ₀ f₁ f₁' f₂ g refl)
scut⊗r-hass {Γ₁ = Γ} {Δ} ._ {Δ'} {A₂ = A₂} f₁ f₁' f₂ (ex {Γ = Γ₁} {.(Γ₀ ++ _ ∷ Δ')} {A} {B} g) refl | inj₂ (inj₁ (Γ₀ , refl , refl))
   rewrite cases++-inj₂ (B ∷ A ∷ Γ₀) (Γ ++ Δ ++ Γ₁) Δ' A₂ = 
   ex {Γ = Γ ++ Δ ++ Γ₁} (scut⊗r-hass (Γ₁ ++ _ ∷ _ ∷ Γ₀) f₁ f₁' f₂ g refl)
scut⊗r-hass {Γ₁ = Γ} {Δ} {Γ₂} Δ₀ {A₂ = A₂} f₁ f₁' f₂ (ex {Γ = Δ₀} {Δ₁} {A} g) refl | inj₂ (inj₂ (inj₁ (refl , refl , refl)))
   rewrite cases++-inj₂ [] (Γ ++ Δ ++ Δ₀) (A ∷ Δ₁) A₂ =
   ≡-to-≗ (scut⊗r-ex-fma-cxt Γ₂ f₁ f₁' (ccut (Δ₀ ++ _ ∷ []) f₂ g refl))
   ∙ cong-ex-fma-cxt Γ₂ (scut⊗r-hass (Δ₀ ++ _ ∷ []) f₁ f₁' f₂ g refl)
scut⊗r-hass {Γ₁ = Γ} {Δ} {Γ₂} _ {Δ'} {A₂ = A₂} f₁ f₁' f₂ (ex {Γ = Γ₁} {Δ'} {B = B} g) refl | inj₂ (inj₂ (inj₂ (refl , refl , refl)))
   rewrite cases++-inj₂ (B ∷ []) (Γ ++ Δ ++ Γ₁) Δ' A₂ =
   ≡-to-≗ (scut⊗r-ex-cxt-fma Γ₂ f₁ f₁' (ccut Γ₁ f₂ g refl))
   ∙ cong-ex-cxt-fma {Γ = Γ ++ Δ ++ Γ₁} Γ₂ (scut⊗r-hass Γ₁ f₁ f₁' f₂ g refl)
scut⊗r-hass Δ₀ {Δ'} f₁ f₁' f₂ (⊗r {Γ = Γ} {Δ} g g₁) eq with cases++ Δ₀ Γ Δ' Δ eq
scut⊗r-hass {Γ₁ = Γ₁} {Γ₁'}{Γ₂} Δ₀ {.(Γ₀ ++ Δ)} {A₂ = A₂} {_ ⊗ _} f₁ f₁' f₂ (⊗r {Γ = .(Δ₀ ++ A₂ ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ Γ₁' ++ Δ₀) Γ₀ Δ A₂ =
  ⊗r {Γ = Γ₁ ++ Γ₁' ++ Δ₀ ++ Γ₂ ++ Γ₀}{Δ} (scut⊗r-hass Δ₀ f₁ f₁' f₂ g refl) refl
scut⊗r-hass {Γ₁ = Γ₁} {Γ₁'} .(Γ ++ Γ₀) {Δ'} {A₂ = A₂} {_ ⊗ _} f₁ f₁' f₂ (⊗r {Γ = Γ} {.(Γ₀ ++ A₂ ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ (Γ₁ ++ Γ₁' ++ Γ) Δ' A₂ = refl
scut⊗r-hass {Γ₁ = Γ} {Δ} Δ₀ {A₁' = B} f₁ f₁' f₂ (⊗l g) refl = 
  proof≗
  scut f₁ (ccut [] f₁' (ccut (B ∷ Δ₀) f₂ g refl) refl)
  ≗〈 cong-scut2 f₁ (ccut-hass [] f₁' f₂ g refl) 〉
  scut f₁ (ccut (Δ ++ Δ₀) f₂ (ccut [] f₁' g refl) refl)
  ≗〈 scut-hass (Δ ++ Δ₀) f₁ f₂ (ccut [] f₁' g refl) refl 〉
   ccut (Γ ++ Δ ++ Δ₀) f₂ (scut f₁ (ccut [] f₁' g refl)) refl
  qed≗

scut-hass Δ₀ ax f₂ g refl = refl
scut-hass Δ₀ (uf f₁) f₂ g refl = uf (scut-hass Δ₀ f₁ f₂ g refl)
scut-hass Δ₀ Ir f₂ g refl = ≡-to-≗ 
  (begin
  scut Ir (ccut Δ₀ f₂ g refl)
  ≡⟨ sym (Il-1-scutIr (ccut Δ₀ f₂ g refl)) ⟩
  Il-1 (ccut Δ₀ f₂ g refl)
  ≡⟨ ccutIl-1 Δ₀ f₂ g refl ⟩
  ccut Δ₀ f₂ (Il-1 g) refl
  ≡⟨ cong (λ x → ccut Δ₀ f₂ x refl) (Il-1-scutIr g) ⟩ 
  ccut Δ₀ f₂ (scut Ir g) refl
  ∎)
scut-hass Δ₀ (⊗r f₁ f₃) f₂ g r = scut⊗r-hass Δ₀ f₁ f₃ f₂ g r  
scut-hass Δ₀ {Δ'} {A₂ = A₂} (ex {Γ = Γ} {Δ} {A} {B} f₁) f₂ g refl
  rewrite cases++-inj₂ (B ∷ A ∷ Δ ++ Δ₀) Γ Δ' A₂ = ex (scut-hass Δ₀ f₁ f₂ g refl)
scut-hass Δ₀ (Il f₁) f₂ g refl = Il (scut-hass Δ₀ f₁ f₂ g refl)
scut-hass Δ₀ (⊗l f₁) f₂ g refl = ⊗l (scut-hass Δ₀ f₁ f₂ g refl)
 
ccut-hass Δ₀ f₁ f₂ ax r = ⊥-elim ([]disj∷ Δ₀ r)
ccut-hass {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (ex {Γ = Γ} {Δ} {A} {B} g) r with cases++2 (Δ₀ ++ A₁ ∷ Δ₁) Γ Δ₂ Δ r
ccut-hass {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {.(Γ₀ ++ B ∷ A ∷ Δ)} {A₁} {A₂} f₁ f₂ (ex {Γ = .(Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Γ₀)} {Δ} {A} {B} g) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ (Δ₁ ++ A₂ ∷ Γ₀) (B ∷ A ∷ Δ) A₁ |
          cases++-inj₁ Δ₀ (Δ₁ ++ Γ₂ ++ Γ₀) (B ∷ A ∷ Δ) A₁ |
          cases++-inj₁ (Δ₀ ++ Γ₁ ++ Δ₁) Γ₀ (B ∷ A ∷ Δ) A₂ =
          ex {Γ = Δ₀ ++ Γ₁ ++ Δ₁ ++ Γ₂ ++ Γ₀} (ccut-hass Δ₀ f₁ f₂ g refl)
ccut-hass {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {.(A ∷ Δ)} {A₁} {A₂} f₁ f₂ (ex {Γ = .(Δ₀ ++ A₁ ∷ Δ₁)} {Δ} {A} {.A₂} g) refl | inj₂ (inj₂ (inj₁ (refl , refl , refl)))
  rewrite cases++-inj₁ Δ₀ Δ₁ (A₂ ∷ A ∷ Δ) A₁ |
          cases++-inj₂ [] (Δ₀ ++ Γ₁ ++ Δ₁) (A ∷ Δ) A₂ =
          ≡-to-≗ (ccut-ex-fma-cxt2 Δ₀ Γ₂ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁ ++ A ∷ []) f₂ g refl))
          ∙ cong-ex-fma-cxt Γ₂ (ccut-hass Δ₀ {Δ₁ = Δ₁ ++ _ ∷ []} f₁ f₂ g refl)
... | inj₂ (inj₁ (Γ₀ , refl , q)) with cases++2 Δ₀ Γ Δ₁ Γ₀ (sym q)
ccut-hass {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = .(Γ₀' ++ B ∷ A ∷ Γ₀)} {Δ₂} {A₁} {A₂} f₁ f₂ (ex {Γ = .(Δ₀ ++ A₁ ∷ Γ₀')} {.(Γ₀ ++ A₂ ∷ Δ₂)} {A} {B} g) refl | inj₂ (inj₁ (Γ₀ , refl , refl)) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀' (B ∷ A ∷ Γ₀ ++ A₂ ∷ Δ₂) A₁ |
          cases++-inj₁ Δ₀ Γ₀' (B ∷ A ∷ Γ₀ ++ Γ₂ ++ Δ₂) A₁ |
          cases++-inj₂ (B ∷ A ∷ Γ₀) (Δ₀ ++ Γ₁ ++ Γ₀') Δ₂ A₂ =
          ex {Γ = Δ₀ ++ Γ₁ ++ Γ₀'} (ccut-hass Δ₀ {Δ₁ = Γ₀' ++ _ ∷ _ ∷ Γ₀} f₁ f₂ g refl)
ccut-hass {Γ₁ = Γ₁} {Γ₂} .(Γ ++ B ∷ A ∷ Γ₀') {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (ex {Γ = Γ} {.((Γ₀' ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)} {A} {B} g) refl | inj₂ (inj₁ (.(Γ₀' ++ A₁ ∷ Δ₁) , refl , refl)) | inj₂ (inj₁ (Γ₀' , refl , refl))
  rewrite cases++-inj₂ (B ∷ A ∷ Γ₀') Γ (Δ₁ ++ A₂ ∷ Δ₂) A₁ |
          cases++-inj₂ (B ∷ A ∷ Γ₀') Γ (Δ₁ ++ Γ₂ ++ Δ₂) A₁ |
          cases++-inj₂ (B ∷ A ∷ Γ₀' ++ Γ₁ ++ Δ₁) Γ Δ₂ A₂ =
          ex (ccut-hass (Γ ++ _ ∷ _ ∷ Γ₀') f₁ f₂ g refl)
ccut-hass {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = .(A ∷ Γ₀)} {Δ₂} {A₁} {A₂} f₁ f₂ (ex {Γ = .Δ₀} {.(Γ₀ ++ A₂ ∷ Δ₂)} {A} {.A₁} g) refl | inj₂ (inj₁ (Γ₀ , refl , refl)) | inj₂ (inj₂ (inj₁ (refl , refl , refl)))
  rewrite cases++-inj₂ [] Δ₀ (A ∷ Γ₀ ++ A₂ ∷ Δ₂) A₁ |
          cases++-inj₂ [] Δ₀ (A ∷ Γ₀ ++ Γ₂ ++ Δ₂) A₁ =
          cong-ex-fma-cxt Γ₁ (ccut-hass (Δ₀ ++ _ ∷ []) f₁ f₂ g refl)
          ∙ ~ (≡-to-≗ (ccut-ex-fma-cxt2' Δ₀ Γ₁ f₂ (ccut (Δ₀ ++ A ∷ []) f₁ g refl)))
ccut-hass {Γ₁ = Γ₁} {Γ₂} .(Γ ++ B ∷ []) {Δ₁ = .Γ₀} {Δ₂} {A₁} {A₂} f₁ f₂ (ex {Γ = Γ} {.(Γ₀ ++ A₂ ∷ Δ₂)} {.A₁} {B} g) refl | inj₂ (inj₁ (Γ₀ , refl , refl)) | inj₂ (inj₂ (inj₂ (refl , refl , refl)))
  rewrite cases++-inj₂ (B ∷ []) Γ (Γ₀ ++ A₂ ∷ Δ₂) A₁ |
          cases++-inj₂ (B ∷ []) Γ (Γ₀ ++ Γ₂ ++ Δ₂) A₁ =
          cong-ex-cxt-fma Γ₁ (ccut-hass Γ f₁ f₂ g refl)
          ∙ ~ (≡-to-≗ (ccut-ex-cxt-fma2' Γ Γ₁ f₂ (ccut Γ f₁ g refl)))
ccut-hass {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (ex {Γ = Γ} {.Δ₂} {.A₂} {B} g) r | inj₂ (inj₂ (inj₂ (refl , refl , q))) with cases++ Γ Δ₀ [] (_ ∷ Δ₁) q
... | inj₁ (Γ₀ , p , p') = ⊥-elim ([]disj∷ Γ₀ p')
ccut-hass {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = .[]} {Δ₂} {A₁} {A₂} f₁ f₂ (ex {Γ = .(Δ₀ ++ [])} {Δ₂} {A₂} {.A₁} g) refl | inj₂ (inj₂ (inj₂ (refl , refl , refl))) | inj₂ ([] , refl , refl)
  rewrite cases++-inj₂ [] Δ₀ (A₂ ∷ Δ₂) A₁ =
  ≡-to-≗ (ccut-ex-cxt-cxt2 Δ₀ Γ₂ f₁ (ccut Δ₀ f₂ g refl))
  ∙ ex-cxt-cxt≗ Γ₂ Γ₁ _
  ∙ cong-ex-cxt-cxt2 Γ₂ Γ₁ (~ (ccut-hass Δ₀ f₂ f₁ g refl))
  ∙ ~ (≡-to-≗ (ccut-ex-cxt-cxt2' Δ₀ Γ₁ f₂ (ccut (Δ₀ ++ A₂ ∷ []) f₁ g refl)))
ccut-hass {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = .(Γ₀ ++ B ∷ [])} {Δ₂} {.x} {A₂} f₁ f₂ (ex {Γ = .(Δ₀ ++ x ∷ Γ₀)} {Δ₂} {A₂} {B} g) refl | inj₂ (inj₂ (inj₂ (refl , refl , refl))) | inj₂ (x ∷ Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀ (B ∷ A₂ ∷ Δ₂) x | cases++-inj₂ (B ∷ []) (Δ₀ ++ Γ₁ ++ Γ₀) Δ₂ A₂ =
  ≡-to-≗ (ccut-ex-cxt-fma2 Δ₀ Γ₂ f₁ (ccut (Δ₀ ++ x ∷ Γ₀) f₂ g refl))
  ∙ cong-ex-cxt-fma {Γ = Δ₀ ++ Γ₁ ++ Γ₀} Γ₂ (ccut-hass Δ₀ f₁ f₂ g refl)
ccut-hass Δ₀ {_}{Δ₁}{_}{A₁} f₁ f₂ (uf g) r with cases∷ (Δ₀ ++ A₁ ∷ Δ₁) r
ccut-hass Δ₀ f₁ f₂ (uf g) r | inj₁ (p , q , _) = ⊥-elim ([]disj∷ Δ₀ (sym q))
ccut-hass Δ₀ f₁ f₂ (uf g) r | inj₂ (Γ₀ , refl , _) with cases∷ Δ₀ r
ccut-hass .[] f₁ f₂ (uf g) r | inj₂ (Γ₀ , refl , refl) | inj₁ (refl , refl , refl) = scut-hass Γ₀ f₁ f₂ g refl
ccut-hass .(_ ∷ Δ₀) f₁ f₂ (uf g) r | inj₂ (._ , refl , refl) | inj₂ (Δ₀ , refl , refl) = uf (ccut-hass Δ₀ f₁ f₂ g refl)
ccut-hass Δ₀ f₁ f₂ Ir r = ⊥-elim ([]disj∷ Δ₀ r)
ccut-hass Δ₀ {_}{Δ₁}{Δ₂}{A₁}{A₂} f₁ f₂ (⊗r {Γ = Γ}{Δ} g g') r with cases++ (Δ₀ ++ A₁ ∷ Δ₁) Γ Δ₂ Δ r | cases++ Δ₀ Γ (Δ₁ ++ A₂ ∷ Δ₂) Δ r
ccut-hass Δ₀ {Δ₁ = Δ₁} {A₂ = A₂} f₁ f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p' , q') with canc++ (Δ₁ ++ A₂ ∷ Γ₀) Γ₀' {Δ} q'
ccut-hass {_}{Γ₁}{Γ₂} Δ₀ {_}{Δ₁}{_}{A₁}{A₂} f₁ f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl
  with cases++ Δ₀ (Δ₀ ++ A₁ ∷ Δ₁ ++ Γ₂ ++ Γ₀) _ Δ refl | cases++ (Δ₀ ++ Γ₁ ++ Δ₁) (Δ₀ ++ Γ₁ ++ Δ₁ ++ A₂ ∷ Γ₀) _ Δ refl
ccut-hass Δ₀ f₁ f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | inj₁ (Λ₀ , p , q) | inj₁ (Λ₀' , p' , q') with canc++ Γ₀ Λ₀' {Δ} q'
ccut-hass {_}{_}{Γ₂} Δ₀ {_}{Δ₁} f₁ f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | inj₁ (Λ₀ , p , q) | inj₁ (.Γ₀ , refl , refl) | refl with canc++ (Δ₁ ++ Γ₂ ++ Γ₀) Λ₀ {Δ} q
ccut-hass {_} {Γ₁} {Γ₂} Δ₀ {.((Δ₀ ++ _ ∷ Δ₁ ++ _ ∷ Γ₀) ++ Δ)} {Δ₁} {.(Γ₀ ++ Δ)} {_} {_} f₁ f₂ (⊗r {_} {.(Δ₀ ++ _ ∷ Δ₁ ++ _ ∷ Γ₀)} {Δ} g g') r | inj₁ (Γ₀ , refl , refl) | inj₁ (.(Δ₁ ++ _ ∷ Γ₀) , refl , refl) | refl | inj₁ (.(Δ₁ ++ Γ₂ ++ Γ₀) , refl , refl) | inj₁ (.Γ₀ , refl , refl) | refl | refl = 
  ⊗r {Γ = Δ₀ ++ Γ₁ ++ Δ₁ ++ Γ₂ ++ Γ₀}{Δ} (ccut-hass Δ₀ f₁ f₂ g refl) refl
ccut-hass Δ₀ f₁ f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | inj₁ (Λ₀ , p , q) | inj₂ (Λ₀' , p' , q') = ⊥-elim (canc⊥3 Γ₀ Δ Λ₀' p')
ccut-hass {_}{_}{Γ₂} Δ₀ {_}{Δ₁} f₁ f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | inj₂ (Λ₀ , p , q) | _ = ⊥-elim (canc⊥3 (Δ₁ ++ Γ₂ ++ Γ₀) Δ Λ₀ p)
ccut-hass Δ₀ {_}{Δ₁}{Δ₂}{_}{A₂} f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , q) | inj₁ (Γ₀' , refl , q') with canc++ Δ₁ (Γ₀' ++ Γ₀) {A₂ ∷ Δ₂} q'
ccut-hass {_}{_}{Γ₂} Δ₀ {_}{_}{Δ₂}{A₁} f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) | refl with cases++ Δ₀ (Δ₀ ++ A₁ ∷ Γ₀') _ (Γ₀ ++ Γ₂ ++ Δ₂) refl
ccut-hass {_}{_}{Γ₂} Δ₀ {_}{_}{Δ₂} f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) | refl | inj₁ (Λ₀ , p , q) with canc++ Γ₀' Λ₀ {Γ₀ ++ Γ₂ ++ Δ₂} q
ccut-hass {_}{Γ₁} Δ₀ {_}{_}{Δ₂}{_}{A₂} f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) | refl | inj₁ (.Γ₀' , refl , refl) | refl
  with cases++ (Δ₀ ++ Γ₁ ++ Γ₀' ++ Γ₀) (Δ₀ ++ Γ₁ ++ Γ₀') Δ₂ (Γ₀ ++ A₂ ∷ Δ₂) refl
ccut-hass Δ₀ {_}{_}{Δ₂} f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) | refl | inj₁ (.Γ₀' , refl , refl) | refl | inj₁ (Λ , p , q) = ⊥-elim (canc⊥3 [] Δ₂ (Λ ++ Γ₀) q)
ccut-hass Δ₀ {_}{_}{Δ₂}{_}{A₂} f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) | refl | inj₁ (.Γ₀' , refl , refl) | refl | inj₂ (Λ , p , q) with canc++ Γ₀ Λ {A₂ ∷ Δ₂} p
ccut-hass Δ₀ f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) | refl | inj₁ (.Γ₀' , refl , refl) | refl | inj₂ (.Γ₀ , refl , refl) | refl = refl
ccut-hass Δ₀ f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) | refl | inj₂ (Λ₀ , p , q) = ⊥-elim (canc⊥2 Δ₀ {Γ₀' ++ Λ₀} q)
ccut-hass Δ₀ {_}{Δ₁}{_}{A₁} f₁ f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p' , q') = ⊥-elim (canc⊥3 Γ₀ Δ (Γ₀' ++ A₁ ∷ Δ₁) p')
ccut-hass ._ {_}{Δ₁}{Δ₂}{A₁}{A₂} f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , q) | inj₂ (Γ₀' , p' , refl) with canc++ Γ₀ (Γ₀' ++ A₁ ∷ Δ₁) {A₂ ∷ Δ₂} p'
ccut-hass {_}{_}{Γ₂} ._ {_}{Δ₁}{Δ₂}{A₁} f₁ f₂ (⊗r {Γ = Γ} g g') r | inj₂ (._ , refl , refl) | inj₂ (Γ₀' , refl , refl) | refl with cases++ (Γ ++ Γ₀') Γ (Δ₁ ++ Γ₂ ++ Δ₂) (Γ₀' ++ A₁ ∷ Δ₁ ++ Γ₂ ++ Δ₂) refl
ccut-hass _ f₁ f₂ (⊗r {Γ = Γ} g g') r | inj₂ (._ , refl , refl) | inj₂ (Γ₀ , refl , refl) | refl | inj₁ (Γ₀' , p' , q') = ⊥-elim (canc⊥4 Γ {Γ₀'} {Γ₀} p')
ccut-hass _ f₁ f₂ (⊗r {Γ = Γ} g g') r | inj₂ (._ , refl , refl) | inj₂ (Γ₀ , refl , refl) | refl | inj₂ (Γ₀' , p' , q') with ++canc {xs = Γ₀}{Γ₀'} Γ q'
ccut-hass {_}{Γ₁} _ {_}{Δ₁}{Δ₂}{_}{A₂} f₁ f₂ (⊗r {Γ = Γ} g g') r | inj₂ (._ , refl , refl) | inj₂ (Γ₀ , refl , refl) | refl | inj₂ (.Γ₀ , refl , refl) | refl
  with cases++ (Γ ++ Γ₀ ++ Γ₁ ++ Δ₁) Γ Δ₂ (Γ₀ ++ Γ₁ ++ Δ₁ ++ A₂ ∷ Δ₂) refl
ccut-hass {_}{Γ₁} _ {_}{Δ₁}{Δ₂} f₁ f₂ (⊗r g g') r | inj₂ (._ , refl , refl) | inj₂ (Γ₀ , refl , refl) | refl | inj₂ (.Γ₀ , refl , refl) | refl | inj₁ (Γ₀' , p' , q') = ⊥-elim (canc⊥3 [] Δ₂ (Γ₀' ++ Γ₀ ++ Γ₁ ++ Δ₁) q')
ccut-hass {_}{Γ₁} ._ {_}{Δ₁}{Δ₂}{_}{A₂} f₁ f₂ (⊗r g g') r | inj₂ (._ , refl , refl) | inj₂ (Γ₀ , refl , refl) | refl | inj₂ (.Γ₀ , refl , refl) | refl | inj₂ (Γ₀' , p' , q') with canc++ (Γ₀ ++ Γ₁ ++ Δ₁) Γ₀' {A₂ ∷ Δ₂} p'
ccut-hass _ f₁ f₂ (⊗r g g') r | inj₂ (._ , refl , refl) | inj₂ (Γ₀ , refl , refl) | refl | inj₂ (.Γ₀ , refl , refl) | refl | inj₂ (._ , refl , refl) | refl = ⊗r refl (ccut-hass Γ₀ f₁ f₂ g' refl)
ccut-hass Δ₀ f₁ f₂ (Il g) refl = Il (ccut-hass Δ₀ f₁ f₂ g refl)
ccut-hass Δ₀ f₁ f₂ (⊗l {B = B} g) refl = ⊗l (ccut-hass (B ∷ Δ₀) f₁ f₂ g refl)

cong-scut⊗r ax p q = ⊗r p q
cong-scut⊗r (⊗r h h') p q = ⊗r (cong-scut⊗r h p q) refl
cong-scut⊗r {Γ = Γ}{f = f}{g}{f'}{g'} (⊗l h) p q =
  proof≗
  scut f (ccut [] f' h refl)
  ≗〈 cong-scut1 p 〉
  scut g (ccut [] f' h refl)
  ≗〈 cong-scut2 g (cong-ccut1 [] h refl q) 〉
  scut g (ccut [] g' h refl)
  qed≗
cong-scut⊗r {Γ = Γ} {Δ} (ex {Γ = Λ} h) p q =
  ex {Γ = Γ ++ Δ ++ Λ} (cong-scut⊗r h p q)

cong-scut1 refl = refl
cong-scut1 (~ p) = ~ (cong-scut1 p)
cong-scut1 (p ∙ p₁) = (cong-scut1 p) ∙ (cong-scut1 p₁)
cong-scut1 (uf p) = uf (cong-scut1 p)
cong-scut1 (⊗l p) = ⊗l (cong-scut1 p)
cong-scut1 (Il p) = Il (cong-scut1 p)
cong-scut1 {h = h} (⊗r p p') = cong-scut⊗r h p p'
cong-scut1 {h = h} axI = (~ (IlIl-1 h)) ∙ Il (≡-to-≗ (Il-1-scutIr h))
cong-scut1 {h = h} ax⊗ = 
  proof≗
  h
  ≗〈 ~ ⊗l⊗l-1 h 〉 
  ⊗l (⊗l-1 h)
  ≗〈 ⊗l (≡-to-≗ (⊗l-1-scut⊗r h)) 〉
  ⊗l (scut (⊗r ax (uf ax)) h)
  qed≗
cong-scut1 {h = h} ⊗ruf = scut⊗ruf h
cong-scut1 {h = h} ⊗rIl = scut⊗rIl h
cong-scut1 {h = h} ⊗r⊗l = scut⊗r⊗l h
cong-scut1 (ex p) = ex (cong-scut1 p) 
cong-scut1 exex = exex
cong-scut1 exuf = exuf
cong-scut1 exIl = exIl
cong-scut1 ex⊗l = ex⊗l
cong-scut1 {h = ax} ex⊗r₁ = ex⊗r₁
cong-scut1 {h = ex {Γ = Γ} h} (ex⊗r₁ {Γ₁ = Γ₁} {Γ₂} {Δ}) =
  ~ exex {Γ₁ = Γ₁}{Γ₂ ++ Δ ++ Γ}
  ∙ ex {Γ = Γ₁ ++ _ ∷ _ ∷ Γ₂ ++ Δ ++ Γ} (cong-scut1 {h = h} ex⊗r₁)
cong-scut1 {f = f}{g} {⊗r h h₁} ex⊗r₁ =
  ex⊗r₁ ∙ ⊗r (cong-scut1 {f = f}{g}{h} ex⊗r₁) refl
cong-scut1 {h = ⊗l h} ex⊗r₁ = refl
cong-scut1 {h = ax} ex⊗r₂ = ex⊗r₂
cong-scut1 {h = ex {Γ = Γ} h} (ex⊗r₂ {Γ = Γ₁} {Δ₁} {Δ₂}) =
  ~ exex {Γ₁ = Γ₁ ++ Δ₁}{Δ₂ ++ Γ}
  ∙ ex {Γ = Γ₁ ++ Δ₁ ++ _ ∷ _ ∷ Δ₂ ++ Γ} (cong-scut1 {h = h} ex⊗r₂)
cong-scut1 {f = f}{g}{⊗r h h₁} (ex⊗r₂ {Γ = Γ} {Δ₁}) =
  ex⊗r₁ {Γ₁ = Γ ++ Δ₁} ∙ ⊗r (cong-scut1 {f = f}{g}{h} ex⊗r₂) refl
cong-scut1 {h = ⊗l h} (ex⊗r₂ {f = f}) =
  ~ (scut-ex f) ∙ cong-scut2 f (~ (ccut-ex [] _ h refl))
cong-scut1 ex-iso = ex-iso
cong-scut1 ex-braid = ex-braid


cong-scut2 ax p = p
cong-scut2 (uf h) p = uf (cong-scut2 h p)
cong-scut2 Ir {f}{g} p = 
    proof≗
    scut Ir f
    ≗〈 ≡-to-≗ (sym (Il-1-scutIr f)) 〉
    Il-1 f
    ≗〈 congIl-1 p 〉
    Il-1 g
    ≗〈 ≡-to-≗ (Il-1-scutIr g) 〉 
    scut Ir g
    qed≗
cong-scut2 (⊗r h h') refl = refl
cong-scut2 (⊗r h h') (~ p) = ~ (cong-scut2 (⊗r h h') p)
cong-scut2 (⊗r h h') (p ∙ p') = (cong-scut2 (⊗r h h') p) ∙ (cong-scut2 (⊗r h h') p')
cong-scut2 (⊗r {Γ = Γ} h h') (⊗l p) = cong-scut2 h (cong-ccut2 [] refl p)
cong-scut2 (⊗r h h') (⊗r p p') = ⊗r (cong-scut2 (⊗r h h') p) p'
cong-scut2 (⊗r {Γ = Γ} h h') ax⊗ with cong-ccut2 Γ {f = h'} refl (~ (scut⊗r h ax (uf ax)))
cong-scut2 (⊗r {Γ = Γ}{B = B} h h') ax⊗ | ih with cases++ Γ Γ [] (B ∷ []) refl
cong-scut2 (⊗r h h') ax⊗ | ih | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
cong-scut2 (⊗r {Γ = Γ} h h') ax⊗ | ih | inj₂ ([] , refl , refl) =
  proof≗
  ⊗r h h'
  ≗〈 ⊗r (~ (≡-to-≗ (scut-unit h))) refl 〉 
  ⊗r (scut h ax) h'
  ≗〈 ~ (scut⊗r h ax h') 〉
  scut h (⊗r ax h')
  ≗〈 ≡-to-≗ (cong (scut h) (cong (⊗r ax) (sym (scut-unit h')))) 〉 
  scut h (⊗r ax (scut h' ax))
  qed≗
cong-scut2 (⊗r h h') ax⊗ | ih | inj₂ (_ ∷ Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ (proj₂ (inj∷ p)))
cong-scut2 (⊗r {Γ = Γ} h h') (⊗r⊗l {f = f}{g}) = ~ (scut⊗r h (ccut [] h' f refl) g)
cong-scut2 (⊗r {Γ = Γ} {Δ} h h') (ex {Γ = Γ₁} p) =
  ex {Γ = Γ ++ Δ ++ Γ₁} (cong-scut2 (⊗r h h') p)
cong-scut2 (⊗r {Γ = Γ} {Δ} h h') (exex {Γ₁ = Γ₁}) = exex {Γ₁ = Γ ++ Δ ++ Γ₁}
cong-scut2 (⊗r {Δ = Δ} h h') (ex⊗l {Γ}) = ~ scut-ex {Δ₁ = Δ ++ Γ} h
cong-scut2 (⊗r {Γ = Γ} {Δ} h h') (ex⊗r₁ {Γ₁ = Γ₁}) = ex⊗r₁ {Γ₁ = Γ ++ Δ ++ Γ₁}
cong-scut2 (⊗r h h') ex⊗r₂ = ex⊗r₂
cong-scut2 (⊗r {Γ = Γ} {Δ} h h') (ex-iso {Γ = Γ₁}) = ex-iso {Γ = Γ ++ Δ ++ Γ₁}
cong-scut2 (⊗r {Γ = Γ} {Δ} h h') (ex-braid {Γ = Γ₁}) = ex-braid {Γ = Γ ++ Δ ++ Γ₁}
cong-scut2 (Il h) p = Il (cong-scut2 h p)
cong-scut2 (⊗l h) p = ⊗l (cong-scut2 h p)
cong-scut2 (ex h) p = ex (cong-scut2 h p)

cong-ccut1 Δ₀ ax r p = ⊥-elim ([]disj∷ Δ₀ r)
cong-ccut1 Δ₀ (uf g) r p with cases∷ Δ₀ r
cong-ccut1 .[] (uf g) r p | inj₁ (refl , refl , refl) = cong-scut1 p
cong-ccut1 .(_ ∷ Δ₀) (uf g) r p | inj₂ (Δ₀ , refl , refl) = uf (cong-ccut1 Δ₀ g refl p)
cong-ccut1 Δ₀ Ir r p = ⊥-elim ([]disj∷ Δ₀ r)
cong-ccut1 Δ₀ {Δ'} (⊗r {Γ = Γ}{Δ} g g') r p with cases++ Δ₀ Γ Δ' Δ r
cong-ccut1 Δ₀ (⊗r g g') r p | inj₁ (Γ₀ , refl , refl) = ⊗r (cong-ccut1 Δ₀ g refl p) refl
cong-ccut1 ._ (⊗r g g') r p | inj₂ (Γ₀ , refl , refl) = ⊗r refl (cong-ccut1 Γ₀ g' refl p)
cong-ccut1 Δ₀ (Il g) refl p = Il (cong-ccut1 Δ₀ g refl p)
cong-ccut1 Δ₀ (⊗l {B = B} g) refl p = ⊗l (cong-ccut1 (B ∷ Δ₀) g refl p)
cong-ccut1 Δ₀ {Δ'} (ex {Γ = Γ} {Δ} g) r p with cases++2 Δ₀ Γ Δ' Δ r
cong-ccut1 {Γ = Γ} Δ₀ {.(Γ₀ ++ _ ∷ _ ∷ Δ)} (ex {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g) r p | inj₁ (Γ₀ , refl , refl) = ex {Γ = Δ₀ ++ Γ ++ Γ₀} (cong-ccut1 Δ₀ g refl p)
... | inj₂ (inj₁ (Γ₀ , refl , refl)) = ex (cong-ccut1 (Γ ++ _ ∷ _ ∷ Γ₀) g refl p)
cong-ccut1 {Γ = Γ} Δ₀ {.(_ ∷ Δ)} (ex {Γ = .Δ₀} {Δ} g) r p | inj₂ (inj₂ (inj₁ (refl , refl , refl))) = cong-ex-fma-cxt Γ (cong-ccut1 (Δ₀ ++ _ ∷ []) g refl p)
cong-ccut1 {Γ = Γ₁} .(Γ ++ _ ∷ []) {Δ'} (ex {Γ = Γ} {.Δ'} g) r p | inj₂ (inj₂ (inj₂ (refl , refl , refl))) = cong-ex-cxt-fma Γ₁ (cong-ccut1 Γ g refl p)

cong-ccut2 Δ₀ r refl = refl
cong-ccut2 Δ₀ r (~ p) = ~ (cong-ccut2 Δ₀ r p)
cong-ccut2 Δ₀ r (p ∙ p₁) = (cong-ccut2 Δ₀ r p) ∙ (cong-ccut2 Δ₀ r p₁)
cong-ccut2 Δ₀ r (uf p) with cases∷ Δ₀ r
cong-ccut2 .[] {f = f} r (uf p) | inj₁ (refl , refl , refl) = cong-scut2 f p
cong-ccut2 .(_ ∷ Γ₀) r (uf p) | inj₂ (Γ₀ , refl , refl) = uf (cong-ccut2 Γ₀ refl p)
cong-ccut2 Δ₀ refl (⊗l {B = B} p) = ⊗l (cong-ccut2 (B ∷ Δ₀) refl p)
cong-ccut2 Δ₀ refl (Il p) = Il (cong-ccut2 Δ₀ refl p)
cong-ccut2 Δ₀ {Δ'} r (⊗r {Γ = Γ}{Δ} p p') with cases++ Δ₀ Γ Δ' Δ r
cong-ccut2 Δ₀ r (⊗r p p') | inj₁ (Γ₀ , refl , refl) = ⊗r (cong-ccut2 Δ₀ refl p) p'
cong-ccut2 ._ r (⊗r p p') | inj₂ (Γ₀ , refl , refl) = ⊗r p (cong-ccut2 Γ₀ refl p')
cong-ccut2 Δ₀ r axI = ⊥-elim ([]disj∷ Δ₀ r)
cong-ccut2 Δ₀ r ax⊗ = ⊥-elim ([]disj∷ Δ₀ r)
cong-ccut2 Δ₀ {Δ'} r (⊗ruf {Γ}{Δ}{A' = A'}) with cases++ Δ₀ (A' ∷ Γ) Δ' Δ r | cases∷ Δ₀ r
cong-ccut2 .[] {f = f} r (⊗ruf {f = g} {g'}) | inj₁ (Γ₀ , refl , refl) | inj₁ (refl , refl , refl) = ~ (scut⊗r f g g')
cong-ccut2 ._ r ⊗ruf | inj₁ (Γ₀ , p , refl) | inj₂ (Γ₀' , t , refl) with inj∷ p
cong-ccut2 ._ {_}{A} r (⊗ruf {Δ = Δ}) | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl) | refl , refl with cases++ Γ₀' (Γ₀' ++ A ∷ Γ₀) (Γ₀ ++ Δ) Δ refl
cong-ccut2 ._ r (⊗ruf {Δ = Δ}) | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl) | refl , refl | inj₁ (Γ₀'' , p , q) with canc++ Γ₀ Γ₀'' {Δ} q
cong-ccut2 ._ r ⊗ruf | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl) | refl , refl | inj₁ (.Γ₀ , refl , refl) | refl = ⊗ruf
cong-ccut2 ._ r (⊗ruf {Δ = Δ}) | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl) | refl , refl | inj₂ (Γ₀'' , p , q) = ⊥-elim (canc⊥3 Γ₀ Δ Γ₀'' p)
cong-ccut2 ._ r ⊗ruf | inj₂ (Γ₀ , refl , refl) | inj₁ (_ , () , u)
cong-ccut2 ._ r ⊗ruf | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , t , u) with inj∷ u
cong-ccut2 ._ {Δ'}{A} r (⊗ruf {Γ}) | inj₂ (Γ₀ , refl , refl) | inj₂ (._ , refl , refl) | refl , refl with cases++ (Γ ++ Γ₀) Γ Δ' (Γ₀ ++ A ∷ Δ') refl
cong-ccut2 ._ {Δ'} r ⊗ruf | inj₂ (Γ₀ , refl , refl) | inj₂ (._ , refl , refl) | refl , refl | inj₁ (Γ₀' , t , u) = ⊥-elim (canc⊥3 [] Δ' (Γ₀' ++ Γ₀) u)
cong-ccut2 ._ {Δ'}{A} r ⊗ruf | inj₂ (Γ₀ , refl , refl) | inj₂ (._ , refl , refl) | refl , refl | inj₂ (Γ₀' , t , u) with canc++ Γ₀ Γ₀' {A ∷ Δ'} t
cong-ccut2 ._ r ⊗ruf | inj₂ (Γ₀ , refl , refl) | inj₂ (._ , refl , refl) | refl , refl | inj₂ (.Γ₀ , refl , refl) | refl = ⊗ruf
cong-ccut2 Δ₀ {Δ'} r (⊗rIl {Γ}{Δ}) with cases++ Δ₀ Γ Δ' Δ r
cong-ccut2 Δ₀ r ⊗rIl | inj₁ (Γ₀ , refl , refl) = ⊗rIl
cong-ccut2 ._ r ⊗rIl | inj₂ (Γ₀ , refl , refl) = ⊗rIl
cong-ccut2 Δ₀ {Δ'} r (⊗r⊗l {Γ}{Δ}) with cases++ Δ₀ Γ Δ' Δ r
cong-ccut2 Δ₀ {_}{A} refl (⊗r⊗l {Δ = Δ}) | inj₁ (Γ₀ , refl , refl) with cases++ Δ₀ (Δ₀ ++ A ∷ Γ₀) (Γ₀ ++ Δ) Δ refl
cong-ccut2 Δ₀ refl (⊗r⊗l {Δ = Δ}) | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , q) with canc++ Γ₀ Γ₀' {Δ} q
cong-ccut2 Δ₀ refl ⊗r⊗l | inj₁ (Γ₀ , refl , refl) | inj₁ (.Γ₀ , refl , refl) | refl = ⊗r⊗l
cong-ccut2 Δ₀ refl (⊗r⊗l {Δ = Δ}) | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , q) = ⊥-elim (canc⊥3 Γ₀ Δ Γ₀' p)
cong-ccut2 ._ {Δ'}{A} refl (⊗r⊗l {Γ}) | inj₂ (Γ₀ , refl , refl) with cases++ (Γ ++ Γ₀) Γ Δ' (Γ₀ ++ A ∷ Δ') refl
cong-ccut2 ._ {Δ'} refl ⊗r⊗l | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , q) = ⊥-elim (canc⊥3 [] Δ' (Γ₀' ++ Γ₀) q)
cong-ccut2 ._ {Δ'}{A} refl ⊗r⊗l | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , q) with canc++ Γ₀ Γ₀' {A ∷ Δ'} p
cong-ccut2 ._ refl ⊗r⊗l | inj₂ (Γ₀ , refl , refl) | inj₂ (.Γ₀ , refl , refl) | refl = ⊗r⊗l
cong-ccut2 Δ₀ {Δ'} r (ex {Γ = Γ} {Δ} p) with cases++2 Δ₀ Γ Δ' Δ r
cong-ccut2 {Γ = Γ} Δ₀ r (ex {Γ = _} {_} p) | inj₁ (Γ₀ , refl , refl) =
  ex {Γ = Δ₀ ++ Γ ++ Γ₀} (cong-ccut2 Δ₀ refl p)
... | inj₂ (inj₁ (Γ₀ , refl , refl)) = ex {Γ = Γ} (cong-ccut2 (Γ ++ _ ∷ _ ∷ Γ₀) refl p)
cong-ccut2 {Γ = Γ} Δ₀ r (ex {Γ = _} {_} p) | inj₂ (inj₂ (inj₁ (refl , refl , refl))) =
  cong-ex-fma-cxt Γ (cong-ccut2 (Δ₀ ++ _ ∷ []) refl p)
cong-ccut2 {Γ = Γ} ._ r (ex {Γ = Γ₁} {_} p) | inj₂ (inj₂ (inj₂ (refl , refl , refl))) =
  cong-ex-cxt-fma Γ (cong-ccut2 Γ₁ refl p)
cong-ccut2 Δ₀ {Δ'} {A = A₁} r (exex {Γ₁ = Γ₁} {Γ₂} {Γ₃} {A} {B} {A'}) with cases++2 Δ₀ (Γ₁ ++ B ∷ A ∷ Γ₂) Δ' Γ₃ r
cong-ccut2 ._ {Δ'} {A = A₁} refl (exex {Γ₁ = Γ₁} {Γ₂} {Γ₃} {A} {B} {A'} {B'}) | inj₂ (inj₁ (Γ₀ , refl , refl))
  rewrite cases++-inj₂ (B ∷ A ∷ Γ₂ ++ B' ∷ A' ∷ Γ₀) Γ₁ Δ' A₁ |
          cases++-inj₂ (B ∷ A ∷ Γ₂ ++ A' ∷ B' ∷ Γ₀) Γ₁ Δ' A₁ |
          cases++-inj₂ (B' ∷ A' ∷ Γ₀) (Γ₁ ++ A ∷ B ∷ Γ₂) Δ' A₁ = exex
cong-ccut2 {Γ = Γ} ._ {A = A₁} refl (exex {Γ₁ = Γ₁} {Γ₂} {Γ₃} {A} {B} {A'}) | inj₂ (inj₂ (inj₁ (refl , refl , refl)))
  rewrite cases++-inj₂ (B ∷ A ∷ Γ₂) Γ₁ (A' ∷ Γ₃) A₁ |
          cases++-inj₂ (B ∷ A ∷ Γ₂ ++ A' ∷ []) Γ₁ Γ₃ A₁ |
          cases++-inj₂ [] (Γ₁ ++ A ∷ B ∷ Γ₂) (A' ∷ Γ₃) A₁ = ex-fma-cxt-ex Γ
cong-ccut2 {Γ = Γ} ._ {Δ'} {A = A₁} refl (exex {Γ₁ = Γ₁} {Γ₂} {Γ₃} {A} {B} {A'} {B'}) | inj₂ (inj₂ (inj₂ (refl , refl , refl))) 
  rewrite cases++-inj₂ (B ∷ A ∷ Γ₂ ++ B' ∷ []) Γ₁ Δ' A₁ |
          cases++-inj₂ (B ∷ A ∷ Γ₂) Γ₁ (B' ∷ Δ') A₁ |
          cases++-inj₂ (B' ∷ []) (Γ₁ ++ A ∷ B ∷ Γ₂) Δ' A₁ = ex-cxt-fma-ex Γ
... | inj₁ (Γ₀ , q , refl) with cases++2 Δ₀ Γ₁ Γ₀ Γ₂ q
cong-ccut2 {Γ = Γ} Δ₀ {.((Γ₀' ++ _ ∷ _ ∷ Γ₂) ++ _ ∷ _ ∷ _)} {A = A₁} refl (exex {Γ₁ = Γ₁} {Γ₂} {Γ₃} {A} {B} {A'}{B'}) | inj₁ (.(Γ₀' ++ _ ∷ _ ∷ Γ₂) , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀' (B ∷ A ∷ Γ₂ ++ B' ∷ A' ∷ Γ₃) A₁ |
          cases++-inj₁ Δ₀ Γ₀' (B ∷ A ∷ Γ₂ ++ A' ∷ B' ∷ Γ₃) A₁ |
          cases++-inj₁ Δ₀ (Γ₀' ++ A ∷ B ∷ Γ₂) (B' ∷ A' ∷ Γ₃) A₁ = exex {Γ₁ = Δ₀ ++ Γ ++ Γ₀'}
cong-ccut2 {Γ = Γ} ._ {A = A₁} refl (exex {Γ₁ = Γ₁} {Γ₃ = Γ₃} {A} {B} {A'}{B'}) | inj₁ (Γ₀ , refl , refl) | inj₂ (inj₁ (Γ₀' , refl , refl))
  rewrite cases++-inj₂ (B ∷ A ∷ Γ₀') Γ₁ (Γ₀ ++ B' ∷ A' ∷ Γ₃) A₁ |
          cases++-inj₂ (B ∷ A ∷ Γ₀') Γ₁ (Γ₀ ++ A' ∷ B' ∷ Γ₃) A₁ |
          cases++-inj₁ (Γ₁ ++ A ∷ B ∷ Γ₀') Γ₀ (B' ∷ A' ∷ Γ₃) A₁  = exex {Γ₁ = Γ₁} {Γ₀' ++ Γ ++ Γ₀}
cong-ccut2 {Γ = Γ} Δ₀ {A = A₁} refl (exex {Γ₁ = Γ₁} {Γ₂} {Γ₃} {A} {B} {A'}{B'} ) | inj₁ (.(_ ∷ Γ₂) , refl , refl) | inj₂ (inj₂ (inj₁ (refl , refl , refl)))
  rewrite cases++-inj₂ [] Δ₀ (A ∷ Γ₂ ++ B' ∷ A' ∷ Γ₃) A₁ |
          cases++-inj₂ [] Δ₀ (A ∷ Γ₂ ++ A' ∷ B' ∷ Γ₃) A₁ |
          cases++-inj₁ (Δ₀ ++ A ∷ []) Γ₂ (B' ∷ A' ∷ Γ₃) A₁ = ~ ex-ex-fma-cxt Γ
cong-ccut2 {Γ = Γ} ._ {A = A₁} refl (exex {Γ₁ = Γ₁} {Γ₃ = Γ₃} {A} {B} {A'}{B'}) | inj₁ (Γ₀ , refl , refl) | inj₂ (inj₂ (inj₂ (refl , refl , refl))) 
  rewrite cases++-inj₂ (B ∷ []) Γ₁ (Γ₀ ++ B' ∷ A' ∷ Γ₃) A₁ |
          cases++-inj₂ (B ∷ []) Γ₁ (Γ₀ ++ A' ∷ B' ∷ Γ₃) A₁ |
          cases++-inj₁ Γ₁ (B ∷ Γ₀) (B' ∷ A' ∷ Γ₃) A₁ = ~ ex-ex-cxt-fma Γ
cong-ccut2 {Γ = Γ} Δ₀ {Δ'} r (exuf {Γ₁} {Δ} {A'} {A} {B}) with cases∷ Δ₀ r
cong-ccut2 {Γ = Γ} .[] {A = A₁} {f = f} refl (exuf {Γ₁} {Δ} {A'} {A} {B}) | inj₁ (refl , refl , refl) = ~ scut-ex f
... | inj₂ (Γ₀ , p , refl) with cases++2 Γ₀ Γ₁ Δ' Δ p
cong-ccut2 {Γ = Γ} ._ {A = A₁} refl (exuf {Γ₁} {Δ} {A'} {A} {B}) | inj₂ (Γ₀ , p , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Γ₀ Γ₀' (B ∷ A ∷ Δ) A₁ = exuf {Γ₀ ++ Γ ++ Γ₀'} 
cong-ccut2 {Γ = Γ}  ._ {Δ'} {A = A₁} refl (exuf {Γ₁} {Δ} {A'} {A} {B}) | inj₂ (._ , refl , refl) | inj₂ (inj₁ (Γ₀' , refl , refl))
  rewrite cases++-inj₂ (B ∷ A ∷ Γ₀') Γ₁ Δ' A₁ = exuf
cong-ccut2 {Γ = Γ} _ {A = A₁} refl (exuf {Γ₁} {Δ} {A'} {A} {B}) | inj₂ (Γ₀ , refl , refl) | inj₂ (inj₂ (inj₁ (refl , refl , refl)))
  rewrite cases++-inj₂ [] Γ₀ (A ∷ Δ) A₁ = ex-fma-cxt-uf Γ₀ Γ
cong-ccut2 {Γ = Γ} _ {Δ'} {A = A₁} refl (exuf {Γ₁} {Δ} {A'} {A} {B}) | inj₂ (._ , refl , refl) | inj₂ (inj₂ (inj₂ (refl , refl , refl)))
  rewrite cases++-inj₂ (B ∷ []) Γ₁ Δ' A₁ = ex-cxt-fma-uf Γ₁ Γ
cong-ccut2 {Γ = Γ₁} Δ₀ {Δ'} r (exIl {Γ} {Δ}) with cases++2 Δ₀ Γ Δ' Δ r
... | inj₁ (Γ₀ , refl , refl) = exIl {Δ₀ ++ Γ₁ ++ Γ₀}
... | inj₂ (inj₁ (Γ₀ , refl , refl)) = exIl
... | inj₂ (inj₂ (inj₁ (refl , refl , refl))) = ex-fma-cxt-Il Γ Γ₁
... | inj₂ (inj₂ (inj₂ (refl , refl , refl))) = ex-cxt-fma-Il Γ Γ₁
cong-ccut2 {Γ = Γ} Δ₀ {Δ'} {A₁} r (ex⊗l {Γ₁} {Δ} {B' = B'} {A} {B}) with cases++2 Δ₀ Γ₁ Δ' Δ r
cong-ccut2 {Γ = Γ} Δ₀ {_}{A₁} refl (ex⊗l {Γ₁} {Δ} {B' = B'} {A} {B}) | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀ (B ∷ A ∷ Δ) A₁ = ex⊗l {Δ₀ ++ Γ ++ Γ₀}
cong-ccut2 {Γ = Γ} ._ {Δ'} {A₁} refl (ex⊗l {Γ₁} {Δ} {B' = B'} {A} {B}) | inj₂ (inj₁ (Γ₀ , refl , refl))
  rewrite cases++-inj₂ (B ∷ A ∷ Γ₀) Γ₁ Δ' A₁ = ex⊗l
cong-ccut2 {Γ = Γ} Δ₀ {_} {A₁} refl (ex⊗l {Γ₁} {Δ} {B' = B'} {A} {B}) | inj₂ (inj₂ (inj₁ (refl , refl , refl)))
  rewrite cases++-inj₂ [] Δ₀ (A ∷ Δ) A₁ = ex-fma-cxt-⊗l Δ₀ Γ
cong-ccut2 {Γ = Γ} _ {Δ'} {A₁} refl (ex⊗l {Γ₁} {Δ} {B' = B'} {A} {B}) | inj₂ (inj₂ (inj₂ (refl , refl , refl)))
  rewrite cases++-inj₂ (B ∷ []) Γ₁ Δ' A₁ = ex-cxt-fma-⊗l Γ₁ Γ
cong-ccut2 {Γ = Γ} Δ₀ {Δ'} {A} r (ex⊗r₁ {Γ₁ = Γ₁} {Γ₂} {Δ} {A₁} {B}) with cases++2 Δ₀ Γ₁ Δ' (Γ₂ ++ Δ) r
cong-ccut2 {Γ = Γ} Δ₀ {_}{A} refl (ex⊗r₁ {Γ₁ = Γ₁} {Γ₂} {Δ} {A₁} {B}) | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ (Γ₀ ++ B ∷ A₁ ∷ Γ₂) Δ A |
          cases++-inj₁ Δ₀ (Γ₀ ++ A₁ ∷ B ∷ Γ₂) Δ A |
          cases++-inj₁ Δ₀ Γ₀ (B ∷ A₁ ∷ Γ₂) A = ex⊗r₁ {Γ₁ = Δ₀ ++ Γ ++ Γ₀}
cong-ccut2 {Γ = Γ} Δ₀ {_}{A} refl (ex⊗r₁ {Γ₁ = Γ₁} {Γ₂} {Δ} {A₁} {B}) | inj₂ (inj₂ (inj₁ (refl , refl , refl)))
  rewrite cases++-inj₁ Δ₀ (A₁ ∷ Γ₂) Δ A |
          cases++-inj₁ (Δ₀ ++ A₁ ∷ []) Γ₂ Δ A |
          cases++-inj₂ [] Δ₀ (A₁ ∷ Γ₂) A = ex-fma-cxt-⊗r₁ Δ₀ Γ
cong-ccut2 {Γ = Γ} _ {_}{A} refl (ex⊗r₁ {Γ₁ = Γ₁} {Γ₂} {Δ} {A₁} {B}) | inj₂ (inj₂ (inj₂ (refl , refl , refl)))
  rewrite cases++-inj₁ (Γ₁ ++ B ∷ []) Γ₂ Δ A |
          cases++-inj₁ Γ₁ (B ∷ Γ₂) Δ A |
          cases++-inj₂ (B ∷ []) Γ₁ Γ₂ A = ex-cxt-fma-⊗r₁ Γ₁ Γ
... | inj₂ (inj₁ (Γ₀ , p , refl)) with cases++ Γ₀ Γ₂ Δ' Δ p
cong-ccut2 {Γ = Γ} _ {_}{A} refl (ex⊗r₁ {Γ₁ = Γ₁} {Γ₂} {Δ} {A₁} {B}) | inj₂ (inj₁ (Γ₀ , refl , refl)) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ B ∷ A₁ ∷ Γ₀) Γ₀' Δ A |
          cases++-inj₁ (Γ₁ ++ A₁ ∷ B ∷ Γ₀) Γ₀' Δ A |
          cases++-inj₂ (B ∷ A₁ ∷ Γ₀) Γ₁ Γ₀' A = ex⊗r₁
cong-ccut2 {Γ = Γ} _ {Δ'} {A} refl (ex⊗r₁ {Γ₁ = Γ₁} {Γ₂} {Δ} {A₁} {B}) | inj₂ (inj₁ (_ , refl , refl)) | inj₂ (Γ₀' , refl , refl)
  rewrite cases++-inj₂ Γ₀' (Γ₁ ++ B ∷ A₁ ∷ Γ₂) Δ' A |
          cases++-inj₂ Γ₀' (Γ₁ ++ A₁ ∷ B ∷ Γ₂) Δ' A = ex⊗r₁
cong-ccut2 {Γ = Γ} Δ₀ {Δ'} {A} r (ex⊗r₂ {Γ = Γ₁} {Δ₁} {Δ₂} {A₁} {B}) with cases++2 Δ₀ (Γ₁ ++ Δ₁) Δ' Δ₂ r
cong-ccut2 {Γ = Γ} _ {Δ'} {A} refl (ex⊗r₂ {Γ = Γ₁} {Δ₁} {Δ₂} {A₁} {B}) | inj₂ (inj₁ (Γ₀ , refl , refl)) 
  rewrite cases++-inj₂ (Δ₁ ++ B ∷ A₁ ∷ Γ₀) Γ₁ Δ' A |
          cases++-inj₂ (Δ₁ ++ A₁ ∷ B ∷ Γ₀) Γ₁ Δ' A |
          cases++-inj₂ (B ∷ A₁ ∷ Γ₀) Δ₁ Δ' A = ex⊗r₂
cong-ccut2 {Γ = Γ} _ {_}{A} refl (ex⊗r₂ {Γ = Γ₁} {Δ₁} {Δ₂} {A₁} {B}) | inj₂ (inj₂ (inj₁ (refl , refl , refl)))
  rewrite cases++-inj₂ Δ₁ Γ₁ (A₁ ∷ Δ₂) A |
          cases++-inj₂ (Δ₁ ++ A₁ ∷ []) Γ₁ Δ₂ A |
          cases++-inj₂ [] Δ₁ (A₁ ∷ Δ₂) A = ex-fma-cxt-⊗r₂ Δ₁ Γ
cong-ccut2 {Γ = Γ} _ {Δ'} {A} refl (ex⊗r₂ {Γ = Γ₁} {Δ₁} {Δ₂} {A₁} {B}) | inj₂ (inj₂ (inj₂ (refl , refl , refl)))
  rewrite cases++-inj₂ (Δ₁ ++ B ∷ []) Γ₁ Δ' A |
          cases++-inj₂ Δ₁ Γ₁ (B ∷ Δ') A |
          cases++-inj₂ (B ∷ []) Δ₁ Δ' A = ex-cxt-fma-⊗r₂ Δ₁ Γ
... | inj₁ (Γ₀ , p , refl) with cases++ Δ₀ Γ₁ Γ₀ Δ₁ p
cong-ccut2 {Γ = Γ} Δ₀ {_}{A} refl (ex⊗r₂ {Γ = Γ₁} {Δ₁} {Δ₂} {A₁} {B}) | inj₁ (_ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀' (Δ₁ ++ B ∷ A₁ ∷ Δ₂) A |
          cases++-inj₁ Δ₀ Γ₀' (Δ₁ ++ A₁ ∷ B ∷ Δ₂) A = ex⊗r₂
cong-ccut2 {Γ = Γ} _ {_}{A} refl (ex⊗r₂ {Γ = Γ₁} {Δ₁} {Δ₂} {A₁} {B}) | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl)
  rewrite cases++-inj₂ Γ₀' Γ₁ (Γ₀ ++ B ∷ A₁ ∷ Δ₂) A |
          cases++-inj₂ Γ₀' Γ₁ (Γ₀ ++ A₁ ∷ B ∷ Δ₂) A |
          cases++-inj₁ Γ₀' Γ₀ (B ∷ A₁ ∷ Δ₂) A = ex⊗r₂ {Δ₁ = Γ₀' ++ Γ ++ Γ₀}
cong-ccut2 {Γ = Γ₁} Δ₀ {Δ'} {A} r (ex-iso {Γ = Γ} {Δ} {A₁} {B}) with cases++2 Δ₀ Γ Δ' Δ r
cong-ccut2 {Γ = Γ₁} Δ₀ {_} {A} refl (ex-iso {Γ = Γ} {Δ} {A₁} {B}) | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀ (B ∷ A₁ ∷ Δ) A = ex-iso {Γ = Δ₀ ++ Γ₁ ++ Γ₀}
cong-ccut2 {Γ = Γ₁} _ {Δ'} {A} refl (ex-iso {Γ = Γ} {Δ} {A₁} {B}) | inj₂ (inj₁ (Γ₀ , refl , refl))
  rewrite cases++-inj₂ (B ∷ A₁ ∷ Γ₀) Γ Δ' A = ex-iso
cong-ccut2 {Γ = Γ₁} Δ₀ {_}{A} refl (ex-iso {Γ = Γ} {Δ} {A₁} {B}) | inj₂ (inj₂ (inj₁ (refl , refl , refl)))
  rewrite cases++-inj₂ (B ∷ []) Δ₀ Δ A = ex-fma-cxt-iso2 Γ₁
cong-ccut2 {Γ = Γ₁} _ {Δ'} {A} refl (ex-iso {Γ = Γ} {Δ} {A₁} {B}) | inj₂ (inj₂ (inj₂ (refl , refl , refl)))
  rewrite cases++-inj₂ [] Γ (A₁ ∷ Δ') A = ex-fma-cxt-iso1 Γ₁
cong-ccut2 {Γ = Γ} Δ₀ {Δ'} {A} r (ex-braid {Γ = Γ₁} {Δ} {A₁} {B} {C}) with cases++2 Δ₀ Γ₁ Δ' (A₁ ∷ Δ) r
cong-ccut2 {Γ = Γ} Δ₀ {_}{A} refl (ex-braid {Γ = Γ₁} {Δ} {A₁} {B} {C}) | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ (Γ₀ ++ C ∷ []) (B ∷ A₁ ∷ Δ) A |
          cases++-inj₁ Δ₀ (Γ₀ ++ B ∷ []) (C ∷ A₁ ∷ Δ) A |
          cases++-inj₁ Δ₀ Γ₀ (C ∷ A₁ ∷ B ∷ Δ) A |
          cases++-inj₁ Δ₀ Γ₀ (B ∷ A₁ ∷ C ∷ Δ) A |
          cases++-inj₁ Δ₀ (Γ₀ ++ A₁ ∷ []) (C ∷ B ∷ Δ) A = ex-braid {Γ = Δ₀ ++ Γ ++ Γ₀}
cong-ccut2 {Γ = Γ} _ {Δ'} {A} refl (ex-braid {Γ = Γ₁} {Δ} {A₁} {B} {C}) | inj₂ (inj₁ ([] , refl , refl))
  rewrite cases++-inj₂ (B ∷ []) (Γ₁ ++ C ∷ []) Δ' A |
          cases++-inj₂ (C ∷ []) (Γ₁ ++ B ∷ []) Δ' A |
          cases++-inj₂ (C ∷ []) Γ₁ (B ∷ Δ') A |
          cases++-inj₂ (B ∷ []) Γ₁ (C ∷ Δ') A |
          cases++-inj₁ Γ₁ [] (C ∷ B ∷ Δ') A = ex-cxt-fma-braid Γ
cong-ccut2 {Γ = Γ} _ {Δ'} {A} refl (ex-braid {Γ = Γ₁} {Δ} {A₁} {B} {C}) | inj₂ (inj₁ (_ ∷ Γ₀ , refl , refl))
  rewrite cases++-inj₂ (C ∷ A₁ ∷ Γ₀) (Γ₁ ++ B ∷ []) Δ' A |
          cases++-inj₂ (B ∷ A₁ ∷ Γ₀) (Γ₁ ++ C ∷ []) Δ' A |
          cases++-inj₂ (C ∷ A₁ ∷ B ∷ Γ₀) Γ₁ Δ' A |
          cases++-inj₂ (B ∷ A₁ ∷ C ∷ Γ₀) Γ₁ Δ' A |
          cases++-inj₂ (C ∷ B ∷ Γ₀) (Γ₁ ++ A₁ ∷ []) Δ' A = ex-braid
cong-ccut2 {Γ = Γ} Δ₀ {_}{A} refl (ex-braid {Γ = Γ₁} {Δ} {A₁} {B} {C}) | inj₂ (inj₂ (inj₁ (refl , refl , refl)))
  rewrite cases++-inj₁ Δ₀ [] (B ∷ A₁ ∷ Δ) A |
          cases++-inj₂ [] (Δ₀ ++ B ∷ []) (A₁ ∷ Δ) A |
          cases++-inj₂ [] Δ₀ (A₁ ∷ B ∷ Δ) A |
          cases++-inj₂ (B ∷ A₁ ∷ []) Δ₀ Δ A |
          cases++-inj₂ [] (Δ₀ ++ A₁ ∷ []) (B ∷ Δ) A = ex-fma-cxt-braid Γ
cong-ccut2 {Γ = Γ} {_}{A} refl (ex-braid {Γ = Γ₁} {Δ} {A₁} {B} {C}) | inj₂ (inj₂ (inj₂ (refl , refl , refl)))
  rewrite cases++-inj₂ [] (Γ₁ ++ C ∷ []) (A₁ ∷ Δ) B |
          cases++-inj₁ Γ₁ [] (C ∷ A₁ ∷ Δ) B |
          cases++-inj₂ (C ∷ A₁ ∷ []) Γ₁ Δ B |
          cases++-inj₂ [] Γ₁ (A₁ ∷ C ∷ Δ) B |
          cases++-inj₂ (C ∷ []) (Γ₁ ++ A₁ ∷ []) Δ B = ~ ex-cxt-fma-ex-fma-cxt-braid Γ

cong-scut : {S : Stp} → {Γ Δ' : Cxt} → {A C : Fma} → 
             {f g : S ∣ Γ ⊢ A}  → {h k : just A ∣ Δ' ⊢ C} →
             f ≗ g → h ≗ k → scut f h ≗ scut g k
cong-scut {g = g} p q = cong-scut1 p ∙ cong-scut2 g q             

cong-ccut : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} →  {A C : Fma} → 
             {f f' : nothing ∣ Γ ⊢ A}{g g' : T ∣ Δ ⊢ C}  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
             f ≗ f' → g ≗ g' → ccut Δ₀ f g r ≗ ccut Δ₀ f' g' r
cong-ccut Δ₀ {g = g} r p q = cong-ccut1 Δ₀ g r p  ∙ cong-ccut2 Δ₀ r q

-- ====================================================================

-- associativity of cut

scutscut-vass : {S : Stp} → {Γ Δ Δ' : Cxt} → {A B C : Fma}
  → (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(h : just B ∣ Δ' ⊢ C)
  → scut f (scut g h) ≗ scut (scut f g) h
scutscut⊗r-vass : {S : Stp} → {Γ Γ' Δ Δ' : Cxt} → {A A' B C : Fma}
  → (f1 : S ∣ Γ ⊢ A)(f2 : nothing ∣ Γ' ⊢ A')(g : just (A ⊗ A') ∣ Δ ⊢ B)(h : just B ∣ Δ' ⊢ C)
  → scut (⊗r f1 f2) (scut g h) ≗ scut (scut (⊗r f1 f2) g) h
ccutscut-vass : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' Δ'' : Cxt} → {A B C : Fma}
  → (f : nothing ∣ Γ ⊢ A)(g : T ∣ Δ ⊢ B)(h : just B ∣ Δ'' ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
  → ccut Δ₀ f (scut g h) (cong₂ _++_ r (refl {x = Δ''})) ≗ scut (ccut Δ₀ f g r) h
ccutscut⊗r-vass1 : {T : Stp} → {Γ Δ Δ2 : Cxt} → (Δ₀ : Cxt) → {Δ' Δ'' : Cxt} → {A B B2 C : Fma}
  → (f : nothing ∣ Γ ⊢ A)(g1 : T ∣ Δ ⊢ B)(g2 : nothing ∣ Δ2 ⊢ B2)(h : just (B ⊗ B2) ∣ Δ'' ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
  → ccut Δ₀ f (scut (⊗r g1 g2) h) (cong (_++ (Δ2 ++ Δ'')) {y = Δ₀ ++ A ∷ Δ'} r)
    ≗ scut (⊗r (ccut Δ₀ f g1 r) g2) h
ccutscut⊗r-vass2 : {T : Stp} → {Γ Δ Δ2 : Cxt} → (Δ₀ : Cxt) → {Δ' Δ'' : Cxt} → {A B B2 C : Fma}
  → (f : nothing ∣ Γ ⊢ A)(g1 : T ∣ Δ ⊢ B)(g2 : nothing ∣ Δ2 ⊢ B2)(h : just (B ⊗ B2) ∣ Δ'' ⊢ C)
  → (r : Δ2 ≡ Δ₀ ++ A ∷ Δ')
  → ccut (Δ ++ Δ₀) f (scut (⊗r g1 g2) h) (cong (λ x → Δ ++ x ++ Δ'') {y = Δ₀ ++ A ∷ Δ'} r)
    ≗ scut (⊗r g1 (ccut Δ₀ f g2 r)) h
ccutccut-vass : {T : Stp} → {Γ Δ : Cxt} → (Γ₀ Δ₀ : Cxt) → {Δ' Γ' : Cxt} → {A B C : Fma}
  → (f : nothing ∣ Γ ⊢ A)(g : nothing ∣ Γ₀ ++ A ∷ Γ' ⊢ B)(h : T ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ B ∷ Δ')
  → ccut (Δ₀ ++ Γ₀) f (ccut Δ₀ g h r) refl ≗ ccut Δ₀ (ccut Γ₀ f g refl) h r

scutscut-vass ax g h = refl
scutscut-vass (uf f) g h = uf (scutscut-vass f g h)
scutscut-vass Ir g h = ≡-to-≗ 
  (begin
  scut Ir (scut g h)
  ≡⟨ sym (Il-1-scutIr (scut g h)) ⟩
  Il-1 (scut g h)
  ≡⟨ scutIl-1 g h ⟩ 
  scut (Il-1 g) h
  ≡⟨ cong (λ x → scut x h) (Il-1-scutIr g) ⟩
  scut (scut Ir g) h
  ∎)
scutscut-vass (⊗r f1 f2) g h = scutscut⊗r-vass f1 f2 g h
scutscut-vass (Il f) g h = Il (scutscut-vass f g h)
scutscut-vass (⊗l f) g h = ⊗l (scutscut-vass f g h)
scutscut-vass (ex f) g h = ex (scutscut-vass f g h)

scutscut⊗r-vass f f' ax h = refl
scutscut⊗r-vass {Γ = Γ} {Γ'} f f' (ex {Γ = Γ₁} g) h =
  ex {Γ = Γ ++ Γ' ++ Γ₁} (scutscut⊗r-vass f f' g h)
scutscut⊗r-vass f f' (⊗r g g') ax = refl
scutscut⊗r-vass {Γ = Γ}{Δ} f f' (⊗r {Γ = Γ₁} {Δ₁} g g') (⊗r {Γ = Γ₂} {Δ₂} h h') =
  ⊗r {Γ = Γ ++ Δ ++ Γ₁ ++ Δ₁ ++ Γ₂}{Δ₂} (scutscut⊗r-vass f f' (⊗r g g') h) refl
scutscut⊗r-vass {Γ = Γ'}{Δ'} f f' (⊗r {Γ = Γ} g g') (⊗l h) =
  scutscut⊗r-vass f f' g (ccut [] g' h refl)
scutscut⊗r-vass {Γ = Γ'} {Δ'} f f' (⊗r {Γ = Γ} {Δ} g g') (ex {Γ = Γ₁} h) =
  ex {Γ = Γ' ++ Δ' ++ Γ ++ Δ ++ Γ₁} (scutscut⊗r-vass f f' (⊗r g g') h)
scutscut⊗r-vass {Γ = Γ} f f' (⊗l g) h = 
  proof≗
  scut f (ccut [] f' (scut g h) refl)
  ≗〈 cong-scut2 f (ccutscut-vass [] f' g h refl) 〉 
  scut f (scut (ccut [] f' g refl) h)
  ≗〈 scutscut-vass f (ccut [] f' g refl) h 〉
  scut (scut f (ccut [] f' g refl)) h
  qed≗


ccutscut⊗r-vass1 {Δ2 = Δ2} Δ₀ {Δ'} {A = A} f g1 g2 ax refl
  rewrite cases++-inj₁ Δ₀ Δ' Δ2 A = refl
ccutscut⊗r-vass1 {Γ = Γ₁} {Δ2 = Δ2} Δ₀ {Δ'} {A = A} f g1 g2 (ex {Γ = Γ} {Δ} {A₁} {B = B} h) refl 
  rewrite cases++-inj₁ Δ₀ Δ' Δ2 A |
          cases++-inj₁ Δ₀ (Δ' ++ Δ2 ++ Γ) (B ∷ A₁ ∷ Δ) A =
  ex {Γ = Δ₀ ++ Γ₁ ++ Δ' ++ Δ2 ++ Γ} (ccutscut⊗r-vass1 Δ₀ f g1 g2 h refl)
ccutscut⊗r-vass1 {Δ2 = Δ2} Δ₀ {Δ'} {A = A} f g1 g2 (⊗r {Γ = Γ} {Δ} h h₁) refl
  rewrite cases++-inj₁ Δ₀ (Δ' ++ Δ2 ++ Γ) Δ A =
  ⊗r (ccutscut⊗r-vass1 Δ₀ f g1 g2 h refl) refl
ccutscut⊗r-vass1 Δ₀ f g1 g2 (⊗l h) refl =
  ccutscut-vass Δ₀ f g1 (ccut [] g2 h refl) refl

ccutscut⊗r-vass2 {Δ = Δ} Δ₀ {Δ'} {A = A} f g1 g2 ax refl
  rewrite cases++-inj₂ Δ₀ Δ Δ' A = refl
ccutscut⊗r-vass2 {Γ = Γ₁} {Δ = Δ} Δ₀ {Δ'} {A = A} f g1 g2 (ex {Γ = Γ} {Δ₁} {A₁} {B} h) refl
  rewrite cases++-inj₁ (Δ ++ Δ₀) (Δ' ++ Γ) (B ∷ A₁ ∷ Δ₁) A =
  ex {Γ = Δ ++ Δ₀ ++ Γ₁ ++ Δ' ++ Γ} (ccutscut⊗r-vass2 Δ₀ f g1 g2 h refl)
ccutscut⊗r-vass2 {Δ = Δ} Δ₀ {Δ'} {A = A} f g1 g2 (⊗r {Γ = Γ} {Δ₁} h h₁) refl
  rewrite cases++-inj₁ (Δ ++ Δ₀) (Δ' ++ Γ) Δ₁ A =
  ⊗r (ccutscut⊗r-vass2 Δ₀ f g1 g2 h refl) refl 
ccutscut⊗r-vass2 {Δ = Δ} Δ₀ f g1 g2 (⊗l h) refl =
  proof≗
  ccut (Δ ++ Δ₀) f (scut g1 (ccut [] g2 h refl)) refl
  ≗〈 ~ (scut-hass Δ₀ g1 f (ccut [] g2 h refl) refl) 〉 
  scut g1 (ccut Δ₀ f (ccut [] g2 h refl) refl)
  ≗〈 cong-scut2 g1 (ccutccut-vass Δ₀ [] f g2 h refl) 〉 
  scut g1 (ccut [] (ccut Δ₀ f g2 refl) h refl)
  qed≗


ccutscut-vass Δ₀ f ax h r = ⊥-elim ([]disj∷ Δ₀ r)
ccutscut-vass Δ₀ {_}{Δ''} f (uf g) h r with cases∷ Δ₀ r | cases∷ Δ₀ (cong₂ _++_ r (refl {x = Δ''}))
ccutscut-vass .[] f (uf g) h r | inj₁ (refl , refl , refl) | inj₁ (refl , refl , refl) = scutscut-vass f g h
ccutscut-vass .[] f (uf g) h r | inj₁ (p , refl , _) | inj₂ (Γ₀' , q' , ())
ccutscut-vass .(_ ∷ Γ₀) f (uf g) h r | inj₂ (Γ₀ , q , refl) | inj₁ (p' , () , s')
ccutscut-vass .(_ ∷ Γ₀) f (uf g) h r | inj₂ (Γ₀ , refl , refl) | inj₂ (.Γ₀ , refl , refl) = uf (ccutscut-vass Γ₀ f g h refl)
ccutscut-vass Δ₀ f Ir h r = ⊥-elim ([]disj∷ Δ₀ r)
ccutscut-vass Δ₀ {Δ'} f (⊗r {Γ = Γ}{Δ} g g') h r with cases++ Δ₀ Γ Δ' Δ r
ccutscut-vass Δ₀ {.(Γ₀ ++ Δ)} {A = _} {_ ⊗ _} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') h refl | inj₁ (Γ₀ , refl , refl) =
  ccutscut⊗r-vass1 Δ₀ f g g' h refl
ccutscut-vass .(Γ ++ Γ₀) {Δ'} {A = _} {_ ⊗ _} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') h refl | inj₂ (Γ₀ , refl , refl) =
  ccutscut⊗r-vass2 Γ₀ f g g' h refl
ccutscut-vass Δ₀ f (Il g) h refl = Il (ccutscut-vass Δ₀ f g h refl)
ccutscut-vass Δ₀ f (⊗l {B = B} g) h refl = ⊗l (ccutscut-vass (B ∷ Δ₀) f g h refl)
ccutscut-vass Δ₀ {Δ'} f (ex {Γ = Γ} {Δ} g) h eq with cases++2 Δ₀ Γ Δ' Δ eq
ccutscut-vass {Γ = Γ} Δ₀ {.(Γ₀ ++ B ∷ A₁ ∷ Δ)} {Δ''} {A} f (ex {Γ = .(Δ₀ ++ A ∷ Γ₀)} {Δ} {A₁} {B} g) h refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀ (B ∷ A₁ ∷ Δ ++ Δ'') A =
  ex {Γ = Δ₀ ++ Γ ++ Γ₀} (ccutscut-vass Δ₀ f g h refl)
ccutscut-vass .(Γ ++ B ∷ A₁ ∷ Γ₀) {Δ'} {Δ''} {A} f (ex {Γ = Γ} {.(Γ₀ ++ A ∷ Δ')} {A₁} {B} g) h refl | inj₂ (inj₁ (Γ₀ , refl , refl))
  rewrite cases++-inj₂ ( B ∷ A₁ ∷ Γ₀) Γ (Δ' ++ Δ'') A =
  ex (ccutscut-vass (Γ ++ _ ∷ _ ∷ Γ₀) f g h refl)
ccutscut-vass {Γ = Γ} Δ₀ {.(A₁ ∷ Δ)} {Δ''} {A} f (ex {Γ = Δ₀} {Δ} {A₁} g) h refl | inj₂ (inj₂ (inj₁ (refl , refl , refl)))
  rewrite cases++-inj₂ [] Δ₀ (A₁ ∷ Δ ++ Δ'') A =
  cong-ex-fma-cxt Γ (ccutscut-vass (Δ₀ ++ _ ∷ []) f g h refl)
  ∙ ≡-to-≗ (sym (scut-ex-fma-cxt Γ _ _))
ccutscut-vass {Γ = Γ₁} .(Γ ++ B ∷ []) {Δ'} {Δ''} {A} f (ex {Γ = Γ} {Δ'} {B = B} g) h refl | inj₂ (inj₂ (inj₂ (refl , refl , refl)))
  rewrite cases++-inj₂ (B ∷ []) Γ (Δ' ++ Δ'') A =
  cong-ex-cxt-fma Γ₁ (ccutscut-vass Γ f g h refl)
  ∙ ≡-to-≗ (sym (scut-ex-cxt-fma Γ₁ _ _))

ccutccut-vass Γ₀ Δ₀ f g ax r = ⊥-elim ([]disj∷ Δ₀ r)
ccutccut-vass Γ₀ Δ₀ f g (uf h) r with cases∷ Δ₀ r
ccutccut-vass Γ₀ .[] f g (uf h) r | inj₁ (refl , refl , refl) = ccutscut-vass Γ₀ f g h refl
ccutccut-vass Γ₀ .(_ ∷ Δ₀) f g (uf h) r | inj₂ (Δ₀ , refl , refl) = uf (ccutccut-vass Γ₀ Δ₀ f g h refl)
ccutccut-vass Γ₀ Δ₀ f g Ir r = ⊥-elim ([]disj∷ Δ₀ r)
ccutccut-vass Γ₀ Δ₀ {Δ'} f g (⊗r {Γ = Γ}{Δ} h h') r with cases++ Δ₀ Γ Δ' Δ r
ccutccut-vass Γ₀ Δ₀ {_}{Γ'}{A} f g (⊗r {Δ = Δ} h h') r | inj₁ (Λ₀ , refl , refl) with cases++ (Δ₀ ++ Γ₀) (Δ₀ ++ Γ₀ ++ A ∷ Γ' ++ Λ₀) (Γ' ++ Λ₀ ++ Δ) Δ refl
ccutccut-vass Γ₀ Δ₀ {_}{Γ'} f g (⊗r {Δ = Δ} h h') r | inj₁ (Λ₀ , refl , refl) | inj₁ (Λ₀' , p , q) with canc++ (Γ' ++ Λ₀) Λ₀' {Δ} q
ccutccut-vass {Γ = Γ} Γ₀ Δ₀ {.(Λ₀ ++ Δ)} {Γ'} {_} f g (⊗r {_} {.(Δ₀ ++ _ ∷ Λ₀)} {Δ} h h') r | inj₁ (Λ₀ , refl , refl) | inj₁ (.(Γ' ++ Λ₀) , refl , refl) | refl =
  ⊗r {Γ = Δ₀ ++ Γ₀ ++ Γ ++ Γ' ++ Λ₀}{Δ} (ccutccut-vass Γ₀ Δ₀ f g h refl) refl
ccutccut-vass Γ₀ Δ₀ {_}{Γ'} f g (⊗r {Δ = Δ} h h') r | inj₁ (Λ₀ , refl , refl) | inj₂ (Λ₀' , p , q) = ⊥-elim (canc⊥3 (Γ' ++ Λ₀) Δ Λ₀' p)
ccutccut-vass Γ₀ _ {Δ'}{Γ'}{A} f g (⊗r {Γ = Γ} h h') r | inj₂ (Λ₀ , refl , refl) with cases++ (Γ ++ Λ₀ ++ Γ₀) Γ (Γ' ++ Δ') (Λ₀ ++ Γ₀ ++ A ∷ Γ' ++ Δ') refl
ccutccut-vass Γ₀ .(Γ ++ Λ₀) {Δ'} {Γ'} {A} f g (⊗r {Γ = Γ} {.(Λ₀ ++ _ ∷ Δ')} h h') r | inj₂ (Λ₀ , refl , refl) | inj₁ (Λ₀' , p , q) = ⊥-elim (canc⊥4 Γ {Λ₀'}{Λ₀ ++ Γ₀} p)
ccutccut-vass Γ₀ .(Γ ++ Λ₀) {Δ'} {Γ'} {A} f g (⊗r {Γ = Γ} {.(Λ₀ ++ _ ∷ Δ')} h h') r | inj₂ (Λ₀ , refl , refl) | inj₂ (Λ₀' , p , q) with ++canc {xs = Λ₀ ++ Γ₀}{Λ₀'} Γ q
ccutccut-vass Γ₀ .(Γ ++ Λ₀) {Δ'} {Γ'} {A} f g (⊗r {Γ = Γ} {.(Λ₀ ++ _ ∷ Δ')} h h') r | inj₂ (Λ₀ , refl , refl) | inj₂ (.(Λ₀ ++ Γ₀) , refl , refl) | refl = ⊗r refl (ccutccut-vass Γ₀ Λ₀ f g h' refl)
ccutccut-vass Γ₀ Δ₀ f g (Il h) refl = Il (ccutccut-vass Γ₀ Δ₀ f g h refl)
ccutccut-vass Γ₀ Δ₀ f g (⊗l {B = B} h) refl = ⊗l (ccutccut-vass Γ₀ (B ∷ Δ₀) f g h refl)
ccutccut-vass Γ₀ Δ₀ {Δ'} f g (ex {Γ = Γ} {Δ} h) r with cases++2 Δ₀ Γ Δ' Δ r
ccutccut-vass {Γ = Γ} Γ₀ Δ₀ {.(Λ₀ ++ B ∷ A₁ ∷ Δ)} {Γ'} {A} f g (ex {Γ = .(Δ₀ ++ _ ∷ Λ₀)} {Δ} {A₁} {B} h) refl | inj₁ (Λ₀ , refl , refl)
  rewrite cases++-inj₁ (Δ₀ ++ Γ₀) (Γ' ++ Λ₀) (B ∷ A₁ ∷ Δ) A =
  ex {Γ = Δ₀ ++ Γ₀ ++ Γ ++ Γ' ++ Λ₀} (ccutccut-vass Γ₀ Δ₀ f g h refl)
ccutccut-vass Γ₀ .(Γ ++ B ∷ A₁ ∷ Λ₀) {Δ'} {Γ'} {A} f g (ex {Γ = Γ} {.(Λ₀ ++ _ ∷ Δ')} {A₁} {B} h) refl | inj₂ (inj₁ (Λ₀ , refl , refl))
  rewrite cases++-inj₂ (B ∷ A₁ ∷ Λ₀ ++ Γ₀) Γ (Γ' ++ Δ') A =
  ex (ccutccut-vass Γ₀ (Γ ++ _ ∷ _ ∷ Λ₀) f g h refl)
ccutccut-vass {Γ = Γ} Γ₀ Δ₀ {.(_ ∷ Δ)} {Γ'} {A = A} f g (ex {Γ = Δ₀} {Δ} {A₁} h) refl | inj₂ (inj₂ (inj₁ (refl , refl , refl))) =
  proof≗
    ccut (Δ₀ ++ Γ₀) f (ex-fma-cxt (Γ₀ ++ _ ∷ Γ') (ccut (Δ₀ ++ _ ∷ []) g h refl)) refl
  ≗〈 ≡-to-≗ (cong (λ z → ccut (Δ₀ ++ Γ₀) f z refl) (ex-fma-cxt++ Γ₀ (_ ∷ Γ') (ccut (Δ₀ ++ _ ∷ []) g h refl))) 〉 
    ccut (Δ₀ ++ Γ₀) f (ex-fma-cxt {Γ = Δ₀ ++ Γ₀ ++ _ ∷ []} Γ' (ex {Γ = Δ₀ ++ Γ₀} (ex-fma-cxt Γ₀ (ccut (Δ₀ ++ _ ∷ []) g h refl)))) refl
  ≗〈 ≡-to-≗ (ccut-ex-fma-cxt2 (Δ₀ ++ Γ₀) Γ' f _) 〉 
    ex-fma-cxt {Γ = Δ₀ ++ Γ₀ ++ Γ} Γ' (ccut (Δ₀ ++ Γ₀) f (ex {Γ = Δ₀ ++ Γ₀} (ex-fma-cxt Γ₀ (ccut (Δ₀ ++ _ ∷ []) g h refl))) refl)
  ≗〈 cong-ex-fma-cxt Γ' (≡-to-≗ lem) 〉 
    ex-fma-cxt {Γ = Δ₀ ++ Γ₀ ++ Γ} Γ' (ex-fma-cxt {Γ = Δ₀ ++ Γ₀} Γ (ex-fma-cxt Γ₀ (ccut (Δ₀ ++ _ ∷ Γ₀) f (ccut (Δ₀ ++ _ ∷ []) g h refl) refl)))
  ≗〈 cong-ex-fma-cxt Γ' (≡-to-≗ (sym (ex-fma-cxt++ Γ₀ Γ _))) 〉 
    ex-fma-cxt {Γ = Δ₀ ++ Γ₀ ++ Γ} Γ' (ex-fma-cxt (Γ₀ ++ Γ) (ccut (Δ₀ ++ _ ∷ Γ₀) f (ccut (Δ₀ ++ _ ∷ []) g h refl) refl))
  ≗〈 ≡-to-≗ (sym (ex-fma-cxt++ (Γ₀ ++ Γ) Γ' _)) 〉 
    ex-fma-cxt (Γ₀ ++ Γ ++ Γ') (ccut (Δ₀ ++ _ ∷ Γ₀) f (ccut (Δ₀ ++ _ ∷ []) g h refl) refl)
  ≗〈 cong-ex-fma-cxt (Γ₀ ++ Γ ++ Γ') (ccutccut-vass Γ₀ (Δ₀ ++ _ ∷ []) f g h refl) 〉 
    _
  qed≗
  where
    lem : ccut (Δ₀ ++ Γ₀) f (ex {Γ = Δ₀ ++ Γ₀} (ex-fma-cxt Γ₀ (ccut (Δ₀ ++ _ ∷ []) g h refl))) refl
          ≡ ex-fma-cxt {Γ = Δ₀ ++ Γ₀} Γ (ex-fma-cxt Γ₀ (ccut (Δ₀ ++ _ ∷ Γ₀) f (ccut (Δ₀ ++ _ ∷ []) g h refl) refl))
    lem rewrite cases++-inj₂ [] (Δ₀ ++ Γ₀) (A₁ ∷ Γ' ++ Δ) A =
      cong (ex-fma-cxt Γ) (ccut-ex-fma-cxt2' Δ₀ Γ₀ f _)
ccutccut-vass {Γ = Γ₁} Γ₀ .(Γ ++ _ ∷ []) {Δ'} {Γ'} {A = A} f g (ex {Γ = Γ} {Δ'} {_}{B} h) refl | inj₂ (inj₂ (inj₂ (refl , refl , refl))) =
  proof≗
    ccut (Γ ++ _ ∷ Γ₀) f (ex-cxt-fma (Γ₀ ++ _ ∷ Γ') (ccut Γ g h refl)) refl
  ≗〈 ≡-to-≗ (cong (λ z → ccut (Γ ++ _ ∷ Γ₀) f z refl) (ex-cxt-fma++ Γ₀ (_ ∷ Γ') _)) 〉
    ccut (Γ ++ _ ∷ Γ₀) f (ex-cxt-fma Γ₀ (ex {Γ = Γ ++ Γ₀} (ex-cxt-fma {Γ = Γ ++ Γ₀ ++ _ ∷ []} Γ' (ccut Γ g h refl)))) refl
  ≗〈 ≡-to-≗ (ccut-ex-cxt-fma2' Γ Γ₀ f _)  〉
    ex-cxt-fma {Γ = Γ}{Γ₁ ++ Γ' ++ Δ'} Γ₀ (ccut (Γ ++ Γ₀ ++ _ ∷ []) f (ex {Γ = Γ ++ Γ₀} (ex-cxt-fma {Γ = Γ ++ Γ₀ ++ _ ∷ []} Γ' (ccut Γ g h refl))) refl)
  ≗〈 cong-ex-cxt-fma Γ₀ (≡-to-≗ lem) 〉
    ex-cxt-fma {Γ = Γ} {Γ₁ ++ Γ' ++ Δ'} Γ₀ (ex-cxt-fma {Γ = Γ ++ Γ₀} Γ₁ (ex-cxt-fma {Γ = Γ ++ Γ₀ ++ Γ₁} Γ' (ccut (Γ ++ Γ₀) f (ccut Γ g h refl) refl)))
  ≗〈 cong-ex-cxt-fma Γ₀ (≡-to-≗ (sym (ex-cxt-fma++ {Γ = Γ ++ Γ₀} Γ₁ Γ' _))) 〉
    ex-cxt-fma {Γ = Γ} {Γ₁ ++ Γ' ++ Δ'} Γ₀ (ex-cxt-fma {Γ = Γ ++ Γ₀} (Γ₁ ++ Γ') (ccut (Γ ++ Γ₀) f (ccut Γ g h refl) refl))
  ≗〈 ≡-to-≗ (sym (ex-cxt-fma++ Γ₀ (Γ₁ ++ Γ') _)) 〉
    ex-cxt-fma (Γ₀ ++ Γ₁ ++ Γ') (ccut (Γ ++ Γ₀) f (ccut Γ g h refl) refl)
  ≗〈 cong-ex-cxt-fma (Γ₀ ++ Γ₁ ++ Γ') (ccutccut-vass Γ₀ Γ f g h refl) 〉
    _
  qed≗
  where
    lem : ccut (Γ ++ Γ₀ ++ _ ∷ []) f (ex {Γ = Γ ++ Γ₀} (ex-cxt-fma {Γ = Γ ++ Γ₀ ++ _ ∷ []} Γ' (ccut Γ g h refl))) refl
          ≡ ex-cxt-fma {Γ = Γ ++ Γ₀} Γ₁ (ex-cxt-fma {Γ = Γ ++ Γ₀ ++ Γ₁} Γ' (ccut (Γ ++ Γ₀) f (ccut Γ g h refl) refl))
    lem rewrite cases++-inj₂ (B ∷ []) (Γ ++ Γ₀) (Γ' ++ Δ') A =
                cong (ex-cxt-fma {Γ = Γ ++ Γ₀} Γ₁) (ccut-ex-cxt-fma2 (Γ ++ Γ₀) Γ' f _)
