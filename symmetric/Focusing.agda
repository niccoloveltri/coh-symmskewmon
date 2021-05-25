{-# OPTIONS --rewriting #-}

module Focusing where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities

open import Fsk
open import SeqCalc


-- =======================================================================

-- focused sequent calculus

StpR : Set
StpR = Maybe At

infix 15 _∣_⊢L_ _∣_⊢R_ _∣_；_⊢C_

mutual 
  data _∣_⊢L_ : Stp → Cxt → Fma → Set where
    uf : {Γ : Cxt} → {A C : Fma} → 
              just A ∣ Γ ⊢L C → nothing ∣ A ∷ Γ ⊢L C
    Il : {Γ : Cxt} → {C : Fma} → 
              nothing ∣ Γ ⊢L C → just I ∣ Γ ⊢L C 
    ⊗l : {Γ : Cxt} → {A B C : Fma} → 
              just A ∣ B ∷ [] ； Γ ⊢C C → just (A ⊗ B) ∣ Γ ⊢L C
    swRL :  {S : StpR} → {T : Stp} → mmap ` S ≡ T → 
              {Γ : Cxt} → {C : Fma} → 
              S ∣ Γ ⊢R C → T ∣ Γ ⊢L C

  data _∣_⊢R_ : StpR → Cxt → Fma → Set where
    ax : {X : At} → just X ∣ [] ⊢R ` X
    Ir : nothing ∣ [] ⊢R I
    ⊗r : {S : StpR} → {Γ Δ : Cxt} → {A B : Fma} → 
              S ∣ Γ ⊢R A → nothing ∣ Δ ⊢L B → S ∣ Γ ++ Δ ⊢R A ⊗ B 

  data _∣_；_⊢C_ : Stp → Cxt → Cxt → Fma → Set where
    ex : {S : Stp} {Φ Γ Δ Λ : Cxt} {A C : Fma} → 
         (f : S ∣ Φ ； Λ ⊢C C) (eq : Λ ≡ Γ ++ A ∷ Δ) → S ∣ Φ ++ A ∷ [] ； Γ ++ Δ ⊢C C
    swCL : {S : Stp} {Γ : Cxt} {C : Fma} → 
              (f : S ∣ Γ ⊢L C) → S ∣ [] ； Γ ⊢C C

-- =======================================================================

-- all the sequent calculus rules are admissible in phase C

ufC : ∀{Φ Γ A C} → just A ∣ Φ ； Γ ⊢C C → nothing ∣ A ∷ Φ ； Γ ⊢C C
ufC (ex f refl) = ex (ufC f) refl
ufC (swCL {Γ = Γ} f) = ex {Φ = []}{[]} (swCL (uf f)) refl

exC' : ∀{S} Φ {Ψ Γ Λ A B C} → S ∣ Λ ； Γ ⊢C C → Λ ≡ Φ ++ A ∷ B ∷ Ψ
  → S ∣ Φ ++ B ∷ A ∷ Ψ ； Γ ⊢C C 
exC' Φ {Ψ} {A = A} {B} (ex {Φ = Φ'} {A = A'} f eq') eq with cases++ Φ' Φ [] (A ∷ B ∷ Ψ) (sym eq)
... | inj₁ (Ψ₀ , p , q) = ⊥-elim ([]disj∷ Ψ₀ q)
exC' Φ {.[]} {A = A} {B} (ex {Φ = .(Φ₁ ++ _ ∷ [])} {Γ} {Δ} {A = B} (ex {Φ = Φ₁} {Γ₁} {Δ₁} f refl) eq') eq | inj₂ (A ∷ [] , refl , q) with snoc≡ Φ₁ Φ q | cases++ Γ Γ₁ Δ Δ₁ eq'
... | refl , refl | inj₁ (Γ₀ , refl , refl) = ex {Φ = Φ ++ B ∷ []} {Γ ++ Γ₀} (ex {Φ = Φ} {Γ} f refl) refl
... | refl , refl | inj₂ (Γ₀ , refl , refl) = ex {Φ = Φ ++ B ∷ []} {Γ₁} (ex {Φ = Φ}{Γ₁ ++ A ∷ Γ₀} f refl) refl
exC' Φ {.[]} {A = A} {B} (ex {Φ = .[]} {A = .B} (swCL f) eq') eq | inj₂ (A ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ q)
exC' Φ {A = A} {B} (ex {Φ = .(Φ ++ A ∷ B ∷ Ψ₀)} {Γ} {A = A'} f refl) eq | inj₂ (A ∷ B ∷ Ψ₀ , refl , refl) = ex {Φ = Φ ++ _ ∷ _ ∷ Ψ₀} {Γ} (exC' _ f refl) refl
exC' Φ (swCL f) eq = ⊥-elim ([]disj∷ Φ eq)

exC : ∀{S} Φ {Ψ Γ A B C} → S ∣ Φ ++ A ∷ B ∷ Ψ ； Γ ⊢C C
  → S ∣ Φ ++ B ∷ A ∷ Ψ ； Γ ⊢C C 
exC Φ f = exC' Φ f refl

ex-cxt-fmaC : {S : Stp} (Φ Λ : Cxt) {Ψ Γ : Cxt} {A C : Fma} → 
              S ∣ Φ ++ Λ ++ A ∷ Ψ ； Γ ⊢C C  → S ∣ Φ ++ A ∷ Λ ++ Ψ ； Γ ⊢C C
ex-cxt-fmaC Φ [] f = f
ex-cxt-fmaC Φ (x ∷ Λ) f = exC Φ (ex-cxt-fmaC (Φ ++ x ∷ []) Λ f)


IlC : ∀ {Γ Δ C} → nothing ∣ Γ ； Δ ⊢C C → just I ∣ Γ ； Δ ⊢C C 
IlC (ex f eq) = ex (IlC f) eq
IlC (swCL f) = swCL (Il f)

⊗lC' : ∀ {Γ Γ' Δ A B C} (f : just A ∣ Γ' ； Δ ⊢C C) (p : Γ' ≡ B ∷ Γ) → just (A ⊗ B) ∣ Γ ； Δ ⊢C C
⊗lC' (ex {Φ = []} f refl) refl = swCL (⊗l (ex f refl))
⊗lC' (ex {Φ = A' ∷ Φ} f refl) refl = ex (⊗lC' f refl) refl

⊗lC : ∀ {Γ Δ A B C} → just A ∣ B ∷ Γ ； Δ ⊢C C → just (A ⊗ B) ∣ Γ ； Δ ⊢C C
⊗lC f = ⊗lC' f refl

mutual
  ⊗rCL : {S : Stp} → {Φ Γ Δ : Cxt} → {A B : Fma}
    → S ∣ Φ ； Γ ⊢C A → nothing ∣ Δ ⊢L B
    → S ∣ Φ ； Γ ++ Δ ⊢C A ⊗ B
  ⊗rCL (ex {Φ = Φ} {Γ} f refl) g = ex {Φ = Φ} {Γ} (⊗rCL f g) refl
  ⊗rCL (swCL f) g = swCL (⊗rLL f g)

  ⊗rLL : {S : Stp} → {Γ Δ : Cxt} → {A B : Fma}
    → S ∣ Γ ⊢L A → nothing ∣ Δ ⊢L B
    → S ∣ Γ ++ Δ ⊢L A ⊗ B
  ⊗rLL (Il f) g = Il (⊗rLL f g)
  ⊗rLL (⊗l f) g = ⊗l (⊗rCL f g)
  ⊗rLL (uf f) g = uf (⊗rLL f g)
  ⊗rLL (swRL nS f) g = swRL nS (⊗r f g) 

⊗rC : ∀ {S Φ Ψ Γ A B}
  → S ∣ Φ ； [] ⊢C A → nothing ∣ Ψ ； Γ ⊢C B
  → S ∣ Φ ++ Ψ ； Γ ⊢C A ⊗ B
⊗rC {Φ = Φ} f (ex {Φ = Ψ} {Γ} g eq) = ex {Φ = Φ ++ Ψ} {Γ} (⊗rC f g) eq
⊗rC f (swCL g) = ⊗rCL f g

axC : {A : Fma} → just A ∣ [] ； [] ⊢C A
axC {` X} = swCL (swRL refl ax)
axC {I} = swCL (Il (swRL refl Ir))
axC {A ⊗ B} = ⊗lC (⊗rC axC (ufC axC))

-- =======================================================================

-- embedding focused derivations in the sequent calculus

mutual 
  embC : {S : Stp} → {Γ Δ : Cxt} → {C : Fma} →
              S ∣ Γ ； Δ ⊢C C → S ∣ Γ ++ Δ ⊢ C
  embC (ex {Γ = Γ} f refl) = ex-cxt-fma Γ (embC f)
  embC (swCL f) = embL f

  embL : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              S ∣ Γ ⊢L C → S ∣ Γ ⊢ C
  embL (Il f) = Il (embL f)
  embL (⊗l f) = ⊗l (embC f)
  embL (uf f) = uf (embL f)
  embL (swRL refl f) = embR f

  embR : {S : StpR} → {Γ : Cxt} → {C : Fma} →
              S ∣ Γ ⊢R C → mmap ` S ∣ Γ ⊢ C
  embR ax = ax
  embR Ir = Ir
  embR (⊗r f₁ f₂) = ⊗r (embR f₁) (embL f₂)

emb : {S : Stp} → {Γ : Cxt} → {C : Fma}
  → S ∣ Γ ； [] ⊢C C → S ∣ Γ ⊢ C
emb = embC


-- =======================================================================

-- the focusing function

focus : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              S ∣ Γ ⊢ C → S ∣ Γ ； [] ⊢C C
focus ax = axC
focus (uf f) = ufC (focus f) 
focus Ir = swCL (swRL refl Ir)
focus (⊗r f g) = ⊗rC (focus f) (focus g)
focus (Il f) = IlC (focus f)
focus (⊗l f) = ⊗lC (focus f)
focus (ex f) = exC _ (focus f)

-- =======================================================================

-- focusing is well-defined, i.e. it sends ≗-related derivations into
-- propositionally equal focused derivations

exCexC' : ∀{S Φ₁ Φ₂ Φ₃ Λ Δ A B A' B' C} (f : S ∣ Λ ； Δ ⊢C C)
  → (eq : Λ ≡ Φ₁ ++ A ∷ B ∷ Φ₂ ++ A' ∷ B' ∷ Φ₃)
  → exC' (Φ₁ ++ B ∷ A ∷ Φ₂) (exC' Φ₁ f eq) refl
    ≡ exC' Φ₁ (exC' (Φ₁ ++ A ∷ B ∷ Φ₂) f eq) refl
exCexC' {Φ₁ = Φ₁} {Φ₂} {Φ₃} {A = A} {B} {A'} {B'} (ex {Φ = Φ} f eq') eq with cases++ Φ Φ₁ [] (A ∷ B ∷ Φ₂ ++ A' ∷ B' ∷ Φ₃) (sym eq)
... | inj₁ (Ψ₀ , p , q) = ⊥-elim ([]disj∷ Ψ₀ q)
... | inj₂ (x ∷ [] , p , q) = ⊥-elim ([]disj∷ Φ₂ (sym (inj∷ (inj∷ p .proj₂) .proj₂)))
... | inj₂ (x ∷ x₁ ∷ Ψ₀ , p , q) with cases++ Ψ₀ Φ₂ [] (A' ∷ B' ∷ Φ₃) (inj∷ (inj∷ p .proj₂) .proj₂)
... | inj₁ (Ψ₀' , p' , q') = ⊥-elim ([]disj∷ Ψ₀' q')
exCexC' {Φ₁ = Φ₁} {Φ₂} {.[]} {A = x} {x₁} {A'} {B'} (ex {Φ = .(Φ ++ A ∷ [])} {Γ} {Δ} (ex {Φ = Φ} {Γ₁} {Δ₁} {A = A} f refl) eq') eq | inj₂ (x ∷ x₁ ∷ .(Φ₂ ++ A' ∷ []) , refl , q) | inj₂ (A' ∷ [] , refl , refl) with snoc≡ Φ (Φ₁ ++ _ ∷ _ ∷ Φ₂) q | cases++ Γ Γ₁ Δ Δ₁ eq'
exCexC' {Φ₁ = Φ₁} {Φ₂} {.[]} {_} {_} {x} {x₁} {A'} {B'} (ex {_} {.((Φ₁ ++ x ∷ x₁ ∷ Φ₂) ++ A' ∷ [])} {Γ} {.(Γ₀ ++ Δ₁)} (ex {Φ = .(Φ₁ ++ x ∷ x₁ ∷ Φ₂)} {.(Γ ++ B' ∷ Γ₀)} {Δ₁} {A = A'} f refl) refl) refl | inj₂ (x ∷ x₁ ∷ .(Φ₂ ++ A' ∷ []) , refl , refl) | inj₂ (A' ∷ [] , refl , refl) | refl , refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Φ₂) Φ₁ [] A' | cases++-inj₂ (A' ∷ []) (Φ₁ ++ x₁ ∷ x ∷ Φ₂) [] B' |
          cases++-inj₂ (x₁ ∷ x ∷ Φ₂) Φ₁ [] A' | cases++-inj₂ (A' ∷ []) (Φ₁ ++ x ∷ x₁ ∷ Φ₂) [] B' |
          snoc≡-refl (Φ₁ ++ x₁ ∷ x ∷ Φ₂) A' | snoc≡-refl (Φ₁ ++ x ∷ x₁ ∷ Φ₂) A' |
          cases++-inj₁ Γ Γ₀ Δ₁ B' | cases++-inj₂ (x ∷ x₁ ∷ Φ₂ ++ B' ∷ []) Φ₁ [] A' | cases++-inj₂ (x ∷ x₁ ∷ Φ₂) Φ₁ [] B' = refl
exCexC' {Φ₁ = Φ₁} {Φ₂} {.[]} {_} {_} {x} {x₁} {A'} {B'} (ex {_} {.((Φ₁ ++ x ∷ x₁ ∷ Φ₂) ++ A' ∷ [])} {.(Γ₁ ++ Γ₀)} {Δ} (ex {Φ = .(Φ₁ ++ x ∷ x₁ ∷ Φ₂)} {Γ₁} {.(Γ₀ ++ B' ∷ Δ)} {A = .A'} f refl) refl) refl | inj₂ (x ∷ x₁ ∷ .(Φ₂ ++ A' ∷ []) , refl , refl) | inj₂ (A' ∷ [] , refl , refl) | refl , refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Φ₂) Φ₁ [] A' | cases++-inj₂ (A' ∷ []) (Φ₁ ++ x₁ ∷ x ∷ Φ₂) [] B' |
          cases++-inj₂ (x₁ ∷ x ∷ Φ₂) Φ₁ [] A' | cases++-inj₂ (A' ∷ []) (Φ₁ ++ x ∷ x₁ ∷ Φ₂) [] B' |
          snoc≡-refl (Φ₁ ++ x₁ ∷ x ∷ Φ₂) A' | snoc≡-refl (Φ₁ ++ x ∷ x₁ ∷ Φ₂) A' |
          cases++-inj₂ Γ₀ Γ₁ Δ B' | cases++-inj₂ (x ∷ x₁ ∷ Φ₂ ++ B' ∷ []) Φ₁ [] A' | cases++-inj₂ (x ∷ x₁ ∷ Φ₂) Φ₁ [] B' = refl
exCexC' {Φ₁ = Φ₁} {Φ₂} {.[]} {A = A} {B} {A'} {B'} (ex {Φ = .[]} (swCL f) eq') eq | inj₂ (x ∷ x₁ ∷ Ψ₀ , p , q) | inj₂ (A' ∷ [] , refl , q') = ⊥-elim ([]disj∷ Φ₁ q)
exCexC' {Φ₁ = Φ₁} {Φ₂} {.(Ψ₀' ++ A ∷ [])} {A = x} {x₁} {A'} {B'} (ex {Φ = .(Φ₁ ++ x ∷ x₁ ∷ Φ₂ ++ A' ∷ B' ∷ Ψ₀')} {Γ} {Δ} {A = A} f refl) refl | inj₂ (x ∷ x₁ ∷ .(Φ₂ ++ A' ∷ B' ∷ Ψ₀') , refl , refl) | inj₂ (A' ∷ B' ∷ Ψ₀' , refl , refl)
  rewrite cases++-inj₂ (A' ∷ B' ∷ Ψ₀') (Φ₁ ++ x ∷ x₁ ∷ Φ₂) [] A | cases++-inj₂ (x ∷ x₁ ∷ Φ₂ ++ B' ∷ A' ∷ Ψ₀') Φ₁ [] A |
          cases++-inj₂ (A' ∷ B' ∷ Ψ₀') (Φ₁ ++ x₁ ∷ x ∷ Φ₂) [] A | cases++-inj₂ (x₁ ∷ x ∷ Φ₂ ++ B' ∷ A' ∷ Ψ₀') Φ₁ [] A =
            cong (λ y → ex {Φ = Φ₁ ++ _ ∷ _ ∷ Φ₂ ++ _ ∷ _ ∷ Ψ₀'} {Γ} {Δ} y refl) (exCexC' f refl)
exCexC' {Φ₁ = Φ₁} (swCL f) eq = ⊥-elim ([]disj∷ Φ₁ eq)

exCexC : ∀{S Φ₁ Φ₂ Φ₃ Δ A B A' B' C}
  → (f : S ∣ Φ₁ ++ A ∷ B ∷ Φ₂ ++ A' ∷ B' ∷ Φ₃ ； Δ ⊢C C)
  → exC (Φ₁ ++ B ∷ A ∷ Φ₂) (exC Φ₁ f)
    ≡ exC Φ₁ (exC (Φ₁ ++ A ∷ B ∷ Φ₂) f)
exCexC f = exCexC' f refl

exC-iso' : ∀{S Φ Ψ Λ Δ A B C} (f : S ∣ Λ ； Δ ⊢C C)
  → (eq : Λ ≡ Φ ++ A ∷ B ∷ Ψ)
  → exC' Φ (exC' Φ f eq) refl ≡ subst (λ x → S ∣ x ； Δ ⊢C C) eq f
exC-iso' {Φ = Φ} {Ψ} {A = A} {B} (ex {Φ = Φ₁} f eq') eq with cases++ Φ₁ Φ [] (A ∷ B ∷ Ψ) (sym eq)
... | inj₁ (Φ₀ , p , q) = ⊥-elim ([]disj∷ Φ₀ q)
exC-iso' {Φ = Φ} {A = A} {B} (ex {Γ = Γ} {Δ} (ex {Φ = Φ₁} {Γ = Γ₁} {Δ₁} f refl) eq') eq | inj₂ (A ∷ [] , refl , q) with snoc≡ Φ₁ Φ q | cases++ Γ Γ₁ Δ Δ₁ eq'
exC-iso' {Φ = Φ} {A = A} {B} (ex {Γ = Γ} (ex {Φ = Φ} {Δ = Δ₁} f refl) refl) refl | inj₂ (A ∷ [] , refl , q) | refl , refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (B ∷ []) Φ [] A | snoc≡-refl Φ B | cases++-inj₂ Γ₀ Γ Δ₁ A = refl
exC-iso' {Φ = Φ} {A = A} {B} (ex {Δ = Δ} (ex {Γ = Γ₁} f refl) refl) refl | inj₂ (A ∷ [] , refl , q) | refl , refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (B ∷ []) Φ [] A | snoc≡-refl Φ B | cases++-inj₁ Γ₁ Γ₀ Δ A = refl
exC-iso' {Φ = Φ} (ex (swCL f) eq') eq | inj₂ (A ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ q)
exC-iso' {Φ = Φ} {A = A} {B} (ex {A = A₁} f refl) refl | inj₂ (A ∷ B ∷ Φ₀ , refl , refl)
  rewrite cases++-inj₂ (B ∷ A ∷ Φ₀) Φ [] A₁ = cong (λ y → ex {Φ = Φ ++ A ∷ B ∷ Φ₀} y refl) (exC-iso' f refl)
exC-iso' {Φ = Φ} (swCL f) eq = ⊥-elim ([]disj∷ Φ eq)

exC-iso : ∀{S Φ Ψ Δ A B C} (f : S ∣ Φ ++ A ∷ B ∷ Ψ ； Δ ⊢C C)
  → exC Φ (exC Φ f) ≡ f
exC-iso f = exC-iso' f refl

⊗rCLufC : {Γ Δ Λ : Cxt}{A A' B : Fma}
  → (f : just A' ∣ Γ ； Δ ⊢C A)(g : nothing ∣ Λ ⊢L B)
  → ⊗rCL (ufC f) g ≡ ufC (⊗rCL f g)
⊗rCLufC (ex f refl) g = cong (λ x → ex x refl) (⊗rCLufC f g)
⊗rCLufC (swCL f) g = refl

⊗rCufC : {Γ Δ Λ : Cxt}{A A' B : Fma}
  → (f : just A' ∣ Γ ； [] ⊢C A)(g : nothing ∣ Δ ； Λ ⊢C B)
  → ⊗rC (ufC f) g ≡ ufC (⊗rC f g)
⊗rCufC f (ex g refl) = cong (λ x → ex x refl) (⊗rCufC f g)
⊗rCufC f (swCL g) = ⊗rCLufC f g

⊗rCLIlC : {Γ Δ Λ : Cxt}{A B : Fma}
  → (f : nothing ∣ Γ ； Δ ⊢C A)(g : nothing ∣ Λ ⊢L B)
  → ⊗rCL (IlC f) g ≡ IlC (⊗rCL f g)
⊗rCLIlC (ex f refl) g = cong (λ x → ex x refl) (⊗rCLIlC f g)
⊗rCLIlC (swCL f) g = refl

⊗rCIlC : {Γ Δ Λ : Cxt}{A B : Fma}
  → (f : nothing ∣ Γ ； [] ⊢C A)(g : nothing ∣ Δ ； Λ ⊢C B)
  → ⊗rC (IlC f) g ≡ IlC (⊗rC f g)
⊗rCIlC {Γ} f (ex {Φ = Φ} g refl) = cong (λ x → ex {Φ = Γ ++ Φ} x refl) (⊗rCIlC f g)
⊗rCIlC f (swCL g) = ⊗rCLIlC f g

⊗rCL⊗lC : {Γ Γ' Δ Λ : Cxt}{A A' B B' : Fma}
  → (f : just A' ∣ Γ' ； Δ ⊢C A)(g : nothing ∣ Λ ⊢L B)
  → (eq : Γ' ≡ B' ∷ Γ)
  → ⊗rCL (⊗lC' f eq) g ≡ ⊗lC' (⊗rCL f g) eq
⊗rCL⊗lC (ex {Φ = []} f refl) g refl = refl
⊗rCL⊗lC (ex {Φ = x ∷ Φ} f refl) g refl = cong (λ x → ex x refl) (⊗rCL⊗lC f g refl)

⊗rC⊗lC : {Γ Δ Λ : Cxt}{A A' B B' : Fma}
  → (f : just A' ∣ B' ∷ Γ ； [] ⊢C A)(g : nothing ∣ Δ ； Λ ⊢C B)
  → ⊗rC (⊗lC f) g ≡ ⊗lC (⊗rC f g)
⊗rC⊗lC {Γ} f (ex {Φ = Φ} g refl) = cong (λ x → ex {Φ = Γ ++ Φ} x refl) (⊗rC⊗lC f g)
⊗rC⊗lC f (swCL g) = ⊗rCL⊗lC f g refl

exCufC : ∀ {Φ Ψ Δ Λ A A' B C}
  → (f : just A' ∣ Λ ； Δ ⊢C C)
  → (eq : Λ ≡ Φ ++ A ∷ B ∷ Ψ)
  → exC' (A' ∷ Φ) (ufC f) (cong (A' ∷_) eq)
    ≡ ufC (exC' Φ f eq)
exCufC {Φ} {Ψ} {A = A} {B = B} (ex {Φ = Φ₁} f eq₁) eq with cases++ Φ₁ Φ [] (A ∷ B ∷ Ψ) (sym eq)
... | inj₁ (Φ₀ , p , q) = ⊥-elim ([]disj∷ Φ₀ q)
exCufC {Φ} {.[]} {A = A} {B = B} (ex {Φ = .(Φ₁ ++ _ ∷ [])} {Γ} {Δ} (ex {Φ = Φ₁} {Γ₁} {Δ₁} f refl) eq₁) eq | inj₂ (A ∷ [] , refl , q) with snoc≡ Φ₁ Φ q | cases++ Γ Γ₁ Δ Δ₁ eq₁
exCufC {Φ} {.[]} {_} {_} {A} {B = B} (ex {_} {.(Φ ++ _ ∷ [])} {Γ} {.(Γ₀ ++ Δ₁)} (ex {Φ = .Φ} {.(Γ ++ B ∷ Γ₀)} {Δ₁} f refl) refl) refl | inj₂ (A ∷ [] , refl , refl) | refl , refl | inj₁ (Γ₀ , refl , refl) rewrite cases++-inj₂ (A ∷ []) Φ [] B | snoc≡-refl Φ A | cases++-inj₁ Γ Γ₀ Δ₁ B = refl
exCufC {Φ} {.[]} {_} {_} {A} {B = B} (ex {_} {.(Φ ++ _ ∷ [])} {.(Γ₁ ++ Γ₀)} {Δ} (ex {Φ = .Φ} {Γ₁} {.(Γ₀ ++ B ∷ Δ)} f refl) refl) refl | inj₂ (A ∷ [] , refl , refl) | refl , refl | inj₂ (Γ₀ , refl , refl) rewrite cases++-inj₂ (A ∷ []) Φ [] B | snoc≡-refl Φ A | cases++-inj₂ Γ₀ Γ₁ Δ B = refl
exCufC {Φ} {.[]} {A = A} {B = B} (ex {Φ = .[]} (swCL f) eq₁) eq | inj₂ (A ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ q)
exCufC {Φ} {.(Φ₀ ++ A₁ ∷ [])} {A = A} {B = B} (ex {Φ = .(Φ ++ A ∷ B ∷ Φ₀)} {A = A₁} f refl) refl | inj₂ (A ∷ B ∷ Φ₀ , refl , refl)
  rewrite cases++-inj₂ (A ∷ B ∷ Φ₀) Φ [] A₁ = cong (λ x → ex x refl) (exCufC f refl)
exCufC {Φ} (swCL f) eq = ⊥-elim ([]disj∷ Φ eq)

exCIlC : ∀ {Φ Ψ Δ Λ A B C}
  → (f : nothing ∣ Λ ； Δ ⊢C C)
  → (eq : Λ ≡ Φ ++ A ∷ B ∷ Ψ)
  → exC' Φ (IlC f) eq ≡ IlC (exC' Φ f eq)
exCIlC {Φ} {Ψ} {A = A} {B} (ex {Φ = Φ₁} f eq₁) eq with cases++ Φ₁ Φ [] (A ∷ B ∷ Ψ) (sym eq)
... | inj₁ (Φ₀ , p , q) = ⊥-elim ([]disj∷ Φ₀ q)
exCIlC {Φ} {.[]} {A = A} {B} (ex {Φ = .(Φ₁ ++ _ ∷ [])} {Γ} {Δ} (ex {Φ = Φ₁} {Γ₁} {Δ₁} f refl) eq₁) eq | inj₂ (A ∷ [] , refl , q) with snoc≡ Φ₁ Φ q | cases++ Γ Γ₁ Δ Δ₁ eq₁
exCIlC {Φ} {.[]} {_} {_} {A} {B} (ex {_} {.(Φ ++ _ ∷ [])} {Γ} {.(Γ₀ ++ Δ₁)} (ex {Φ = .Φ} {.(Γ ++ B ∷ Γ₀)} {Δ₁} f refl) refl) refl | inj₂ (A ∷ [] , refl , refl) | refl , refl | inj₁ (Γ₀ , refl , refl) = refl
exCIlC {Φ} {.[]} {_} {_} {A} {B} (ex {_} {.(Φ ++ _ ∷ [])} {.(Γ₁ ++ Γ₀)} {Δ} (ex {Φ = .Φ} {Γ₁} {.(Γ₀ ++ B ∷ Δ)} f refl) refl) refl | inj₂ (A ∷ [] , refl , refl) | refl , refl | inj₂ (Γ₀ , refl , refl) = refl
exCIlC {Φ} {.[]} {A = A} {B} (ex {Φ = .[]} (swCL f) eq₁) eq | inj₂ (A ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ q)
exCIlC {Φ} {.(Φ₀ ++ _ ∷ [])} {A = A} {B} (ex {Φ = .(Φ ++ A ∷ B ∷ Φ₀)} f refl) refl | inj₂ (A ∷ B ∷ Φ₀ , refl , refl) = cong (λ x → ex {Φ = Φ ++ _ ∷ _ ∷ Φ₀} x refl) (exCIlC f refl)
exCIlC {Φ} (swCL f) eq = ⊥-elim ([]disj∷ Φ eq)

exC⊗lC : ∀ {Φ Ψ Δ Λ A' B' A B C}
  → (f : just A' ∣ Λ ； Δ ⊢C C)
  → (eq : Λ ≡ B' ∷ Φ ++ A ∷ B ∷ Ψ)
  → exC' Φ (⊗lC' f eq) refl ≡ ⊗lC' (exC' (_ ∷ Φ) f eq) refl
exC⊗lC {Φ} {Ψ} {B' = B'} {A} {B} (ex {Φ = Φ₁} f eq₁) eq with cases++ Φ₁ (B' ∷ Φ) [] (A ∷ B ∷ Ψ) (sym eq)
... | inj₁ (Φ₀ , p , q) = ⊥-elim ([]disj∷ Φ₀ q)
exC⊗lC {Φ} {.[]} {B' = B'} {A} {B} (ex {Φ = .(Φ₁ ++ _ ∷ [])} {Γ} {Δ} (ex {Φ = Φ₁} {Γ₁} {Δ₁} f refl) eq₁) eq | inj₂ (A ∷ [] , refl , q) with snoc≡ Φ₁ (B' ∷ Φ) q | cases++ Γ Γ₁ Δ Δ₁ eq₁
exC⊗lC {Φ} {.[]} {B' = B'} {A} {B} (ex {_} {.((B' ∷ Φ) ++ _ ∷ [])} {Γ} {.(Γ₀ ++ Δ₁)} (ex {Φ = .(B' ∷ Φ)} {.(Γ ++ B ∷ Γ₀)} {Δ₁} f refl) refl) refl | inj₂ (A ∷ [] , refl , q) | refl , refl | inj₁ (Γ₀ , refl , refl) rewrite cases++-inj₂ (A ∷ []) Φ [] B | snoc≡-refl Φ A | cases++-inj₁ Γ Γ₀ Δ₁ B = refl
exC⊗lC {Φ} {.[]} {B' = B'} {A} {B} (ex {_} {.((B' ∷ Φ) ++ _ ∷ [])} {.(Γ₁ ++ Γ₀)} {Δ} (ex {Φ = .(B' ∷ Φ)} {Γ₁} {.(Γ₀ ++ B ∷ Δ)} f refl) refl) refl | inj₂ (A ∷ [] , refl , refl) | refl , refl | inj₂ (Γ₀ , refl , refl) rewrite cases++-inj₂ (A ∷ []) Φ [] B | snoc≡-refl Φ A | cases++-inj₂ Γ₀ Γ₁ Δ B = refl
exC⊗lC {Φ} {.(Φ₀ ++ A₁ ∷ [])} {B' = B'} {A} {B} (ex {Φ = .(B' ∷ Φ ++ A ∷ B ∷ Φ₀)} {A = A₁} f refl) refl | inj₂ (A ∷ B ∷ Φ₀ , refl , refl)
  rewrite cases++-inj₂  (A ∷ B ∷ Φ₀) Φ [] A₁ = cong (λ x → ex {Φ = Φ ++ _ ∷ _ ∷ Φ₀} x refl) (exC⊗lC f refl)

exC⊗rCL₁ : ∀{S Φ₁ Φ₂ Γ Λ Δ A' B' A B}
  → (f : S ∣ Λ ； Γ ⊢C A) (g : nothing ∣ Δ ⊢L B)
  → (eq : Λ ≡ Φ₁ ++ A' ∷ B' ∷ Φ₂)
  → exC' Φ₁ (⊗rCL f g) eq ≡ ⊗rCL (exC' Φ₁ f eq) g
exC⊗rCL₁ {Φ₁ = Φ₁} {Φ₂} {A' = A'} {B'} (ex {Φ = Φ} f eq₁) g eq with cases++ Φ Φ₁ [] (A' ∷ B' ∷ Φ₂) (sym eq)
... | inj₁ (Φ₀ , p , q) = ⊥-elim ([]disj∷ Φ₀ q)
exC⊗rCL₁ {Φ₁ = Φ₁} {.[]} {A' = A'} {B'} (ex {Φ = .(Φ ++ _ ∷ [])} {Γ} {Δ} (ex {Φ = Φ} {Γ₁} {Δ₁} f refl) eq₁) g eq | inj₂ (A' ∷ [] , refl , q) with snoc≡ Φ Φ₁ q | cases++ Γ Γ₁ Δ Δ₁ eq₁
exC⊗rCL₁ {Φ₁ = Φ₁} {.[]} {Δ = Δ} {A'} {B'} (ex {_} {.(Φ₁ ++ _ ∷ [])} {Γ} {.(Γ₀ ++ Δ₁)} (ex {Φ = Φ₁} {.(Γ ++ B' ∷ Γ₀)} {Δ₁} f refl) refl) g refl | inj₂ (A' ∷ [] , refl , refl) | refl , refl | inj₁ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ (A' ∷ []) Φ₁ [] B' | snoc≡-refl Φ₁ A' | cases++-inj₁ Γ Γ₀ (Δ₁ ++ Δ) B' = refl
exC⊗rCL₁ {Φ₁ = Φ₁} {.[]} {Δ = Δ₁} {A'} {B'} (ex {_} {.(Φ₁ ++ _ ∷ [])} {.(Γ₁ ++ Γ₀)} {Δ} (ex {Φ = Φ₁} {Γ₁} {.(Γ₀ ++ B' ∷ Δ)} f refl) refl) g refl | inj₂ (A' ∷ [] , refl , refl) | refl , refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (A' ∷ []) Φ₁ [] B' | snoc≡-refl Φ₁ A' | cases++-inj₂ Γ₀ Γ₁  (Δ ++ Δ₁) B' = refl
exC⊗rCL₁ {Φ₁ = Φ₁} {.[]} {A' = A'} {B'} (ex {Φ = .[]} (swCL f) eq₁) g eq | inj₂ (A' ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ₁ q)
exC⊗rCL₁ {Φ₁ = Φ₁} {.(Φ₀ ++ A ∷ [])} {A' = A'} {B'} (ex {Φ = .(Φ₁ ++ A' ∷ B' ∷ Φ₀)} {A = A} f refl) g refl | inj₂ (A' ∷ B' ∷ Φ₀ , refl , refl)
  rewrite cases++-inj₂ (A' ∷ B' ∷ Φ₀) Φ₁ [] A = cong (λ x → ex {Φ = Φ₁ ++ B' ∷ A' ∷ Φ₀} x refl) (exC⊗rCL₁ f g refl)
exC⊗rCL₁ {Φ₁ = Φ₁} (swCL f) g eq = ⊥-elim ([]disj∷ Φ₁ eq)

exC⊗rC₁ : ∀{S Φ₁ Φ₂ Ψ Δ A' B' A B}
  → (f : S ∣ Φ₁ ++ A' ∷ B' ∷ Φ₂ ； [] ⊢C A) (g : nothing ∣ Ψ ； Δ ⊢C B)
  → exC Φ₁ (⊗rC f g) ≡ ⊗rC (exC Φ₁ f) g
exC⊗rC₁ {Φ₁ = Φ₁} {Φ₂} {A' = A'} {B'} f (ex {Φ = Φ} {Γ} {A = A} g refl)
  rewrite cases++-inj₂ (A' ∷ B' ∷ Φ₂ ++ Φ) Φ₁ [] A =
  cong (λ x → ex {Φ = Φ₁ ++ _ ∷ _ ∷ Φ₂ ++ Φ} x refl) (exC⊗rC₁ f g)
exC⊗rC₁ f (swCL g) = exC⊗rCL₁ f g refl

exC⊗rC₂ : ∀{S Φ₁ Φ₂ Ψ Λ Δ A' B' A B}
  → (f : S ∣ Ψ ； [] ⊢C A) (g : nothing ∣ Λ ； Δ ⊢C B)
  → (eq : Λ ≡ Φ₁ ++ A' ∷ B' ∷ Φ₂)
  → exC' (Ψ ++ Φ₁) (⊗rC f g) (cong (Ψ ++_) eq) ≡ ⊗rC f (exC' Φ₁ g eq)
exC⊗rC₂ {Φ₁ = Φ₁} {Φ₂} {Ψ} {A' = A'} {B'} f (ex {Φ = Φ} {A = A} g eq₁) eq with cases++ Φ Φ₁ [] (A' ∷ B' ∷ Φ₂) (sym eq)
... | inj₁ (Φ₀ , p , q) = ⊥-elim ([]disj∷ Φ₀ q)
exC⊗rC₂ {Φ₁ = Φ₁} {.[]} {Ψ} {A' = A'} {B'} f (ex {Φ = .(Φ ++ _ ∷ [])} {Γ} {Δ} {A = B'} (ex {Φ = Φ} {Γ₁} {Δ₁} g refl) eq₁) eq | inj₂ (A' ∷ [] , refl , q) with snoc≡ Φ Φ₁ q | cases++ Γ Γ₁ Δ Δ₁ eq₁
exC⊗rC₂ {Φ₁ = Φ₁} {.[]} {Ψ} {_} {_} {A'} {B'} f (ex {_} {.(Φ₁ ++ _ ∷ [])} {Γ} {.(Γ₀ ++ Δ₁)} (ex {Φ = .Φ₁} {.(Γ ++ B' ∷ Γ₀)} {Δ₁} g refl) refl) refl | inj₂ (A' ∷ [] , refl , refl) | refl , refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (A' ∷ []) (Ψ ++ Φ₁) [] B' | snoc≡-refl (Ψ ++ Φ₁) A' | cases++-inj₁ Γ Γ₀ Δ₁ B' = refl
exC⊗rC₂ {Φ₁ = Φ₁} {.[]} {Ψ} {_} {_} {A'} {B'} f (ex {_} {.(Φ₁ ++ _ ∷ [])} {.(Γ₁ ++ Γ₀)} {Δ} (ex {Φ = .Φ₁} {Γ₁} {.(Γ₀ ++ B' ∷ Δ)} g refl) refl) refl | inj₂ (A' ∷ [] , refl , refl) | refl , refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (A' ∷ []) (Ψ ++ Φ₁) [] B' | snoc≡-refl (Ψ ++ Φ₁) A' | cases++-inj₂ Γ₀ Γ₁ Δ B' = refl
exC⊗rC₂ {Φ₁ = Φ₁} {.[]} {Ψ} {A' = A'} {B'} f (ex {Φ = .[]} {A = .B'} (swCL f₁) eq₁) eq | inj₂ (A' ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ₁ q)
exC⊗rC₂ {Φ₁ = Φ₁} {.(Φ₀ ++ A ∷ [])} {Ψ} {A' = A'} {B'} f (ex {Φ = .(Φ₁ ++ A' ∷ B' ∷ Φ₀)} {Γ} {A = A} g refl) refl | inj₂ (A' ∷ B' ∷ Φ₀ , refl , refl)
  rewrite cases++-inj₂ (A' ∷ B' ∷ Φ₀) (Ψ ++ Φ₁) [] A =
  cong (λ x → ex {Φ = Ψ ++ Φ₁ ++ B' ∷ A' ∷ Φ₀} x refl) (exC⊗rC₂ f g refl)
exC⊗rC₂ {Φ₁ = Φ₁} f (swCL f₁) eq = ⊥-elim ([]disj∷ Φ₁ eq)

exC-braid : ∀{S Φ A B C Λ Ψ Δ D}
  → (f : S ∣ Λ ； Δ ⊢C D)
  → (eq : Λ ≡ Φ ++ A ∷ B ∷ C ∷ Ψ)
  → exC Φ (exC (Φ ++ B ∷ []) (exC' Φ f eq))
    ≡ exC (Φ ++ C ∷ []) (exC Φ (exC' (Φ ++ A ∷ []) f eq))
exC-braid {Φ = Φ} {A} {B} {C} {Ψ = Ψ} (ex {Φ = Φ₁} f eq₁) eq with cases++ Φ₁ Φ [] (A ∷ B ∷ C ∷ Ψ) (sym eq)
... | inj₁ (Φ₀ , p , q) = ⊥-elim ([]disj∷ Φ₀ q)
exC-braid {Φ = Φ} {A} {B} {C} {Ψ = .[]} (ex {Φ = .((Φ₁ ++ _ ∷ []) ++ _ ∷ [])} (ex (ex {Φ = Φ₁} f refl) eq₂) eq₁) eq | inj₂ (A ∷ B ∷ [] , refl , q) with snoc≡ (Φ₁ ++ _ ∷ []) (Φ ++ A ∷ []) q
... | q' , refl with snoc≡ Φ₁ Φ q'
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ _ ∷ []) ++ B ∷ [])} {Γ} {Δ} (ex {Γ = Γ₁} {Δ₁} (ex {Φ = Φ} f refl) eq₂) eq₁) eq | inj₂ (A ∷ B ∷ [] , refl , refl) | q' , refl | refl , refl with cases++ Γ Γ₁ Δ Δ₁ eq₁
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {Γ} {.(Γ₀ ++ Δ₁)} (ex {Γ = .(Γ ++ C ∷ Γ₀)} {Δ₁} (ex {Φ = Φ} {Γ₁} {Δ} f refl) eq₂) refl) eq | inj₂ (A ∷ B ∷ [] , refl , refl) | q' , refl | refl , refl | inj₁ (Γ₀ , refl , refl) with cases++ (Γ ++ C ∷ Γ₀) Γ₁ Δ₁ Δ eq₂
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {Γ} {.(Γ₀ ++ Γ₀' ++ Δ)} (ex {_} {_} {.(Γ ++ C ∷ Γ₀)} {.(Γ₀' ++ Δ)} (ex {Φ = Φ} {.(Γ ++ C ∷ Γ₀ ++ B ∷ Γ₀')} {Δ} f refl) refl) refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C |
          snoc≡-refl Φ A | cases++-inj₁ (Γ ++ C ∷ Γ₀) Γ₀' Δ B |
          snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₁ Γ (Γ₀ ++ Γ₀') Δ C |
          cases++-inj₂ (B ∷ C ∷ []) Φ [] A | cases++-inj₂ (B ∷ []) Φ [] C |
          snoc≡-refl Φ B | cases++-inj₁ Γ Γ₀ (Γ₀' ++ A ∷ Δ) C |
          cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₁ Γ Γ₀ (Γ₀' ++ Δ) C |
          cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) Φ [] C | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B |
          snoc≡-refl Φ A | cases++-inj₁ Γ (Γ₀ ++ B ∷ Γ₀') Δ C |
          snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₁ (Γ ++ Γ₀) Γ₀' Δ B = refl
... | inj₂ (Γ₀' , refl , q) with cases++ Γ Γ₁ Γ₀ Γ₀' (sym q)
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {Γ} {.((Γ₀'' ++ Γ₀') ++ Δ₁)} (ex {_} {_} {.(Γ ++ C ∷ Γ₀'' ++ Γ₀')} {Δ₁} (ex {Φ = Φ} {.(Γ ++ C ∷ Γ₀'')} {.(Γ₀' ++ B ∷ Δ₁)} f refl) refl) refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₁ (.(Γ₀'' ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl) | inj₁ (Γ₀'' , refl , refl) 
  rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C |
          snoc≡-refl Φ A | cases++-inj₂ Γ₀' (Γ ++ C ∷ Γ₀'') Δ₁ B |
          snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₁ Γ Γ₀'' (Γ₀' ++ Δ₁) C |
          cases++-inj₂ (B ∷ C ∷ []) Φ [] A | cases++-inj₂ (B ∷ []) Φ [] C |
          snoc≡-refl Φ B | cases++-inj₁ Γ (Γ₀'' ++ A ∷ Γ₀') Δ₁ C |
          cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₁ Γ (Γ₀'' ++ Γ₀') Δ₁ C |
          cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B | cases++-inj₂ (A ∷ []) Φ [] C |
          snoc≡-refl Φ A | cases++-inj₁ Γ Γ₀'' (Γ₀' ++ B ∷ Δ₁) C |
          snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₂ Γ₀' (Γ ++ Γ₀'') Δ₁ B = refl
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {.(Γ₁ ++ Γ₀'')} {.(Γ₀ ++ Δ₁)} (ex {_} {_} {.((Γ₁ ++ Γ₀'') ++ C ∷ Γ₀)} {Δ₁} (ex {Φ = Φ} {Γ₁} {.((Γ₀'' ++ C ∷ Γ₀) ++ B ∷ Δ₁)} f refl) refl) refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₁ (Γ₀ , refl , refl) | inj₂ (.(Γ₀'' ++ C ∷ Γ₀) , refl , refl) | inj₂ (Γ₀'' , refl , refl) 
  rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C | snoc≡-refl Φ A | cases++-inj₂ (Γ₀'' ++ C ∷ Γ₀) Γ₁ Δ₁ B |
          snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₂ Γ₀'' Γ₁ (Γ₀ ++ Δ₁) C | cases++-inj₂ (B ∷ C ∷ []) Φ [] A |
          cases++-inj₂ (B ∷ []) Φ [] C | snoc≡-refl Φ B | cases++-inj₁ (Γ₁ ++ A ∷ Γ₀'') Γ₀ Δ₁ C |
          cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₁ (Γ₁ ++ Γ₀'') Γ₀ Δ₁ C |
          cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) Φ [] C | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B |
          snoc≡-refl Φ A | cases++-inj₂ Γ₀'' Γ₁ (Γ₀ ++ B ∷ Δ₁) C |
          snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₂ (Γ₀'' ++ Γ₀) Γ₁ Δ₁ B = refl
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {.(Γ₁ ++ Γ₀)} {Δ} (ex {Γ = Γ₁} {.(Γ₀ ++ C ∷ Δ)} (ex {Φ = Φ} {Γ} {Δ₁} f refl) eq₂) refl) eq | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₂ (Γ₀ , refl , refl) with cases++ Γ₁ Γ (Γ₀ ++ C ∷ Δ) Δ₁ eq₂
... | inj₁ (Γ₀' , refl , q) with cases++ Γ₀ Γ₀' Δ Δ₁ (sym q)
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {.(Γ₁ ++ Γ₀)} {.(Γ₀'' ++ Δ₁)} (ex {Γ = Γ₁} {.(Γ₀ ++ C ∷ Γ₀'' ++ Δ₁)} (ex {Φ = Φ} {.(Γ₁ ++ B ∷ Γ₀ ++ C ∷ Γ₀'')} {Δ₁} f refl) refl) refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₂ (Γ₀ , refl , refl) | inj₁ (.(Γ₀ ++ C ∷ Γ₀'') , refl , refl) | inj₁ (Γ₀'' , refl , refl) 
  rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C | snoc≡-refl Φ A | cases++-inj₁ Γ₁ (Γ₀ ++ C ∷ Γ₀'') Δ₁ B |
          snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₁ (Γ₁ ++ Γ₀) Γ₀'' Δ₁ C | cases++-inj₂ (B ∷ C ∷ []) Φ [] A |
          cases++-inj₂ (B ∷ []) Φ [] C | snoc≡-refl Φ B | cases++-inj₂ Γ₀ Γ₁ (Γ₀'' ++ A ∷ Δ₁) C |
          cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₂ Γ₀ Γ₁ (Γ₀'' ++ Δ₁) C |
          cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B | cases++-inj₂ (A ∷ []) Φ [] C |
          snoc≡-refl Φ A | cases++-inj₁ (Γ₁ ++ B ∷ Γ₀) Γ₀'' Δ₁ C |
          snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₁ Γ₁ (Γ₀ ++ Γ₀'') Δ₁ B = refl
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {.(Γ₁ ++ Γ₀' ++ Γ₀'')} {Δ} (ex {Γ = Γ₁} {.((Γ₀' ++ Γ₀'') ++ C ∷ Δ)} (ex {Φ = Φ} {.(Γ₁ ++ B ∷ Γ₀')} {.(Γ₀'' ++ C ∷ Δ)} f refl) refl) refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₂ (.(Γ₀' ++ Γ₀'') , refl , refl) | inj₁ (Γ₀' , refl , refl) | inj₂ (Γ₀'' , refl , refl)
  rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C | snoc≡-refl Φ A | cases++-inj₁ Γ₁ Γ₀' (Γ₀'' ++ C ∷ Δ) B |
          snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₂ Γ₀'' (Γ₁ ++ Γ₀') Δ C | cases++-inj₂ (B ∷ C ∷ []) Φ [] A |
          cases++-inj₂ (B ∷ []) Φ [] C | snoc≡-refl Φ B | cases++-inj₂ (Γ₀' ++ A ∷ Γ₀'') Γ₁ Δ C |
          cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₂ (Γ₀' ++ Γ₀'') Γ₁ Δ C |
          cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) Φ [] C | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B |
          snoc≡-refl Φ A | cases++-inj₂ (Γ₀'') (Γ₁ ++ B ∷ Γ₀') Δ C |
          snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₁ Γ₁ Γ₀' (Γ₀'' ++ Δ) B = refl
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {.((Γ ++ Γ₀') ++ Γ₀)} {Δ} (ex {Γ = .(Γ ++ Γ₀')} {.(Γ₀ ++ C ∷ Δ)} (ex {Φ = Φ} {Γ} {.(Γ₀' ++ B ∷ Γ₀ ++ C ∷ Δ)} f refl) refl) refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl) 
  rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C | snoc≡-refl Φ A | cases++-inj₂ Γ₀' Γ (Γ₀ ++ C ∷ Δ) B |
          snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₂ (Γ₀' ++ Γ₀) Γ Δ C | cases++-inj₂ (B ∷ C ∷ []) Φ [] A |
          cases++-inj₂ (B ∷ []) Φ [] C | snoc≡-refl Φ B | cases++-inj₂ Γ₀ (Γ ++ A ∷ Γ₀') Δ C |
          cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₂ Γ₀ (Γ ++ Γ₀') Δ C |
          cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B | cases++-inj₂ (A ∷ []) Φ [] C |
          snoc≡-refl Φ A | cases++-inj₂ (Γ₀' ++ B ∷ Γ₀) Γ Δ C |
          snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₂ Γ₀' Γ (Γ₀ ++ Δ) B = refl
exC-braid {Φ = x ∷ Φ} {A} {B} {C} {Ψ = .[]} (ex {Φ = .([] ++ _ ∷ [])} (ex (swCL f) eq₂) eq₁) eq | inj₂ (A ∷ B ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ (inj∷ q .proj₂))
exC-braid {Φ = Φ} {A} {B} {C} {Ψ = .[]} (ex {Φ = .[]} (swCL f) eq₁) eq | inj₂ (A ∷ B ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ q)
exC-braid {Φ = Φ} {A} {B} {C} {Ψ = .(Φ₀ ++ A₁ ∷ [])} (ex {Φ = .(Φ ++ A ∷ B ∷ C ∷ Φ₀)} {Γ} {Δ} {A = A₁} f refl) refl | inj₂ (A ∷ B ∷ C ∷ Φ₀ , refl , refl) 
  rewrite cases++-inj₂ (B ∷ C ∷ Φ₀) (Φ ++ A ∷ []) [] A₁ | cases++-inj₂ (A ∷ C ∷ B ∷ Φ₀) Φ [] A₁ |
          cases++-inj₂ (C ∷ A ∷ B ∷ Φ₀) (Φ ++ C ∷ []) [] A₁ | cases++-inj₂ (A ∷ C ∷ Φ₀) (Φ ++ B ∷ []) [] A₁ |
          cases++-inj₂ (B ∷ C ∷ A ∷ Φ₀) Φ [] A₁ | cases++-inj₂ (A ∷ B ∷ Φ₀) (Φ ++ C ∷ []) [] A₁ =
          cong (λ x → ex {Φ = Φ ++ C ∷ B ∷ A ∷ Φ₀} {Γ}{Δ} x refl) (exC-braid f refl)
exC-braid {Φ = Φ} (swCL f) eq = ⊥-elim ([]disj∷ Φ eq)


focus-compat : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              {f g : S ∣ Γ ⊢ C} → f ≗ g → focus f ≡ focus g
focus-compat refl = refl
focus-compat (~ p) = sym (focus-compat p)
focus-compat (p ∙ p₁) = trans (focus-compat p) (focus-compat p₁)
focus-compat (uf p) = cong ufC (focus-compat p)
focus-compat (⊗l p) = cong ⊗lC (focus-compat p)
focus-compat (Il p) = cong IlC (focus-compat p)
focus-compat (⊗r p p₁) = cong₂ ⊗rC (focus-compat p) (focus-compat p₁)
focus-compat axI = refl
focus-compat ax⊗ = refl
focus-compat (⊗ruf {f = f} {g}) = ⊗rCufC (focus f) (focus g)
focus-compat (⊗rIl {f = f} {g}) = ⊗rCIlC (focus f) (focus g)
focus-compat (⊗r⊗l {f = f} {g}) = ⊗rC⊗lC (focus f) (focus g)
focus-compat (ex p) = cong (exC _) (focus-compat p)
focus-compat (exex {f = f}) = exCexC (focus f)
focus-compat (exuf {f = f}) = exCufC (focus f) refl
focus-compat (exIl {f = f}) = exCIlC (focus f) refl
focus-compat (ex⊗l {f = f}) = exC⊗lC (focus f) refl
focus-compat (ex⊗r₁ {f = f} {g}) = exC⊗rC₁ (focus f) (focus g)
focus-compat (ex⊗r₂ {f = f} {g}) = exC⊗rC₂ (focus f) (focus g) refl
focus-compat ex-iso = exC-iso _
focus-compat (ex-braid {Γ = Γ} {Δ} {f = f}) = exC-braid {Φ = Γ} (focus f) refl

-- =======================================================================

-- focus and emb are each other inverses

act : {S : Stp} (Φ : Cxt) {Γ : Cxt} {A C : Fma}
  → (f : S ∣ Φ ； A ∷ Γ ⊢C C)
  → S ∣ Φ ++ A ∷ [] ； Γ ⊢C C
act Φ f = ex {Γ = []} f refl

act⋆ : {S : Stp} (Φ Γ : Cxt) {Δ : Cxt} {C : Fma}
  → (f : S ∣ Φ ； Γ ++ Δ ⊢C C)
  → S ∣ Φ ++ Γ ； Δ ⊢C C
act⋆ _ [] f = f
act⋆ Φ (A ∷ Γ) f = act⋆ (Φ ++ A ∷ []) Γ (act Φ f)

focus-ex-cxt-fma : ∀{S} Φ Γ {A Δ C}
  → (f : S ∣ Φ ++ Γ ++ A ∷ Δ ⊢ C)
  → focus (ex-cxt-fma Γ f) ≡ ex-cxt-fmaC Φ Γ (focus f)
focus-ex-cxt-fma Φ [] f = refl
focus-ex-cxt-fma Φ (x ∷ Γ) f =
  cong (exC Φ) (focus-ex-cxt-fma (Φ ++ x ∷ []) Γ f)

exC-act⋆ : ∀{S} Φ Γ {Ψ Δ A B C}
  → (f : S ∣ Φ ++ B ∷ A ∷ Ψ ； Γ ++ Δ ⊢C C)
  → exC Φ (act⋆ (Φ ++ B ∷ A ∷ Ψ) Γ {Δ} f)
    ≡ act⋆ (Φ ++ A ∷ B ∷ Ψ) Γ (exC Φ f)
exC-act⋆ Φ [] f = refl
exC-act⋆ Φ (A' ∷ Γ) {Ψ} {Δ} f with exC-act⋆ Φ Γ {Ψ ++ A' ∷ []} {Δ} (act (Φ ++ _ ∷ _ ∷ Ψ) f)
exC-act⋆ Φ (A' ∷ Γ) {Ψ} {Δ} {A} {B} f | p rewrite cases++-inj₂ (B ∷ A ∷ Ψ) Φ [] A' = p

ex-cxt-fmaC-act⋆ : ∀{S} Φ Γ {Δ A C}
  → (f : S ∣ Φ ； Γ ++ A ∷ Δ ⊢C C)
  → ex-cxt-fmaC Φ Γ (act⋆ Φ (Γ ++ A ∷ Δ) f)
     ≡ act⋆ (Φ ++ A ∷ []) (Γ ++ Δ) {[]} (ex {Φ = Φ}{Γ} f refl) 
ex-cxt-fmaC-act⋆ Φ [] f = refl
ex-cxt-fmaC-act⋆ Φ (B ∷ Γ) {Δ} {A} f =
  begin
    exC Φ (ex-cxt-fmaC (Φ ++ B ∷ []) Γ (act⋆ (Φ ++ B ∷ []) (Γ ++ _ ∷ Δ) (act Φ f)))
  ≡⟨ cong (exC Φ {Γ ++ Δ} {[]}) (ex-cxt-fmaC-act⋆ (Φ ++ B ∷ []) Γ {Δ} (act Φ f)) ⟩
    exC Φ (act⋆ (Φ ++ B ∷ A ∷ []) (Γ ++ Δ) (ex {Φ = Φ ++ B ∷ []} {Γ} {Δ} (ex {Φ = Φ} {[]} f refl) refl))
  ≡⟨ exC-act⋆ Φ (Γ ++ Δ) (ex {Φ = Φ ++ B ∷ []} {Γ} {Δ} (ex {Φ = Φ} {[]} f refl) refl) ⟩
    act⋆ (Φ ++ A ∷ B ∷ []) (Γ ++ Δ) (exC Φ (ex {Φ = Φ ++ B ∷ []} {Γ} {Δ} (ex {Φ = Φ} {[]} f refl) refl))
  ≡⟨ cong (act⋆ (Φ ++ A ∷ B ∷ []) (Γ ++ Δ)) lem ⟩
    act⋆ (Φ ++ A ∷ B ∷ []) (Γ ++ Δ) {[]} (act (Φ ++ A ∷ []) (ex {Φ = Φ} {B ∷ Γ} f refl))
  ∎
  where
    lem : exC Φ (ex {Φ = Φ ++ B ∷ []} {Γ} {Δ} (ex {Φ = Φ} {[]} f refl) refl)
          ≡ act (Φ ++ A ∷ []) (ex {Φ = Φ} {B ∷ Γ} f refl)
    lem rewrite cases++-inj₂ (B ∷ []) Φ [] A |
                snoc≡-refl Φ B = refl

act⋆-ufC : ∀ Φ Γ {Δ A C}
  → (f : just A ∣ Φ ； Γ ++ Δ ⊢C C)
  → act⋆ (A ∷ Φ) Γ (ufC f) ≡ ufC {Γ = Δ} (act⋆ Φ Γ f)
act⋆-ufC Φ [] f = refl
act⋆-ufC Φ (B ∷ Γ) f = act⋆-ufC (Φ ++ B ∷ []) Γ (act Φ f)

act⋆-IlC : ∀ Φ Γ {Δ C}
  → (f : nothing ∣ Φ ； Γ ++ Δ ⊢C C)
  → act⋆ Φ Γ {Δ} (IlC f) ≡ IlC (act⋆ Φ Γ f)
act⋆-IlC Φ [] f = refl
act⋆-IlC Φ (A ∷ Γ) f = act⋆-IlC (Φ ++ A ∷ []) Γ (act Φ f)

act⋆-⊗lC : ∀ Φ Γ {Δ A B C}
  → (f : just A ∣ B ∷ Φ ； Γ ++ Δ ⊢C C)
  → act⋆ Φ Γ {Δ} (⊗lC f) ≡ ⊗lC (act⋆ (B ∷ Φ) Γ f)
act⋆-⊗lC Φ [] f = refl
act⋆-⊗lC Φ (A ∷ Γ) f = act⋆-⊗lC (Φ ++ A ∷ []) Γ _

⊗lC-eq : ∀{Φ Γ A B C}
  → (f : just A ∣ Φ ； Γ ⊢C C)
  → (eq : Φ ≡ B ∷ [])
  → swCL (⊗l (subst (λ x → just A ∣ x ； Γ ⊢C C) eq f)) ≡ ⊗lC' f eq
⊗lC-eq (ex {Φ = []} f refl) refl = refl
⊗lC-eq (ex {Φ = x ∷ Φ} f eq₁) eq = ⊥-elim ([]disj∷ Φ (sym (inj∷ eq .proj₂)))

act⋆-⊗rC : ∀ {S Φ} Ψ Γ {Δ A B}
  → (f : S ∣ Φ ； [] ⊢C A) (g : nothing ∣ Ψ ； Γ ++ Δ ⊢C B)
  → act⋆ (Φ ++ Ψ) Γ {Δ} (⊗rC f g) ≡ ⊗rC f (act⋆ Ψ Γ g)
act⋆-⊗rC Ψ [] f g = refl
act⋆-⊗rC Ψ (D ∷ Γ) f g = act⋆-⊗rC (Ψ ++ D ∷ []) Γ f _

act⋆-⊗rCL : ∀ {S} Φ Γ {Δ Λ A B}
  → (f : S ∣ Φ ； Γ ++ Δ ⊢C A) (g : nothing ∣ Λ ⊢L B)
  → act⋆ Φ Γ {Δ ++ Λ} (⊗rCL f g) ≡ ⊗rCL (act⋆ Φ Γ f) g
act⋆-⊗rCL Φ [] f g = refl
act⋆-⊗rCL Φ (D ∷ Γ) f g = act⋆-⊗rCL (Φ ++ D ∷ []) Γ _ _

act⋆act⋆ : {S : Stp} (Φ Γ : Cxt) {Δ Λ : Cxt} {C : Fma}
  → (f : S ∣ Φ ； Γ ++ Δ ++ Λ ⊢C C)
  → act⋆ (Φ ++ Γ) Δ {Λ} (act⋆ Φ Γ {Δ ++ Λ} f)
    ≡ act⋆ Φ (Γ ++ Δ) f
act⋆act⋆ Φ [] f = refl
act⋆act⋆ Φ (B ∷ Γ) {Δ}{Λ} f = act⋆act⋆ (Φ ++ B ∷ []) Γ {Δ}{Λ} _

mutual 
  focus-embC : {S : Stp} → {Γ Δ : Cxt} → {C : Fma}
    → (f : S ∣ Γ ； Δ ⊢C C)
    → focus (embC f) ≡ act⋆ Γ Δ f
  focus-embC (ex {Φ = Φ} {Γ}{Δ} {A = A} f refl) =
    begin
      focus (ex-cxt-fma Γ (embC f))
    ≡⟨ focus-ex-cxt-fma Φ Γ (embC f) ⟩
      ex-cxt-fmaC Φ Γ (focus (embC f)) 
    ≡⟨ cong (ex-cxt-fmaC Φ Γ) (focus-embC f) ⟩
      ex-cxt-fmaC Φ Γ (act⋆ Φ (Γ ++ A ∷ Δ) f)
    ≡⟨ ex-cxt-fmaC-act⋆ Φ Γ f ⟩
      act⋆ (Φ ++ A ∷ []) (Γ ++ Δ) (ex {Φ = Φ}{Γ} f refl)
    ∎
  focus-embC (swCL f) = focus-embL f

  focus-embL : {S : Stp} → {Γ : Cxt} → {C : Fma}
    → (f : S ∣ Γ ⊢L C)
    → focus (embL f) ≡ act⋆ [] Γ (swCL f)
  focus-embL (uf {Γ} f) =
    trans (cong ufC (focus-embL f))
          (sym (act⋆-ufC [] Γ (swCL f)))
  focus-embL (Il {Γ} f) = 
    trans (cong IlC (focus-embL f))
          (sym (act⋆-IlC [] Γ (swCL f)))
  focus-embL (⊗l {Γ} f) =
      trans (cong ⊗lC (focus-embC f))
            (sym (trans (cong (act⋆ [] Γ) (⊗lC-eq f refl))
                        (act⋆-⊗lC [] Γ f)))
  focus-embL (swRL refl f) = focus-embR f 

  focus-embR : {S : StpR} → {Γ : Cxt} → {C : Fma}
    → (f : S ∣ Γ ⊢R C)
    → focus (embR f) ≡ act⋆ [] Γ (swCL (swRL refl f))
  focus-embR ax = refl
  focus-embR Ir = refl
  focus-embR (⊗r {Γ = Γ} {Δ} f g) = 
    trans (cong₂ ⊗rC (focus-embR f) (focus-embL g))
   (trans (sym (act⋆-⊗rC [] Δ _ _))
   (trans (cong (act⋆ Γ Δ) (sym (act⋆-⊗rCL [] Γ _ _)))
          (act⋆act⋆ [] Γ {Δ} _)))


embC-exC' : ∀{S Φ Ψ Δ Λ A B C}
  → (f : S ∣ Λ ； Δ ⊢C C)
  → (eq : Λ ≡ Φ ++ A ∷ B ∷ Ψ)
  → embC (exC' Φ f eq) ≗ ex {Γ = Φ} (embC (subst (λ x → S ∣ x ； Δ ⊢C C) eq f))
embC-exC' {Φ = Φ} {Ψ} {A = A} {B} (ex {Φ = Φ₁} f eq') eq with cases++ Φ₁ Φ [] (A ∷ B ∷ Ψ) (sym eq)
... | inj₁ (Φ₀ , p , q) = ⊥-elim ([]disj∷ Φ₀ q)
embC-exC' {Φ = Φ} {.[]} {A = A} {B} (ex {Φ = .(Φ₁ ++ _ ∷ [])} {Γ} {Δ} (ex {Φ = Φ₁} {Γ₁} {Δ₁} f refl) eq') eq | inj₂ (A ∷ [] , refl , q) with snoc≡ Φ₁ Φ q | cases++ Γ Γ₁ Δ Δ₁ eq'
embC-exC' {Φ = Φ} {.[]} {_} {_} {A} {B} (ex {_} {.(Φ ++ _ ∷ [])} {Γ} {.(Γ₀ ++ Δ₁)} (ex {Φ = Φ} {.(Γ ++ B ∷ Γ₀)} {Δ₁} f refl) refl) refl | inj₂ (A ∷ [] , refl , refl) | refl , refl | inj₁ (Γ₀ , refl , refl) =
  proof≗
    ex-cxt-fma {Γ = Φ ++ B ∷ []} (Γ ++ Γ₀) (ex-cxt-fma {Γ = Φ} Γ (embC f)) 
  ≗〈 ≡-to-≗ (ex-cxt-fma++ {Γ = Φ ++ B ∷ []} Γ Γ₀ _) 〉
    ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ (ex-cxt-fma {Γ = Φ ++ B ∷ Γ} Γ₀ (ex-cxt-fma {Γ = Φ} Γ (embC f)))
  ≗〈 cong-ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ (ex-cxt-fma-ex-cxt-fma Γ Γ₀) 〉
    ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ (ex-cxt-fma {Γ = Φ} Γ (ex-cxt-fma {Γ = Φ ++ Γ ++ B ∷ []} Γ₀ (embC f)))
  ≗〈 cong-ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ (cong-ex-cxt-fma {Γ = Φ} Γ (~ (ex-iso {Γ = Φ ++ Γ}))) 〉
    ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ (ex-cxt-fma {Γ = Φ} Γ (ex {Γ = Φ ++ Γ} (ex {Γ = Φ ++ Γ} (ex-cxt-fma {Γ = Φ ++ Γ ++ B ∷ []} Γ₀ (embC f)))))
  ≗〈 ~ ex-cxt-fma-braid {Γ = Φ} Γ 〉
    ex (ex-cxt-fma {Γ = Φ ++ A ∷ []} Γ (ex-cxt-fma {Γ = Φ} Γ (ex {Γ = Φ ++ Γ} (ex-cxt-fma {Γ = Φ ++ Γ ++ B ∷ []} Γ₀ (embC f)))))
  ≗〈 ≡-to-≗ (sym (cong ex (cong (ex-cxt-fma {Γ = Φ ++ A ∷ []} Γ) (ex-cxt-fma++ {Γ = Φ} Γ (B ∷ Γ₀) _)))) 〉
    ex (ex-cxt-fma {Γ = Φ ++ A ∷ []} Γ (ex-cxt-fma {Γ = Φ} (Γ ++ B ∷ Γ₀) (embC f)))
  qed≗
embC-exC' {Φ = Φ} {.[]} {_} {_} {A} {B} (ex {_} {.(Φ ++ _ ∷ [])} {.(Γ ++ Γ₀)} {Δ} (ex {Φ = Φ} {Γ} {.(Γ₀ ++ B ∷ Δ)} f refl) refl) refl | inj₂ (A ∷ [] , refl , refl) | refl , refl | inj₂ (Γ₀ , refl , refl) = 
  proof≗
    ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ (ex-cxt-fma {Γ = Φ} (Γ ++ A ∷ Γ₀) (embC f))
  ≗〈 ≡-to-≗ (cong (ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ) (ex-cxt-fma++ {Γ = Φ} Γ (A ∷ Γ₀) _)) 〉 
    ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ (ex-cxt-fma {Γ = Φ} Γ (ex {Γ = Φ ++ Γ} (ex-cxt-fma {Γ = Φ ++ Γ ++ A ∷ []} Γ₀ (embC f))))
  ≗〈 ~ ex-cxt-fma-braid {Γ = Φ} Γ 〉 
    ex (ex-cxt-fma {Γ = Φ ++ A ∷ []} Γ (ex-cxt-fma {Γ = Φ} Γ (ex-cxt-fma {Γ = Φ ++ Γ ++ A ∷ []} Γ₀ (embC f))) )
  ≗〈 ex (cong-ex-cxt-fma {Γ = Φ ++ A ∷ []} Γ (~ ex-cxt-fma-ex-cxt-fma Γ Γ₀)) 〉 
    ex (ex-cxt-fma {Γ = Φ ++ A ∷ []} Γ (ex-cxt-fma {Γ = Φ ++ A ∷ Γ} Γ₀ (ex-cxt-fma {Γ = Φ} Γ (embC f))))
  ≗〈 ≡-to-≗ (sym (cong ex (ex-cxt-fma++ {Γ = Φ ++ A ∷ []} Γ Γ₀ _))) 〉 
    ex (ex-cxt-fma {Γ = Φ ++ A ∷ []} (Γ ++ Γ₀) (ex-cxt-fma {Γ = Φ} Γ (embC f)))
  qed≗
embC-exC' {Φ = Φ} {.[]} {A = A} {B} (ex {Φ = .[]} (swCL f) eq') eq | inj₂ (A ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ q)
embC-exC' {Φ = Φ} {.(Φ₀ ++ _ ∷ [])} {A = A} {B} (ex {Φ = .(Φ ++ A ∷ B ∷ Φ₀)} {Γ} {Δ} f refl) refl | inj₂ (A ∷ B ∷ Φ₀ , refl , refl) =
  cong-ex-cxt-fma {Γ = Φ ++ _ ∷ _ ∷ Φ₀} Γ (embC-exC' f refl) ∙ ex-cxt-fma-ex Γ
embC-exC' {Φ = Φ} (swCL f) eq = ⊥-elim ([]disj∷ Φ eq)

embC-ufC : ∀{Φ Γ A C}
  → (f : just A ∣ Φ ； Γ ⊢C C)
  → embC (ufC f) ≗ uf (embC f)
embC-ufC (ex {Φ = Φ} {Γ} f refl) =
  cong-ex-cxt-fma Γ (embC-ufC f)
  ∙ ex-cxt-fma-uf Φ Γ
embC-ufC (swCL f) = refl

embC-IlC : ∀{Φ Γ C}
  → (f : nothing ∣ Φ ； Γ ⊢C C)
  → embC (IlC f) ≗ Il (embC f)
embC-IlC (ex {Φ = Φ} {Γ} f refl) =
  cong-ex-cxt-fma Γ (embC-IlC f)
  ∙ ex-cxt-fma-Il Φ Γ
embC-IlC (swCL f) = refl

embC-⊗lC : ∀{Φ Γ Λ A B C}
  → (f : just A ∣ Λ ； Γ ⊢C C)
  → (eq : Λ ≡ B ∷ Φ)
  → embC (⊗lC' f eq) ≗ ⊗l (embC (subst (λ x → just A ∣ x ； Γ ⊢C C) eq f))
embC-⊗lC (ex {Φ = []} f refl) refl = refl
embC-⊗lC (ex {Φ = x ∷ Φ}{Γ} f refl) refl = 
  cong-ex-cxt-fma Γ (embC-⊗lC f refl)
  ∙ ex-cxt-fma-⊗l Φ Γ

embC-⊗rLL : ∀{S Γ Δ A B}
  → (f : S ∣ Γ ⊢L A)
  → (g : nothing ∣ Δ ⊢L B)
  → embL (⊗rLL f g) ≗ ⊗r (embL f) (embL g)
embC-⊗rCL : ∀{S Φ Γ Δ A B}
  → (f : S ∣ Φ ； Γ ⊢C A)
  → (g : nothing ∣ Δ ⊢L B)
  → embC (⊗rCL f g) ≗ ⊗r (embC f) (embL g)

embC-⊗rLL (uf f) g =
  uf (embC-⊗rLL f g) ∙ ~ ⊗ruf
embC-⊗rLL (Il f) g = 
  Il (embC-⊗rLL f g) ∙ ~ ⊗rIl
embC-⊗rLL (⊗l f) g = 
  ⊗l (embC-⊗rCL f g) ∙ ~ ⊗r⊗l
embC-⊗rLL (swRL refl f) g = refl

embC-⊗rCL (ex {Γ = Γ} f refl) g =
  cong-ex-cxt-fma Γ (embC-⊗rCL f g)
  ∙ ex-cxt-fma-⊗r₁ _ Γ
embC-⊗rCL (swCL f) g = embC-⊗rLL f g
 
embC-⊗rC : ∀{S Φ Ψ Γ A B}
  → (f : S ∣ Φ ； [] ⊢C A)
  → (g : nothing ∣ Ψ ； Γ ⊢C B)
  → embC (⊗rC f g) ≗ ⊗r (embC f) (embC g)
embC-⊗rC {Φ = Φ} f (ex {Φ = Ψ} {Γ = Γ} g refl) =
  cong-ex-cxt-fma {Γ = Φ ++ Ψ} Γ (embC-⊗rC f g)
  ∙ ex-cxt-fma-⊗r₂ Ψ Γ
embC-⊗rC f (swCL g) = embC-⊗rCL f g

embC-axC : ∀ {A} → embC axC ≗ ax {A}
embC-axC {` X} = refl
embC-axC {I} = ~ axI
embC-axC {A ⊗ B} =
  embC-⊗lC (⊗rC axC (ufC axC)) refl
  ∙ ⊗l (embC-⊗rC axC (ufC axC)
       ∙ ⊗r embC-axC (embC-ufC axC ∙ uf embC-axC))
  ∙ (~ ax⊗)

emb-focus : {S : Stp} → {Γ : Cxt} → {C : Fma} →
             (f : S ∣ Γ ⊢ C)  → emb (focus f) ≗ f
emb-focus ax = embC-axC
emb-focus (uf f) = embC-ufC (focus f) ∙ uf (emb-focus f)
emb-focus (ex f) = embC-exC' (focus f) refl ∙ ex (emb-focus f)
emb-focus Ir = refl
emb-focus (⊗r f g) = embC-⊗rC (focus f) (focus g) ∙ ⊗r (emb-focus f) (emb-focus g)
emb-focus (Il f) = embC-IlC (focus f) ∙ Il (emb-focus f)
emb-focus (⊗l f) = embC-⊗lC (focus f) refl ∙ ⊗l (emb-focus f)


