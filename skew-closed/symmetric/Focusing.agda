{-# OPTIONS --rewriting #-}

module Focusing where

open import Data.Empty
open import Data.Unit
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

-- Polarity of formulae

isPos : Fma → Set
isPos (A ⊸ B) = ⊥
isPos I = ⊤
isPos (` X) = ⊤

isPPos : Fma → Set
isPPos (A ⊸ B) = ⊥
isPPos I = ⊤
isPPos (` X) = ⊥

isNeg : Fma → Set
isNeg (` X) = ⊤
isNeg (A ⊸ B) = ⊤
isNeg I = ⊥

isIrr : Stp → Set
isIrr nothing = ⊤
isIrr (just A) = isNeg A

Pos : Set
Pos = Σ Fma λ A → isPos A

PPos : Set
PPos = Σ Fma λ A → isPPos A

Neg : Set
Neg = Σ Fma λ A → isNeg A

Irr : Set
Irr = Σ Stp λ S → isIrr S

pos : Pos → Fma
pos (A , a) = A

ppos : PPos → Fma
ppos (A , a) = A

neg : Neg → Fma
neg (A , a) = A

irr : Irr → Stp
irr (S , _) = S

-- =======================================================================

-- focused sequent calculus

infix 15 _∣_⊢L_ _∣_⊢R_ _∣_；_⊢C_

data _∣_；_⊢C_ : Stp → Cxt → Cxt → Fma → Set
data _∣_⊢R_ : Stp → Cxt → Fma → Set
data _∣_⊢L_ : Stp → Cxt → Pos → Set
data _∣_⊢LF_ : Stp → Cxt → Pos → Set
data _∣_⊢RF_ : Stp → Cxt → Pos → Set


data _∣_；_⊢C_ where
  ex : {S : Stp} {Φ Γ Δ Λ : Cxt} {A C : Fma} → 
       (f : S ∣ Λ ； Δ ⊢C C) (eq : Λ ≡ Φ ++ A ∷ Γ) →
       S ∣ Φ ++ Γ ； A ∷ Δ ⊢C C
  sw : {S : Stp} {Γ : Cxt} {C : Fma} → 
       (f : S ∣ Γ ⊢R C) → S ∣ Γ ； [] ⊢C C

data _∣_⊢R_ where
  ⊸r : {S : Stp} {Γ : Cxt} {A B : Fma} →
        (f : S ∣ Γ ； A ∷ [] ⊢C B) → S ∣ Γ ⊢R A ⊸ B
  sw : {S : Stp} {Γ : Cxt} {P : Pos} → 
       (f : S ∣ Γ ⊢L P) → S ∣ Γ ⊢R pos P

data _∣_⊢L_ where
  uf : {Γ : Cxt} {A : Fma} {P : Pos} → 
       (f : just A ∣ Γ ⊢L P) → nothing ∣ A ∷ Γ ⊢L P
  Il : {Γ : Cxt} {P : Pos} → 
       (f : nothing ∣ Γ ⊢L P) →
       just I ∣ Γ ⊢L P 
  lf : {S : Irr} {Γ : Cxt} {P : Pos} → 
       (f : irr S ∣ Γ ⊢LF P) → irr S ∣ Γ ⊢L P
  rf : {S : Irr} {Γ : Cxt} {P : Pos} → 
       (f : irr S ∣ Γ ⊢RF P) → irr S ∣ Γ ⊢L P

data _∣_⊢LF_ where
  ax : {X : At} → just (` X) ∣ [] ⊢LF (` X , _)
  ⊸l : {Γ Δ : Cxt} {A B : Fma} {P : Pos} →
        (f : nothing ∣ Γ ⊢R A) (g : just B ∣ Δ ⊢LF P) →
        just (A ⊸ B) ∣ Γ ++ Δ ⊢LF P
  blur : {Γ : Cxt} {P : Pos} {P' : PPos} →
         (f : just (ppos P') ∣ Γ ⊢L P) → just (ppos P') ∣ Γ ⊢LF P

data _∣_⊢RF_ where
  Ir : nothing ∣ [] ⊢RF (I , _)

-- ====================================================================

-- All the sequent calculus rules are admissible as focused rules

exC' : ∀ {S Φ} Γ {Δ Λ A B C} →
     (f : S ∣ Φ ； Λ ⊢C C) (eq : Λ ≡ Γ ++ A ∷ B ∷ Δ) → 
     S ∣ Φ ； Γ ++ B ∷ A ∷ Δ ⊢C C 
exC' Γ (sw f) eq = ⊥-elim ([]disj∷ Γ eq)
exC' [] (ex {Φ = Φ} {Γ} (ex {Φ = Φ₁} {Γ₁} f refl) eq) refl with cases++ Φ Φ₁ Γ Γ₁ eq
... | inj₁ (Γ₀ , refl , refl) = ex {Φ = Φ ++ Γ₀} (ex f refl) refl
... | inj₂ (Γ₀ , refl , refl) = ex (ex {Φ = Φ₁ ++ _ ∷ Γ₀} f refl) refl
exC' (A' ∷ Γ) (ex f refl) refl = ex (exC' Γ f refl) refl

exC : ∀ {S Φ} Γ {Δ A B C} 
      (f : S ∣ Φ ； Γ ++ A ∷ B ∷ Δ ⊢C C) → 
      S ∣ Φ ； Γ ++ B ∷ A ∷ Δ ⊢C C 
exC Γ f = exC' Γ f refl

act : {S : Stp} {Φ Γ : Cxt} {A C : Fma}
  → (f : S ∣ Φ ∷ʳ A ； Γ ⊢C C)
  → S ∣ Φ ； A ∷ Γ ⊢C C
act f = ex {Γ = []} f refl

act⋆ : {S : Stp} {Γ Φ : Cxt} (Ψ : Cxt) {C : Fma}
  → (f : S ∣ Φ ++ Ψ ； Γ ⊢C C)
  → S ∣ Φ ； Ψ ++ Γ ⊢C C
act⋆ [] f = f
act⋆ (A ∷ Ψ) f = act (act⋆ Ψ f)

⊸rC' : {S : Stp} (Γ : Cxt) {Φ Λ : Cxt} {A B : Fma} →
       (f : S ∣ Φ ； Λ ⊢C B) (eq : Λ ≡ Γ ∷ʳ A) →
       S ∣ Φ ； Γ ⊢C A ⊸ B
⊸rC' Γ (sw f) eq = ⊥-elim ([]disj∷ Γ eq)
⊸rC' [] (ex f refl) refl = sw (⊸r (ex f refl))
⊸rC' (A' ∷ Γ) (ex f refl) refl = ex (⊸rC' Γ f refl) refl

⊸rC : {S : Stp} (Γ : Cxt) {Φ : Cxt} {A B : Fma} →
       (f : S ∣ Φ ； Γ ∷ʳ A ⊢C B) → 
       S ∣ Φ ； Γ ⊢C A ⊸ B
⊸rC Γ f = ⊸rC' Γ f refl


ufC : {Φ Γ : Cxt} {A C : Fma} → 
      (f : just A ∣ Φ ； Γ ⊢C C) →
      nothing ∣ A ∷ Φ ； Γ ⊢C C
ufR : {Γ : Cxt} {A C : Fma} → 
      (f : just A ∣ Γ ⊢R C) →
      nothing ∣ A ∷ Γ ⊢R C

ufC (ex {Φ = Φ} f refl) = ex {Φ = _ ∷ Φ} (ufC f) refl
ufC (sw f) = sw (ufR f)

ufR (⊸r f) = ⊸r (ufC f)
ufR (sw f) = sw (uf f)

⊸lRC : {Φ Ψ Γ : Cxt} {A B C : Fma} → 
      (f : nothing ∣ Φ ⊢R A) (g : just B ∣ Ψ ； Γ ⊢C C) →
      just (A ⊸ B) ∣ Φ ++ Ψ ； Γ ⊢C C
⊸lRR : {Γ Δ : Cxt} {A B C : Fma} → 
      (f : nothing ∣ Γ ⊢R A) (g : just B ∣ Δ ⊢R C) →
      just (A ⊸ B) ∣ Γ ++ Δ ⊢R C

⊸lRC {Φ} f (ex {Φ = Φ₁} g refl) = ex {Φ = Φ ++ Φ₁} (⊸lRC f g) refl
⊸lRC f (sw g) = sw (⊸lRR f g)

⊸lRR f (⊸r g) = ⊸r (⊸lRC f g)
⊸lRR {B = ` X} f (sw {P = P} (lf g)) = sw {P = P} (lf (⊸l f g))
⊸lRR {B = B ⊸ B'} f (sw {P = P} (lf g)) = sw {P = P} (lf (⊸l f g))
⊸lRR {B = I} f (sw {P = P} (Il g)) = sw {P = P} (lf (⊸l f (blur (Il g))))

⊸lC : {Φ Γ Δ : Cxt} {A B C : Fma} → 
      (f : nothing ∣ Φ ； Γ ⊢C A) (g : just B ∣ [] ； Δ ⊢C C) →
      just (A ⊸ B) ∣ Φ ； Γ ++ Δ ⊢C C
⊸lC (ex f refl) g = ex (⊸lC f g) refl
⊸lC (sw f) g = ⊸lRC f g

IrC : nothing ∣ [] ； [] ⊢C I
IrC = sw (sw (rf Ir))

IlC : {Φ Γ : Cxt} {C : Fma} → 
     (f : nothing ∣ Φ ； Γ ⊢C C) →
     just I ∣ Φ ； Γ ⊢C C
IlR : {Γ : Cxt} {C : Fma} → 
     (f : nothing ∣ Γ ⊢R C) →
     just I ∣ Γ ⊢R C

IlC (ex f refl) = ex (IlC f) refl
IlC (sw f) = sw (IlR f)

IlR (⊸r f) = ⊸r (IlC f)
IlR (sw f) = sw (Il f)

axC : (A : Fma) → just A ∣ [] ； [] ⊢C A
axC (` X) = sw (sw (lf ax))
axC I = sw (sw (Il (rf Ir)))
axC (A ⊸ B) = sw (⊸r (ex {Φ = []} (⊸lC (ufC (axC A)) (axC B)) refl))

-- ====================================================================

-- Embedding of focused derivations in the sequent calculus

embC : {S : Stp} {Γ Δ : Cxt} {C : Fma} →
       S ∣ Γ ； Δ ⊢C C → S ∣ Γ ++ Δ ⊢ C
embR : {S : Stp} {Γ : Cxt} {C : Fma} →
       S ∣ Γ ⊢R C → S ∣ Γ ⊢ C
embL : {S : Stp} {Γ : Cxt} {P : Pos} → 
        S ∣ Γ ⊢L P → S ∣ Γ ⊢ pos P
embF : {S : Stp} {Γ : Cxt} {P : Pos} → 
        S ∣ Γ ⊢LF P → S ∣ Γ ⊢ pos P

embC (ex {Φ = Φ} {Γ = Γ} f refl) = ex-fma-cxt Γ (embC f)
embC (sw f) = embR f

embR (⊸r f) = ⊸r (embC f)
embR (sw f) = embL f

embL (uf f) = uf (embL f)
embL (Il f) = Il (embL f)
embL (lf f) = embF f
embL (rf Ir) = Ir

embF ax = ax
embF (⊸l f g) = ⊸l (embR f) (embF g)
embF (blur f) = embL f

emb : {S : Stp} {Γ : Cxt} {C : Fma}
  → S ∣ [] ； Γ ⊢C C → S ∣ Γ ⊢ C
emb = embC

-- ====================================================================

-- The focusing procedure

focus : {S : Stp} {Γ : Cxt} {C : Fma} →
              S ∣ Γ ⊢ C → S ∣ [] ； Γ ⊢C C
focus ax = axC _
focus (uf f) = act (ufC (focus f))
focus Ir = IrC
focus (⊸r f) = ⊸rC _ (focus f)
focus (Il f) = IlC (focus f)
focus (ex f) = exC _ (focus f)
focus (⊸l f g) = ⊸lC (focus f) (focus g)

-- ====================================================================

-- Focusing sends ≗-related derivations to equal focused derivations
 
exexC : ∀{S Φ₁ Φ₂ Φ₃ Λ Δ A B A' B' C} (f : S ∣ Δ ； Λ ⊢C C)
  → (eq : Λ ≡ Φ₁ ++ A ∷ B ∷ Φ₂ ++ A' ∷ B' ∷ Φ₃)
  → exC' (Φ₁ ++ B ∷ A ∷ Φ₂) (exC' Φ₁ f eq) refl
    ≡ exC' Φ₁ (exC' (Φ₁ ++ A ∷ B ∷ Φ₂) f eq) refl
exexC {Φ₁ = Φ₁} (sw f) eq = ⊥-elim ([]disj∷ Φ₁ eq)
exexC {Φ₁ = []} (ex {Φ = Φ} {Γ} (ex {Φ = Φ₁} {Γ = Γ₁} f eq) eq₁) eq₂ with cases++ Φ Φ₁ Γ Γ₁ eq₁
exexC {Λ = A ∷ _ ∷ _} (ex {Φ = Φ} (ex {Γ = Γ₁} f refl) refl) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Φ Γ₀ Γ₁ A = refl
exexC {Λ = A ∷ _ ∷ _} (ex {Γ = Γ} (ex {Φ = Φ₁} f refl) refl) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ Φ₁ Γ A = refl
exexC {Φ₁ = D ∷ Φ₁} {Φ₂} {Φ₃} (ex f refl) refl =
  cong (λ x → ex x refl) (exexC f refl)

exC-iso : ∀{S Φ Ψ Λ Δ A B C} (f : S ∣ Δ ； Λ ⊢C C)
  → (eq : Λ ≡ Φ ++ A ∷ B ∷ Ψ)
  → exC' Φ (exC' Φ f eq) refl ≡ subst (λ x → S ∣ Δ ； x ⊢C C) eq f
exC-iso {Φ = Φ} (sw f) eq = ⊥-elim ([]disj∷ Φ eq)
exC-iso {Φ = []} (ex {Φ = Φ} {Γ} (ex {Φ = Φ₁} {Γ₁} f refl) eq) refl with  cases++ Φ Φ₁ Γ Γ₁ eq
exC-iso {B = B} (ex {Φ = Φ} (ex {Γ = Γ} f refl) refl) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ Φ Γ B = refl
exC-iso {B = B} (ex {Γ = Γ} (ex {Φ = Φ} f refl) refl) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Φ Γ₀ Γ B = refl
exC-iso {Φ = A' ∷ Φ} (ex f refl) refl = cong (λ x → ex x refl) (exC-iso f refl)


⊸rufC : {Φ Γ Λ : Cxt} {A B C : Fma} 
    → (f : just A ∣ Φ ； Λ ⊢C C) (eq : Λ ≡ Γ ++ B ∷ [])
    → ⊸rC' Γ (ufC f) eq ≡ ufC (⊸rC' Γ f eq)
⊸rufC {Γ = Γ} (sw f) eq = ⊥-elim ([]disj∷ Γ eq)
⊸rufC {Γ = []} (ex f refl) refl = refl
⊸rufC {Γ = A' ∷ Γ} (ex {Φ = Φ} f refl) refl =
  cong (λ x → ex {Φ = _ ∷ Φ} x refl) (⊸rufC f refl)

⊸rIlC : {Φ Γ Λ : Cxt}{B C : Fma} 
    → (f : nothing ∣ Φ ； Λ ⊢C C) (eq : Λ ≡ Γ ++ B ∷ [])
    → ⊸rC' Γ (IlC f) eq ≡ IlC (⊸rC' Γ f eq)
⊸rIlC {Γ = Γ} (sw f) eq = ⊥-elim ([]disj∷ Γ eq)
⊸rIlC {Γ = []} (ex f refl) refl = refl
⊸rIlC {Γ = A ∷ Γ} (ex f refl) refl = cong (λ x → ex x refl) (⊸rIlC f refl)

⊸r⊸lRC : {Φ Ψ Δ Λ : Cxt}{A B C D : Fma}
  → (f : nothing ∣ Φ ⊢R A)(g : just B ∣ Ψ ； Λ ⊢C D) (eq : Λ ≡ Δ ++ C ∷ [])
  → ⊸rC' Δ (⊸lRC f g) eq ≡ ⊸lRC f (⊸rC' Δ g eq)
⊸r⊸lRC {Δ = Δ} f (sw f₁) eq = ⊥-elim ([]disj∷ Δ eq)
⊸r⊸lRC {Δ = []} f (ex g refl) refl = refl
⊸r⊸lRC {Φ} {Δ = A' ∷ Δ} f (ex {Φ = Φ₁} g refl) refl =
  cong (λ x → ex {Φ = Φ ++ Φ₁} x refl) (⊸r⊸lRC f g refl)

⊸r⊸lC : {Φ Γ Δ Λ : Cxt}{A B C D : Fma}
  → (f : nothing ∣ Φ ； Γ ⊢C A)(g : just B ∣ [] ； Λ ⊢C D) (eq : Λ ≡ Δ ++ C ∷ [])
  → ⊸rC' (Γ ++ Δ) (⊸lC f g) (cong (Γ ++_) eq) ≡ ⊸lC f (⊸rC' Δ g eq)
⊸r⊸lC (ex f refl) g refl = cong (λ x → ex x refl) (⊸r⊸lC f g refl)
⊸r⊸lC (sw f) g refl = ⊸r⊸lRC f g refl

exufC : ∀ {Φ Ψ Δ Λ A A' B C}
  → (f : just A' ∣ Δ ； Λ ⊢C C) (eq : Λ ≡ Φ ++ A ∷ B ∷ Ψ)
  → exC' Φ (ufC f) eq ≡ ufC (exC' Φ f eq)
exufC {Φ} (sw f) eq = ⊥-elim ([]disj∷ Φ eq)
exufC {[]} (ex {Φ = Φ} {Γ} (ex {Φ = Φ₁} {Γ₁} f refl) eq) refl with cases++ Φ Φ₁ Γ Γ₁ eq
exufC {A = A} (ex {Φ = Φ} (ex {Γ = Γ} f refl) refl) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Φ Γ₀ Γ A = refl
exufC {A = A} (ex {Γ = Γ} (ex {Φ = Φ} f refl) refl) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ Φ Γ A = refl
exufC {A' ∷ Φ} (ex {Φ = Φ₁} f refl) refl = cong (λ x → ex {Φ = _ ∷ Φ₁} x refl) (exufC f refl)

exIlC : ∀ {Φ Ψ Δ Λ A B C}
  → (f : nothing ∣ Δ ； Λ ⊢C C) (eq : Λ ≡ Φ ++ A ∷ B ∷ Ψ)
  → exC' Φ (IlC f) eq ≡ IlC (exC' Φ f eq)
exIlC {Φ} (sw f) eq = ⊥-elim ([]disj∷ Φ eq)
exIlC {[]} (ex {Φ = Φ} {Γ} (ex {Φ = Φ₁} {Γ₁} f refl) eq) refl with cases++ Φ Φ₁ Γ Γ₁ eq
exIlC {A = A} (ex {Φ = Φ} (ex {Γ = Γ} f refl) refl) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Φ Γ₀ Γ A = refl
exIlC {A = A} (ex {Γ = Γ} (ex {Φ = Φ} f refl) refl) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ Φ Γ A = refl
exIlC {D ∷ Φ} (ex f refl) refl = cong (λ x → ex x refl) (exIlC f refl)

ex⊸rC : ∀ {S Φ Ψ Δ Λ A' B' A B}
  → (f : S ∣ Δ ； Λ ⊢C B') (eq : Λ ≡ Φ ++ A ∷ B ∷ Ψ ∷ʳ A')
  → exC' Φ (⊸rC' (Φ ++ A ∷ B ∷ Ψ) f eq) refl ≡ ⊸rC' (Φ ++ B ∷ A ∷ Ψ) (exC' Φ f eq) refl
ex⊸rC {Φ = Φ} (sw f) eq = ⊥-elim ([]disj∷ Φ eq)
ex⊸rC {Φ = []} (ex {Φ = Φ} {Γ} (ex {Φ = Φ₁} {Γ₁} f refl) eq) refl with cases++ Φ Φ₁ Γ Γ₁ eq
ex⊸rC {A = A} (ex {Φ = Φ} (ex {Γ = Γ} f refl) refl) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Φ Γ₀ Γ A = refl
ex⊸rC {A = A} (ex {Γ = Γ} (ex {Φ = Φ} f refl) refl) refl | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ Γ₀ Φ Γ A = refl
ex⊸rC {Φ = D ∷ Φ} (ex f refl) refl = cong (λ x → ex x refl) (ex⊸rC f refl)

ex⊸lC₁ : {Γ₁ Γ₂ Δ Φ Λ : Cxt}{A A' B B' C : Fma}
    → (f : nothing ∣ Φ ； Λ ⊢C A')(g : just B' ∣ [] ； Δ ⊢C C)(eq : Λ ≡ Γ₁ ++ A ∷ B ∷ Γ₂)
    → exC' Γ₁ (⊸lC f g) (cong (_++ Δ) {y = Γ₁ ++ A ∷ B ∷ Γ₂} eq) ≡ ⊸lC (exC' Γ₁ f eq) g
ex⊸lC₁ {Γ₁} (sw f) g eq = ⊥-elim ([]disj∷ Γ₁ eq)
ex⊸lC₁ {[]} (ex {Φ = Φ} {Γ} (ex {Φ = Φ₁} {Γ₁} f refl) eq) g refl with cases++ Φ Φ₁ Γ Γ₁ eq
ex⊸lC₁ {A = A} (ex {Φ = Φ} (ex {Γ = Γ} f refl) refl) g refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Φ Γ₀ Γ A = refl
ex⊸lC₁ {A = A} (ex {Γ = Γ} (ex {Φ = Φ} f refl) refl) g refl | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ Γ₀ Φ Γ A = refl
ex⊸lC₁ {D ∷ Γ₁} (ex f refl) g refl = cong (λ x → ex x refl) (ex⊸lC₁ f g refl)

ex⊸lC₂ : {Γ₁ Γ₂ Δ Φ Λ : Cxt}{A A' B B' C : Fma}
    → (f : nothing ∣ Φ ； Δ ⊢C A')(g : just B' ∣ [] ； Λ ⊢C C)(eq : Λ ≡ Γ₁ ++ A ∷ B ∷ Γ₂)
    → exC' (Δ ++ Γ₁)  (⊸lC f g) (cong (Δ ++_) {y = Γ₁ ++ A ∷ B ∷ Γ₂} eq) ≡ ⊸lC f (exC' Γ₁ g eq)
ex⊸lRC₂ : {Γ₁ Γ₂ Φ Δ Λ : Cxt}{A A' B B' C : Fma}
    → (f : nothing ∣ Δ ⊢R A')(g : just B' ∣ Φ ； Λ ⊢C C)(eq : Λ ≡ Γ₁ ++ A ∷ B ∷ Γ₂)
    → exC' Γ₁  (⊸lRC f g) eq ≡ ⊸lRC f (exC' Γ₁ g eq)

ex⊸lC₂ (ex f refl) g refl = cong (λ x → ex x refl) (ex⊸lC₂ f g refl)
ex⊸lC₂ (sw f) g refl = ex⊸lRC₂ f g refl

ex⊸lRC₂ {Γ₁} f (sw g) eq = ⊥-elim ([]disj∷ Γ₁ eq)
ex⊸lRC₂ {[]} f (ex {Φ = Φ} {Γ} (ex {Φ = Φ₁} {Γ₁} g refl) eq) refl with cases++ Φ Φ₁ Γ Γ₁ eq
ex⊸lRC₂ {Δ = Δ} {A = A} f (ex {Φ = Φ} (ex {Γ = Γ} g refl) refl) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ (Δ ++ Φ) Γ₀ Γ A = refl
ex⊸lRC₂ {Δ = Δ} {A = A} f (ex {Γ = Γ} (ex {Φ = Φ} g refl) refl) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ (Δ ++ Φ) Γ A = refl
ex⊸lRC₂ {D ∷ Γ₁} {Δ = Δ} f (ex {Φ = Φ} g refl) refl =
  cong (λ x → ex {Φ = Δ ++ Φ} x refl) (ex⊸lRC₂ f g refl)

exC-braid : ∀{S Φ A B C Λ Ψ Δ D}
  → (f : S ∣ Δ ； Λ ⊢C D) (eq : Λ ≡ Φ ++ A ∷ B ∷ C ∷ Ψ)
  → exC Φ (exC (Φ ++ B ∷ []) (exC' Φ f eq))
    ≡ exC (Φ ++ C ∷ []) (exC Φ (exC' (Φ ++ A ∷ []) f eq))
exC-braid {Φ = Φ} (sw f) eq = ⊥-elim ([]disj∷ Φ eq)
exC-braid {Φ = []} (ex {Φ = Φ} {Γ} (ex {Φ = Φ₁} {Γ₁} (ex f refl) eq) eq') refl with cases++ Φ Φ₁ Γ Γ₁ eq'
exC-braid (ex {Φ = Φ} (ex {Γ = Γ₁} (ex {Φ = Φ₂} {Γ₂} f refl) eq) refl) refl | inj₁ (Γ₀ , refl , refl) with cases++ Φ Φ₂ (Γ₀ ++ _ ∷ Γ₁) Γ₂ eq
exC-braid {A = A} {B} {C} (ex (ex {Γ = Γ} (ex {Φ = Φ} f refl) refl) refl) refl | inj₁ (Λ , refl , refl) | inj₂ (Ω , refl , refl) 
  rewrite cases++-inj₁ (Φ ++ Ω) Λ Γ A | cases++-inj₂ Ω Φ (Λ ++ B ∷ Γ) A |
          cases++-inj₂ (Ω ++ Λ) Φ Γ B | cases++-inj₂ (Ω ++ A ∷ Λ) Φ Γ B |
          cases++-inj₂ Ω Φ (Λ ++ Γ) A | cases++-inj₁ (Φ ++ C ∷ Ω) Λ Γ A  = refl
... | inj₁ (Γ₀' , refl , q) with cases++ Γ₀ Γ₀' Γ₁ Γ₂ (sym q)
exC-braid {A = A} {B} {C} (ex {Φ = Φ} (ex (ex {Γ = Γ} f refl) refl) refl) refl | inj₁ (Λ , refl , refl) | inj₁ (._ , refl , refl) | inj₁ (Ω , refl , refl)
  rewrite cases++-inj₁ Φ Λ (Ω ++ Γ) A | cases++-inj₁ (Φ ++ A ∷ Λ) Ω Γ B |
          cases++-inj₁ Φ (Λ ++ B ∷ Ω) Γ A | cases++-inj₁ Φ (Λ ++ Ω) Γ A |
          cases++-inj₁ Φ Λ (Ω ++ C ∷ Γ) A | cases++-inj₁ (Φ ++ Λ) Ω Γ B = refl
exC-braid {A = A} {B} {C} (ex {Φ = Φ} (ex {Γ = Γ} (ex f refl) refl) refl) refl | inj₁ (._ , refl , refl) | inj₁ (Λ , refl , refl) | inj₂ (Ω , refl , refl)
  rewrite cases++-inj₁ Φ (Λ ++ Ω) Γ A | cases++-inj₂ Ω (Φ ++ A ∷ Λ) Γ B |
          cases++-inj₁ Φ Λ (Ω ++ B ∷ Γ) A | cases++-inj₁ Φ Λ (Ω ++ Γ) A |
          cases++-inj₂ Ω (Φ ++ Λ) Γ B | cases++-inj₁ Φ (Λ ++ C ∷ Ω) Γ A = refl
exC-braid (ex {Γ = Γ} (ex {Φ = Φ₁} (ex {Φ = Φ₂} {Γ₂} f refl) eq) refl) refl | inj₂ (Γ₀ , refl , refl) with cases++ Φ₁ Φ₂ (Γ₀ ++ _ ∷ Γ) Γ₂ eq
exC-braid {A = A} {B} {C} (ex {Γ = Γ} (ex (ex {Φ = Φ} f refl) refl) refl) refl | inj₂ (Λ , refl , refl) | inj₂ (Ω , refl , refl)
  rewrite cases++-inj₂ Λ (Φ ++ Ω) Γ A | cases++-inj₂ (Ω ++ Λ) Φ Γ A |
          cases++-inj₂ (Ω ++ B ∷ Λ) Φ Γ A | cases++-inj₂ Λ (Φ ++ C ∷ Ω) Γ A |
          cases++-inj₂ Ω Φ (Λ ++ Γ) B = refl
... | inj₁ (Γ₀' , refl , q) with cases++ Γ₀ Γ₀' Γ Γ₂ (sym q)
exC-braid {A = A} {B} {C} (ex (ex {Φ = Φ} (ex {Γ = Γ} f refl) refl) refl) refl | inj₂ (Λ , refl , refl) | inj₁ (._ , refl , refl) | inj₁ (Ω , refl , refl)
  rewrite cases++-inj₂ Λ Φ (Ω ++ Γ) A | cases++-inj₁ (Φ ++ Λ) Ω Γ A |
          cases++-inj₁ (Φ ++ B ∷ Λ) Ω Γ A | cases++-inj₂ Λ Φ (Ω ++ C ∷ Γ) A |
            cases++-inj₁ Φ (Λ ++ Ω) Γ B = refl
exC-braid {A = A} {B} {C} (ex {Γ = Γ} (ex {Φ = Φ} (ex f refl) refl) refl) refl | inj₂ (._ , refl , refl) | inj₁ (Λ , refl , refl) | inj₂ (Ω , refl , refl)
  rewrite cases++-inj₂ (Λ ++ Ω) Φ Γ A | cases++-inj₂ Ω (Φ ++ Λ) Γ A |
          cases++-inj₂ Ω  (Φ ++ B ∷ Λ) Γ A | cases++-inj₂ (Λ ++ C ∷ Ω) Φ Γ A |
          cases++-inj₁ Φ Λ (Ω ++ Γ) B = refl
exC-braid {Φ = A' ∷ Φ} (ex f refl) refl = cong (λ x → ex x refl) (exC-braid f refl)

focus-compat : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              {f g : S ∣ Γ ⊢ C} → f ≗ g → focus f ≡ focus g
focus-compat refl = refl
focus-compat (~ p) = sym (focus-compat p)
focus-compat (p ∙ p₁) = trans (focus-compat p) (focus-compat p₁)
focus-compat (uf p) = cong (λ x → act (ufC x)) (focus-compat p)
focus-compat (Il p) = cong IlC (focus-compat p)
focus-compat (⊸r p) = cong (⊸rC _) (focus-compat p)
focus-compat (⊸l p p₁) = cong₂ ⊸lC (focus-compat p) (focus-compat p₁)
focus-compat axI = refl
focus-compat ax⊸ = refl
focus-compat (⊸ruf {f = f}) = cong act (⊸rufC (focus f) refl)
focus-compat (⊸rIl {f = f}) = ⊸rIlC (focus f) refl
focus-compat (⊸r⊸l {f = f} {g}) = ⊸r⊸lC (focus f) (focus g) refl
focus-compat (ex {Γ = Γ} p) = cong (exC Γ) (focus-compat p)
focus-compat (exex {f = f}) = exexC (focus f) refl
focus-compat (exuf {f = f}) = cong act (exufC (focus f) refl)
focus-compat (exIl {f = f}) = exIlC (focus f) refl
focus-compat (ex⊸r {f = f}) = ex⊸rC (focus f) refl
focus-compat (ex⊸l₁ {f = f} {g}) = ex⊸lC₁ (focus f) (focus g) refl
focus-compat (ex⊸l₂ {f = f} {g}) = ex⊸lC₂ (focus f) (focus g) refl
focus-compat {g = g} ex-iso = exC-iso (focus g) refl
focus-compat (ex-braid {f = f}) = exC-braid (focus f) refl

-- ====================================================================

-- ∀ f. focus (emb f) ≡ f

act⋆-ufC : ∀ {Φ} Γ {A P}
  → (f : just A ∣ Φ ++ Γ ⊢L P)
  → ufC (act⋆ Γ (sw (sw f))) ≡ act⋆ Γ (sw (sw (uf f)))
act⋆-ufC [] f = refl
act⋆-ufC {Φ} (B ∷ Γ) f = cong act (act⋆-ufC {Φ = Φ ∷ʳ B} Γ f)

act⋆-IlC : ∀ {Φ} Γ {P}
  → (f : nothing ∣ Φ ++ Γ ⊢L P)
  → IlC (act⋆ Γ (sw (sw f))) ≡ act⋆ Γ (sw (sw (Il f)))
act⋆-IlC [] f = refl
act⋆-IlC {Φ} (B ∷ Γ) f = cong act (act⋆-IlC {Φ = Φ ∷ʳ B} Γ f)

act⋆-⊸rC : ∀ {S Φ} Γ {Δ A B}
  → (f : S ∣ Φ ++ Γ ； Δ ∷ʳ A ⊢C B)
  → ⊸rC (Γ ++ Δ) (act⋆ Γ f) ≡ act⋆ Γ (⊸rC Δ f)
act⋆-⊸rC [] f = refl
act⋆-⊸rC {Φ = Φ} (A' ∷ Γ) f = cong act (act⋆-⊸rC {Φ = Φ ∷ʳ A'} Γ f)

act⋆-⊸lC : ∀ {Φ Γ} Λ {Δ A B C} →
           (f : nothing ∣ Φ ++ Λ ； Γ ⊢C A) (g : just B ∣ [] ； Δ ⊢C C) →
           ⊸lC (act⋆ Λ f) g ≡ act⋆ Λ (⊸lC f g) 
act⋆-⊸lC [] f g = refl
act⋆-⊸lC {Φ} (A' ∷ Λ) f g = cong act (act⋆-⊸lC {Φ ∷ʳ A'} Λ f g)

act⋆-⊸lRC : ∀ {Φ Ψ} Λ {Δ A B C} →
           (f : nothing ∣ Φ ⊢R A) (g : just B ∣ Ψ ++ Λ ； Δ ⊢C C) →
           ⊸lRC f (act⋆ Λ g) ≡ act⋆ Λ (⊸lRC f g) 
act⋆-⊸lRC [] f g = refl
act⋆-⊸lRC {Ψ = Ψ} (A' ∷ Λ) f g = cong act (act⋆-⊸lRC {Ψ = Ψ ∷ʳ A'} Λ f g)

act⋆act⋆ : {S : Stp} {Φ Γ : Cxt} (Ψ Θ : Cxt) {C : Fma}
  → (f : S ∣ Φ ++ Ψ ++ Θ ； Γ ⊢C C)
  → act⋆ {Φ = Φ} Ψ (act⋆ Θ f) ≡ act⋆ (Ψ ++ Θ) f
act⋆act⋆ [] Θ f = refl
act⋆act⋆ (A ∷ Ψ) Θ f = cong act (act⋆act⋆ Ψ Θ f)

ex-fma-cxtC : {S : Stp} (Γ Λ : Cxt) {Φ Δ : Cxt} {A C : Fma} → 
              S ∣ Φ ； Γ ++ A ∷ Λ ++ Δ ⊢C C  → S ∣ Φ ； Γ ++ Λ ++ A ∷ Δ ⊢C C
ex-fma-cxtC Γ [] f = f
ex-fma-cxtC Γ (B ∷ Λ) f = ex-fma-cxtC (Γ ∷ʳ _) Λ (exC Γ f)

focus-ex-fma-cxt : ∀{S Φ} Λ {Γ A C}
  → (f : S ∣ Φ ++ A ∷ Λ ++ Γ ⊢ C)
  → focus (ex-fma-cxt {_}{Φ}{Γ} Λ f) ≡ ex-fma-cxtC Φ Λ (focus f)
focus-ex-fma-cxt [] f = refl
focus-ex-fma-cxt {Φ = Φ} (B ∷ Λ) f = focus-ex-fma-cxt {Φ = Φ ∷ʳ B} Λ (ex f)

ex-fma-cxtC++ : {S : Stp} (Γ Λ Ω : Cxt) {Φ Δ : Cxt} {A C : Fma} → 
              (f : S ∣ Φ ； Γ ++ A ∷ Λ ++ Ω ++ Δ ⊢C C) →
              ex-fma-cxtC Γ (Λ ++ Ω) {Φ} {Δ} f ≡ ex-fma-cxtC (Γ ++ Λ) Ω (ex-fma-cxtC Γ Λ {_}{Ω ++ Δ} f)
ex-fma-cxtC++ Γ [] Ω f = refl
ex-fma-cxtC++ Γ (B ∷ Λ) Ω f = ex-fma-cxtC++ (Γ ∷ʳ B) Λ Ω (exC Γ f)

ex-fma-cxtC-act∷ : ∀{S Φ Ψ Γ} Δ {A B C}
  → (f : S ∣ Ψ ∷ʳ B ； Γ ++ A ∷ Δ ++ Φ ⊢C C)
  → ex-fma-cxtC (B ∷ Γ) Δ {Ψ}{Φ} (act f) ≡ act (ex-fma-cxtC Γ Δ f)
ex-fma-cxtC-act∷ [] f = refl
ex-fma-cxtC-act∷ {Γ = Γ} (D ∷ Δ) f = ex-fma-cxtC-act∷ {Γ = Γ ∷ʳ D} Δ _

ex-fma-cxtC-act⋆ : ∀{S Φ Ψ} Γ {Δ A C}
  → (f : S ∣ Ψ ++ Γ ； A ∷ Δ ++ Φ ⊢C C)
  → ex-fma-cxtC Γ Δ {Ψ}{Φ} (act⋆ Γ f) ≡ act⋆ Γ (ex-fma-cxtC [] Δ f)
ex-fma-cxtC-act⋆ [] f = refl
ex-fma-cxtC-act⋆ {Ψ = Ψ} (B ∷ Γ) {Δ} f =
  trans (ex-fma-cxtC-act∷ Δ (act⋆ Γ f))
        (cong act (ex-fma-cxtC-act⋆ {Ψ = Ψ ∷ʳ B} Γ f))


snoc? : {A : Set} (xs : List A) → xs ≡ [] ⊎ Σ (List A) λ ys → Σ A λ x → xs ≡ ys ∷ʳ x × length xs ≡ suc (length ys)
snoc? [] = inj₁ refl
snoc? (x ∷ xs) with snoc? xs
... | inj₁ refl = inj₂ ([] , x , refl , refl)
... | inj₂ (ys , y , refl , eq) = inj₂ (x ∷ ys , y , refl , cong suc eq)


exC-ax⋆ : ∀ {S Φ} Γ {Δ A B C} →
     (f : S ∣ Φ ++ Γ ； A ∷ B ∷ Δ ⊢C C)  →
     exC Γ (act⋆ Γ f) ≡ act⋆ Γ (exC [] f)
exC-ax⋆ [] f = refl
exC-ax⋆ {Φ = Φ} (A' ∷ Γ) {Δ} f =
  cong (λ x → ex x refl) (exC-ax⋆ {Φ = Φ ∷ʳ A'} Γ f)


ex-fma-cxtC-act⋆[] : ∀{S Φ Γ} Δ {A C} n 
  → length Δ ≡ n → (f : S ∣ Γ ++ A ∷ Δ ； Φ ⊢C C)
  → ex-fma-cxtC [] Δ {Γ}{Φ} (act (act⋆ Δ f)) ≡ act⋆ Δ (ex {Φ = Γ} f refl) 
ex-fma-cxtC-act⋆[] [] zero eq f = refl
ex-fma-cxtC-act⋆[] {_}{Φ}{Γ} Δ {A} (suc n) eq f with snoc? Δ
... | inj₁ refl = refl
... | inj₂ (Δ' , B , refl , eq') = 
  trans (ex-fma-cxtC++ [] Δ' (B ∷ []) _)
  (trans (cong (λ x → exC Δ' (ex-fma-cxtC [] Δ' (act x))) (sym (act⋆act⋆ Δ' (B ∷ []) f)))
  (trans (cong (exC Δ') (ex-fma-cxtC-act⋆[] Δ' n (suc-injective (trans (sym eq') eq)) (act f)))
  (trans (exC-ax⋆ Δ' _)
         lem)))
  where
    lem : act⋆ {_} {_ ∷ _ ∷ Φ} Δ' (exC [] (ex {_}{Γ}{Δ'} {_ ∷ Φ} (act {_} {Γ ++ _ ∷ Δ'} f) refl))
      ≡ act⋆ {_}{_}{Γ} (Δ' ++ B ∷ []) (ex f refl)
    lem rewrite cases++-inj₁ Γ Δ' [] A = act⋆act⋆ Δ' (B ∷ []) _


focus-embC : {S : Stp} {Γ Δ : Cxt} {C : Fma}
  → (f : S ∣ Γ ； Δ ⊢C C)
  → focus (embC f) ≡ act⋆ Γ f
focus-embR : {S : Stp} {Γ : Cxt} {C : Fma}
  → (f : S ∣ Γ ⊢R C)
  → focus (embR f) ≡ act⋆ Γ (sw f)
focus-embL : {S : Stp} {Γ : Cxt} {P : Pos}
  → (f : S ∣ Γ ⊢L P)
  → focus (embL f) ≡ act⋆ Γ (sw (sw f))
focus-embF : {S : Irr} {Γ : Cxt} {P : Pos}
  → (f : irr S ∣ Γ ⊢LF P)
  → focus (embF f) ≡ act⋆ Γ (sw (sw (lf {S} f)))

focus-embC (ex {Φ = Φ}{Γ = Γ} f refl) = 
  trans (focus-ex-fma-cxt Γ (embC f))
  (trans (cong (ex-fma-cxtC Φ Γ) (focus-embC f))
  (trans (cong (ex-fma-cxtC Φ Γ) (sym (act⋆act⋆ Φ (_ ∷ Γ) f)))
  (trans (ex-fma-cxtC-act⋆ Φ {Γ} (act (act⋆ Γ f)))
  (trans (cong (act⋆ Φ) (ex-fma-cxtC-act⋆[] Γ _ refl f))
         (act⋆act⋆ Φ Γ _)))))
focus-embC (sw f) = focus-embR f

focus-embR {Γ = Γ} (⊸r (ex f refl)) =
  trans (cong (⊸rC Γ) (focus-embC (ex f refl)))
        (act⋆-⊸rC Γ {[]} (ex f refl))
focus-embR (sw f) = focus-embL f

focus-embL (uf f) = cong act
  (trans (cong ufC (focus-embL f))
         (act⋆-ufC _ f))
focus-embL (Il f) =
  trans (cong IlC (focus-embL f))
        (act⋆-IlC _ f)
focus-embL (lf f) = focus-embF f
focus-embL (rf Ir) = refl

focus-embF ax = refl
focus-embF (⊸l {Γ = Γ} {Δ} {B = ` X} f g) =
  trans (cong₂ ⊸lC (focus-embR f) (focus-embF g))
  (trans (act⋆-⊸lC Γ (sw f) _)
  (trans (cong (act⋆ Γ) (act⋆-⊸lRC Δ f _))
         (act⋆act⋆ Γ Δ _)))
focus-embF (⊸l {Γ = Γ} {Δ} {B = B ⊸ B'} f g) = 
  trans (cong₂ ⊸lC (focus-embR f) (focus-embF g))
  (trans (act⋆-⊸lC Γ (sw f) _)
  (trans (cong (act⋆ Γ) (act⋆-⊸lRC Δ f _))
         (act⋆act⋆ Γ Δ _)))
focus-embF (⊸l {Γ = Γ} {Δ} {B = I} f (blur (Il g))) = 
  trans (cong₂ ⊸lC (focus-embR f) (focus-embL (Il g)))
  (trans (act⋆-⊸lC Γ (sw f) _)
  (trans (cong (act⋆ Γ) (act⋆-⊸lRC Δ f _))
         (act⋆act⋆ Γ Δ _)))

focus-emb : {S : Stp} {Γ : Cxt} {C : Fma}
  → (f : S ∣ [] ； Γ ⊢C C)
  → focus (emb f) ≡ f
focus-emb f = focus-embC f  

-- ====================================================================

-- ∀ f. emb (focus f) ≗ f

emb-exC : ∀{S Φ Ψ Δ Λ A B C}
  → (f : S ∣ Δ ； Λ ⊢C C)
  → (eq : Λ ≡ Φ ++ A ∷ B ∷ Ψ)
  → embC (exC' Φ f eq) ≗ ex {Γ = Δ ++ Φ} (embC (subst (λ x → S ∣ Δ ； x ⊢C C) eq f))
emb-exC {Φ = Φ} (sw f) eq = ⊥-elim ([]disj∷ Φ eq)
emb-exC {Φ = []} (ex {Φ = Φ} {Γ} (ex {Φ = Φ₁} {Γ₁} f refl) eq) refl with cases++ Φ Φ₁ Γ Γ₁ eq
emb-exC {_} {[]} {_} {_} {_ ∷ _ ∷ _} (ex {Φ = Φ} {.(Γ₀ ++ Γ₁)} (ex {Φ = .(Φ ++ _ ∷ Γ₀)} {Γ₁} f refl) refl) refl | inj₁ (Γ₀ , refl , refl) =
  cong-ex-fma-cxt Γ₁ (≡-to-≗ (ex-fma-cxt++ Γ₀ (_ ∷ Γ₁) (embC f)))
  ∙ ex-fma-cxt-braid Γ₁
  ∙ ex {Γ = Φ ++ Γ₀ ++ Γ₁} (cong-ex-fma-cxt Γ₁ (ex-fma-cxt-ex-fma-cxt Γ₀ Γ₁)
                            ∙ ~ (≡-to-≗ (ex-fma-cxt++ Γ₀ Γ₁ _)))
emb-exC {_} {[]} {_} {_} {_ ∷ _ ∷ _} (ex {Φ = .(Φ₁ ++ Γ₀)} {Γ} (ex {Φ = Φ₁} {.(Γ₀ ++ _ ∷ Γ)} f refl) refl) refl | inj₂ (Γ₀ , refl , refl) =
  ≡-to-≗ (ex-fma-cxt++ Γ₀ Γ _)
  ∙ cong-ex-fma-cxt Γ (~ ex-fma-cxt-ex-fma-cxt {Γ₂ = []} Γ₀ Γ
                       ∙ cong-ex-fma-cxt Γ (~ ex-iso {Γ = Φ₁ ++ Γ₀}))
  ∙ ex-fma-cxt-braid {Γ = Φ₁ ++ Γ₀} Γ
  ∙ ex {Γ = Φ₁ ++ Γ₀ ++ Γ} (cong-ex-fma-cxt Γ (≡-to-≗ (sym (ex-fma-cxt++ Γ₀ (_ ∷ Γ) _))))
emb-exC {Φ = D ∷ Φ} (ex {Γ = Γ} f refl) refl =
  cong-ex-fma-cxt Γ (emb-exC f refl) ∙ ex-ex-fma-cxt Γ

emb-ufC : ∀{Φ Γ A C}
  → (f : just A ∣ Φ ； Γ ⊢C C)
  → embC (ufC f) ≗ uf (embC f)
emb-ufR : ∀{Γ A C}
  → (f : just A ∣ Γ ⊢R C)
  → embR (ufR f) ≗ uf (embR f)

emb-ufC (ex {Φ = Φ} {Γ} f refl) = 
  cong-ex-fma-cxt Γ (emb-ufC f)
  ∙ ex-fma-cxt-uf Φ Γ
emb-ufC (sw f) = emb-ufR f

emb-ufR (⊸r f) =
  ⊸r (emb-ufC f) ∙ ⊸ruf
emb-ufR (sw f) = refl

emb-IlC : ∀{Φ Γ C}
  → (f : nothing ∣ Φ ； Γ ⊢C C)
  → embC (IlC f) ≗ Il (embC f)
emb-IlR : ∀{Γ C}
  → (f : nothing ∣ Γ ⊢R C)
  → embR (IlR f) ≗ Il (embR f)

emb-IlC (ex {Φ = Φ} {Γ} f refl) =
  cong-ex-fma-cxt Γ (emb-IlC f)
  ∙ ex-fma-cxt-Il Φ Γ
emb-IlC (sw f) = emb-IlR f

emb-IlR (⊸r f) =
  ⊸r (emb-IlC f) ∙ ⊸rIl
emb-IlR (sw f) = refl

emb-⊸rC : ∀{S Φ Γ Λ A B}
  → (f : S ∣ Φ ； Λ ⊢C B) (eq : Λ ≡ Γ ∷ʳ A)
  → embC (⊸rC' Γ f eq) ≗ ⊸r (embC (subst (λ x → S ∣ Φ ； x ⊢C B) eq f))
emb-⊸rC {Γ = Γ} (sw f) eq = ⊥-elim ([]disj∷ Γ eq)
emb-⊸rC {Γ = []} (ex f refl) refl = refl
emb-⊸rC {Γ = x ∷ Γ} (ex {Γ = Γ₁} f refl) refl =
  cong-ex-fma-cxt Γ₁ (emb-⊸rC f refl)
  ∙ ex-fma-cxt-⊸r _ Γ₁

emb-⊸lRR : ∀{Γ Δ A B C}
  → (f : nothing ∣ Γ ⊢R A) (g : just B ∣ Δ ⊢R C)
  → embR (⊸lRR f g) ≗ ⊸l (embR f) (embR g)
emb-⊸lRC : ∀{Φ Ψ Γ A B C}
  → (f : nothing ∣ Φ ⊢R A) (g : just B ∣ Ψ ； Γ ⊢C C)
  → embC (⊸lRC f g) ≗ ⊸l (embR f) (embC g)

emb-⊸lRR f (⊸r g) = ⊸r (emb-⊸lRC f g) ∙ ⊸r⊸l
emb-⊸lRR {B = ` X} f (sw (lf g)) = refl
emb-⊸lRR {B = B ⊸ B'} f (sw (lf g)) = refl
emb-⊸lRR {B = I} f (sw (Il g)) = refl

emb-⊸lRC f (ex {Γ = Γ} g refl) =
  cong-ex-fma-cxt Γ (emb-⊸lRC f g) ∙ ex-fma-cxt-⊸l₂ _ Γ
emb-⊸lRC f (sw g) = emb-⊸lRR f g

emb-⊸lC : ∀{Φ Γ Δ A B C}
  → (f : nothing ∣ Φ ； Γ ⊢C A) (g : just B ∣ [] ； Δ ⊢C C)
  → embC (⊸lC f g) ≗ ⊸l (embC f) (embC g)
emb-⊸lC (ex {Γ = Γ} f refl) g =
  cong-ex-fma-cxt Γ (emb-⊸lC f g) ∙ ex-fma-cxt-⊸l₁ _ Γ
emb-⊸lC (sw f) g = emb-⊸lRC f g

emb-axC : ∀ A → embC (axC A) ≗ ax
emb-axC (` X) = refl
emb-axC I = ~ axI
emb-axC (A ⊸ B) =
  ⊸r (emb-⊸lC (ufC (axC A)) (axC B)
     ∙ ⊸l (emb-ufC (axC A) ∙ uf (emb-axC A)) (emb-axC B))
  ∙ ~ ax⊸

emb-focus : {S : Stp} → {Γ : Cxt} → {C : Fma} →
             (f : S ∣ Γ ⊢ C)  → emb (focus f) ≗ f
emb-focus ax = emb-axC _
emb-focus (uf f) =
  emb-ufC (focus f) ∙ uf (emb-focus f)
emb-focus (ex f) =
  emb-exC (focus f) refl ∙ ex (emb-focus f)
emb-focus Ir = refl
emb-focus (Il f) =
  emb-IlC (focus f) ∙ Il (emb-focus f)
emb-focus (⊸r f) =
  emb-⊸rC (focus f) refl ∙ ⊸r (emb-focus f)
emb-focus (⊸l f g) =
  emb-⊸lC (focus f) (focus g) ∙ ⊸l (emb-focus f) (emb-focus g)

