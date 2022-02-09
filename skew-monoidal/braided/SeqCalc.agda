{-# OPTIONS --rewriting #-}

module SeqCalc where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.Bool
open import Data.Bool.Properties
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import Fsk

-- =======================================================================

-- Sequent calculus

-- -- (In addition to the conclusion, sequents have a stoup and a context.)

Stp : Set
Stp = Maybe Fma

Cxt : Set
Cxt = List Fma


-- In the braided case we have two exchange rules, see the Boolean
-- argument of ex.

infix 15 _∣_⊢_

data _∣_⊢_ : Stp → Cxt → Fma → Set where
  ax : {A : Fma} → just A ∣ [] ⊢ A
  uf : {Γ : Cxt} → {A C : Fma} → 
              just A ∣ Γ ⊢ C → nothing ∣ A ∷ Γ ⊢ C
  ex : {S : Stp} → {Γ Δ : Cxt} → {A B C : Fma} → Bool →
              S ∣ Γ ++ A ∷ B ∷ Δ ⊢ C → S ∣ Γ ++ B ∷ A ∷ Δ ⊢ C 
  Ir : nothing ∣ [] ⊢ I
  ⊗r : {S : Stp} → {Γ Δ : Cxt} → {A B : Fma} → 
              S ∣ Γ ⊢ A → nothing ∣ Δ ⊢ B → S ∣ Γ ++ Δ ⊢ A ⊗ B 
  Il : {Γ : Cxt} → {C : Fma} → 
              nothing ∣ Γ ⊢ C → just I ∣ Γ ⊢ C 
  ⊗l : {Γ : Cxt} → {A B C : Fma} → 
              just A ∣ B ∷ Γ ⊢ C → just (A ⊗ B) ∣ Γ ⊢ C

subst-cxt : {S : Stp} → {Γ Γ' : Cxt} → {A : Fma} → 
      Γ ≡ Γ' → S ∣ Γ ⊢ A → S ∣ Γ' ⊢ A 
subst-cxt refl f = f

-- other general admissible form of exchange

ex-fma-cxt : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma} (b : Bool) → 
              S ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C → S ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C 
ex-fma-cxt [] b f = f
ex-fma-cxt {Γ = Γ} (B ∷ Λ) b f = ex-fma-cxt {Γ = Γ ++ B ∷ []} Λ b (ex b f) 

ex-cxt-cxt1 : {S : Stp} → {Γ Δ : Cxt} (Λ₁ Λ₂ : Cxt) → {C : Fma} → (b : Bool)→ 
              S ∣ Γ ++ Λ₁ ++ Λ₂ ++ Δ ⊢ C → S ∣ Γ ++ Λ₂ ++ Λ₁ ++ Δ ⊢ C 
ex-cxt-cxt1 {Γ = Γ} [] Λ₂ b f = f
ex-cxt-cxt1 {Γ = Γ} {Δ} (A ∷ Λ₁) Λ₂ b f =
  ex-fma-cxt {Γ = Γ} Λ₂ b (ex-cxt-cxt1 {Γ = Γ ++ A ∷ []} {Δ} Λ₁ Λ₂ b f)

ex-cxt-fma : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma} → Bool →  
              S ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C  → S ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C
ex-cxt-fma {Γ = Γ} [] b f = f
ex-cxt-fma {Γ = Γ} (B ∷ Λ) b f = ex b (ex-cxt-fma {Γ = Γ ++ B ∷ []} Λ b f)

ex-cxt-cxt2 : {S : Stp} → {Γ Δ : Cxt} (Λ₁ Λ₂ : Cxt) → {C : Fma} → Bool →  
              S ∣ Γ ++ Λ₁ ++ Λ₂ ++ Δ ⊢ C → S ∣ Γ ++ Λ₂ ++ Λ₁ ++ Δ ⊢ C 
ex-cxt-cxt2 Λ₁ [] b f = f
ex-cxt-cxt2 {Γ = Γ} {Δ} Λ₁ (A ∷ Λ₂) b f =
  ex-cxt-cxt2 {Γ = Γ ++ A ∷ []}{Δ} Λ₁ Λ₂ b (ex-cxt-fma {Γ = Γ}{Λ₂ ++ Δ} Λ₁ b f) 

ex-cxt-cxt2[] : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {C : Fma}(b : Bool)
  → (f : S ∣ Γ ++ Λ ++ Δ ⊢ C)
  → ex-cxt-cxt2 {Γ = Γ}{Δ} [] Λ b f ≡ f
ex-cxt-cxt2[] [] b f = refl
ex-cxt-cxt2[] {Γ = Γ}{Δ} (x ∷ Λ) b f = ex-cxt-cxt2[] {Γ = Γ ++ x ∷ []}{Δ} Λ b f

-- ====================================================================

-- -- inverted left rules

Il-1 : {Γ : Cxt} → {C : Fma} → 
              just I ∣ Γ ⊢ C → nothing ∣ Γ ⊢ C
Il-1 ax = Ir
Il-1 (ex b p) = ex b (Il-1 p)
Il-1 (⊗r p p₁) = ⊗r (Il-1 p) p₁
Il-1 (Il p) = p

⊗l-1 : {Γ : Cxt} → {A B C : Fma} → 
            just (A ⊗ B) ∣ Γ ⊢ C → just A ∣ B ∷ Γ ⊢ C
⊗l-1 ax = ⊗r ax (uf ax)
⊗l-1 (ex {Γ = Γ} b f) = ex {Γ = _ ∷ Γ} b (⊗l-1 f)
⊗l-1 (⊗r f f₁) = ⊗r (⊗l-1 f) f₁
⊗l-1 (⊗l f) = f

-- ====================================================================

-- admissibility of cut

-- -- (There are two kinds of cut: stoup ccut and context cut.)

mutual 
  scut : {S : Stp} → {Γ Δ' : Cxt} → {A C : Fma} → 
              S ∣ Γ ⊢ A  →  just A ∣ Δ' ⊢ C  →  S ∣ Γ ++ Δ' ⊢ C

  scut ax g = g
  scut (uf f) g = uf (scut f g)
  scut (ex b f) g = ex b (scut f g)
  scut Ir ax = Ir
  scut Ir (ex b g) = ex b (scut Ir g)
  scut Ir (⊗r g g') = ⊗r (scut Ir g) g'
  scut Ir (Il g) = g
  scut (⊗r f f') ax = ⊗r f f'
  scut (⊗r {Γ = Γ}{Δ} f f') (ex {Γ = Γ'} b g) = ex {Γ = Γ ++ Δ ++ Γ'} b (scut (⊗r f f') g)
  scut (⊗r f f') (⊗r g g') = ⊗r (scut (⊗r f f') g) g'
  scut (⊗r f f') (⊗l g) = scut f (ccut [] f' g refl)
  scut (Il f) g = Il (scut f g)
  scut (⊗l f) g = ⊗l (scut f g)


  ccut : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
             nothing ∣ Γ ⊢ A  →  T ∣ Δ ⊢ C  → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                        T ∣ (Δ₀ ++ Γ) ++ Δ' ⊢ C

  ccut Δ₀ f ax p = ⊥-elim ([]disj∷ Δ₀ p)
  ccut Δ₀ {Δ'} f (ex {Γ = Γ}{Δ}{A}{B} b g) p with cases++2 Δ₀ Γ Δ' Δ p
  ccut {Γ = Γ} Δ₀ f (ex b g) p | inj₁ (Γ₀ , refl , refl) = ex {Γ = Δ₀ ++ Γ ++ Γ₀} b (ccut Δ₀ f g refl)
  ccut ._ {Δ'} f (ex {Γ = Γ} {_} {A} {B} b g) p | inj₂ (inj₁ (Γ₀ , refl , refl)) = ex {Γ = Γ} b (ccut (Γ ++ A ∷ B ∷ Γ₀) f g refl)
  ccut {Γ = Γ} Δ₀ {Δ'} f (ex {Δ = Δ} {A} {B} b g) p | inj₂ (inj₂ (inj₁ (refl , refl , refl)))
    = ex-fma-cxt Γ b (ccut (Δ₀ ++ A ∷ []) f g refl)
  ccut {Γ = Γ'} Δ₀ f (ex {Γ = Γ} {Δ} {A} {B} b g) p | inj₂ (inj₂ (inj₂ (refl , refl , refl)))
    = ex-cxt-fma Γ' b (ccut Γ f g refl)
  ccut Δ₀ f (uf g) p with cases∷ Δ₀ p 
  ccut .[] f (uf g) p | inj₁ (refl , refl , refl) = scut f g
  ccut .(_ ∷ Δ₀) f (uf g) p | inj₂ (Δ₀ , r , refl) =  uf (ccut Δ₀ f g r)
  ccut Δ₀ f Ir p = ⊥-elim ([]disj∷ Δ₀ p)
  ccut Δ₀ {Δ'} f (⊗r {Γ = Γ}{Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
  ccut Δ₀ f (⊗r g g') p | inj₁ (Γ₀ , refl , refl) = ⊗r (ccut Δ₀ f g refl) g'
  ccut ._ f (⊗r g g') p | inj₂ (Γ₀ , refl , refl) = ⊗r g (ccut Γ₀  f g' refl)
  ccut Δ₀ f (Il g) r = Il (ccut Δ₀ f g r) 
  ccut Δ₀ f (⊗l {B = B} g) r = ⊗l (ccut (B ∷ Δ₀) f g (cong (_∷_ B) r))

-- ====================================================================

-- -- equality of proofs 

data _≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where
  refl : ∀{S}{Γ}{A}{f : S ∣ Γ ⊢ A} → f ≗ f
  ~_ : ∀{S}{Γ}{A}{f g : S ∣ Γ ⊢ A} → f ≗ g → g ≗ f
  _∙_ : ∀{S}{Γ}{A}{f g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗ h → f ≗ h
  uf : ∀{Γ}{A}{C}{f g : just A ∣ Γ ⊢ C} → f ≗ g → uf f ≗ uf g
  ⊗l : ∀{Γ}{A}{B}{C}{f g : just A ∣ B ∷ Γ ⊢ C} → f ≗ g → ⊗l f ≗ ⊗l g
  Il : ∀{Γ}{C}{f g : nothing ∣ Γ ⊢ C} → f ≗ g → Il f ≗ Il g
  ⊗r : ∀{S}{Γ}{Δ}{A}{B}{f g : S ∣ Γ ⊢ A}{f' g' : nothing ∣ Δ ⊢ B}
    → f ≗ g → f' ≗ g' → ⊗r f f' ≗ ⊗r g g'
  axI : ax ≗ Il Ir
  ax⊗ : {A B : Fma} → ax {A ⊗ B} ≗ ⊗l (⊗r ax (uf ax))
  ⊗ruf : {Γ Δ : Cxt}{A A' B : Fma}
    → {f : just A' ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (uf f) g ≗ uf (⊗r f g)
  ⊗rIl : {Γ Δ : Cxt}{A B : Fma}
    → {f : nothing ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (Il f) g ≗ Il (⊗r f g)
  ⊗r⊗l : {Γ Δ : Cxt}{A A' B B' : Fma}
    → {f : just A' ∣ B' ∷ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (⊗l f) g ≗ ⊗l (⊗r f g)

-- equations for ex
  ex : ∀{S Γ Δ A B C}{f g : S ∣ Γ ++ A ∷ B ∷ Δ ⊢ C} b
    → f ≗ g → ex b f ≗ ex b g
  exex : {S : Stp}{Γ₁ Γ₂ Γ₃ : Cxt} {A B A' B' C : Fma} {b : Bool}
    → {f : S ∣ Γ₁ ++ A ∷ B ∷ Γ₂ ++ A' ∷ B' ∷ Γ₃ ⊢ C}
    → ex {Γ = Γ₁ ++ B ∷ A ∷ Γ₂} true (ex {Γ = Γ₁} b f)
         ≗ ex {Γ = Γ₁} b (ex {Γ = Γ₁ ++ A ∷ B ∷ Γ₂} true f)
  exuf : {Γ Δ : Cxt}{A' A B C : Fma}
    → {f : just A' ∣ Γ ++ A ∷ B ∷ Δ ⊢ C}
    → ex {Γ = A' ∷ Γ} true (uf f) ≗ uf (ex true f)  
  exIl : {Γ Δ : Cxt}{A B C : Fma}
    → {f : nothing ∣ Γ ++ A ∷ B ∷ Δ ⊢ C}
    → ex true (Il f) ≗ Il (ex true f)
  ex⊗l : {Γ Δ : Cxt}{A' B' A B C : Fma}
    → {f : just A' ∣ B' ∷ Γ ++ A ∷ B ∷ Δ ⊢ C}
    → ex true (⊗l f) ≗ ⊗l (ex {Γ = B' ∷ Γ} true f)
  ex⊗r₁ : {S : Stp}{Γ₁ Γ₂ Δ : Cxt}{A B C C' : Fma}
    → {f : S ∣ Γ₁ ++ A ∷ B ∷ Γ₂ ⊢ C}{g : nothing ∣ Δ ⊢ C'}
    → ex true (⊗r f g) ≗ ⊗r (ex true f) g
  ex⊗r₂ : {S : Stp}{Γ Δ₁ Δ₂ : Cxt}{A B C C' : Fma}
    → {f : S ∣ Γ ⊢ C}{g : nothing ∣ Δ₁ ++ A ∷ B ∷ Δ₂ ⊢ C'}
    → ex {Γ = Γ ++ Δ₁} true (⊗r f g) ≗ ⊗r f (ex true g)
  ex-iso : ∀{S Γ Δ A B C} {f : S ∣ Γ ++ A ∷ B ∷ Δ ⊢ C} b
    → ex {Γ = Γ} b (ex {Γ = Γ} (not b) f) ≗ f
  ex-braid : ∀{S Γ Δ A B C D} {f : S ∣ Γ ++ A ∷ B ∷ C ∷ Δ ⊢ D}
    → ex {Γ = Γ} true (ex {Γ = Γ ++ B ∷ []} true (ex {Γ = Γ} true f))
      ≗ ex {Γ = Γ ++ C ∷ []} true (ex {Γ = Γ} true (ex {Γ = Γ ++ A ∷ []} true f))

≡-to-≗ : ∀{S}{Γ}{A}{f f' : S ∣ Γ ⊢ A} → f ≡ f' → f ≗ f'
≡-to-≗ refl = refl

-- ====================================================================

-- some derivable equations of exchange

ex-braid' : ∀{S Γ Δ A B C D} {f : S ∣ Γ ++ A ∷ B ∷ C ∷ Δ ⊢ D}
  → ex {Γ = Γ ++ _ ∷ []} true (ex {Γ = Γ} true (ex {Γ = Γ ++ _ ∷ []} false f))
    ≗ ex {Γ = Γ} false (ex {Γ = Γ ++ _ ∷ []} true (ex {Γ = Γ} true f))
ex-braid' {Γ = Γ} =
  ~ (ex-iso _)
  ∙ ex _ (ex-braid ∙ ex {Γ = Γ ++ _ ∷ []} _ (ex _ (ex-iso {Γ = Γ ++ _ ∷ []} _)))

ex-braid'' : ∀{S Γ Δ A B C D} {f : S ∣ Γ ++ A ∷ B ∷ C ∷ Δ ⊢ D}
  → ex {Γ = Γ} true (ex {Γ = Γ ++ _ ∷ []} false (ex {Γ = Γ} false f))
    ≗ ex {Γ = Γ ++ _ ∷ []} false (ex {Γ = Γ} false (ex {Γ = Γ ++ _ ∷ []} true f))
ex-braid'' {Γ = Γ} =
  ~ (ex-iso {Γ = Γ ++ _ ∷ []} _)
  ∙ ex {Γ = Γ ++ _ ∷ []} _ (ex-braid' ∙ ex _ (ex {Γ = Γ ++ _ ∷ []} _ (ex-iso _)))

ex-braid-b : ∀{S Γ Δ A B C D} {f : S ∣ Γ ++ A ∷ B ∷ C ∷ Δ ⊢ D} b
  → ex {Γ = Γ} b (ex {Γ = Γ ++ B ∷ []} b (ex {Γ = Γ} b f))
    ≗ ex {Γ = Γ ++ C ∷ []} b (ex {Γ = Γ} b (ex {Γ = Γ ++ A ∷ []} b f))
ex-braid-b true = ex-braid
ex-braid-b {Γ = Γ} false =
  ~ (~ ex-iso _ ∙ ex _ (ex-braid'' ∙ ex {Γ = Γ ++ _ ∷ []} _ (ex _ (ex-iso {Γ = Γ ++ _ ∷ []} _))))

ex-braid-b2 : ∀{S Γ Δ A B C D} {f : S ∣ Γ ++ A ∷ B ∷ C ∷ Δ ⊢ D} b b'
  → ex {Γ = Γ} b' (ex {Γ = Γ ++ B ∷ []} b (ex {Γ = Γ} b f))
    ≗ ex {Γ = Γ ++ C ∷ []} b (ex {Γ = Γ} b (ex {Γ = Γ ++ A ∷ []} b' f))
ex-braid-b2 {Γ = Γ} true false =
  ex false (ex {Γ = Γ ++ _ ∷ []} true (ex true (~ (ex-iso {Γ = Γ ++ _ ∷ []} true))) 
           ∙ ~ ex-braid {Γ = Γ})
  ∙ ex-iso false
ex-braid-b2 true true = ex-braid
ex-braid-b2 {Γ = Γ} false false = ex-braid-b _
ex-braid-b2 {Γ = Γ} false true = 
  ex _ (ex {Γ = Γ ++ _ ∷ []} _ (ex _ (~ (ex-iso {Γ = Γ ++ _ ∷ []} _))) 
           ∙ ~ ex-braid-b {Γ = Γ} _)
  ∙ ex-iso _

ex-braid-b3 : ∀{S Γ Δ A B C D} {f : S ∣ Γ ++ A ∷ B ∷ C ∷ Δ ⊢ D} b b'
  → ex {Γ = Γ} b' (ex {Γ = Γ ++ B ∷ []} b' (ex {Γ = Γ} b f))
    ≗ ex {Γ = Γ ++ C ∷ []} b (ex {Γ = Γ} b' (ex {Γ = Γ ++ A ∷ []} b' f))
ex-braid-b3 {Γ = Γ} false false = ex-braid-b _
ex-braid-b3 {Γ = Γ} false true =
  ~ ex-iso {Γ = Γ ++ _ ∷ []} false
  ∙ ex {Γ = Γ ++ _ ∷ []} false (~ ex-braid
                               ∙ ex true (ex {Γ = Γ ++ _ ∷ []} true (ex-iso _)))
ex-braid-b3 {Γ = Γ} true false = 
  ~ ex-iso {Γ = Γ ++ _ ∷ []} _
  ∙ ex {Γ = Γ ++ _ ∷ []} _ (~ ex-braid-b _
                            ∙ ex _ (ex {Γ = Γ ++ _ ∷ []} _ (ex-iso _)))
ex-braid-b3 {Γ = Γ} true true = ex-braid

exex-b : {S : Stp}{Γ₁ Γ₂ Γ₃ : Cxt} {A B A' B' C : Fma}{b' : Bool}(b : Bool)
  → {f : S ∣ Γ₁ ++ A ∷ B ∷ Γ₂ ++ A' ∷ B' ∷ Γ₃ ⊢ C}
  → ex {Γ = Γ₁ ++ B ∷ A ∷ Γ₂} b (ex {Γ = Γ₁} b' f)
       ≗ ex {Γ = Γ₁} b' (ex {Γ = Γ₁ ++ A ∷ B ∷ Γ₂} b f)
exex-b {Γ₁ = Γ₁} {Γ₂} false = 
 ex {Γ = Γ₁ ++ _ ∷ _ ∷ Γ₂} false
        (ex _ (~ ex-iso {Γ = Γ₁ ++ _ ∷ _ ∷ Γ₂} true
              ∙ ex {Γ = Γ₁ ++ _ ∷ _ ∷ Γ₂} true (~ ex-iso (not _))
              ∙ exex)
        ∙ ex-iso _)
   ∙ ≡-to-≗ (cong (λ x → ex {Γ = Γ₁ ++ _ ∷ _ ∷ Γ₂} false (ex {Γ = Γ₁ ++ _ ∷ _ ∷ Γ₂} true (ex x _))) (not-involutive _))
   ∙ ex-iso {Γ = Γ₁ ++ _ ∷ _ ∷ Γ₂} false
exex-b {Γ₁ = Γ₁} {Γ₂} true = exex

exuf-b : {Γ Δ : Cxt}{A' A B C : Fma}(b : Bool)
  → {f : just A' ∣ Γ ++ A ∷ B ∷ Δ ⊢ C}
  → ex {Γ = A' ∷ Γ} b (uf f) ≗ uf (ex b f)  
exuf-b false =
  ex false (~ (exuf ∙ uf (ex-iso _)))
  ∙ ex-iso _
exuf-b true = exuf

exIl-b : {Γ Δ : Cxt}{A B C : Fma}(b : Bool)
  → {f : nothing ∣ Γ ++ A ∷ B ∷ Δ ⊢ C}
  → ex b (Il f) ≗ Il (ex b f)
exIl-b false =
  ex false (~ (exIl ∙ Il (ex-iso _)))
  ∙ ex-iso _
exIl-b true = exIl

ex⊗l-b : {Γ Δ : Cxt}{A B A' B' C : Fma}(b : Bool)
  → {f : just A' ∣ B' ∷ Γ ++ A ∷ B ∷ Δ ⊢ C}
  → ex b (⊗l f) ≗ ⊗l (ex {Γ = _ ∷ Γ} b f)
ex⊗l-b false =
  ex false (~ (ex⊗l ∙ ⊗l (ex-iso _)))
  ∙ ex-iso _
ex⊗l-b true = ex⊗l

ex⊗r₁-b : {S : Stp}{Γ₁ Γ₂ Δ : Cxt}{A B C C' : Fma}(b : Bool)
    → {f : S ∣ Γ₁ ++ A ∷ B ∷ Γ₂ ⊢ C}{g : nothing ∣ Δ ⊢ C'}
    → ex b (⊗r f g) ≗ ⊗r (ex b f) g
ex⊗r₁-b true = ex⊗r₁
ex⊗r₁-b false =
  ex false (~ (ex⊗r₁ ∙ ⊗r (ex-iso _) refl))
  ∙ ex-iso _

ex⊗r₂-b : {S : Stp}{Γ Δ₁ Δ₂ : Cxt}{A B C C' : Fma}(b : Bool)
  → {f : S ∣ Γ ⊢ C}{g : nothing ∣ Δ₁ ++ A ∷ B ∷ Δ₂ ⊢ C'}
  → ex {Γ = Γ ++ Δ₁} b (⊗r f g) ≗ ⊗r f (ex b g)
ex⊗r₂-b true = ex⊗r₂
ex⊗r₂-b {Γ = Γ} {Δ₁} false =
  ex {Γ = Γ ++ Δ₁} false (~ (ex⊗r₂ ∙ ⊗r refl (ex-iso _)))
  ∙ ex-iso {Γ = Γ ++ Δ₁} _


-- ====================================================================

-- -- equational reasoning sugar for ≗

infix 4 _≗'_
infix 1 proof≗_
infixr 2 _≗〈_〉_
infix 3 _qed≗

data _≗'_ {S  : Stp}{Γ : Cxt}{A : Fma} (f g : S ∣ Γ ⊢ A) : Set where
  relto :  f ≗ g → f ≗' g

proof≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} {f g : S ∣ Γ ⊢ A} → f ≗' g → f ≗ g
proof≗ relto p = p

_≗〈_〉_ :  {S  : Stp}{Γ : Cxt}{A : Fma} (f : S ∣ Γ ⊢ A) {g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗' h → f ≗' h 

_ ≗〈 p 〉 relto q = relto (p ∙ q)

_qed≗  :  {S  : Stp}{Γ : Cxt}{A : Fma} (f : S ∣ Γ ⊢ A) → f ≗' f
_qed≗ _ = relto refl

-- ====================================================================

-- compatibility of inverse left rules with ≗

congIl-1 : {Γ : Cxt} → {C : Fma} → 
              {f g : just I ∣ Γ ⊢ C} →
              f ≗ g → Il-1 f ≗ Il-1 g
congIl-1 refl = refl
congIl-1 (~ p) = ~ (congIl-1 p)
congIl-1 (p ∙ p₁) = (congIl-1 p) ∙ (congIl-1 p₁)
congIl-1 (Il p) = p
congIl-1 (⊗r p p₁) = ⊗r (congIl-1 p) p₁
congIl-1 axI = refl
congIl-1 ⊗rIl = refl
congIl-1 (ex b p) = ex b (congIl-1 p)
congIl-1 exex = exex
congIl-1 exIl = refl
congIl-1 ex⊗r₁ = ex⊗r₁
congIl-1 ex⊗r₂ = ex⊗r₂
congIl-1 (ex-iso b) = ex-iso b
congIl-1 ex-braid = ex-braid

cong⊗l-1 : {Γ : Cxt} → {A B C : Fma} → 
            {f g : just (A ⊗ B) ∣ Γ ⊢ C} →
            f ≗ g → ⊗l-1 f ≗ ⊗l-1 g
cong⊗l-1 refl = refl
cong⊗l-1 (~ p) = ~ (cong⊗l-1 p)
cong⊗l-1 (p ∙ p₁) = (cong⊗l-1 p) ∙ (cong⊗l-1 p₁)
cong⊗l-1 (⊗l p) = p
cong⊗l-1 (⊗r p p₁) = ⊗r (cong⊗l-1 p) p₁
cong⊗l-1 ax⊗ = refl
cong⊗l-1 ⊗r⊗l = refl            
cong⊗l-1 (ex b p) = ex b (cong⊗l-1 p)
cong⊗l-1 exex = exex
cong⊗l-1 ex⊗l = refl
cong⊗l-1 ex⊗r₁ = ex⊗r₁
cong⊗l-1 ex⊗r₂ = ex⊗r₂
cong⊗l-1 (ex-iso b) = ex-iso b
cong⊗l-1 ex-braid = ex-braid

-- ====================================================================

-- Il-1 and ⊗l-1 are inverses up to ≗

IlIl-1 : {Γ : Cxt} → {C : Fma} → 
              (f : just I ∣ Γ ⊢ C) → Il (Il-1 f) ≗ f
IlIl-1 ax = ~ axI
IlIl-1 (⊗r f f₁) = (~ ⊗rIl) ∙ (⊗r (IlIl-1 f) refl)
IlIl-1 (Il f) = refl            
IlIl-1 (ex b f) = ~ (exIl-b b) ∙ ex b (IlIl-1 f)

⊗l⊗l-1 : {Γ : Cxt} → {A B C : Fma} → 
            (f : just (A ⊗ B) ∣ Γ ⊢ C) → ⊗l (⊗l-1 f) ≗ f
⊗l⊗l-1 ax = ~ ax⊗
⊗l⊗l-1 (⊗r f f₁) = (~ ⊗r⊗l) ∙ (⊗r (⊗l⊗l-1 f) refl)
⊗l⊗l-1 (⊗l f) = refl            
⊗l⊗l-1 (ex b f) = ~ ex⊗l-b b ∙ ex b (⊗l⊗l-1 f)

-- ====================================================================

-- Lots of admissible equations involving exchange

cong-ex-fma-cxt : ∀{S Γ Δ} Λ {A C}{f g : S ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C} b
    → f ≗ g → ex-fma-cxt {Γ = Γ}{Δ} Λ b f ≗ ex-fma-cxt Λ b g
cong-ex-fma-cxt [] b eq = eq
cong-ex-fma-cxt {Γ = Γ} (x ∷ Λ) b eq = cong-ex-fma-cxt Λ b (ex b eq)

cong-ex-cxt-fma : ∀{S Γ Δ} Λ {A C}{f g : S ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C} b
    → f ≗ g → ex-cxt-fma {Γ = Γ} Λ b f ≗ ex-cxt-fma Λ b g
cong-ex-cxt-fma [] b eq = eq
cong-ex-cxt-fma {Γ = Γ} (x ∷ Λ) b eq = ex b (cong-ex-cxt-fma {Γ = Γ ++ x ∷ []} Λ b eq)

cong-ex-cxt-cxt2 : ∀{S Γ Δ} Λ₁ Λ₂ {C}{f g : S ∣ Γ ++ Λ₁ ++ Λ₂ ++ Δ ⊢ C} b
    → f ≗ g → ex-cxt-cxt2 {Γ = Γ}{Δ} Λ₁ Λ₂ b f ≗ ex-cxt-cxt2 {Γ = Γ}{Δ} Λ₁ Λ₂ b g
cong-ex-cxt-cxt2 Λ₁ [] b p = p
cong-ex-cxt-cxt2 Λ₁ (x ∷ Λ₂) b p =
  cong-ex-cxt-cxt2 Λ₁ Λ₂ b (cong-ex-cxt-fma Λ₁ b p)

ex-cxt-fma-ex : ∀{S Γ₁ Γ₂ Γ₃} Λ {A B A' C}{f : S ∣ Γ₁ ++ A ∷ B ∷ Γ₂ ++ Λ ++ A' ∷ Γ₃ ⊢ C}{b'} b
  → ex-cxt-fma {Γ = Γ₁ ++ B ∷ A ∷ Γ₂} Λ b (ex {Γ = Γ₁} b' f)
      ≗ ex {Γ = Γ₁} b' (ex-cxt-fma {Γ = Γ₁ ++ A ∷ B ∷ Γ₂} Λ b f)
ex-cxt-fma-ex [] b = refl
ex-cxt-fma-ex {Γ₁ = Γ₁} {Γ₂ = Γ₂}{Γ₃} (x ∷ Λ) b = 
  ex {Γ = Γ₁ ++ _ ∷ _ ∷ Γ₂} b (ex-cxt-fma-ex {Γ₂ = Γ₂ ++ _ ∷ []} Λ b)  ∙ exex-b b

ex-fma-cxt-ex : ∀{S Γ₁ Γ₂ Γ₃} Λ {A B A' C}{f : S ∣ Γ₁ ++ A ∷ B ∷ Γ₂ ++ A' ∷ Λ ++ Γ₃ ⊢ C}{b'} b
  → ex-fma-cxt {Γ = Γ₁ ++ B ∷ A ∷ Γ₂}{Γ₃} Λ b (ex {Γ = Γ₁} b' f)
      ≗ ex {Γ = Γ₁} b' (ex-fma-cxt {Γ = Γ₁ ++ A ∷ B ∷ Γ₂} Λ b f)
ex-fma-cxt-ex [] b = refl
ex-fma-cxt-ex {Γ₁ = Γ₁} {Γ₂} {Γ₃} (x ∷ Λ) b =
  cong-ex-fma-cxt Λ b (exex-b b) ∙ ex-fma-cxt-ex Λ b

ex-ex-cxt-fma : ∀{S Γ₁ Γ₂ Γ₃} Λ {A B A' C}{f : S ∣ Γ₁ ++ Λ ++ A' ∷ Γ₂ ++ A ∷ B ∷ Γ₃ ⊢ C}{b'} b
  → ex-cxt-fma {Γ = Γ₁} Λ b (ex {Γ = Γ₁ ++ Λ ++ _ ∷ Γ₂} b' f)
      ≗ ex {Γ = Γ₁ ++ _ ∷ Λ ++ Γ₂} b' (ex-cxt-fma {Γ = Γ₁} Λ b f)
ex-ex-cxt-fma [] b = refl
ex-ex-cxt-fma {Γ₁ = Γ₁} {Γ₂} (x ∷ Λ) b =
  ex b (ex-ex-cxt-fma {Γ₁ = Γ₁ ++ _ ∷ []} Λ b) ∙ ~ exex-b {Γ₁ = Γ₁}{Λ ++ Γ₂} _

ex-ex-fma-cxt : ∀{S Γ₁ Γ₂ Γ₃} Λ {A B A' C}{f : S ∣ Γ₁ ++ A' ∷ Λ ++ Γ₂ ++ A ∷ B ∷ Γ₃ ⊢ C}{b'} b
  → ex-fma-cxt {Γ = Γ₁} Λ b (ex {Γ = Γ₁ ++ _ ∷ Λ ++ Γ₂} b' f)
      ≗ ex {Γ = Γ₁ ++ Λ ++ _ ∷ Γ₂} b' (ex-fma-cxt {Γ = Γ₁} Λ b f)
ex-ex-fma-cxt [] b = refl
ex-ex-fma-cxt {Γ₁ = Γ₁} {Γ₂} (x ∷ Λ) b = 
  cong-ex-fma-cxt Λ b (~ exex-b {Γ₁ = Γ₁}{Λ ++ Γ₂} _) ∙ ex-ex-fma-cxt Λ b 

ex-fma-cxt-ex-fma-cxt : ∀{S Γ₁ Γ₂ Γ₃} Λ Λ' {A A' C}{f : S ∣ Γ₁ ++ A ∷ Λ ++ Γ₂ ++ A' ∷ Λ' ++ Γ₃ ⊢ C}{b'} b
  → ex-fma-cxt {Γ = Γ₁ ++ Λ ++ A ∷ Γ₂}{Γ₃} Λ' b (ex-fma-cxt {Γ = Γ₁} Λ b' f)
      ≗ ex-fma-cxt {Γ = Γ₁} Λ b' (ex-fma-cxt {Γ = Γ₁ ++ A ∷ Λ ++ Γ₂} Λ' b f)
ex-fma-cxt-ex-fma-cxt [] Λ' b = refl
ex-fma-cxt-ex-fma-cxt {Γ₁ = Γ₁}  (x ∷ Λ) Λ' b =
  ex-fma-cxt-ex-fma-cxt {Γ₁ = Γ₁ ++ _ ∷ []} Λ Λ' b
  ∙ cong-ex-fma-cxt Λ _ (ex-fma-cxt-ex Λ' b)

ex-cxt-fma-ex-cxt-fma : ∀{S Γ₁ Γ₂ Γ₃} Λ Λ' {A A' C}{f : S ∣ Γ₁ ++ Λ ++ A ∷ Γ₂ ++ Λ' ++ A' ∷ Γ₃ ⊢ C}{b'} b
  → ex-cxt-fma {Γ = Γ₁ ++ A ∷ Λ ++ Γ₂} Λ' b (ex-cxt-fma {Γ = Γ₁} Λ b' f)
      ≗ ex-cxt-fma {Γ = Γ₁} Λ b' (ex-cxt-fma {Γ = Γ₁ ++ Λ ++ A ∷ Γ₂} Λ' b f)
ex-cxt-fma-ex-cxt-fma [] Λ' b = refl
ex-cxt-fma-ex-cxt-fma {Γ₁ = Γ₁} {Γ₂} (x ∷ Λ) Λ' b =
  ex-cxt-fma-ex {Γ₁ = Γ₁}{Λ ++ Γ₂} Λ' _
  ∙ ex _ (ex-cxt-fma-ex-cxt-fma {Γ₁ = Γ₁ ++ x ∷ []} Λ Λ' b)

ex-cxt-fma-braid : ∀{S Γ} Λ {Δ A B C} b
  → {f : S ∣ Γ ++ Λ ++ B ∷ A ∷ Δ ⊢ C}
  → ex {Γ = Γ} b (ex-cxt-fma {Γ = Γ ++ B ∷ []} Λ b (ex-cxt-fma {Γ = Γ} Λ b f))
    ≗ ex-cxt-fma {Γ = Γ ++ A ∷ []} Λ b (ex-cxt-fma {Γ = Γ} Λ b (ex {Γ = Γ ++ Λ} b f))
ex-cxt-fma-braid [] b = refl
ex-cxt-fma-braid {Γ = Γ} (x ∷ Λ) {Δ} {A} {B} b {f = f} =
  proof≗
    ex {Γ = Γ} b (ex {Γ = Γ ++ B ∷ []} b (ex-cxt-fma {Γ = Γ ++ B ∷ x ∷ []} Λ b (ex {Γ = Γ} b (ex-cxt-fma {Γ = Γ ++ x ∷ []} Λ b f))))
  ≗〈 ex b (ex {Γ = Γ ++ B ∷ []} b (ex-cxt-fma-ex Λ b)) 〉
    ex {Γ = Γ} b (ex {Γ = Γ ++ B ∷ []} b (ex {Γ = Γ} b (ex-cxt-fma {Γ = Γ ++ x ∷ B ∷ []} Λ b (ex-cxt-fma {Γ = Γ ++ x ∷ []} Λ b f))))
  ≗〈 ex-braid-b b 〉 
    ex {Γ = Γ ++ A ∷ []} b (ex {Γ = Γ} b (ex {Γ = Γ ++ x ∷ []} b (ex-cxt-fma {Γ = Γ ++ x ∷ B ∷ []} Λ b (ex-cxt-fma {Γ = Γ ++ x ∷ []} Λ b f))))
  ≗〈 ex {Γ = Γ ++ A ∷ []} b (ex b (ex-cxt-fma-braid {Γ = Γ ++ x ∷ []} Λ b)) 〉
    ex {Γ = Γ ++ A ∷ []} b (ex {Γ = Γ} b (ex-cxt-fma {Γ = Γ ++ x ∷ A ∷ []} Λ b (ex-cxt-fma {Γ = Γ ++ x ∷ []} Λ b (ex {Γ = Γ ++ x ∷ Λ} b f))))
  ≗〈 ex {Γ = Γ ++ A ∷ []} b (~ (ex-cxt-fma-ex Λ b)) 〉
    _
  qed≗

ex-fma-cxt-braid : ∀{S Γ} Λ {Δ A B C} b
  → {f : S ∣ Γ ++ B ∷ A ∷ Λ ++ Δ ⊢ C}
  → ex-fma-cxt {Γ = Γ} Λ b (ex-fma-cxt {Γ = Γ ++ _ ∷ []}{Δ} Λ b (ex {Γ = Γ} b f))
    ≗ ex {Γ = Γ ++ Λ} b (ex-fma-cxt {Γ = Γ} Λ b (ex-fma-cxt {Γ = Γ ++ _ ∷ []} Λ b f))
ex-fma-cxt-braid [] b = refl
ex-fma-cxt-braid {Γ = Γ} (x ∷ Λ) b {f = f} =
  proof≗
    ex-fma-cxt {Γ = Γ ++ _ ∷ []} Λ b (ex b (ex-fma-cxt {Γ = Γ ++ _ ∷ _ ∷ []} Λ b (ex {Γ = Γ ++ _ ∷ []} b (ex b f))))
  ≗〈 cong-ex-fma-cxt Λ b (~ (ex-fma-cxt-ex Λ b)) 〉
    ex-fma-cxt {Γ = Γ ++ _ ∷ []} Λ b (ex-fma-cxt {Γ = Γ ++ _ ∷ _ ∷ []} Λ b (ex {Γ = Γ} b (ex {Γ = Γ ++ _ ∷ []} b (ex {Γ = Γ} b f))))
  ≗〈 cong-ex-fma-cxt Λ b (cong-ex-fma-cxt Λ b (ex-braid-b b)) 〉 --ex-braid
    ex-fma-cxt {Γ = Γ ++ _ ∷ []} Λ b (ex-fma-cxt {Γ = Γ ++ _ ∷ _ ∷ []} Λ b (ex {Γ = Γ ++ _ ∷ []} b (ex {Γ = Γ} b (ex {Γ = Γ ++ _ ∷ []} b f))))
  ≗〈 ex-fma-cxt-braid {Γ = Γ ++ _ ∷ []} Λ b 〉
    ex {Γ = Γ ++ _ ∷ Λ} b (ex-fma-cxt {Γ = Γ ++ _ ∷ []} Λ b (ex-fma-cxt {Γ = Γ ++ _ ∷ _ ∷ []} Λ b (ex b (ex {Γ = Γ ++ _ ∷ []} b f))))
  ≗〈 ex {Γ = Γ ++ _ ∷ Λ} b (cong-ex-fma-cxt Λ b (ex-fma-cxt-ex Λ b)) 〉
    ex {Γ = Γ ++ _ ∷ Λ} b (ex-fma-cxt {Γ = Γ ++ _ ∷ []} Λ b (ex b (ex-fma-cxt {Γ = Γ ++ _ ∷ _ ∷ []} Λ b (ex {Γ = Γ ++ _ ∷ []} b f))))
  qed≗

ex-cxt-fma-ex-fma-cxt-braid : ∀{S Γ} Λ {Δ A B C} b
  → {f : S ∣ Γ ++ B ∷ Λ ++ A ∷ Δ ⊢ C}
  → ex-fma-cxt {Γ = Γ ++ A ∷ []}{Δ} Λ b (ex b (ex-cxt-fma {Γ = Γ ++ B ∷ []} Λ b f))
    ≗ ex-cxt-fma {Γ = Γ} Λ b (ex {Γ = Γ ++ Λ} b (ex-fma-cxt {Γ = Γ}{A ∷ Δ} Λ b f))
ex-cxt-fma-ex-fma-cxt-braid [] b = refl
ex-cxt-fma-ex-fma-cxt-braid {Γ = Γ} (x ∷ Λ) {Δ} {A}{B} b {f = f} =
  proof≗
    ex-fma-cxt {Γ = Γ ++ A ∷ _ ∷ []} Λ b (ex {Γ = Γ ++ A ∷ []} b (ex b (ex {Γ = Γ ++ B ∷ []} b (ex-cxt-fma {Γ = Γ ++ B ∷ x ∷ []} Λ b f))))
  ≗〈 cong-ex-fma-cxt Λ b (~ ex-braid-b b) 〉
    ex-fma-cxt {Γ = Γ ++ A ∷ _ ∷ []} Λ b (ex {Γ = Γ} b (ex {Γ = Γ ++ _ ∷ []} b (ex {Γ = Γ} b (ex-cxt-fma {Γ = Γ ++ B ∷ x ∷ []} Λ b f))))
  ≗〈 ex-fma-cxt-ex Λ b 〉
    ex b (ex-fma-cxt {Γ = Γ ++ _ ∷ _ ∷ []} Λ b (ex {Γ = Γ ++ _ ∷ []} b (ex {Γ = Γ} b (ex-cxt-fma {Γ = Γ ++ B ∷ x ∷ []} Λ b f))))
  ≗〈 ex b (cong-ex-fma-cxt Λ b (ex {Γ = Γ ++ _ ∷ []} b (~ ex-cxt-fma-ex Λ b))) 〉
    ex b (ex-fma-cxt {Γ = Γ ++ _ ∷ _ ∷ []} Λ b (ex {Γ = Γ ++ _ ∷ []} b (ex-cxt-fma {Γ = Γ ++ _ ∷ _ ∷ []} Λ b (ex b f))))
  ≗〈 ex b (ex-cxt-fma-ex-fma-cxt-braid {Γ = Γ ++ _ ∷ []} Λ b) 〉
    ex b (ex-cxt-fma {Γ = Γ ++ x ∷ []} Λ b (ex {Γ = Γ ++ _ ∷ Λ} b (ex-fma-cxt {Γ = Γ ++ _ ∷ []} Λ b (ex b f))))
  qed≗

ex-fma-cxt-ex-braid : ∀{S Γ₁} Δ₁ {Δ₂ Γ₂ A B A' C}{b'} b
  → {f : S ∣ Γ₁ ++ A' ∷ Δ₁ ++ A ∷ B ∷ Δ₂ ++ Γ₂ ⊢ C}
  → ex-fma-cxt {Γ = Γ₁}{Γ₂} (Δ₁ ++ B ∷ A ∷ Δ₂) b (ex {Γ = Γ₁ ++ A' ∷ Δ₁} b' f)
    ≗ ex {Γ = Γ₁ ++ Δ₁} b' (ex-fma-cxt {Γ = Γ₁} (Δ₁ ++ A ∷ B ∷ Δ₂) b f)
ex-fma-cxt-ex-braid [] {Δ₂} b =
  cong-ex-fma-cxt Δ₂ b (~ ex-braid-b2 b _) 
  ∙ ex-fma-cxt-ex Δ₂ b
ex-fma-cxt-ex-braid {Γ₁ = Γ₁} (x ∷ Δ₁) {Δ₂} b =
  cong-ex-fma-cxt (Δ₁ ++ _ ∷ _ ∷ Δ₂) b (~ exex-b _)
  ∙ ex-fma-cxt-ex-braid {Γ₁ = Γ₁ ++ x ∷ []} Δ₁ b 

ex-cxt-fma-ex-braid : ∀{S Γ₁} Δ₁ {Δ₂ Γ₂ A B A' C}{b'} b
  → {f : S ∣ Γ₁ ++ Δ₁ ++ A ∷ B ∷ Δ₂ ++ A' ∷ Γ₂ ⊢ C}
  → ex-cxt-fma {Γ = Γ₁} (Δ₁ ++ B ∷ A ∷ Δ₂) b (ex {Γ = Γ₁ ++ Δ₁} b' f)
    ≗ ex {Γ = Γ₁ ++ A' ∷ Δ₁} b' (ex-cxt-fma {Γ = Γ₁} (Δ₁ ++ A ∷ B ∷ Δ₂) b f)
ex-cxt-fma-ex-braid {Γ₁ = Γ₁} [] {Δ₂} b =
  ex b (ex {Γ = Γ₁ ++ _ ∷ []} b (ex-cxt-fma-ex Δ₂ b))
  ∙ ex-braid-b3 _ _
ex-cxt-fma-ex-braid {Γ₁ = Γ₁} (x ∷ Δ₁) b =
  ex b (ex-cxt-fma-ex-braid {Γ₁ = Γ₁ ++ x ∷ []} Δ₁ b)
  ∙ ~ exex-b _

ex-cxt-fma++ : {S : Stp} → {Γ Δ : Cxt} (Λ Λ' : Cxt) → {A C : Fma} (b : Bool)→ 
              (f : S ∣ Γ ++ Λ ++ Λ' ++ A ∷ Δ ⊢ C)  →
              ex-cxt-fma {Γ = Γ} (Λ ++ Λ') b f ≡ ex-cxt-fma {Γ = Γ} Λ b (ex-cxt-fma {Γ = Γ ++ Λ} Λ' b f)
ex-cxt-fma++ [] Λ' b f = refl
ex-cxt-fma++ {Γ = Γ} (x ∷ Λ) Λ' b f = cong (ex b) (ex-cxt-fma++ {Γ = Γ ++ x ∷ []} Λ Λ' b f)

ex-fma-cxt++ : {S : Stp} → {Γ Δ : Cxt} (Λ Λ' : Cxt) → {A C : Fma} (b : Bool)→ 
              (f : S ∣ Γ ++ A ∷ Λ ++ Λ' ++ Δ ⊢ C)  →
              ex-fma-cxt {Γ = Γ}{Δ} (Λ ++ Λ') b f ≡ ex-fma-cxt {Γ = Γ ++ Λ} Λ' b (ex-fma-cxt {Γ = Γ} Λ b f)
ex-fma-cxt++ [] Λ' b f = refl
ex-fma-cxt++ {Γ = Γ} (x ∷ Λ) Λ' b f = ex-fma-cxt++ {Γ = Γ ++ x ∷ []} Λ Λ' b (ex b f)

ex-fma-cxt-uf : ∀ Γ Λ {Δ A B C} b
    → {f : just A ∣ Γ ++ B ∷ Λ ++ Δ ⊢ C}
    → ex-fma-cxt {Γ = A ∷ Γ}{Δ} Λ b (uf f) ≗ uf (ex-fma-cxt Λ b f)
ex-fma-cxt-uf Γ [] b = refl
ex-fma-cxt-uf Γ (x ∷ Λ) b =
  cong-ex-fma-cxt Λ b (exuf-b b) ∙ ex-fma-cxt-uf (Γ ++ x ∷ []) Λ b 

ex-cxt-fma-uf : ∀ Γ Λ {Δ A B C} b
    → {f : just A ∣ Γ ++ Λ ++ B ∷ Δ ⊢ C}
    → ex-cxt-fma {Γ = A ∷ Γ} Λ b (uf f) ≗ uf (ex-cxt-fma Λ b f)
ex-cxt-fma-uf Γ [] b = refl
ex-cxt-fma-uf Γ (A' ∷ Λ) b =
  ex b (ex-cxt-fma-uf (Γ ++ A' ∷ []) Λ b) ∙ exuf-b b

ex-fma-cxt-Il : ∀ Γ Λ {Δ A C} b
    → {f : nothing ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C}
    → ex-fma-cxt {Γ = Γ}{Δ} Λ b (Il f) ≗ Il (ex-fma-cxt Λ b f)
ex-fma-cxt-Il Γ [] b = refl
ex-fma-cxt-Il Γ (x ∷ Λ) b =
  cong-ex-fma-cxt Λ b (exIl-b b) ∙ ex-fma-cxt-Il (Γ ++ _ ∷ []) Λ b

exIl-1 : {Γ Δ Λ : Cxt}{A B C : Fma} (b : Bool) (f : just I ∣ Λ ⊢ C)
  → (eq : Λ ≡ Γ ++ A ∷ B ∷ Δ)
  → ex b (Il-1 (subst (λ x → just I ∣ x ⊢ C) eq f))
     ≡ Il-1 (ex b (subst (λ x → just I ∣ x ⊢ C) eq f))
exIl-1 {Γ} b ax eq = ⊥-elim ([]disj∷ Γ eq)
exIl-1 b (ex b' f) eq = refl
exIl-1 b (⊗r f f₁) eq = refl
exIl-1 b (Il f) eq = refl

ex-fma-cxt-Il-1 : ∀ Γ Λ {Δ A C} b
    → {f : just I ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C}
    → ex-fma-cxt {Γ = Γ}{Δ} Λ b (Il-1 f) ≡ Il-1 (ex-fma-cxt Λ b f)
ex-fma-cxt-Il-1 Γ [] b = refl
ex-fma-cxt-Il-1 Γ (x ∷ Λ) b {f = f} =
  trans (cong (ex-fma-cxt Λ b) (exIl-1 b f refl))
        (ex-fma-cxt-Il-1 (Γ ++ x ∷ []) Λ b)

ex-cxt-fma-Il : ∀ Γ Λ {Δ A C} b
    → {f : nothing ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C}
    → ex-cxt-fma {Γ = Γ} Λ b (Il f) ≗ Il (ex-cxt-fma Λ b f)
ex-cxt-fma-Il Γ [] b = refl
ex-cxt-fma-Il Γ (A' ∷ Λ) b =
  ex b (ex-cxt-fma-Il (Γ ++ A' ∷ []) Λ b) ∙ exIl-b b

ex-cxt-fma-Il-1 : ∀ Γ Λ {Δ A C} b
    → {f : just I ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C}
    → ex-cxt-fma {Γ = Γ}{Δ} Λ b (Il-1 f) ≡ Il-1 (ex-cxt-fma Λ b f)
ex-cxt-fma-Il-1 Γ [] b = refl
ex-cxt-fma-Il-1 Γ (x ∷ Λ) b =
  cong (ex b) (ex-cxt-fma-Il-1 (Γ ++ x ∷ []) Λ b)

ex-fma-cxt-⊗l : ∀ Γ Λ {Δ A B A' C} b
    → {f : just A ∣ B ∷ Γ ++ A' ∷ Λ ++ Δ ⊢ C}
    → ex-fma-cxt {Γ = Γ}{Δ} Λ b (⊗l f) ≗ ⊗l (ex-fma-cxt Λ b f)
ex-fma-cxt-⊗l Γ [] b = refl
ex-fma-cxt-⊗l Γ (x ∷ Λ) b =
  cong-ex-fma-cxt Λ b (ex⊗l-b b) ∙ ex-fma-cxt-⊗l (Γ ++ _ ∷ []) Λ b

ex-cxt-fma-⊗l : ∀ Γ Λ {Δ A B A' C} b
    → {f : just A ∣ B ∷ Γ ++ Λ ++ A' ∷ Δ ⊢ C}
    → ex-cxt-fma {Γ = Γ} Λ b (⊗l f) ≗ ⊗l (ex-cxt-fma Λ b f)
ex-cxt-fma-⊗l Γ [] b = refl
ex-cxt-fma-⊗l Γ (A' ∷ Λ) b =
  ex b (ex-cxt-fma-⊗l (Γ ++ A' ∷ []) Λ b) ∙ ex⊗l-b b

ex-fma-cxt-⊗r₁ : ∀ {S} Γ Λ {Δ Δ' A B A'} b
    → {f : S ∣ Γ ++ A' ∷ Λ ++ Δ ⊢ A} {g : nothing ∣ Δ' ⊢ B}
    → ex-fma-cxt {Γ = Γ}{Δ ++ Δ'} Λ b (⊗r f g) ≗ ⊗r (ex-fma-cxt Λ b f) g
ex-fma-cxt-⊗r₁ Γ [] b = refl
ex-fma-cxt-⊗r₁ Γ (x ∷ Λ) b =
  cong-ex-fma-cxt Λ b (ex⊗r₁-b b) ∙ ex-fma-cxt-⊗r₁ (Γ ++ _ ∷ []) Λ b

ex-cxt-fma-⊗r₁ : ∀ {S} Γ Λ {Δ Δ' A B A'} b
    → {f : S ∣ Γ ++ Λ ++ A' ∷ Δ ⊢ A} {g : nothing ∣ Δ' ⊢ B}
    → ex-cxt-fma {Γ = Γ} Λ b (⊗r f g) ≗ ⊗r (ex-cxt-fma Λ b f) g
ex-cxt-fma-⊗r₁ Γ [] b = refl
ex-cxt-fma-⊗r₁ Γ (A' ∷ Λ) b =
  ex b (ex-cxt-fma-⊗r₁ (Γ ++ A' ∷ []) Λ b) ∙ (ex⊗r₁-b b)

ex-fma-cxt-⊗r₂ : ∀ {S} Γ Λ {Δ Δ' A B A'} b
    → {f : S ∣ Δ' ⊢ A} {g : nothing ∣ Γ ++ A' ∷ Λ ++ Δ ⊢ B}
    → ex-fma-cxt {Γ = Δ' ++ Γ}{Δ} Λ b (⊗r f g) ≗ ⊗r f (ex-fma-cxt {Γ = Γ} Λ b g)
ex-fma-cxt-⊗r₂ Γ [] b = refl
ex-fma-cxt-⊗r₂ Γ (x ∷ Λ) b =
  cong-ex-fma-cxt Λ b (ex⊗r₂-b b) ∙ ex-fma-cxt-⊗r₂ (Γ ++ _ ∷ []) Λ b

ex-cxt-fma-⊗r₂ : ∀ {S} Γ Λ {Δ Δ' A B A'} b
    → {f : S ∣ Δ' ⊢ A} {g : nothing ∣ Γ ++ Λ ++ A' ∷ Δ ⊢ B}
    → ex-cxt-fma {Γ = Δ' ++ Γ} Λ b (⊗r f g) ≗ ⊗r f (ex-cxt-fma {Γ = Γ} Λ b g)
ex-cxt-fma-⊗r₂ Γ [] b = refl
ex-cxt-fma-⊗r₂ Γ (A' ∷ Λ) {Δ' = Δ'} b =
  ex {Γ = Δ' ++ Γ} b (ex-cxt-fma-⊗r₂ (Γ ++ A' ∷ []) Λ b) ∙ (ex⊗r₂-b b)

ex-fma-cxt-iso1 : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma}{b : Bool}
  → {f : S ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C}
  → ex-cxt-fma {Γ = Γ}{Δ} Λ b (ex-fma-cxt {Γ = Γ} Λ (not b) f) ≗ f
ex-fma-cxt-iso1 [] = refl
ex-fma-cxt-iso1 {Γ = Γ} (x ∷ Λ) =
  ex _ (ex-fma-cxt-iso1 {Γ = Γ ++ _ ∷ []} Λ) ∙ ex-iso _

ex-fma-cxt-iso2 : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma} {b : Bool}
  → {f : S ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C}
  → ex-fma-cxt {Γ = Γ}{Δ} Λ b (ex-cxt-fma {Γ = Γ} Λ (not b) f) ≗ f
ex-fma-cxt-iso2 [] = refl
ex-fma-cxt-iso2 {Γ = Γ} (x ∷ Λ) =
  cong-ex-fma-cxt Λ _ (ex-iso _) ∙ ex-fma-cxt-iso2 {Γ = Γ ++ _ ∷ []} Λ

ex-ex-cxt-cxt2 : {S : Stp} → {Γ₁ Γ₂ Γ₃ : Cxt} (Λ₁ Λ₂ : Cxt) → {A B C : Fma} {b : Bool}
  → (f : S ∣ Γ₁ ++ A ∷ B ∷ Γ₂ ++ Λ₁ ++ Λ₂ ++ Γ₃ ⊢ C)
  → ex-cxt-cxt2 {Γ = Γ₁ ++ B ∷ A ∷ Γ₂} {Γ₃} Λ₁ Λ₂ b (ex b f)
    ≗ ex b (ex-cxt-cxt2 {Γ = Γ₁ ++ A ∷ B ∷ Γ₂} {Γ₃} Λ₁ Λ₂ b f)
ex-ex-cxt-cxt2 Λ₁ [] f = refl
ex-ex-cxt-cxt2 {Γ₁ = Γ₁} {Γ₂} {Γ₃} Λ₁ (x ∷ Λ₂) f =
  cong-ex-cxt-cxt2 Λ₁ Λ₂ _ (ex-cxt-fma-ex {Γ₁ = Γ₁}{Γ₂} Λ₁ _)
  ∙ ex-ex-cxt-cxt2 {Γ₁ = Γ₁} {Γ₂ ++ x ∷ []} {Γ₃} Λ₁ Λ₂ _

ex-cxt-cxt2∷ : {S : Stp} → {Γ Δ : Cxt} (Λ₁ Λ₂ : Cxt) → {A C : Fma} {b : Bool}
  → (f : S ∣ Γ ++ A ∷ Λ₁ ++ Λ₂ ++ Δ ⊢ C)
  → ex-cxt-cxt2 {Γ = Γ}{Δ} (A ∷ Λ₁) Λ₂ b f
    ≗ ex-fma-cxt {Γ = Γ} Λ₂ b (ex-cxt-cxt2 {Γ = Γ ++ A ∷ []}{Δ} Λ₁ Λ₂ b f)
ex-cxt-cxt2∷ Λ₁ [] f = refl
ex-cxt-cxt2∷ {Γ = Γ} {Δ} Λ₁ (x ∷ Λ₂) f = 
  ex-cxt-cxt2∷ {Γ = Γ ++ x ∷ []} {Δ} Λ₁ Λ₂ _
  ∙ cong-ex-fma-cxt Λ₂ _ (ex-ex-cxt-cxt2 Λ₁ Λ₂ _)

ex-cxt-cxt≗ : {S : Stp} → {Γ Δ : Cxt} (Λ₁ Λ₂ : Cxt) → {C : Fma} {b : Bool}
  → (f : S ∣ Γ ++ Λ₁ ++ Λ₂ ++ Δ ⊢ C)
  → ex-cxt-cxt1 {Γ = Γ}{Δ} Λ₁ Λ₂ b f ≗ ex-cxt-cxt2 {Γ = Γ}{Δ} Λ₁ Λ₂ b f
ex-cxt-cxt≗ [] Λ₂ f = ~ (≡-to-≗ (ex-cxt-cxt2[] Λ₂ _ f))
ex-cxt-cxt≗ {Γ = Γ} {Δ} (x ∷ Λ₁) Λ₂ f =
  cong-ex-fma-cxt Λ₂ _ (ex-cxt-cxt≗ {Γ = Γ ++ x ∷ []} Λ₁ Λ₂ f)
  ∙ ~ (ex-cxt-cxt2∷ Λ₁ Λ₂ f)
