{-# OPTIONS --rewriting #-}

module SeqCalc where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
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


infix 15 _∣_⊢_

data _∣_⊢_ : Stp → Cxt → Fma → Set where
  ax : {A : Fma} → just A ∣ [] ⊢ A
  uf : {Γ : Cxt} → {A C : Fma} → 
              just A ∣ Γ ⊢ C → nothing ∣ A ∷ Γ ⊢ C
  ex : {S : Stp} → {Γ Δ : Cxt} → {A B C : Fma} → 
              S ∣ Γ ++ A ∷ B ∷ Δ ⊢ C → S ∣ Γ ++ B ∷ A ∷ Δ ⊢ C 
  Ir : nothing ∣ [] ⊢ I
  Il : {Γ : Cxt} → {C : Fma} → 
              nothing ∣ Γ ⊢ C → just I ∣ Γ ⊢ C 
  ⊸r : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
              S ∣ Γ ++ A ∷ [] ⊢ B → S ∣ Γ ⊢ A ⊸ B
  ⊸l : {Γ Δ : Cxt} → {A B C : Fma} →
              nothing ∣ Γ ⊢ A → just B ∣ Δ ⊢ C →
              just (A ⊸ B) ∣ Γ ++ Δ ⊢ C

subst-cxt : {S : Stp} → {Γ Γ' : Cxt} → {A : Fma} → 
      Γ ≡ Γ' → S ∣ Γ ⊢ A → S ∣ Γ' ⊢ A 
subst-cxt refl f = f

-- other general admissible form of exchange

ex-fma-cxt : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma} → 
              S ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C → S ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C 
ex-fma-cxt [] f = f
ex-fma-cxt {Γ = Γ} (B ∷ Λ) f = ex-fma-cxt {Γ = Γ ++ B ∷ []} Λ (ex f) 

ex-cxt-cxt1 : {S : Stp} → {Γ Δ : Cxt} (Λ₁ Λ₂ : Cxt) → {C : Fma} → 
              S ∣ Γ ++ Λ₁ ++ Λ₂ ++ Δ ⊢ C → S ∣ Γ ++ Λ₂ ++ Λ₁ ++ Δ ⊢ C 
ex-cxt-cxt1 {Γ = Γ} [] Λ₂ f = f
ex-cxt-cxt1 {Γ = Γ} {Δ} (A ∷ Λ₁) Λ₂ f =
  ex-fma-cxt {Γ = Γ} Λ₂ (ex-cxt-cxt1 {Γ = Γ ++ A ∷ []} {Δ} Λ₁ Λ₂ f)

ex-cxt-fma : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma} → 
              S ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C  → S ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C
ex-cxt-fma {Γ = Γ} [] f = f
ex-cxt-fma {Γ = Γ} (B ∷ Λ) f = ex (ex-cxt-fma {Γ = Γ ++ B ∷ []} Λ f)

ex-cxt-cxt2 : {S : Stp} → {Γ Δ : Cxt} (Λ₁ Λ₂ : Cxt) → {C : Fma} → 
              S ∣ Γ ++ Λ₁ ++ Λ₂ ++ Δ ⊢ C → S ∣ Γ ++ Λ₂ ++ Λ₁ ++ Δ ⊢ C 
ex-cxt-cxt2 Λ₁ [] f = f
ex-cxt-cxt2 {Γ = Γ} {Δ} Λ₁ (A ∷ Λ₂) f =
  ex-cxt-cxt2 {Γ = Γ ++ A ∷ []}{Δ} Λ₁ Λ₂ (ex-cxt-fma {Γ = Γ}{Λ₂ ++ Δ} Λ₁ f) 

ex-cxt-cxt2[] : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {C : Fma}
  → (f : S ∣ Γ ++ Λ ++ Δ ⊢ C)
  → ex-cxt-cxt2 {Γ = Γ}{Δ} [] Λ f ≡ f
ex-cxt-cxt2[] [] f = refl
ex-cxt-cxt2[] {Γ = Γ}{Δ} (x ∷ Λ) f = ex-cxt-cxt2[] {Γ = Γ ++ x ∷ []}{Δ} Λ f


-- ====================================================================

-- -- inverted left rules

Il-1 : {Γ : Cxt} → {C : Fma} → 
              just I ∣ Γ ⊢ C → nothing ∣ Γ ⊢ C
Il-1 ax = Ir
Il-1 (ex p) = ex (Il-1 p)
Il-1 (⊸r f) = ⊸r (Il-1 f)
Il-1 (Il p) = p

⊸r-1 : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
              S ∣ Γ ⊢ A ⊸ B → S ∣ Γ ++ A ∷ [] ⊢ B
⊸r-1 ax = ⊸l (uf ax) ax
⊸r-1 (uf f) = uf (⊸r-1 f)
⊸r-1 (⊸r f) = f
⊸r-1 (Il f) = Il (⊸r-1 f)
⊸r-1 (⊸l f g) = ⊸l f (⊸r-1 g)              
⊸r-1 {A = A} (ex {Γ = Γ} {Δ} f) = ex (⊸r-1 {Γ = Γ ++ _ ∷ _ ∷ Δ} f)

-- ====================================================================

-- admissibility of cut

-- -- (There are two kinds of cut: stoup ccut and context cut.)

mutual 
  scut : {S : Stp} → {Γ Δ' : Cxt} → {A C : Fma} → 
              S ∣ Γ ⊢ A  →  just A ∣ Δ' ⊢ C  →  S ∣ Γ ++ Δ' ⊢ C

  scut ax g = g
  scut (uf f) g = uf (scut f g)
  scut (ex f) g = ex (scut f g)
  scut Ir ax = Ir
  scut Ir (ex g) = ex (scut Ir g)
  scut Ir (Il g) = g
  scut Ir (⊸r g) = ⊸r (scut Ir g)
  scut (Il f) g = Il (scut f g)
  scut (⊸r f) ax = ⊸r f
  scut (⊸r {Γ = Γ} f) (⊸l g g') = scut (ccut Γ g f refl) g' 
  scut (⊸r f) (⊸r g) = ⊸r (scut (⊸r f) g)
  scut {Γ = Γ} (⊸r f) (ex {Γ = Γ₁} g) = ex {Γ = Γ ++ Γ₁} (scut (⊸r f) g)
  scut (⊸l f f') g = ⊸l f (scut f' g)

  ccut : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
             nothing ∣ Γ ⊢ A  →  T ∣ Δ ⊢ C  → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                        T ∣ (Δ₀ ++ Γ) ++ Δ' ⊢ C

  ccut Δ₀ f ax p = ⊥-elim ([]disj∷ Δ₀ p)
  ccut Δ₀ {Δ'} f (ex {Γ = Γ}{Δ}{A}{B} g) p with cases++2 Δ₀ Γ Δ' Δ p
  ccut {Γ = Γ} Δ₀ f (ex g) p | inj₁ (Γ₀ , refl , refl) = ex {Γ = Δ₀ ++ Γ ++ Γ₀} (ccut Δ₀ f g refl)
  ccut ._ {Δ'} f (ex {Γ = Γ} {_} {A} {B} g) p | inj₂ (inj₁ (Γ₀ , refl , refl)) = ex {Γ = Γ} (ccut (Γ ++ A ∷ B ∷ Γ₀) f g refl)
  ccut {Γ = Γ} Δ₀ {Δ'} f (ex {Δ = Δ} {A} {B} g) p | inj₂ (inj₂ (inj₁ (refl , refl , refl)))
    = ex-fma-cxt Γ (ccut (Δ₀ ++ A ∷ []) f g refl)
  ccut {Γ = Γ'} Δ₀ f (ex {Γ = Γ} {Δ} {A} {B} g) p | inj₂ (inj₂ (inj₂ (refl , refl , refl)))
    = ex-cxt-fma Γ' (ccut Γ f g refl)
  ccut Δ₀ f (uf g) p with cases∷ Δ₀ p 
  ccut .[] f (uf g) p | inj₁ (refl , refl , refl) = scut f g
  ccut .(_ ∷ Δ₀) f (uf g) p | inj₂ (Δ₀ , r , refl) =  uf (ccut Δ₀ f g r)
  ccut Δ₀ f Ir p = ⊥-elim ([]disj∷ Δ₀ p)
  ccut Δ₀ f (Il g) r = Il (ccut Δ₀ f g r) 
  ccut Δ₀ f (⊸r g) refl = ⊸r (ccut Δ₀ f g refl)
  ccut Δ₀ {Δ'} f (⊸l {Γ = Γ}{Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
  ccut Δ₀ f (⊸l g g') p | inj₁ (Γ₀ , r , refl) = ⊸l (ccut Δ₀ f g r) g'
  ccut ._ f (⊸l g g') p | inj₂ (Γ₀ , refl , refl) = ⊸l g (ccut Γ₀ f g' refl)

-- ====================================================================

-- -- equality of proofs 

data _≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where
  refl : ∀{S}{Γ}{A}{f : S ∣ Γ ⊢ A} → f ≗ f
  ~_ : ∀{S}{Γ}{A}{f g : S ∣ Γ ⊢ A} → f ≗ g → g ≗ f
  _∙_ : ∀{S}{Γ}{A}{f g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗ h → f ≗ h
  uf : ∀{Γ}{A}{C}{f g : just A ∣ Γ ⊢ C} → f ≗ g → uf f ≗ uf g
  Il : ∀{Γ}{C}{f g : nothing ∣ Γ ⊢ C} → f ≗ g → Il f ≗ Il g
  ⊸r : ∀{S}{Γ}{A}{C}{f g : S ∣ Γ ++ A ∷ [] ⊢ C} → f ≗ g → ⊸r f ≗ ⊸r g
  ⊸l : ∀{Γ}{Δ}{A}{B}{C}{f g : nothing ∣ Γ ⊢ A}{f' g' : just B ∣ Δ ⊢ C}
    → f ≗ g → f' ≗ g' → ⊸l f f' ≗ ⊸l g g'
  axI : ax ≗ Il Ir
  ax⊸ : {A B : Fma} → ax {A ⊸ B} ≗ ⊸r (⊸l (uf ax) ax)
  ⊸ruf : {Γ : Cxt}{A B C : Fma} {f : just A ∣ Γ ++ B ∷ [] ⊢ C}
    → ⊸r (uf f) ≗ uf (⊸r f)
  ⊸rIl : {Γ : Cxt}{B C : Fma} {f : nothing ∣ Γ ++ B ∷ [] ⊢ C}
    → ⊸r (Il f) ≗ Il (⊸r f)
  ⊸r⊸l : {Γ Δ : Cxt}{A B C D : Fma}
    → {f : nothing ∣ Γ ⊢ A}{g : just B ∣ Δ ++ C ∷ [] ⊢ D}
    → ⊸r {Γ = Γ ++ Δ} (⊸l f g) ≗ ⊸l f (⊸r g)
  ex : ∀{S Γ Δ A B C}{f g : S ∣ Γ ++ A ∷ B ∷ Δ ⊢ C}
    → f ≗ g → ex f ≗ ex g
  exex : {S : Stp}{Γ₁ Γ₂ Γ₃ : Cxt} {A B A' B' C : Fma}
    → {f : S ∣ Γ₁ ++ A ∷ B ∷ Γ₂ ++ A' ∷ B' ∷ Γ₃ ⊢ C}
    → ex {Γ = Γ₁ ++ B ∷ A ∷ Γ₂} (ex {Γ = Γ₁} f)
         ≗ ex {Γ = Γ₁} (ex {Γ = Γ₁ ++ A ∷ B ∷ Γ₂} f)
  exuf : {Γ Δ : Cxt}{A' A B C : Fma}
    → {f : just A' ∣ Γ ++ A ∷ B ∷ Δ ⊢ C}
    → ex {Γ = A' ∷ Γ} (uf f) ≗ uf (ex f)  
  exIl : {Γ Δ : Cxt}{A B C : Fma}
    → {f : nothing ∣ Γ ++ A ∷ B ∷ Δ ⊢ C}
    → ex (Il f) ≗ Il (ex f)
  ex⊸r : {S : Stp} {Γ Δ : Cxt}{A' B' A B : Fma}
    → {f : S ∣ Γ ++ A ∷ B ∷ Δ ∷ʳ A' ⊢ B'}
    → ex (⊸r f) ≗ ⊸r (ex f)
  ex⊸l₁ : {Γ₁ Γ₂ Δ : Cxt}{A A' B B' C : Fma}
    → {f : nothing ∣ Γ₁ ++ A ∷ B ∷ Γ₂ ⊢ A'}{g : just B' ∣ Δ ⊢ C}
    → ex (⊸l f g) ≗ ⊸l (ex f) g
  ex⊸l₂ : {Γ Δ₁ Δ₂ : Cxt}{A B A' B' C : Fma}
    → {f : nothing ∣ Γ ⊢ A'}{g : just B' ∣ Δ₁ ++ A ∷ B ∷ Δ₂ ⊢ C}
    → ex {Γ = Γ ++ Δ₁} (⊸l f g) ≗ ⊸l f (ex g)
  ex-iso : ∀{S Γ Δ A B C} {f : S ∣ Γ ++ A ∷ B ∷ Δ ⊢ C}
    → ex {Γ = Γ} (ex {Γ = Γ} f) ≗ f
  ex-braid : ∀{S Γ Δ A B C D} {f : S ∣ Γ ++ A ∷ B ∷ C ∷ Δ ⊢ D}
    → ex {Γ = Γ} (ex {Γ = Γ ++ B ∷ []} (ex {Γ = Γ} f))
      ≗ ex {Γ = Γ ++ C ∷ []} (ex {Γ = Γ} (ex {Γ = Γ ++ A ∷ []} f))

≡-to-≗ : ∀{S}{Γ}{A}{f f' : S ∣ Γ ⊢ A} → f ≡ f' → f ≗ f'
≡-to-≗ refl = refl

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
congIl-1 (⊸r p) = ⊸r (congIl-1 p)
congIl-1 axI = refl
congIl-1 ⊸rIl = refl
congIl-1 (ex p) = ex (congIl-1 p)
congIl-1 exex = exex
congIl-1 exIl = refl
congIl-1 ex⊸r = ex⊸r
congIl-1 ex-iso = ex-iso
congIl-1 ex-braid = ex-braid

cong⊸r-1 : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
              {f g : S ∣ Γ ⊢ A ⊸ B} → f ≗ g → ⊸r-1 f ≗ ⊸r-1 g
cong⊸r-1 refl = refl
cong⊸r-1 (~ p) = ~ (cong⊸r-1 p)
cong⊸r-1 (p ∙ p₁) = (cong⊸r-1 p) ∙ (cong⊸r-1 p₁)
cong⊸r-1 (uf p) = uf (cong⊸r-1 p)
cong⊸r-1 (⊸r p) = p
cong⊸r-1 (Il p) = Il (cong⊸r-1 p)
cong⊸r-1 (⊸l p p₁) = ⊸l p (cong⊸r-1 p₁)
cong⊸r-1 ax⊸ = refl
cong⊸r-1 ⊸ruf = refl
cong⊸r-1 ⊸rIl = refl
cong⊸r-1 ⊸r⊸l = refl
cong⊸r-1 (ex {Γ = Γ} {Δ} p) = ex (cong⊸r-1 {Γ = Γ ++ _ ∷ _ ∷ Δ} p)
cong⊸r-1 exex = exex
cong⊸r-1 exuf = exuf
cong⊸r-1 exIl = exIl
cong⊸r-1 ex⊸r = refl
cong⊸r-1 ex⊸l₁ = ex⊸l₁
cong⊸r-1 ex⊸l₂ = ex⊸l₂
cong⊸r-1 ex-iso = ex-iso
cong⊸r-1 ex-braid = ex-braid

-- ====================================================================

-- Il-1 and ⊗l-1 are inverses up to ≗

IlIl-1 : {Γ : Cxt} → {C : Fma} → 
              (f : just I ∣ Γ ⊢ C) → Il (Il-1 f) ≗ f
IlIl-1 ax = ~ axI
IlIl-1 (Il f) = refl            
IlIl-1 (ex f) = ~ exIl ∙ ex (IlIl-1 f)
IlIl-1 (⊸r f) = ~ ⊸rIl ∙ ⊸r (IlIl-1 f)

⊸r-iso : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
  (f : S ∣ Γ ⊢ A ⊸ B) → ⊸r (⊸r-1 f) ≗ f
⊸r-iso ax = ~ ax⊸
⊸r-iso (uf f) = ⊸ruf ∙ uf (⊸r-iso f)
⊸r-iso (⊸r f) = refl
⊸r-iso (Il f) = ⊸rIl ∙ Il (⊸r-iso f)
⊸r-iso (⊸l f f₁) = ⊸r⊸l ∙ ⊸l refl (⊸r-iso f₁)
⊸r-iso (ex f) = ~ ex⊸r ∙ ex (⊸r-iso f)

-- ====================================================================

-- Lots of admissible equations involving exchange

cong-ex-fma-cxt : ∀{S Γ Δ} Λ {A C}{f g : S ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C}
    → f ≗ g → ex-fma-cxt {Γ = Γ}{Δ} Λ f ≗ ex-fma-cxt Λ g
cong-ex-fma-cxt [] eq = eq
cong-ex-fma-cxt {Γ = Γ} (x ∷ Λ) eq = cong-ex-fma-cxt Λ (ex eq)

cong-ex-cxt-fma : ∀{S Γ Δ} Λ {A C}{f g : S ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C}
    → f ≗ g → ex-cxt-fma {Γ = Γ} Λ f ≗ ex-cxt-fma Λ g
cong-ex-cxt-fma [] eq = eq
cong-ex-cxt-fma {Γ = Γ} (x ∷ Λ) eq = ex (cong-ex-cxt-fma {Γ = Γ ++ x ∷ []} Λ eq)

cong-ex-cxt-cxt2 : ∀{S Γ Δ} Λ₁ Λ₂ {C}{f g : S ∣ Γ ++ Λ₁ ++ Λ₂ ++ Δ ⊢ C}
    → f ≗ g → ex-cxt-cxt2 {Γ = Γ}{Δ} Λ₁ Λ₂ f ≗ ex-cxt-cxt2 {Γ = Γ}{Δ} Λ₁ Λ₂ g
cong-ex-cxt-cxt2 Λ₁ [] p = p
cong-ex-cxt-cxt2 Λ₁ (x ∷ Λ₂) p =
  cong-ex-cxt-cxt2 Λ₁ Λ₂ (cong-ex-cxt-fma Λ₁ p)

ex-cxt-fma-ex : ∀{S Γ₁ Γ₂ Γ₃} Λ {A B A' C}{f : S ∣ Γ₁ ++ A ∷ B ∷ Γ₂ ++ Λ ++ A' ∷ Γ₃ ⊢ C}
  → ex-cxt-fma {Γ = Γ₁ ++ B ∷ A ∷ Γ₂} Λ (ex {Γ = Γ₁} f)
      ≗ ex {Γ = Γ₁} (ex-cxt-fma {Γ = Γ₁ ++ A ∷ B ∷ Γ₂} Λ f)
ex-cxt-fma-ex [] = refl
ex-cxt-fma-ex {Γ₁ = Γ₁} {Γ₂ = Γ₂}{Γ₃} (x ∷ Λ) = 
  ex {Γ = Γ₁ ++ _ ∷ _ ∷ Γ₂} (ex-cxt-fma-ex {Γ₂ = Γ₂ ++ _ ∷ []} Λ)  ∙ exex

ex-fma-cxt-ex : ∀{S Γ₁ Γ₂ Γ₃} Λ {A B A' C}{f : S ∣ Γ₁ ++ A ∷ B ∷ Γ₂ ++ A' ∷ Λ ++ Γ₃ ⊢ C}
  → ex-fma-cxt {Γ = Γ₁ ++ B ∷ A ∷ Γ₂}{Γ₃} Λ (ex {Γ = Γ₁} f)
      ≗ ex {Γ = Γ₁} (ex-fma-cxt {Γ = Γ₁ ++ A ∷ B ∷ Γ₂} Λ f)
ex-fma-cxt-ex [] = refl
ex-fma-cxt-ex {Γ₁ = Γ₁} {Γ₂} {Γ₃} (x ∷ Λ) =
  cong-ex-fma-cxt Λ exex ∙ ex-fma-cxt-ex Λ

ex-ex-cxt-fma : ∀{S Γ₁ Γ₂ Γ₃} Λ {A B A' C}{f : S ∣ Γ₁ ++ Λ ++ A' ∷ Γ₂ ++ A ∷ B ∷ Γ₃ ⊢ C}
  → ex-cxt-fma {Γ = Γ₁} Λ (ex {Γ = Γ₁ ++ Λ ++ _ ∷ Γ₂} f)
      ≗ ex {Γ = Γ₁ ++ _ ∷ Λ ++ Γ₂} (ex-cxt-fma {Γ = Γ₁} Λ f)
ex-ex-cxt-fma [] = refl
ex-ex-cxt-fma {Γ₁ = Γ₁} {Γ₂} (x ∷ Λ) =
  ex (ex-ex-cxt-fma {Γ₁ = Γ₁ ++ _ ∷ []} Λ) ∙ ~ exex {Γ₁ = Γ₁}{Λ ++ Γ₂}

ex-ex-fma-cxt : ∀{S Γ₁ Γ₂ Γ₃} Λ {A B A' C}{f : S ∣ Γ₁ ++ A' ∷ Λ ++ Γ₂ ++ A ∷ B ∷ Γ₃ ⊢ C}
  → ex-fma-cxt {Γ = Γ₁} Λ (ex {Γ = Γ₁ ++ _ ∷ Λ ++ Γ₂} f)
      ≗ ex {Γ = Γ₁ ++ Λ ++ _ ∷ Γ₂} (ex-fma-cxt {Γ = Γ₁} Λ f)
ex-ex-fma-cxt [] = refl
ex-ex-fma-cxt {Γ₁ = Γ₁} {Γ₂} (x ∷ Λ) = 
  cong-ex-fma-cxt Λ (~ exex {Γ₁ = Γ₁}{Λ ++ Γ₂}) ∙ ex-ex-fma-cxt Λ 

ex-fma-cxt-ex-fma-cxt : ∀{S Γ₁ Γ₂ Γ₃} Λ Λ' {A A' C}{f : S ∣ Γ₁ ++ A ∷ Λ ++ Γ₂ ++ A' ∷ Λ' ++ Γ₃ ⊢ C}
  → ex-fma-cxt {Γ = Γ₁ ++ Λ ++ A ∷ Γ₂}{Γ₃} Λ' (ex-fma-cxt {Γ = Γ₁} Λ f)
      ≗ ex-fma-cxt {Γ = Γ₁} Λ (ex-fma-cxt {Γ = Γ₁ ++ A ∷ Λ ++ Γ₂} Λ' f)
ex-fma-cxt-ex-fma-cxt [] Λ' = refl
ex-fma-cxt-ex-fma-cxt {Γ₁ = Γ₁}  (x ∷ Λ) Λ' =
  ex-fma-cxt-ex-fma-cxt {Γ₁ = Γ₁ ++ _ ∷ []} Λ Λ'
  ∙ cong-ex-fma-cxt Λ (ex-fma-cxt-ex Λ')

ex-cxt-fma-ex-cxt-fma : ∀{S Γ₁ Γ₂ Γ₃} Λ Λ' {A A' C}{f : S ∣ Γ₁ ++ Λ ++ A ∷ Γ₂ ++ Λ' ++ A' ∷ Γ₃ ⊢ C}
  → ex-cxt-fma {Γ = Γ₁ ++ A ∷ Λ ++ Γ₂} Λ' (ex-cxt-fma {Γ = Γ₁} Λ f)
      ≗ ex-cxt-fma {Γ = Γ₁} Λ (ex-cxt-fma {Γ = Γ₁ ++ Λ ++ A ∷ Γ₂} Λ' f)
ex-cxt-fma-ex-cxt-fma [] Λ' = refl
ex-cxt-fma-ex-cxt-fma {Γ₁ = Γ₁} {Γ₂} (x ∷ Λ) Λ' =
  ex-cxt-fma-ex {Γ₁ = Γ₁}{Λ ++ Γ₂} Λ'
  ∙ ex (ex-cxt-fma-ex-cxt-fma {Γ₁ = Γ₁ ++ x ∷ []} Λ Λ')

ex-cxt-fma-braid : ∀{S Γ} Λ {Δ A B C}
  → {f : S ∣ Γ ++ Λ ++ B ∷ A ∷ Δ ⊢ C}
  → ex {Γ = Γ} (ex-cxt-fma {Γ = Γ ++ B ∷ []} Λ (ex-cxt-fma {Γ = Γ} Λ f))
    ≗ ex-cxt-fma {Γ = Γ ++ A ∷ []} Λ (ex-cxt-fma {Γ = Γ} Λ (ex {Γ = Γ ++ Λ} f))
ex-cxt-fma-braid [] = refl
ex-cxt-fma-braid {Γ = Γ} (x ∷ Λ) {Δ} {A} {B} {f = f} =
  proof≗
    ex {Γ = Γ} (ex {Γ = Γ ++ B ∷ []} (ex-cxt-fma {Γ = Γ ++ B ∷ x ∷ []} Λ (ex {Γ = Γ} (ex-cxt-fma {Γ = Γ ++ x ∷ []} Λ f))))
  ≗〈 ex (ex {Γ = Γ ++ B ∷ []} (ex-cxt-fma-ex Λ)) 〉
    ex {Γ = Γ} (ex {Γ = Γ ++ B ∷ []} (ex {Γ = Γ} (ex-cxt-fma {Γ = Γ ++ x ∷ B ∷ []} Λ (ex-cxt-fma {Γ = Γ ++ x ∷ []} Λ f))))
  ≗〈 ex-braid 〉
    ex {Γ = Γ ++ A ∷ []} (ex {Γ = Γ} (ex {Γ = Γ ++ x ∷ []} (ex-cxt-fma {Γ = Γ ++ x ∷ B ∷ []} Λ (ex-cxt-fma {Γ = Γ ++ x ∷ []} Λ f))))
  ≗〈 ex {Γ = Γ ++ A ∷ []} (ex (ex-cxt-fma-braid {Γ = Γ ++ x ∷ []} Λ)) 〉
    ex {Γ = Γ ++ A ∷ []} (ex {Γ = Γ} (ex-cxt-fma {Γ = Γ ++ x ∷ A ∷ []} Λ (ex-cxt-fma {Γ = Γ ++ x ∷ []} Λ (ex {Γ = Γ ++ x ∷ Λ} f))))
  ≗〈 ex {Γ = Γ ++ A ∷ []} (~ (ex-cxt-fma-ex Λ)) 〉
    _
  qed≗

ex-fma-cxt-braid : ∀{S Γ} Λ {Δ A B C}
  → {f : S ∣ Γ ++ B ∷ A ∷ Λ ++ Δ ⊢ C}
  → ex-fma-cxt {Γ = Γ} Λ (ex-fma-cxt {Γ = Γ ++ _ ∷ []}{Δ} Λ (ex {Γ = Γ} f))
    ≗ ex {Γ = Γ ++ Λ} (ex-fma-cxt {Γ = Γ} Λ (ex-fma-cxt {Γ = Γ ++ _ ∷ []} Λ f))
ex-fma-cxt-braid [] = refl
ex-fma-cxt-braid {Γ = Γ} (x ∷ Λ) {f = f} =
  proof≗
    ex-fma-cxt {Γ = Γ ++ _ ∷ []} Λ (ex (ex-fma-cxt {Γ = Γ ++ _ ∷ _ ∷ []} Λ (ex {Γ = Γ ++ _ ∷ []} (ex f))))
  ≗〈 cong-ex-fma-cxt Λ (~ (ex-fma-cxt-ex Λ)) 〉
    ex-fma-cxt {Γ = Γ ++ _ ∷ []} Λ (ex-fma-cxt {Γ = Γ ++ _ ∷ _ ∷ []} Λ (ex {Γ = Γ} (ex {Γ = Γ ++ _ ∷ []} (ex {Γ = Γ} f))))
  ≗〈 cong-ex-fma-cxt Λ (cong-ex-fma-cxt Λ ex-braid) 〉
    ex-fma-cxt {Γ = Γ ++ _ ∷ []} Λ (ex-fma-cxt {Γ = Γ ++ _ ∷ _ ∷ []} Λ (ex {Γ = Γ ++ _ ∷ []} (ex {Γ = Γ} (ex {Γ = Γ ++ _ ∷ []} f))))
  ≗〈 ex-fma-cxt-braid {Γ = Γ ++ _ ∷ []} Λ 〉
    ex {Γ = Γ ++ _ ∷ Λ} (ex-fma-cxt {Γ = Γ ++ _ ∷ []} Λ (ex-fma-cxt {Γ = Γ ++ _ ∷ _ ∷ []} Λ (ex (ex {Γ = Γ ++ _ ∷ []} f))))
  ≗〈 ex {Γ = Γ ++ _ ∷ Λ} (cong-ex-fma-cxt Λ (ex-fma-cxt-ex Λ)) 〉
    ex {Γ = Γ ++ _ ∷ Λ} (ex-fma-cxt {Γ = Γ ++ _ ∷ []} Λ (ex (ex-fma-cxt {Γ = Γ ++ _ ∷ _ ∷ []} Λ (ex {Γ = Γ ++ _ ∷ []} f))))
  qed≗

ex-cxt-fma-ex-fma-cxt-braid : ∀{S Γ} Λ {Δ A B C}
  → {f : S ∣ Γ ++ B ∷ Λ ++ A ∷ Δ ⊢ C}
  → ex-fma-cxt {Γ = Γ ++ A ∷ []}{Δ} Λ (ex (ex-cxt-fma {Γ = Γ ++ B ∷ []} Λ f))
    ≗ ex-cxt-fma {Γ = Γ} Λ (ex {Γ = Γ ++ Λ} (ex-fma-cxt {Γ = Γ}{A ∷ Δ} Λ f))
ex-cxt-fma-ex-fma-cxt-braid [] = refl
ex-cxt-fma-ex-fma-cxt-braid {Γ = Γ} (x ∷ Λ) {Δ} {A}{B} {f = f} =
  proof≗
    ex-fma-cxt {Γ = Γ ++ A ∷ _ ∷ []} Λ (ex {Γ = Γ ++ A ∷ []} (ex (ex {Γ = Γ ++ B ∷ []} (ex-cxt-fma {Γ = Γ ++ B ∷ x ∷ []} Λ f))))
  ≗〈 cong-ex-fma-cxt Λ (~ ex-braid) 〉
    ex-fma-cxt {Γ = Γ ++ A ∷ _ ∷ []} Λ (ex {Γ = Γ} (ex {Γ = Γ ++ _ ∷ []} (ex {Γ = Γ} (ex-cxt-fma {Γ = Γ ++ B ∷ x ∷ []} Λ f))))
  ≗〈 ex-fma-cxt-ex Λ 〉
    ex (ex-fma-cxt {Γ = Γ ++ _ ∷ _ ∷ []} Λ (ex {Γ = Γ ++ _ ∷ []} (ex {Γ = Γ} (ex-cxt-fma {Γ = Γ ++ B ∷ x ∷ []} Λ f))))
  ≗〈 ex (cong-ex-fma-cxt Λ (ex {Γ = Γ ++ _ ∷ []} (~ ex-cxt-fma-ex Λ))) 〉
    ex (ex-fma-cxt {Γ = Γ ++ _ ∷ _ ∷ []} Λ (ex {Γ = Γ ++ _ ∷ []} (ex-cxt-fma {Γ = Γ ++ _ ∷ _ ∷ []} Λ (ex f))))
  ≗〈 ex (ex-cxt-fma-ex-fma-cxt-braid {Γ = Γ ++ _ ∷ []} Λ) 〉
    ex (ex-cxt-fma {Γ = Γ ++ x ∷ []} Λ (ex {Γ = Γ ++ _ ∷ Λ} (ex-fma-cxt {Γ = Γ ++ _ ∷ []} Λ (ex f))))
  qed≗

ex-fma-cxt-ex-braid : ∀{S Γ₁} Δ₁ {Δ₂ Γ₂ A B A' C}
  → {f : S ∣ Γ₁ ++ A' ∷ Δ₁ ++ A ∷ B ∷ Δ₂ ++ Γ₂ ⊢ C}
  → ex-fma-cxt {Γ = Γ₁}{Γ₂} (Δ₁ ++ B ∷ A ∷ Δ₂) (ex {Γ = Γ₁ ++ A' ∷ Δ₁} f)
    ≗ ex {Γ = Γ₁ ++ Δ₁} (ex-fma-cxt {Γ = Γ₁} (Δ₁ ++ A ∷ B ∷ Δ₂) f)
ex-fma-cxt-ex-braid [] {Δ₂} =
  cong-ex-fma-cxt Δ₂ (~ ex-braid)
  ∙ ex-fma-cxt-ex Δ₂
ex-fma-cxt-ex-braid {Γ₁ = Γ₁} (x ∷ Δ₁) {Δ₂} =
  cong-ex-fma-cxt (Δ₁ ++ _ ∷ _ ∷ Δ₂) (~ exex)
  ∙ ex-fma-cxt-ex-braid {Γ₁ = Γ₁ ++ x ∷ []} Δ₁ 

ex-cxt-fma-ex-braid : ∀{S Γ₁} Δ₁ {Δ₂ Γ₂ A B A' C}
  → {f : S ∣ Γ₁ ++ Δ₁ ++ A ∷ B ∷ Δ₂ ++ A' ∷ Γ₂ ⊢ C}
  → ex-cxt-fma {Γ = Γ₁} (Δ₁ ++ B ∷ A ∷ Δ₂) (ex {Γ = Γ₁ ++ Δ₁} f)
    ≗ ex {Γ = Γ₁ ++ A' ∷ Δ₁} (ex-cxt-fma {Γ = Γ₁} (Δ₁ ++ A ∷ B ∷ Δ₂) f)
ex-cxt-fma-ex-braid {Γ₁ = Γ₁} [] {Δ₂} =
  ex (ex {Γ = Γ₁ ++ _ ∷ []} (ex-cxt-fma-ex Δ₂))
  ∙ ex-braid
ex-cxt-fma-ex-braid {Γ₁ = Γ₁} (x ∷ Δ₁) =
  ex (ex-cxt-fma-ex-braid {Γ₁ = Γ₁ ++ x ∷ []} Δ₁)
  ∙ ~ exex

ex-cxt-fma++ : {S : Stp} → {Γ Δ : Cxt} (Λ Λ' : Cxt) → {A C : Fma} → 
              (f : S ∣ Γ ++ Λ ++ Λ' ++ A ∷ Δ ⊢ C)  →
              ex-cxt-fma {Γ = Γ} (Λ ++ Λ') f ≡ ex-cxt-fma {Γ = Γ} Λ (ex-cxt-fma {Γ = Γ ++ Λ} Λ' f)
ex-cxt-fma++ [] Λ' f = refl
ex-cxt-fma++ {Γ = Γ} (x ∷ Λ) Λ' f = cong ex (ex-cxt-fma++ {Γ = Γ ++ x ∷ []} Λ Λ' f)

ex-fma-cxt++ : {S : Stp} → {Γ Δ : Cxt} (Λ Λ' : Cxt) → {A C : Fma} → 
              (f : S ∣ Γ ++ A ∷ Λ ++ Λ' ++ Δ ⊢ C)  →
              ex-fma-cxt {Γ = Γ}{Δ} (Λ ++ Λ') f ≡ ex-fma-cxt {Γ = Γ ++ Λ} Λ' (ex-fma-cxt {Γ = Γ} Λ f)
ex-fma-cxt++ [] Λ' f = refl
ex-fma-cxt++ {Γ = Γ} (x ∷ Λ) Λ' f = ex-fma-cxt++ {Γ = Γ ++ x ∷ []} Λ Λ' (ex f)

ex-fma-cxt-uf : ∀ Γ Λ {Δ A B C}
    → {f : just A ∣ Γ ++ B ∷ Λ ++ Δ ⊢ C}
    → ex-fma-cxt {Γ = A ∷ Γ}{Δ} Λ (uf f) ≗ uf (ex-fma-cxt Λ f)
ex-fma-cxt-uf Γ [] = refl
ex-fma-cxt-uf Γ (x ∷ Λ) =
  cong-ex-fma-cxt Λ exuf ∙ ex-fma-cxt-uf (Γ ++ x ∷ []) Λ 

ex-cxt-fma-uf : ∀ Γ Λ {Δ A B C}
    → {f : just A ∣ Γ ++ Λ ++ B ∷ Δ ⊢ C}
    → ex-cxt-fma {Γ = A ∷ Γ} Λ (uf f) ≗ uf (ex-cxt-fma Λ f)
ex-cxt-fma-uf Γ [] = refl
ex-cxt-fma-uf Γ (A' ∷ Λ) =
  ex (ex-cxt-fma-uf (Γ ++ A' ∷ []) Λ) ∙ exuf

ex-fma-cxt-Il : ∀ Γ Λ {Δ A C}
    → {f : nothing ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C}
    → ex-fma-cxt {Γ = Γ}{Δ} Λ (Il f) ≗ Il (ex-fma-cxt Λ f)
ex-fma-cxt-Il Γ [] = refl
ex-fma-cxt-Il Γ (x ∷ Λ) =
  cong-ex-fma-cxt Λ exIl ∙ ex-fma-cxt-Il (Γ ++ _ ∷ []) Λ

exIl-1 : {Γ Δ Λ : Cxt}{A B C : Fma} (f : just I ∣ Λ ⊢ C)
  → (eq : Λ ≡ Γ ++ A ∷ B ∷ Δ)
  → ex (Il-1 (subst (λ x → just I ∣ x ⊢ C) eq f))
     ≡ Il-1 (ex (subst (λ x → just I ∣ x ⊢ C) eq f))
exIl-1 {Γ} ax eq = ⊥-elim ([]disj∷ Γ eq)
exIl-1 (ex f) eq = refl
exIl-1 (Il f) eq = refl
exIl-1 (⊸r f) eq = refl

ex-fma-cxt-Il-1 : ∀ Γ Λ {Δ A C}
    → {f : just I ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C}
    → ex-fma-cxt {Γ = Γ}{Δ} Λ (Il-1 f) ≡ Il-1 (ex-fma-cxt Λ f)
ex-fma-cxt-Il-1 Γ [] = refl
ex-fma-cxt-Il-1 Γ (x ∷ Λ) {f = f} =
  trans (cong (ex-fma-cxt Λ) (exIl-1 f refl))
        (ex-fma-cxt-Il-1 (Γ ++ x ∷ []) Λ)

ex-cxt-fma-Il : ∀ Γ Λ {Δ A C}
    → {f : nothing ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C}
    → ex-cxt-fma {Γ = Γ} Λ (Il f) ≗ Il (ex-cxt-fma Λ f)
ex-cxt-fma-Il Γ [] = refl
ex-cxt-fma-Il Γ (A' ∷ Λ) =
  ex (ex-cxt-fma-Il (Γ ++ A' ∷ []) Λ) ∙ exIl

ex-cxt-fma-Il-1 : ∀ Γ Λ {Δ A C}
    → {f : just I ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C}
    → ex-cxt-fma {Γ = Γ}{Δ} Λ (Il-1 f) ≡ Il-1 (ex-cxt-fma Λ f)
ex-cxt-fma-Il-1 Γ [] = refl
ex-cxt-fma-Il-1 Γ (x ∷ Λ) =
  cong ex (ex-cxt-fma-Il-1 (Γ ++ x ∷ []) Λ)

ex-fma-cxt-⊸r : ∀ {S} Γ Λ {Δ A B A'}
    → {f : S ∣ Γ ++ A' ∷ Λ ++ Δ ∷ʳ A ⊢ B}
    → ex-fma-cxt {Γ = Γ}{Δ} Λ (⊸r f) ≗ ⊸r (ex-fma-cxt Λ f)
ex-fma-cxt-⊸r Γ [] = refl
ex-fma-cxt-⊸r Γ (x ∷ Λ) =
  cong-ex-fma-cxt Λ ex⊸r ∙ ex-fma-cxt-⊸r (Γ ∷ʳ _) Λ

ex-cxt-fma-⊸r : ∀ {S} Γ Λ {Δ A B A'}
    → {f : S ∣ Γ ++ Λ ++ A' ∷ Δ ∷ʳ A ⊢ B}
    → ex-cxt-fma {Γ = Γ} Λ (⊸r f) ≗ ⊸r (ex-cxt-fma Λ f)
ex-cxt-fma-⊸r Γ [] = refl
ex-cxt-fma-⊸r Γ (A' ∷ Λ) =
  ex (ex-cxt-fma-⊸r (Γ ++ A' ∷ []) Λ) ∙ ex⊸r

ex-fma-cxt-⊸l₁ : ∀ Γ Λ {Δ Δ' A B A' C}
    → {f : nothing ∣ Γ ++ A' ∷ Λ ++ Δ ⊢ A} {g : just B ∣ Δ' ⊢ C}
    → ex-fma-cxt {Γ = Γ}{Δ ++ Δ'} Λ (⊸l f g) ≗ ⊸l (ex-fma-cxt Λ f) g
ex-fma-cxt-⊸l₁ Γ [] = refl
ex-fma-cxt-⊸l₁ Γ (x ∷ Λ) =
  cong-ex-fma-cxt Λ ex⊸l₁ ∙ ex-fma-cxt-⊸l₁ (Γ ++ _ ∷ []) Λ

ex-cxt-fma-⊸l₁ : ∀ Γ Λ {Δ Δ' A B A' C}
    → {f : nothing ∣ Γ ++ Λ ++ A' ∷ Δ ⊢ A} {g : just B ∣ Δ' ⊢ C}
    → ex-cxt-fma {Γ = Γ} Λ (⊸l f g) ≗ ⊸l (ex-cxt-fma Λ f) g
ex-cxt-fma-⊸l₁ Γ [] = refl
ex-cxt-fma-⊸l₁ Γ (A' ∷ Λ) =
  ex (ex-cxt-fma-⊸l₁ (Γ ++ A' ∷ []) Λ) ∙ ex⊸l₁

ex-fma-cxt-⊸l₂ : ∀ Γ Λ {Δ Δ' A B A' C}
    → {f : nothing ∣ Δ' ⊢ A} {g : just B ∣ Γ ++ A' ∷ Λ ++ Δ ⊢ C}
    → ex-fma-cxt {Γ = Δ' ++ Γ}{Δ} Λ (⊸l f g) ≗ ⊸l f (ex-fma-cxt {Γ = Γ} Λ g)
ex-fma-cxt-⊸l₂ Γ [] = refl
ex-fma-cxt-⊸l₂ Γ (x ∷ Λ) =
  cong-ex-fma-cxt Λ ex⊸l₂ ∙ ex-fma-cxt-⊸l₂ (Γ ++ _ ∷ []) Λ


ex-cxt-fma-⊸l₂ : ∀ Γ Λ {Δ Δ' A B A' C}
    → {f : nothing ∣ Δ' ⊢ A} {g : just B ∣ Γ ++ Λ ++ A' ∷ Δ ⊢ C}
    → ex-cxt-fma {Γ = Δ' ++ Γ} Λ (⊸l f g) ≗ ⊸l f (ex-cxt-fma {Γ = Γ} Λ g)
ex-cxt-fma-⊸l₂ Γ [] = refl
ex-cxt-fma-⊸l₂ Γ (A' ∷ Λ) {Δ' = Δ'} =
  ex {Γ = Δ' ++ Γ} (ex-cxt-fma-⊸l₂ (Γ ++ A' ∷ []) Λ) ∙ ex⊸l₂

ex-fma-cxt-iso1 : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma}
  → {f : S ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C}
  → ex-cxt-fma {Γ = Γ}{Δ} Λ (ex-fma-cxt {Γ = Γ} Λ f) ≗ f
ex-fma-cxt-iso1 [] = refl
ex-fma-cxt-iso1 {Γ = Γ} (x ∷ Λ) =
  ex (ex-fma-cxt-iso1 {Γ = Γ ++ _ ∷ []} Λ) ∙ ex-iso

ex-fma-cxt-iso2 : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma}
  → {f : S ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C}
  → ex-fma-cxt {Γ = Γ}{Δ} Λ (ex-cxt-fma {Γ = Γ} Λ f) ≗ f
ex-fma-cxt-iso2 [] = refl
ex-fma-cxt-iso2 {Γ = Γ} (x ∷ Λ) =
  cong-ex-fma-cxt Λ ex-iso ∙ ex-fma-cxt-iso2 {Γ = Γ ++ _ ∷ []} Λ

ex-ex-cxt-cxt2 : {S : Stp} → {Γ₁ Γ₂ Γ₃ : Cxt} (Λ₁ Λ₂ : Cxt) → {A B C : Fma}
  → (f : S ∣ Γ₁ ++ A ∷ B ∷ Γ₂ ++ Λ₁ ++ Λ₂ ++ Γ₃ ⊢ C)
  → ex-cxt-cxt2 {Γ = Γ₁ ++ B ∷ A ∷ Γ₂} {Γ₃} Λ₁ Λ₂ (ex f)
    ≗ ex (ex-cxt-cxt2 {Γ = Γ₁ ++ A ∷ B ∷ Γ₂} {Γ₃} Λ₁ Λ₂ f)
ex-ex-cxt-cxt2 Λ₁ [] f = refl
ex-ex-cxt-cxt2 {Γ₁ = Γ₁} {Γ₂} {Γ₃} Λ₁ (x ∷ Λ₂) f =
  cong-ex-cxt-cxt2 Λ₁ Λ₂ (ex-cxt-fma-ex {Γ₁ = Γ₁}{Γ₂} Λ₁)
  ∙ ex-ex-cxt-cxt2 {Γ₁ = Γ₁} {Γ₂ ++ x ∷ []} {Γ₃} Λ₁ Λ₂ _

ex-cxt-cxt2∷ : {S : Stp} → {Γ Δ : Cxt} (Λ₁ Λ₂ : Cxt) → {A C : Fma}
  → (f : S ∣ Γ ++ A ∷ Λ₁ ++ Λ₂ ++ Δ ⊢ C)
  → ex-cxt-cxt2 {Γ = Γ}{Δ} (A ∷ Λ₁) Λ₂ f
    ≗ ex-fma-cxt {Γ = Γ} Λ₂ (ex-cxt-cxt2 {Γ = Γ ++ A ∷ []}{Δ} Λ₁ Λ₂ f)
ex-cxt-cxt2∷ Λ₁ [] f = refl
ex-cxt-cxt2∷ {Γ = Γ} {Δ} Λ₁ (x ∷ Λ₂) f = 
  ex-cxt-cxt2∷ {Γ = Γ ++ x ∷ []} {Δ} Λ₁ Λ₂ _
  ∙ cong-ex-fma-cxt Λ₂ (ex-ex-cxt-cxt2 Λ₁ Λ₂ _)

ex-cxt-cxt≗ : {S : Stp} → {Γ Δ : Cxt} (Λ₁ Λ₂ : Cxt) → {C : Fma}
  → (f : S ∣ Γ ++ Λ₁ ++ Λ₂ ++ Δ ⊢ C)
  → ex-cxt-cxt1 {Γ = Γ}{Δ} Λ₁ Λ₂ f ≗ ex-cxt-cxt2 {Γ = Γ}{Δ} Λ₁ Λ₂ f
ex-cxt-cxt≗ [] Λ₂ f = ~ (≡-to-≗ (ex-cxt-cxt2[] Λ₂ f))
ex-cxt-cxt≗ {Γ = Γ} {Δ} (x ∷ Λ₁) Λ₂ f =
  cong-ex-fma-cxt Λ₂ (ex-cxt-cxt≗ {Γ = Γ ++ x ∷ []} Λ₁ Λ₂ f)
  ∙ ~ (ex-cxt-cxt2∷ Λ₁ Λ₂ f)

-- ====================================================================


-- There is no general way of swapping the formula in the stoup with a
-- formula in the context

at-stp : {Γ : Cxt} {X Y : At}
  → (f : just (` X) ∣ Γ ⊢ ` Y)
  → Σ (Γ ≡ []) λ eq → Σ (Y ≡ X) λ eq' →
       subst₂ (λ x y → just _ ∣ x ⊢ ` y) eq eq' f ≡ ax
at-stp ax = refl , refl , refl
at-stp (ex {Γ = Γ} f) = ⊥-elim ([]disj∷ Γ (sym (at-stp f .proj₁)))

d1 : {X Y : At}
  → just ((` X ⊸ ` X) ⊸ (` X ⊸ ` Y)) ∣ ` X ⊸ ` X ∷ ` X ∷ [] ⊢ ` Y
d1 = ⊸l (uf ax) (⊸l (uf ax) ax)

d2 : {X Y : At}
  → just ((` X ⊸ ` X) ⊸ (` X ⊸ ` Y)) ∣ ` X ⊸ ` X ∷ ` X ∷ [] ⊢ ` Y
d2 = ⊸l {Γ = []} (⊸r (uf ax)) (⊸l (uf (⊸l (uf ax) ax)) ax)

module NoExchangeWithStoup
  (exS : {Γ : Cxt} {A B C : Fma} → 
         just A ∣ B ∷ Γ ⊢ C → just B ∣ A ∷ Γ ⊢ C) 
  (X Y : At) where

  absurd : ⊥
  absurd =
    ⊥-elim ([]disj∷ [] (sym (at-stp {X = X}{Y} (exS (ex {Γ = []} d1)) .proj₁)))


