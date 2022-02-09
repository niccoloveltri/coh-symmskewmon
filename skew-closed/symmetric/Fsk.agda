
module Fsk where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- generating objects At ("atomic formulae")

postulate At : Set

-- =======================================================================

-- the free symmetric skew-closed category

-- -- objects Fma ("formulae")

infixr 25 _⊸_

data Fma : Set where
  ` : At → Fma
  I : Fma
  _⊸_ : Fma → Fma → Fma

infix 15 _⇒_
infixl 20 _∘_

data _⇒_ : Fma → Fma → Set where
  id : {A : Fma} → A ⇒ A
  _∘_ : {A B C : Fma} → B ⇒ C → A ⇒ B → A ⇒ C
  _⊸_ : {A B C D : Fma} → A ⇒ B → C ⇒ D → B ⊸ C ⇒ A ⊸ D 
  i : {A : Fma} → I ⊸ A ⇒ A
  j : {A : Fma} → I ⇒ A ⊸ A
  L : {A B C : Fma} → B ⊸ C ⇒ (A ⊸ B) ⊸ (A ⊸ C)
  s : {A B C : Fma} → A ⊸ (B ⊸ C) ⇒ B ⊸ (A ⊸ C)

-- -- equality of maps 

infix 15 _≐_
infixl 20 _∙_
infix 21 ~_

data _≐_ : {A B : Fma} → A ⇒ B → A ⇒ B → Set where
  -- ≐ equivalence and congruence
  refl : {A B : Fma} {f : A ⇒ B} → f ≐ f
  ~_ : {A B : Fma} {f g : A ⇒ B} → f ≐ g → g ≐ f
  _∙_ : {A B : Fma} {f g h : A ⇒ B} → f ≐ g → g ≐ h → f ≐ h
  _∘_ : {A B C : Fma} {f g : B ⇒ C} {h k : A ⇒ B} →
                         f ≐ g → h ≐ k → f ∘ h ≐ g ∘ k
  _⊸_ : {A B C D : Fma} {f g : A ⇒ C} {h k : B ⇒ D} →
                         f ≐ g → h ≐ k → f ⊸ h ≐ g ⊸ k

  -- id, ∘ category
  lid : {A B : Fma} {f : A ⇒ B} → id ∘ f ≐ f
  rid : {A B : Fma} {f : A ⇒ B} → f ≐ f ∘ id
  ass : {A B C D : Fma} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
       → f ∘ g ∘ h ≐ f ∘ (g ∘ h)

  -- ⊸ functorial
  f⊸id : {A B : Fma} → id {A} ⊸ id {B} ≐ id
  f⊸∘ : {A B C D E F : Fma} {f : A ⇒ C} {g : B ⇒ D} {h : C ⇒ E} {k : D ⇒ F} →  
                    (h ∘ f) ⊸ (k ∘ g) ≐ f ⊸ k ∘ h ⊸ g

  -- i , j , L natural
  ni : {A B : Fma} {f : A ⇒ B} → f ∘ i ≐ i ∘ id ⊸ f
  nj : {A B : Fma} {f : A ⇒ B} → f ⊸ id ∘ j ≐ id ⊸ f ∘ j
  nL : {A B C D E F : Fma} {f : A ⇒ D} {g : E ⇒ B} {h : C ⇒ F}
    → (f ⊸ g) ⊸ (id ⊸ h) ∘ L ≐ id ⊸ (f ⊸ id) ∘ L ∘ g ⊸ h
  ns : {A B C D E F : Fma} {f : A ⇒ D} {g : B ⇒ E} {h : C ⇒ F} →
                       f ⊸ g ⊸ h ∘ s ≐ s ∘ g ⊸ f ⊸ h

  -- skew closed axioms
  LLL : {A B C D : Fma} → id ⊸ L {A} ∘ L {B}{C}{D} ≐ L ⊸ id ∘ L ∘ L
  ijL : {A C : Fma} → i ∘ j ⊸ id ∘ L ≐ id {A ⊸ C}
  Lj : {A B : Fma} → L ∘ j ≐ j {A ⊸ B}
  iL : {B C : Fma} → id ⊸ i ∘ L {I} {B} {C} ≐ i ⊸ id
  ij : i ∘ j ≐ id

  -- braided skew
  sss : {A B C D : Fma} → s ∘ id ⊸ s ∘ s {A}{B}{C ⊸ D} ≐ (id ⊸ s) ∘ s ∘ (id ⊸ s)
  sL1 : {A B C D : Fma} → id ⊸ L ∘ s ≐ s ∘ id ⊸ s ∘ L {A}{B}{C ⊸ D}
  sL2 : {A B C D : Fma} → L {A}{B}{C ⊸ D} ∘ s ≐ id ⊸ s ∘ s ∘ id ⊸ L
  sL3 : {A B C D : Fma} → id ⊸ s ∘ L ∘ L {A}{B}{C} ≐ s ⊸ id ∘ L ∘ L {D}{B}{C}
  ss : {A B C : Fma} → s ∘ s ≐ id {A ⊸ B ⊸ C}

refl≐' : {A B : Fma}{f g : A ⇒ B} → f ≡ g → f ≐ g
refl≐' refl = refl

≡-to-≐ : {A B : Fma}{f g : A ⇒ B} → f ≡ g → f ≐ g
≡-to-≐ refl = refl


-- equational reasoning sugar for ≐

infix 4 _≐'_
infix 1 proof≐_
infixr 2 _≐⟨_⟩_
infix 3 _qed≐

data _≐'_ {A B : Fma} (f g : A ⇒ B) : Set where
  relto :  f ≐ g → f ≐' g

proof≐_ : {A B : Fma} {f g : A ⇒ B} → f ≐' g → f ≐ g
proof≐ relto p = p

_≐⟨_⟩_ :  {A B : Fma} (f : A ⇒ B) {g h : A ⇒ B} → f ≐ g → g ≐' h → f ≐' h 
_ ≐⟨ p ⟩ relto q = relto (p ∙ q)

_qed≐  :  {A B : Fma} (f : A ⇒ B) → f ≐' f
_qed≐ _ = relto refl

-- some derivable equations

swap⊸ : ∀{A B C D} {f : A ⇒ C}{g : B ⇒ D}
  → f ⊸ id ∘ id ⊸ g ≐ id ⊸ g ∘ f ⊸ id
swap⊸ {f = f}{g} =
  proof≐
    f ⊸ id ∘ id ⊸ g
  ≐⟨ ~ f⊸∘ ⟩
    (id ∘ f) ⊸ (id ∘ g)
  ≐⟨ (lid ∙ rid) ⊸ (lid ∙ rid) ⟩
    (f ∘ id) ⊸ (g ∘ id)
  ≐⟨ f⊸∘ ⟩
    id ⊸ g ∘ f ⊸ id
  qed≐

id⊸∘ : ∀{A}{B}{C}{D} {f : A ⇒ B}{g : B ⇒ C}
  → id {D} ⊸ (g ∘ f) ≐ id ⊸ g ∘ id ⊸ f 
id⊸∘ = (rid ⊸ refl ) ∙ f⊸∘

∘⊸id : ∀{A}{B}{C}{D} {f : A ⇒ B}{g : B ⇒ C}
  → (g ∘ f) ⊸ id {D} ≐ f ⊸ id ∘ g ⊸ id
∘⊸id = (refl ⊸ rid) ∙ f⊸∘

siL : {A B C : Fma} → s ∘ id ⊸ (id ⊸ i) ∘ id ⊸ s ∘ L {I}{A}{B ⊸ C} ≐ s ∘ i ⊸ id
siL =
  proof≐
    s ∘ id ⊸ (id ⊸ i) ∘ id ⊸ s ∘ L
  ≐⟨ ~ ns ∘ refl ∘ refl ⟩
    id ⊸ (id ⊸ i) ∘ s ∘ id ⊸ s ∘ L
  ≐⟨ ass ∘ refl ∙ ass ⟩
    id ⊸ (id ⊸ i) ∘ (s ∘ id ⊸ s ∘ L)
  ≐⟨ refl ∘ (~ sL1) ⟩
    id ⊸ (id ⊸ i) ∘ (id ⊸ L ∘ s)
  ≐⟨ ~ ass ⟩
    id ⊸ (id ⊸ i) ∘ id ⊸ L ∘ s
  ≐⟨ ((~ id⊸∘) ∙ refl ⊸ iL) ∘ refl ⟩
    id ⊸ (i ⊸ id) ∘ s
  ≐⟨ ns ∙ (refl ∘ refl ⊸ f⊸id) ⟩
    s ∘ i ⊸ id
  qed≐

is1 : {A C : Fma} → i ≐ id ⊸ i ∘ s {I}{A}{C}
is1 =
  proof≐
    i
  ≐⟨ rid ⟩
    i ∘ id
  ≐⟨ refl ∘ ((~ f⊸id ∙ ~ ij ⊸ refl) ∙ ∘⊸id) ⟩
    i ∘ (j ⊸ id ∘ i ⊸ id)
  ≐⟨ ~ ass ⟩
    i ∘ j ⊸ id ∘ i ⊸ id
  ≐⟨ refl ∘ ((~ lid) ∙ ((~ ss) ∘ refl) ∙ ass ∙ (refl ∘ (~ siL)) ∙ (refl ∘ (ass ∘ refl ∙ ass) ∙ ~ ass) ∙ (ss ∘ refl) ∙ lid) ⟩
    i ∘ j ⊸ id ∘ (id ⊸ (id ⊸ i) ∘ id ⊸ s ∘ L)
  ≐⟨ ~ ass ∙ ((~ ass ∙ (ass ∘ refl)) ∘ refl) ⟩
    i ∘ (j ⊸ id ∘ id ⊸ (id ⊸ i)) ∘ id ⊸ s ∘ L
  ≐⟨ refl ∘ swap⊸ ∘ refl ∘ refl ⟩
    i ∘ (id ⊸ (id ⊸ i) ∘ j ⊸ id) ∘ id ⊸ s ∘ L
  ≐⟨ (~ ass ∘ refl ∙ ass) ∘ refl ⟩
    i ∘ id ⊸ (id ⊸ i) ∘ (j ⊸ id ∘ id ⊸ s) ∘ L
  ≐⟨ refl ∘ swap⊸ ∘ refl ⟩
    i ∘ id ⊸ (id ⊸ i) ∘ (id ⊸ s ∘ j ⊸ id) ∘ L
  ≐⟨ (~ ass) ∘ refl ⟩
    (i ∘ id ⊸ (id ⊸ i) ∘ id ⊸ s) ∘ j ⊸ id ∘ L
  ≐⟨ (ass ∙ (refl ∘ (~ id⊸∘) ∙ (~ ni))) ∘ refl ∘ refl ⟩
    (id ⊸ i ∘ s ∘ i) ∘ j ⊸ id ∘ L
  ≐⟨ ass ∘ refl ∙ ass ⟩
    id ⊸ i ∘ s ∘ (i ∘ j ⊸ id ∘ L)
  ≐⟨ refl ∘ ijL ⟩
    id ⊸ i ∘ s ∘ id
  ≐⟨ ~ rid ⟩
    id ⊸ i ∘ s
  qed≐

is2 : {A C : Fma} → id ⊸ i ≐ i ∘ s {A}{I}{C}
is2 =
  proof≐
    id ⊸ i
  ≐⟨ rid ∙ ~ (refl ∘ ss) ⟩
    id ⊸ i ∘ (s ∘ s)
  ≐⟨ ~ ass ⟩
    id ⊸ i ∘ s ∘ s
  ≐⟨ (~ is1) ∘ refl ⟩
    i ∘ s
  qed≐
