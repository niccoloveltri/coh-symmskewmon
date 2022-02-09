
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

-- the free symmetric skew monoidal category

-- -- objects Fma ("formulae")

infixl 25 _⊗_

data Fma : Set where
  ` : At → Fma
  I : Fma
  _⊗_ : Fma → Fma → Fma

-- -- morphisms 

infix 15 _⇒_
infixl 20 _∘_

data _⇒_ : Fma → Fma → Set where
  id : {A : Fma} → A ⇒ A
  _∘_ : {A B C : Fma} → B ⇒ C → A ⇒ B → A ⇒ C
  _⊗_ : {A B C D : Fma} → A ⇒ B → C ⇒ D → A ⊗ C ⇒ B ⊗ D 
  l : {A : Fma} → I ⊗ A ⇒ A
  ρ : {A : Fma} → A ⇒ A ⊗ I
  α : {A B C : Fma} → (A ⊗ B) ⊗ C ⇒ A ⊗ (B ⊗ C)
  s : {A B C : Fma} → (A ⊗ B) ⊗ C ⇒ (A ⊗ C) ⊗ B

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
  _⊗_ : {A B C D : Fma} {f g : A ⇒ C} {h k : B ⇒ D} →
                         f ≐ g → h ≐ k → f ⊗ h ≐ g ⊗ k
  -- id, ∘ category
  lid : {A B : Fma} {f : A ⇒ B} → id ∘ f ≐ f
  rid : {A B : Fma} {f : A ⇒ B} → f ≐ f ∘ id
  ass : {A B C D : Fma} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
       → f ∘ g ∘ h ≐ f ∘ (g ∘ h)
  -- ⊗ functorial
  f⊗id : {A B : Fma} → id {A} ⊗ id {B} ≐ id
  f⊗∘ : {A B C D E F : Fma} {f : A ⇒ C} {g : B ⇒ D} {h : C ⇒ E} {k : D ⇒ F} →  
                    (h ∘ f) ⊗ (k ∘ g) ≐ h ⊗ k ∘ f ⊗ g
  -- l, ρ, α, s natural
  nl : {A B : Fma} {f : A ⇒ B} → l ∘ id ⊗ f ≐ f ∘ l
  nρ : {A B : Fma} {f : A ⇒ B} → ρ ∘ f ≐ f ⊗ id ∘ ρ 
  nα : {A B C D E F : Fma} {f : A ⇒ D} {g : B ⇒ E} {h : C ⇒ F} → 
                       α ∘ f ⊗ g ⊗ h ≐ f ⊗ (g ⊗ h) ∘ α
  ns : {A B C D E F : Fma} {f : A ⇒ D} {g : B ⇒ E} {h : C ⇒ F} →
                       s ∘ f ⊗ g ⊗ h ≐ f ⊗ h ⊗ g ∘ s
  -- skew monoidality (m1)-(m5)
  lρ : l ∘ ρ ≐ id 
  lαρ : {A B : Fma} → id {A ⊗ B} ≐ id ⊗ l ∘ α ∘ ρ ⊗ id
  lα :  {A B : Fma} → l ∘ α ≐ l {A} ⊗ id {B}
  αρ : {A B : Fma} → α ∘ ρ ≐ id {A} ⊗ ρ {B}
  ααα : {A B C D : Fma} → 
         α ∘ α ≐ id {A} ⊗ α {B}{C}{D} ∘ (α ∘ α ⊗ id)

  -- braiding equations (b1)-(b4)
  sss : {A B C D : Fma} → s ⊗ id ∘ s ∘ s ⊗ id ≐ s ∘ s ⊗ id ∘ s {A ⊗ B}{C}{D}
  sα1 : {A B C D : Fma} → s ∘ α {A ⊗ B}{C}{D} ≐ α ⊗ id ∘ s ∘ s ⊗ id
  sα2 : {A B C D : Fma} → s ∘ α ⊗ id ≐ α ∘ s ⊗ id ∘ s {A ⊗ B}{C}{D} 
  sα3 : {A B C D : Fma} → α ∘ α ⊗ id ∘ s {A ⊗ B}{C}{D} ≐ id ⊗ s ∘ α ∘ α ⊗ id

  -- symmetry
  ss : {A B C : Fma} → s ∘ s ≐ id {(A ⊗ B) ⊗ C}

refl≐' : {A B : Fma}{f g : A ⇒ B} → f ≡ g → f ≐ g
refl≐' refl = refl

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

id⊗swap : {A B C D : Fma}
  → {f : A ⇒ B} {g : C ⇒ D}
  → id ⊗ f ∘ g ⊗ id ≐ g ⊗ id ∘ id ⊗ f
id⊗swap {f = f}{g} =
  proof≐
    id ⊗ f ∘ g ⊗ id
  ≐⟨ ~ f⊗∘ ⟩
    (id ∘ g) ⊗ (f ∘ id)
  ≐⟨ lid ⊗ (~ rid) ⟩
    g ⊗ f
  ≐⟨ rid ⊗ (~ lid) ⟩
    (g ∘ id) ⊗ (id ∘ f)
  ≐⟨ f⊗∘ ⟩
    g ⊗ id ∘ id ⊗ f
  qed≐

αsρ : {A B C : Fma} → α ⊗ id ∘ s ∘ ρ ≐ id {A} ⊗ ρ {B} ⊗ id {C}
αsρ =
  rid ∙ (refl ∘ ~ ss) ∙ ~ ass
  ∙ (lem ∘ refl)
  ∙ ass ∙ (refl ∘ ss) ∙ ~ rid
  where
    lem : α ⊗ id ∘ s ∘ ρ ∘ s  ≐ id ⊗ ρ ⊗ id ∘ s
    lem =
      proof≐
        α ⊗ id ∘ s ∘ ρ ∘ s
      ≐⟨ ass ⟩
        α ⊗ id ∘ s ∘ (ρ ∘ s)
      ≐⟨ refl ∘ nρ ⟩
        α ⊗ id ∘ s ∘ (s ⊗ id ∘ ρ)
      ≐⟨ ~ ass ⟩
        α ⊗ id ∘ s ∘ s ⊗ id ∘ ρ
      ≐⟨ ~ sα1 ∘ refl ⟩
        s ∘ α ∘ ρ
      ≐⟨ ass ⟩
        s ∘ (α ∘ ρ)
      ≐⟨ refl ∘ αρ ⟩
        s ∘ id ⊗ ρ
      ≐⟨ refl ∘ ~ f⊗id ⊗ refl ⟩
        s ∘ (id ⊗ id) ⊗ ρ
      ≐⟨ ns ⟩
        id ⊗ ρ ⊗ id ∘ s
      qed≐

ρs : {A B : Fma} → s ∘ ρ {A ⊗ B} ≐ ρ ⊗ id
ρs =
  proof≐
    s ∘ ρ
  ≐⟨ ~ (ass ∙ lid) ⟩
    id ∘ s ∘ ρ
  ≐⟨ ~ (f⊗id ∘ refl) ∘ refl ⟩
    id ⊗ id ∘ s ∘ ρ
  ≐⟨ lαρ ⊗ refl ∘ refl ∘ refl ⟩
    (id ⊗ l ∘ α ∘ ρ ⊗ id) ⊗ id ∘ s ∘ ρ
  ≐⟨ refl ⊗ (rid ∙ rid) ∙ f⊗∘ ∙ (f⊗∘ ∘ refl) ∘ refl ∘ refl ⟩
    id ⊗ l ⊗ id ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id ∘ s ∘ ρ
  ≐⟨ ass ∘ refl ⟩
    id ⊗ l ⊗ id ∘ α ⊗ id ∘ (ρ ⊗ id ⊗ id ∘ s) ∘ ρ
  ≐⟨ refl ∘ ~ ns ∘ refl ⟩
    id ⊗ l ⊗ id ∘ α ⊗ id ∘ (s ∘ ρ ⊗ id ⊗ id) ∘ ρ
  ≐⟨ ~ ass ∘ refl ∙ ass ⟩
    id ⊗ l ⊗ id ∘ α ⊗ id ∘ s ∘ (ρ ⊗ id ⊗ id ∘ ρ)
  ≐⟨ refl ∘ ~ nρ ⟩
    id ⊗ l ⊗ id ∘ α ⊗ id ∘ s ∘ (ρ ∘ ρ ⊗ id)
  ≐⟨ ~ ass ∙ (ass ∘ refl ∙ ass ∘ refl) ⟩
    id ⊗ l ⊗ id ∘ (α ⊗ id ∘ s ∘ ρ) ∘ ρ ⊗ id
  ≐⟨ refl ∘ αsρ ∘ refl ⟩
    id ⊗ l ⊗ id ∘ id ⊗ ρ ⊗ id ∘ ρ ⊗ id
  ≐⟨ ~ f⊗∘ ∙ refl ⊗ lid ∘ refl ⟩
    (id ⊗ l ∘ id ⊗ ρ) ⊗ id ∘ ρ ⊗ id
  ≐⟨ (~ f⊗∘ ∙ lid ⊗ refl) ⊗ refl ∘ refl ⟩
    id ⊗ (l ∘ ρ) ⊗ id ∘ ρ ⊗ id
  ≐⟨ refl ⊗ lρ ⊗ refl ∘ refl ⟩
    id ⊗ id ⊗ id ∘ ρ ⊗ id
  ≐⟨ f⊗id ⊗ refl ∙ f⊗id ∘ refl ⟩
    id ∘ ρ ⊗ id
  ≐⟨ lid ⟩
    ρ ⊗ id
  qed≐ 

sρ : {A B : Fma} → s ∘ ρ ⊗ id ≐ ρ {A ⊗ B}
sρ = 
  proof≐
    s ∘ ρ ⊗ id
  ≐⟨ refl ∘ ~ ρs ⟩
    s ∘ (s ∘ ρ)
  ≐⟨ ~ ass ⟩
    s ∘ s ∘ ρ
  ≐⟨ ss ∘ refl ⟩
    id ∘ ρ
  ≐⟨ lid ⟩
    ρ
  qed≐
