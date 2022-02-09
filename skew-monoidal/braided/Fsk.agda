
module Fsk where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- generating objects At ("atomic formulae")

postulate At : Set

-- =======================================================================

-- the free braided skew-monoidal category

-- -- objects Fma ("formulae")

infixl 25 _⊗_

data Fma : Set where
  ` : At → Fma
  I : Fma
  _⊗_ : Fma → Fma → Fma

infix 15 _⇒_
infixl 20 _∘_

-- -- morphisms

-- The structural laws s and its inverse are represented by a single
-- rule s, which takes a Boolean as its argument.

data _⇒_ : Fma → Fma → Set where
  id : {A : Fma} → A ⇒ A
  _∘_ : {A B C : Fma} → B ⇒ C → A ⇒ B → A ⇒ C
  _⊗_ : {A B C D : Fma} → A ⇒ B → C ⇒ D → A ⊗ C ⇒ B ⊗ D 
  l : {A : Fma} → I ⊗ A ⇒ A
  ρ : {A : Fma} → A ⇒ A ⊗ I
  α : {A B C : Fma} → (A ⊗ B) ⊗ C ⇒ A ⊗ (B ⊗ C)
  s : {A B C : Fma} → Bool → (A ⊗ B) ⊗ C ⇒ (A ⊗ C) ⊗ B
  
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
                       s true ∘ f ⊗ g ⊗ h ≐ f ⊗ h ⊗ g ∘ s true
  -- skew monoidality (m1)-(m5)
  lρ : l ∘ ρ ≐ id 
  lαρ : {A B : Fma} → id {A ⊗ B} ≐ id ⊗ l ∘ α ∘ ρ ⊗ id
  lα :  {A B : Fma} → l ∘ α ≐ l {A} ⊗ id {B}
  αρ : {A B : Fma} → α ∘ ρ ≐ id {A} ⊗ ρ {B}
  ααα : {A B C D : Fma} → 
         α ∘ α ≐ id {A} ⊗ α {B}{C}{D} ∘ (α ∘ α ⊗ id)

  -- braiding equations (b1)-(b4)
  sss : {A B C D : Fma} → (s true) ⊗ id ∘ (s true) ∘ (s true) ⊗ id ≐ (s true) ∘ (s true) ⊗ id ∘ (s {A ⊗ B}{C}{D} true)
  sα1 : {A B C D : Fma} → (s true) ∘ α {A ⊗ B}{C}{D} ≐ α ⊗ id ∘ (s true) ∘ (s true) ⊗ id
  sα2 : {A B C D : Fma} → (s true) ∘ α ⊗ id ≐ α ∘ (s true) ⊗ id ∘ (s {A ⊗ B}{C}{D} true)
  sα3 : {A B C D : Fma} → α ∘ α ⊗ id ∘ (s {A ⊗ B}{C}{D} true) ≐ id ⊗ (s true) ∘ α ∘ α ⊗ id
  ss : {A B C : Fma} (b : Bool)→ s b ∘ s (not b) ≐ id {(A ⊗ B) ⊗ C}

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

ns-b : {A B C D E F : Fma} (b : Bool) {f : A ⇒ D} {g : B ⇒ E} {h : C ⇒ F} →
                       s b ∘ f ⊗ g ⊗ h ≐ f ⊗ h ⊗ g ∘ s b
ns-b true = ns
ns-b false {f = f}{g}{h} =
  proof≐
    s false ∘ f ⊗ g ⊗ h
  ≐⟨ rid ⟩
    s false ∘ f ⊗ g ⊗ h ∘ id
  ≐⟨ refl ∘ ~ ss true ⟩
    s false ∘ f ⊗ g ⊗ h ∘ (s true ∘ s false)
  ≐⟨ ~ ass ∙ (ass ∘ refl) ⟩
    s false ∘ (f ⊗ g ⊗ h ∘ s true) ∘ s false
  ≐⟨ refl ∘ ~ ns ∘ refl ⟩
    s false ∘ (s true ∘ f ⊗ h ⊗ g) ∘ s false
  ≐⟨ ~ ass ∘ refl ⟩
    s false ∘ s true ∘ f ⊗ h ⊗ g ∘ s false
  ≐⟨ ss false ∘ refl ∘ refl ⟩
    id ∘ f ⊗ h ⊗ g ∘ s false
  ≐⟨ lid ∘ refl ⟩
    f ⊗ h ⊗ g ∘ s false
  qed≐ 


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

sα1-b : {A B C D : Fma} (b : Bool)→ s b ∘ α {A ⊗ B}{C}{D} ≐ α ⊗ id ∘ s b ∘ s b ⊗ id
sα1-b true = sα1 
sα1-b false =
  refl ∘ (lem ∙ (ass ∘ refl ∙ ass))
  ∙ ~ ass
  ∙ (ss false ∘ refl)
  ∙ lid
  where
    lem2 : α ∘ s true ⊗ id ≐ s true ∘ α ⊗ id ∘ s false
    lem2 =
      rid
      ∙ (refl ∘ ~ ss true)
      ∙ ~ ass
      ∙ (~ sα2 ∘ refl)

    lem : α ≐ s true ∘ α ⊗ id ∘ s false ∘ s false ⊗ id
    lem =
      rid
      ∙ (refl ∘ ~ f⊗id)
      ∙ (refl ∘ ~ ss true ⊗ lid)
      ∙ (refl ∘ f⊗∘)
      ∙ ~ ass
      ∙ (lem2 ∘ refl)

sα2-b : {A B C D : Fma}(b : Bool) → s b ∘ α ⊗ id ≐ α ∘ s b ⊗ id ∘ s {A ⊗ B}{C}{D} b
sα2-b true = sα2
sα2-b false =
  refl ∘ (lem ∙ (ass ∘ refl ∙ ass))
  ∙ ~ ass
  ∙ (ss _ ∘ refl)
  ∙ lid
  where
    lem2 : α ⊗ id ∘ s true ≐ s true ∘ α ∘ s false ⊗ id
    lem2 =
      rid
      ∙ (refl ∘ ~ f⊗id)
      ∙ (refl ∘ ~ ss _ ⊗ lid)
      ∙ (refl ∘ f⊗∘)
      ∙ ~ ass
      ∙ (~ sα1 ∘ refl)

    lem : α ⊗ id ≐ s true ∘ α ∘ s false ⊗ id ∘ s false
    lem =
      rid
      ∙ (refl ∘ ~ ss _)
      ∙ ~ ass
      ∙ (lem2 ∘ refl)

αsρ : {A B C : Fma} (b : Bool) → α ⊗ id ∘ s b ∘ ρ ≐ id {A} ⊗ ρ {B} ⊗ id {C}
αsρ  b =
  rid ∙ (refl ∘ ~ ss b) ∙ ~ ass
  ∙ (lem ∘ refl)
  ∙ ass ∙ (refl ∘ ss b) ∙ ~ rid
  where
    lem : α ⊗ id ∘ s b ∘ ρ ∘ s b  ≐ id ⊗ ρ ⊗ id ∘ s b
    lem =
      proof≐
        α ⊗ id ∘ s b ∘ ρ ∘ s b
      ≐⟨ ass ⟩
        α ⊗ id ∘ s b ∘ (ρ ∘ s b)
      ≐⟨ refl ∘ nρ ⟩
        α ⊗ id ∘ s b ∘ (s b ⊗ id ∘ ρ)
      ≐⟨ ~ ass ⟩
        α ⊗ id ∘ s b ∘ s b ⊗ id ∘ ρ
      ≐⟨ ~ sα1-b b ∘ refl ⟩
        s b ∘ α ∘ ρ
      ≐⟨ ass ⟩
        s b ∘ (α ∘ ρ)
      ≐⟨ refl ∘ αρ ⟩
        s b ∘ id ⊗ ρ
      ≐⟨ refl ∘ ~ f⊗id ⊗ refl ⟩
        s b ∘ (id ⊗ id) ⊗ ρ
      ≐⟨ ns-b b ⟩
        id ⊗ ρ ⊗ id ∘ s b
      qed≐

ρs : {A B : Fma} (b : Bool)→ s b ∘ ρ {A ⊗ B} ≐ ρ ⊗ id
ρs b =
  proof≐
    s b ∘ ρ
  ≐⟨ ~ (ass ∙ lid) ⟩
    id ∘ s b ∘ ρ
  ≐⟨ ~ (f⊗id ∘ refl) ∘ refl ⟩
    id ⊗ id ∘ s b ∘ ρ
  ≐⟨ lαρ ⊗ refl ∘ refl ∘ refl ⟩
    (id ⊗ l ∘ α ∘ ρ ⊗ id) ⊗ id ∘ s b ∘ ρ
  ≐⟨ refl ⊗ (rid ∙ rid) ∙ f⊗∘ ∙ (f⊗∘ ∘ refl) ∘ refl ∘ refl ⟩
    id ⊗ l ⊗ id ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id ∘ s b ∘ ρ
  ≐⟨ ass ∘ refl ⟩
    id ⊗ l ⊗ id ∘ α ⊗ id ∘ (ρ ⊗ id ⊗ id ∘ s b) ∘ ρ
  ≐⟨ refl ∘ ~ ns-b b ∘ refl ⟩
    id ⊗ l ⊗ id ∘ α ⊗ id ∘ (s b ∘ ρ ⊗ id ⊗ id) ∘ ρ
  ≐⟨ ~ ass ∘ refl ∙ ass ⟩
    id ⊗ l ⊗ id ∘ α ⊗ id ∘ s b ∘ (ρ ⊗ id ⊗ id ∘ ρ)
  ≐⟨ refl ∘ ~ nρ ⟩
    id ⊗ l ⊗ id ∘ α ⊗ id ∘ s b ∘ (ρ ∘ ρ ⊗ id)
  ≐⟨ ~ ass ∙ (ass ∘ refl ∙ ass ∘ refl) ⟩
    id ⊗ l ⊗ id ∘ (α ⊗ id ∘ s b ∘ ρ) ∘ ρ ⊗ id
  ≐⟨ refl ∘ αsρ b ∘ refl ⟩
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

sρ : {A B : Fma}(b : Bool) → s b ∘ ρ ⊗ id ≐ ρ {A ⊗ B}
sρ b = 
  proof≐
    s b ∘ ρ ⊗ id
  ≐⟨ refl ∘ ~ ρs (not b) ⟩
    s b ∘ (s (not b) ∘ ρ)
  ≐⟨ ~ ass ⟩
    s b ∘ s (not b) ∘ ρ
  ≐⟨ ss b ∘ refl ⟩
    id ∘ ρ
  ≐⟨ lid ⟩
    ρ
  qed≐

