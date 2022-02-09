{-# OPTIONS --rewriting #-}

module Sound where

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


-- ====================================================================

-- interpretation of sequents

-- -- (Note that an empty stoup contributes an I to the meaning 
-- -- of an antecedent.)

t : Stp → Fma
t nothing = I
t (just A) = A

[_∣_] : Cxt → Fma → Fma
[ [] ∣ C ] = C
[ A ∷ Γ ∣ C ] = A ⊸ [ Γ ∣ C ]

-- ====================================================================

-- some lemmata involving interpretation of sequents

[_∣_]f : (Γ : Cxt) {B C : Fma} → B ⇒ C → [ Γ ∣ B ] ⇒ [ Γ ∣ C ]
[ [] ∣ g ]f = g
[ A ∷ Γ ∣ g ]f = id ⊸ [ Γ ∣ g ]f

[_∣id]f : ∀ Γ {C} → [ Γ ∣ id {C} ]f ≐ id
[ [] ∣id]f = refl
[ A ∷ Γ ∣id]f = (refl ⊸ [ Γ ∣id]f) ∙ f⊸id

[_∣∘]f : (Γ : Cxt) {B C D : Fma} → {f : B ⇒ C} {g : C ⇒ D} → [ Γ ∣ g ∘ f ]f ≐ [ Γ ∣ g ]f ∘ [ Γ ∣ f ]f
[ [] ∣∘]f = refl
[ A ∷ Γ ∣∘]f = (refl ⊸ [ Γ ∣∘]f) ∙ ((rid ⊸ refl) ∙ f⊸∘)

[_∣≐]f : (Γ : Cxt) {B C : Fma} → {f g : B ⇒ C} → f ≐ g → [ Γ ∣ f ]f ≐ [ Γ ∣ g ]f
[ [] ∣≐]f p = p
[ A ∷ Γ ∣≐]f p = refl ⊸ [ Γ ∣≐]f p

φ : (Γ Δ : Cxt) (C : Fma) → [ Γ ++ Δ ∣ C ] ≡ [ Γ ∣ [ Δ ∣ C ] ]
φ [] Δ C = refl
φ (A ∷ Γ) Δ C = cong (_⊸_ A) (φ Γ Δ C)

{-# REWRITE φ #-}

[_∣_∣ass]f : ∀ Γ Δ {A}{B} {g : A ⇒ B}
  → [ Γ ∣ [ Δ ∣ g ]f ]f ≡ [ Γ ++ Δ ∣ g ]f
[ [] ∣ Δ ∣ass]f = refl
[ A ∷ Γ ∣ Δ ∣ass]f = cong (_⊸_ id) [ Γ ∣ Δ ∣ass]f

[exex] : ∀ Γ {A B C D E Δ} →
  [ Γ ++ B ∷ A ∷ Δ ∣ s {C}{D}{E} ]f ∘ [ Γ ∣ s ]f ≐ [ Γ ∣ s ]f ∘ [ Γ ++ A ∷ B ∷ Δ ∣ s ]f
[exex] [] = ns
[exex] (A' ∷ Γ) =
  (~ f⊸∘)
  ∙ lid ⊸ refl
  ∙ refl ⊸ [exex] Γ
  ∙ rid ⊸ refl
  ∙ f⊸∘

[ex-braid] : ∀ Γ {A B C D} → 
  [ Γ ∣ s ]f ∘ [ Γ ++ B ∷ [] ∣ s {A}{C}{D} ]f ∘ [ Γ ∣ s ]f ≐
      [ Γ ++ C ∷ [] ∣ s ]f ∘ [ Γ ∣ s ]f ∘ [ Γ ++ A ∷ [] ∣ s ]f
[ex-braid] [] = sss
[ex-braid] (A' ∷ Γ) =
  (~ id⊸∘) ∘ refl
  ∙ (~ id⊸∘)
  ∙ refl ⊸ [ex-braid] Γ
  ∙ id⊸∘
  ∙ (id⊸∘ ∘ refl)

-- ====================================================================

-- iterated applications of L

L⋆ : (Γ : Cxt) {B C : Fma} → B ⊸ C ⇒ [ Γ ∣ B ] ⊸ [ Γ ∣ C ]
L⋆ [] = id
L⋆ (A ∷ Γ) = L ∘ L⋆ Γ

L⋆LL⋆ : ∀ Γ Δ Λ {A} {B} {C}
  → L⋆ Γ ⊸ id ∘ L ∘ L⋆ (Γ ++ Λ) ≐ id ⊸ L⋆ Γ ∘ L {B} ∘ L⋆ Λ {A}{[ Δ ∣ C ]}
L⋆LL⋆ [] Δ Λ = refl
L⋆LL⋆ (B ∷ Γ) Δ Λ = 
  proof≐
    (L ∘ L⋆ Γ) ⊸ id ∘ L ∘ (L ∘ L⋆ (Γ ++ Λ))
  ≐⟨ ∘⊸id ∘ refl ∘ refl ⟩
    L⋆ Γ ⊸ id ∘ L ⊸ id ∘ L ∘ (L ∘ L⋆ (Γ ++ Λ))
  ≐⟨ (~ ass) ∙ ((ass ∘ refl) ∙ ass ∘ refl) ⟩
    L⋆ Γ ⊸ id ∘ (L ⊸ id ∘ L ∘ L) ∘ L⋆ (Γ ++ Λ)
  ≐⟨ refl ∘ (~ LLL) ∘ refl ⟩
    L⋆ Γ ⊸ id ∘ (id ⊸ L ∘ L) ∘ L⋆ (Γ ++ Λ)
  ≐⟨ (~ ass) ∘ refl ⟩
    L⋆ Γ ⊸ id ∘ id ⊸ L ∘ L ∘ L⋆ (Γ ++ Λ)
  ≐⟨ swap⊸ ∘ refl ∘ refl ⟩
    id ⊸ L ∘ L⋆ Γ ⊸ id ∘ L ∘ L⋆ (Γ ++ Λ)
  ≐⟨ (ass ∘ refl) ∙ ass ⟩
    id ⊸ L ∘ (L⋆ Γ ⊸ id ∘ L ∘ L⋆ (Γ ++ Λ))
  ≐⟨ refl ∘ L⋆LL⋆ Γ Δ Λ ⟩
    id ⊸ L ∘ (id ⊸ L⋆ Γ ∘ L ∘ L⋆ Λ)
  ≐⟨ (~ ass) ∙ (~ ass ∘ refl) ⟩
    id ⊸ L ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Λ
  ≐⟨ ~( id⊸∘) ∘ refl ∘ refl ⟩
    id ⊸ (L ∘ L⋆ Γ) ∘ L ∘ L⋆ Λ
  qed≐

nL⋆ : ∀ Γ {A}{B}{C} (g : B ⇒ C)
  → L⋆ Γ ∘ g ⊸ id {A} ≐ [ Γ ∣ g ]f ⊸ id ∘ L⋆ Γ
nL⋆ [] g = lid ∙ rid
nL⋆ (_ ∷ Γ) g = 
  proof≐
    L ∘ L⋆ Γ ∘ g ⊸ id
  ≐⟨ ass ⟩
    L ∘ (L⋆ Γ ∘ g ⊸ id)
  ≐⟨ refl ∘ nL⋆ Γ g ⟩
    L ∘ ([ Γ ∣ g ]f ⊸ id ∘ L⋆ Γ)
  ≐⟨ (~ ass) ∙ (~ lid ∘ refl ∘ refl) ⟩
    id ∘ L ∘ [ Γ ∣ g ]f ⊸ id ∘ L⋆ Γ
  ≐⟨ ~ (refl ⊸ f⊸id ∙ f⊸id) ∘ refl ∘ refl ∘ refl ⟩ 
    id ⊸ (id ⊸ id) ∘ L ∘ [ Γ ∣ g ]f ⊸ id ∘ L⋆ Γ
  ≐⟨ ~ nL ∘ refl ⟩ 
    (id ⊸ [ Γ ∣ g ]f) ⊸ (id ⊸ id) ∘ L ∘ L⋆ Γ
  ≐⟨ refl ⊸ f⊸id ∘ refl ∘ refl ⟩
    (id ⊸ [ Γ ∣ g ]f) ⊸ id ∘ L ∘ L⋆ Γ
  ≐⟨ ass ⟩
    (id ⊸ [ Γ ∣ g ]f) ⊸ id ∘ (L ∘ L⋆ Γ)
  qed≐

nL⋆2 : ∀ Γ {A}{B}{C} (g : B ⇒ C)
  → L⋆ Γ ∘ id {A} ⊸ g ≐ id ⊸ [ Γ ∣ g ]f ∘ L⋆ Γ
nL⋆2 [] g = lid ∙ rid
nL⋆2 (_ ∷ Γ) g =
  proof≐
    L ∘ L⋆ Γ ∘ id ⊸ g
  ≐⟨ ass ⟩
    L ∘ (L⋆ Γ ∘ id ⊸ g)
  ≐⟨ refl ∘ nL⋆2 Γ g ⟩
    L ∘ (id ⊸ [ Γ ∣ g ]f ∘ L⋆ Γ)
  ≐⟨ (~ ass) ∙ (~ lid ∘ refl ∘ refl) ⟩
    id ∘ L ∘ id ⊸ [ Γ ∣ g ]f ∘ L⋆ Γ
  ≐⟨ ~ (refl ⊸ f⊸id ∙ f⊸id) ∘ refl ∘ refl ∘ refl ⟩
    id ⊸ (id ⊸ id) ∘ L ∘ id ⊸ [ Γ ∣ g ]f ∘ L⋆ Γ
  ≐⟨ (~ nL) ∘ refl ⟩
    (id ⊸ id) ⊸ (id ⊸ [ Γ ∣ g ]f) ∘ L ∘ L⋆ Γ
  ≐⟨ f⊸id ⊸ refl ∘ refl ∘ refl ⟩
    id ⊸ (id ⊸ [ Γ ∣ g ]f) ∘ L ∘ L⋆ Γ
  ≐⟨ ass ⟩
    id ⊸ (id ⊸ [ Γ ∣ g ]f) ∘ (L ∘ L⋆ Γ)
  qed≐

L⋆-j : ∀ Γ {C} → L⋆ Γ ∘ j {C} ≐ j 
L⋆-j [] = lid
L⋆-j (A ∷ Γ) =
  proof≐
    L ∘ L⋆ Γ ∘ j
  ≐⟨ ass ⟩
    L ∘ (L⋆ Γ ∘ j)
  ≐⟨ refl ∘ L⋆-j Γ ⟩
    L ∘ j
  ≐⟨ Lj ⟩
    j
  qed≐

L⋆ass : ∀ Γ Δ {A}{B} → L⋆ (Γ ++ Δ) {A}{B} ≐ L⋆ Γ ∘ L⋆ Δ
L⋆ass [] Δ = ~ lid
L⋆ass (C ∷ Γ) Δ = (refl ∘ L⋆ass Γ Δ) ∙ (~ ass)

-- ====================================================================

-- soundness

sound : {S : Stp} → {Γ : Cxt} → {A : Fma} → S ∣ Γ ⊢ A → t S ⇒ [ Γ ∣ A ]
sound ax = id
sound (uf f) = id ⊸ sound f ∘ j
sound Ir = id
sound (⊸r {S}{Γ}{A}{B} f) = sound f
sound (Il f) = sound f
sound (⊸l {Γ} f g) = i ∘ sound f ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound g 
sound (ex {Γ = Γ} f) = [ Γ ∣ s ]f ∘ sound f

-- ====================================================================

-- the "sound" function is well-defined, since it sends ≗-related
-- derivations to ≐-related derivations.

≗sound≐ : {S : Stp} {Γ : Cxt} {A : Fma} → {f g : S ∣ Γ ⊢ A} → f ≗ g → sound f ≐ sound g
≗sound≐ refl = refl
≗sound≐ (~ p) = ~ (≗sound≐ p)
≗sound≐ (p ∙ p₁) = (≗sound≐ p) ∙ (≗sound≐ p₁)
≗sound≐ (uf p) = refl ⊸ ≗sound≐ p ∘ refl
≗sound≐ (⊸r p) = ≗sound≐ p
≗sound≐ (Il p) = ≗sound≐ p
≗sound≐ (⊸l p p₁) = refl ∘ ≗sound≐ p ⊸ refl ∘ refl ∘ refl ⊸ ≗sound≐ p₁
≗sound≐ axI = refl
≗sound≐ ax⊸ =
  (~ ijL) ∙
  (refl ∘ ~ lid ⊸ refl ∘ refl
  ∙ (rid ∙ (refl ∘ (~ f⊸id ∘ refl) ⊸ refl ∘ rid ∘ ~ f⊸id)))
≗sound≐ ⊸ruf = refl
≗sound≐ ⊸rIl = refl
≗sound≐ ⊸r⊸l = refl
≗sound≐ (ex p) = refl ∘ ≗sound≐ p
≗sound≐ exex =
  (~ ass)
  ∙ ([exex] _ ∘ refl)
  ∙ ass
≗sound≐ exuf =
  (~ ass) ∙ (((~ f⊸∘) ∙ lid ⊸ refl) ∘ refl)
≗sound≐ exIl = refl
≗sound≐ ex⊸r = refl
≗sound≐ (ex⊸l₁ {Γ₁ = Γ₁}{Γ₂}) =
  (~ ass)
  ∙ (((~ ass)
      ∙ ((~ ass) ∘ refl)
      ∙ (ni ∘ refl ∘ refl)
      ∙ (ass ∙ ass)
      ∙ (refl
         ∘ ((~ ass)
            ∙ ((~ swap⊸) ∘ refl)
            ∙ (ass
               ∙ (refl
                  ∘ (refl ∘ L⋆ass Γ₁ (_ ∷ _ ∷ Γ₂)
                    ∙ (~ ass)
                    ∙ ((~ nL⋆2 Γ₁ s) ∘ refl)
                    ∙ ass
                    ∙ (refl
                       ∘ ((~ ass)
                         ∙ ~ ass
                         ∙ (sL3 ∘ refl)
                         ∙ ass
                         ∙ ass))
                    ∙ (~ ass)
                    ∙ (nL⋆ Γ₁ s ∘ refl)
                    ∙ ass
                    ∙ (refl ∘ (~ L⋆ass Γ₁ (_ ∷ _ ∷ Γ₂)))))
               ∙ (~ ass))
            ∙ ((~ ∘⊸id) ∘ refl)))
      ∙ (~ ass))
     ∘ refl)
≗sound≐ (ex⊸l₂ {Γ = Γ}{Δ₁}) =
  (~ ass)
  ∙ (((~ ass)
      ∙ ((~ ass) ∘ refl)
      ∙ (ni ∘ refl ∘ refl)
      ∙ ass ∙ ass
      ∙ (refl
         ∘ ((~ ass)
           ∙ ((~ swap⊸) ∘ refl)
           ∙ ass
           ∙ (refl
              ∘ (refl ⊸ (~ (refl≐' [ Γ ∣ Δ₁ ∣ass]f)) ∘ refl
                ∙ (~ nL⋆2 Γ _)))))
      ∙ (~ ass) ∙ (~ ass))
     ∘ refl)
  ∙ ass
  ∙ (refl ∘ (~ id⊸∘))
≗sound≐ (ex-iso {Γ = Γ}) =
  (~ ass) ∙ (~ [ Γ ∣∘]f ∘ refl) ∙ (([ Γ ∣≐]f ss ∙ [ Γ ∣id]f) ∘ refl) ∙ lid
≗sound≐ ex-braid =
  ~ ass ∙  ~ ass
  ∙ ([ex-braid] _ ∘ refl)
  ∙ ass ∙ ass

