{-# OPTIONS --rewriting #-}

module Adequacy1 where

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
open import CutEqs
open import Sound
open import Complete

-- iterated ⊸r

⊸r⋆ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma} → S ∣ Γ ++ Δ ⊢ C → S ∣ Γ ⊢ [ Δ ∣ C ]
⊸r⋆ [] f = f
⊸r⋆ (A ∷ Δ) f = ⊸r (⊸r⋆ Δ f)

⊸r⋆-1 : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma} → S ∣ Γ ⊢ [ Δ ∣ C ] → S ∣ Γ ++ Δ ⊢ C 
⊸r⋆-1 [] f = f
⊸r⋆-1 {Γ = Γ} (A ∷ Δ) f = ⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ (⊸r-1 f)

⊸r⋆-iso : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma} (f : S ∣ Γ ⊢ [ Δ ∣ C ]) → ⊸r⋆ Δ (⊸r⋆-1 Δ f) ≗ f
⊸r⋆-iso [] f = refl
⊸r⋆-iso (A ∷ Δ) f = (⊸r (⊸r⋆-iso Δ (⊸r-1 f))) ∙ (⊸r-iso f)

⊸r⋆-iso2 : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma} (f : S ∣ Γ ++ Δ ⊢ C) → ⊸r⋆-1 Δ (⊸r⋆ Δ f) ≡ f
⊸r⋆-iso2 [] f = refl
⊸r⋆-iso2 {Γ = Γ} (A ∷ Δ) f = ⊸r⋆-iso2 {Γ = Γ ++ A ∷ []} Δ f

-- many lemmata about ⊸r⋆

⊸r⋆ass : {S : Stp} {Γ : Cxt} (Δ Λ : Cxt) {C : Fma} → (f : S ∣ Γ ++ Δ ++ Λ ⊢ C)
  → ⊸r⋆ {S}{Γ} (Δ ++ Λ) f ≗ ⊸r⋆ Δ (⊸r⋆ Λ f)
⊸r⋆ass [] Λ f = refl
⊸r⋆ass (x ∷ Δ) Λ f = ⊸r (⊸r⋆ass Δ Λ f)

⊸r⋆uf : {Γ : Cxt} (Δ : Cxt) {A C : Fma} (f : just A ∣ Γ ++ Δ ⊢ C)
  → ⊸r⋆ Δ (uf f) ≗ uf (⊸r⋆ Δ f)
⊸r⋆uf [] f = refl
⊸r⋆uf {Γ} (B ∷ Δ) f =
  proof≗
    ⊸r (⊸r⋆ Δ (uf f))
  ≗〈 ⊸r (⊸r⋆uf {Γ ++ B ∷ []} Δ f) 〉
    ⊸r (uf _)
  ≗〈 ⊸ruf 〉
    uf (⊸r (⊸r⋆ Δ f))
  qed≗

⊸r⋆⊸l : {Γ Γ' : Cxt} (Δ : Cxt) {A B C : Fma} (f : nothing ∣ Γ ⊢ A) (g : just B ∣ Γ' ++ Δ ⊢ C)
  → ⊸r⋆ {Γ = Γ ++ Γ'} Δ (⊸l f g) ≗ ⊸l f (⊸r⋆ {Γ = Γ'} Δ g)
⊸r⋆⊸l [] f g = refl
⊸r⋆⊸l {Γ}{Γ'} (A ∷ Δ) f g =
  proof≗
    ⊸r _
  ≗〈 ⊸r (⊸r⋆⊸l {Γ}{Γ' ++ A ∷ []} Δ f g) 〉
    ⊸r _
  ≗〈 ⊸r⊸l 〉
    ⊸l f (⊸r (⊸r⋆ Δ g))
  qed≗

⊸r⋆-1⊸l : {Γ Γ' : Cxt} (Δ : Cxt) {A B C : Fma} (f : nothing ∣ Γ ⊢ A) (g : just B ∣ Γ' ⊢ [ Δ ∣ C ])
  → ⊸r⋆-1 {Γ = Γ ++ Γ'} Δ (⊸l f g) ≗ ⊸l f (⊸r⋆-1 {Γ = Γ'} Δ g)
⊸r⋆-1⊸l [] f g = refl
⊸r⋆-1⊸l (D ∷ Δ) f g = ⊸r⋆-1⊸l Δ f (⊸r-1 g)

⊸r⋆Il : {Γ : Cxt} (Δ : Cxt) {C : Fma} (f : nothing ∣ Γ ++ Δ ⊢ C)
  → ⊸r⋆ Δ (Il f) ≗ Il (⊸r⋆ Δ f)
⊸r⋆Il [] f = refl
⊸r⋆Il {Γ} (A ∷ Δ) f = 
  proof≗
    ⊸r (⊸r⋆ Δ (Il f))
  ≗〈 ⊸r (⊸r⋆Il {Γ ++ A ∷ []} Δ f) 〉
    ⊸r (Il _)
  ≗〈 ⊸rIl 〉
    Il (⊸r (⊸r⋆ Δ f))
  qed≗

⊸r⋆-1Il : {Γ : Cxt} (Δ : Cxt) {C : Fma} (f : nothing ∣ Γ ⊢ [ Δ ∣ C ])
  → ⊸r⋆-1 Δ (Il f) ≡ Il (⊸r⋆-1 Δ f)
⊸r⋆-1Il [] f = refl
⊸r⋆-1Il {Γ} (A ∷ Δ) f = ⊸r⋆-1Il {Γ ++ A ∷ []} Δ (⊸r-1 f)

scut⊸r⊸r⋆ : {S : Stp} {Γ Γ' : Cxt} (Δ : Cxt) {A B D : Fma}
  → (f : S ∣ Γ ++ A ∷ [] ⊢ B)
  → (g : just (A ⊸ B) ∣ Γ' ++ Δ ⊢ D)
  → scut (⊸r f) (⊸r⋆ Δ g) ≡ ⊸r⋆ Δ (scut (⊸r f) g)
scut⊸r⊸r⋆ [] f g = refl
scut⊸r⊸r⋆ {Γ' = Γ'} (A' ∷ Δ) f g = cong ⊸r (scut⊸r⊸r⋆ {Γ' = Γ' ++ A' ∷ []} Δ f g)

scut⊸r⋆ : {S : Stp} {Γ Γ' : Cxt} (Δ : Cxt) {A D : Fma}
  → (f : S ∣ Γ ⊢ A)
  → (g : just A ∣ Γ' ++ Δ ⊢ D)
  → scut f (⊸r⋆ Δ g) ≗ ⊸r⋆ Δ (scut f g)
scut⊸r⋆ [] f g = refl
scut⊸r⋆ (A' ∷ Δ) f g = scut⊸r f (⊸r⋆ Δ g) ∙ ⊸r (scut⊸r⋆ Δ f _)

ex⊸r⋆ : {S : Stp} {Γ Δ : Cxt}(Λ : Cxt){B' A B : Fma}
  → (f : S ∣ Γ ++ A ∷ B ∷ Δ ++ Λ ⊢ B')
  → ex (⊸r⋆ Λ f) ≗ ⊸r⋆ Λ (ex f)
ex⊸r⋆ [] f = refl
ex⊸r⋆ (_ ∷ Λ) f = ex⊸r ∙ ⊸r (ex⊸r⋆ Λ _)

 
cong⊸r⋆ : ∀{S}{Γ} Δ {C}{f g : S ∣ Γ ++ Δ ⊢ C} → f ≗ g → ⊸r⋆ Δ f ≗ ⊸r⋆ Δ g
cong⊸r⋆ [] p = p
cong⊸r⋆ (_ ∷ Δ) p = ⊸r (cong⊸r⋆ Δ p)

cong⊸r⋆-1 : ∀{S}{Γ} Δ {C}{f g : S ∣ Γ ⊢ [ Δ ∣ C ]} → f ≗ g → ⊸r⋆-1 Δ f ≗ ⊸r⋆-1 Δ g
cong⊸r⋆-1 [] p = p
cong⊸r⋆-1 {Γ = Γ} (A ∷ Δ) p = cong⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ (cong⊸r-1 p)

scut⊸r-1 : {S : Stp} {Γ Δ : Cxt} {B C D : Fma}
  → (f : S ∣ Γ ⊢ B)
  → (g : just B ∣ Δ ⊢ C ⊸ D)
  → scut f (⊸r-1 g) ≡ ⊸r-1 {Γ = Γ ++ Δ} (scut f g)
scut⊸r-1 ax g = refl
scut⊸r-1 (uf f) g = cong uf (scut⊸r-1 f g)
scut⊸r-1 Ir (ex g) = cong ex (scut⊸r-1 Ir g)
scut⊸r-1 Ir (Il g) = refl
scut⊸r-1 Ir (⊸r g) = refl
scut⊸r-1 {Γ = Γ} (⊸r f) ax = trans (scut-unit (ccut Γ (uf ax) f refl)) (ccut-unit Γ f refl)
scut⊸r-1 (⊸r f) (⊸r g) = refl
scut⊸r-1 {Γ = Γ} (⊸r f) (⊸l g g') = scut⊸r-1 (ccut Γ g f refl) g'
scut⊸r-1 {Γ = Γ} (⊸r f) (ex {Γ = Γ₁} g) = cong (ex {Γ = Γ ++ Γ₁}) (scut⊸r-1 (⊸r f) g)
scut⊸r-1 (Il f) g = cong Il (scut⊸r-1 f g)
scut⊸r-1 (⊸l f f') g = cong (⊸l f) (scut⊸r-1 f' g)
scut⊸r-1 (ex f) g = cong ex (scut⊸r-1 f g)

scut⊸r⊸r⋆-1 : {S : Stp} {Γ Γ' : Cxt} (Δ : Cxt) {A B D : Fma}
  → (f : S ∣ Γ ++ A ∷ [] ⊢ B)
  → (g : just (A ⊸ B) ∣ Γ' ⊢ [ Δ ∣ D ])
  → scut (⊸r f) (⊸r⋆-1 Δ g) ≡ ⊸r⋆-1 {Γ = Γ ++ Γ'} Δ (scut (⊸r f) g)
scut⊸r⊸r⋆-1 [] f g = refl
scut⊸r⊸r⋆-1 {Γ = Γ}{Γ'} (A' ∷ Δ) f g =
  trans (scut⊸r⊸r⋆-1 {Γ' = Γ' ++ A' ∷ []} Δ f (⊸r-1 g))
        (cong (⊸r⋆-1 {Γ = Γ ++ Γ' ++ A' ∷ []} Δ) (scut⊸r-1 (⊸r f) g))

scut⊸r⋆-1 : {S : Stp} {Γ Γ' : Cxt} (Δ : Cxt) {A D : Fma}
  → (f : S ∣ Γ ⊢ A)
  → (g : just A ∣ Γ' ⊢ [ Δ ∣ D ])
  → scut f (⊸r⋆-1 Δ g) ≡ ⊸r⋆-1 {Γ = Γ ++ Γ'} Δ (scut f g)
scut⊸r⋆-1 [] f g = refl
scut⊸r⋆-1 {Γ = Γ}{Γ'} (_ ∷ Δ) f g =
  trans (scut⊸r⋆-1 Δ f (⊸r-1 g))
        (cong (⊸r⋆-1 {Γ = Γ ++ Γ' ∷ʳ _} Δ) (scut⊸r-1 f g))

scut⊸r⋆⊸r⋆-1 : ∀{S}{Γ} Δ {C}(f : S ∣ Γ ++ Δ ⊢ C)
  → scut (⊸r⋆ Δ f) (⊸r⋆-1 Δ ax) ≡ f
scut⊸r⋆⊸r⋆-1 [] f = scut-unit f
scut⊸r⋆⊸r⋆-1 {Γ = Γ} (A ∷ Δ) f =
  begin
    scut (⊸r⋆ (A ∷ Δ) f) (⊸r⋆-1 (A ∷ Δ) ax)
  ≡⟨ scut⊸r⊸r⋆-1 Δ _ _ ⟩
    ⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ (scut (⊸r (⊸r⋆ Δ f)) (⊸r-1 ax))
  ≡⟨ cong (⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ) (scut-unit (ccut Γ (uf ax) (⊸r⋆ {Γ = Γ ++ A ∷ []} Δ f) refl)) ⟩
    ⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ (ccut Γ (uf ax) (⊸r⋆ {Γ = Γ ++ A ∷ []} Δ f) refl)
  ≡⟨ cong (⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ) (ccut-unit Γ (⊸r⋆ {Γ = Γ ++ A ∷ []} Δ f) refl) ⟩
    ⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ (subst-cxt refl (⊸r⋆ Δ f))
  ≡⟨ ⊸r⋆-iso2 {Γ = Γ ++ A ∷ []} Δ f ⟩
    f
  ∎

ccut⊸r⋆ : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ Λ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
             (f : nothing ∣ Γ ⊢ A)  (g : T ∣ Δ ++ Λ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') (s : Δ ++ Λ ≡ Δ₀ ++ A ∷ Δ' ++ Λ) →  
                                        ccut Δ₀ f (⊸r⋆ Λ g) r ≗ ⊸r⋆ Λ (ccut Δ₀ {Δ' ++ Λ} f g s)
ccut⊸r⋆ Δ₀ [] f g refl refl = refl
ccut⊸r⋆ Δ₀ (A ∷ Λ) {Δ'} {B} f g refl refl = ⊸r (ccut⊸r⋆ {Δ = Δ₀ ++ B ∷ Δ' ++ A ∷ []} Δ₀ Λ f g refl refl )

-- ====================================================================

-- Il? is either identity or Il, depending whether the stoup is empty or not

Il? : {S : Stp} {Γ : Cxt} {C : Fma} → S ∣ Γ ⊢ C → just (t S) ∣ Γ ⊢ C
Il? {just A} f = f
Il? {nothing} f = Il f

Il-1? : {S : Stp} {Γ : Cxt} {C : Fma} → just (t S) ∣ Γ ⊢ C → S ∣ Γ ⊢ C
Il-1? {just A} f = f
Il-1? {nothing} f = Il-1 f

congIl? : {S : Stp} {Γ : Cxt} {C : Fma} {f g : S ∣ Γ ⊢ C} → f ≗ g → Il? f ≗ Il? g
congIl? {just A} p = p
congIl? {nothing} p = Il p

congIl-1? : {S : Stp} {Γ : Cxt} {C : Fma} {f g : just (t S) ∣ Γ ⊢ C} → f ≗ g → Il-1? {S}{Γ} f ≗ Il-1? g
congIl-1? {just A} p = p
congIl-1? {nothing} p = congIl-1 p

scutIl? : {S : Stp} → {Γ Δ : Cxt} → {A C : Fma} → 
            (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ C)  →
            scut (Il? f) g ≡ Il? (scut f g)
scutIl? {just A} f g = refl
scutIl? {nothing} f g = refl            


-- ====================================================================

-- Lemmata involving ⊸r-1 and its relationship with Il-1, exchange,
-- cut rules

⊸r-1Il-1 : ∀{Δ}{C}{D}
  → (g : just I ∣ Δ ⊢ C ⊸ D)
  → ⊸r-1 (Il-1 g) ≡ Il-1 (⊸r-1 g)
⊸r-1Il-1 (⊸r g) = refl
⊸r-1Il-1 (Il g) = refl
⊸r-1Il-1 (ex g) = cong ex (⊸r-1Il-1 g)

ex-fma-cxt-⊸r-1 : ∀ {S} Γ Λ {Δ A B A'}
    → {f : S ∣ Γ ++ A' ∷ Λ ++ Δ ⊢ A ⊸ B}
    → ex-fma-cxt {Γ = Γ}{Δ ∷ʳ A} Λ (⊸r-1 {Γ = Γ ++ _ ∷ Λ ++ Δ} f)
         ≡ ⊸r-1 {Γ = Γ ++ Λ ++ _ ∷ Δ} (ex-fma-cxt Λ f)
ex-fma-cxt-⊸r-1 Γ [] = refl
ex-fma-cxt-⊸r-1 Γ (_ ∷ Λ) = ex-fma-cxt-⊸r-1 (Γ ∷ʳ _) Λ

ex-cxt-fma-⊸r-1 : ∀ {S} Γ Λ {Δ A B A'}
    → {f : S ∣ Γ ++ Λ ++ A' ∷ Δ ⊢ A ⊸ B}
    → ex-cxt-fma {Γ = Γ}{Δ ∷ʳ A} Λ (⊸r-1 {Γ = Γ ++ Λ ++ _ ∷ Δ} f)
         ≡ ⊸r-1 {Γ = Γ ++ _ ∷ Λ ++ Δ} (ex-cxt-fma Λ f)
ex-cxt-fma-⊸r-1 Γ [] = refl
ex-cxt-fma-⊸r-1 Γ (_ ∷ Λ) = cong ex (ex-cxt-fma-⊸r-1 (Γ ∷ʳ _) Λ)


ccut⊸r-1 : {T : Stp} {Γ Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A B C : Fma} 
  → (f : nothing ∣ Γ ⊢ A) (g : T ∣ Δ ⊢ B ⊸ C) (eq : Δ ≡ Δ₀ ++ A ∷ Δ')
  → ccut Δ₀ f (⊸r-1 g) (cong₂ _++_ eq (refl {x = B ∷ []}))
    ≡ ⊸r-1 {Γ = Δ₀ ++ Γ ++ Δ'} (ccut Δ₀ f g eq)
ccut⊸r-1 Δ₀ f ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
ccut⊸r-1 Δ₀ f (uf g) eq with cases∷ Δ₀ eq
ccut⊸r-1 .[] f (uf g) refl | inj₁ (refl , refl , refl) = scut⊸r-1 f g
ccut⊸r-1 .(_ ∷ Γ') f (uf g) refl | inj₂ (Γ' , refl , refl) =
  cong uf (ccut⊸r-1  Γ' f g refl)
ccut⊸r-1 Δ₀ f (⊸r g) refl = refl
ccut⊸r-1 Δ₀ f (Il g) eq = cong Il (ccut⊸r-1 Δ₀ f g eq)
ccut⊸r-1 Δ₀ {Δ'} f (⊸l {Γ} {Δ} g g') eq with cases++ Δ₀ Γ Δ' Δ eq
ccut⊸r-1 {just (_ ⊸ _)} Δ₀ {.(Γ₀ ++ Δ)} {A} {B} f (⊸l {.(Δ₀ ++ A ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) rewrite cases++-inj₁ Δ₀ Γ₀ (Δ ∷ʳ B) A = refl
ccut⊸r-1 {just (_ ⊸ _)} .(Γ ++ Γ₀) {Δ'} {A} {B} f (⊸l {Γ} {.(Γ₀ ++ A ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) rewrite cases++-inj₂ Γ₀ Γ (Δ' ∷ʳ B) A = cong (⊸l g) (ccut⊸r-1 Γ₀ f g' refl)
ccut⊸r-1 Δ₀ {Δ'} f (ex {Γ = Γ} {Δ} g) eq with cases++2 Δ₀ Γ Δ' Δ eq
ccut⊸r-1 {Γ = Γ} Δ₀ {.(Γ₀ ++ B₁ ∷ A₁ ∷ Δ)} {A} {B} f (ex {Γ = .(Δ₀ ++ A ∷ Γ₀)} {Δ} {A₁} {B = B₁} g) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀ (B₁ ∷ A₁ ∷ Δ ++ B ∷ []) A = cong (ex {Γ = Δ₀ ++ Γ ++ Γ₀}) (ccut⊸r-1 Δ₀ f g refl)
ccut⊸r-1 .(Γ ++ B₁ ∷ A₁ ∷ Γ₀) {Δ'} {A} {B} f (ex {Γ = Γ} {.(Γ₀ ++ A ∷ Δ')} {A₁} {B₁} g) refl | inj₂ (inj₁ (Γ₀ , refl , refl))
  rewrite cases++-inj₂ (B₁ ∷ A₁ ∷ Γ₀) Γ (Δ' ++ B ∷ []) A = cong ex (ccut⊸r-1 (Γ ++ A₁ ∷ B₁ ∷ Γ₀) f g refl)
ccut⊸r-1 {Γ = Γ} Δ₀ {.(A ∷ Δ)} {A₁} {B = B} f (ex {Γ = Δ₀} {Δ} {A} g) refl | inj₂ (inj₂ (inj₁ (refl , refl , refl))) 
  rewrite cases++-inj₂ [] Δ₀ (A ∷ Δ ++ B ∷ []) A₁ =
    trans (cong (ex-fma-cxt Γ) (ccut⊸r-1 (Δ₀ ∷ʳ _) f g refl))
          (ex-fma-cxt-⊸r-1 Δ₀ Γ)
ccut⊸r-1 {Γ = Γ₁} .(Γ ++ B₁ ∷ []) {Δ'} {A} {B} f (ex {Γ = Γ} {Δ'} {B = B₁} g) refl | inj₂ (inj₂ (inj₂ (refl , refl , refl)))
  rewrite cases++-inj₂ (B₁ ∷ []) Γ (Δ' ∷ʳ B) A =
    trans (cong (ex-cxt-fma Γ₁) (ccut⊸r-1 Γ f g refl))
          (ex-cxt-fma-⊸r-1 Γ Γ₁)

sound-⊸r-1 : {S : Stp} {Γ : Cxt} {A B : Fma} → (f : S ∣ Γ ⊢ A ⊸ B)
  → sound (⊸r-1 f) ≐ sound f
sound-⊸r-1 ax =
  proof≐
    i ∘ (id ⊸ id ∘ j) ⊸ id ∘ (L ∘ id) ∘ id ⊸ id
  ≐⟨ refl ∘ (f⊸id ∘ refl) ⊸ refl ∘ ~ rid ∘ f⊸id  ⟩
    i ∘ (id ∘ j) ⊸ id ∘ L ∘ id
  ≐⟨ (~ rid) ∙ (refl ∘ lid ⊸ refl ∘ refl) ⟩
    i ∘ j ⊸ id ∘ L
  ≐⟨ ijL ⟩
    id
  qed≐
sound-⊸r-1 (uf f) = refl ⊸ sound-⊸r-1 f ∘ refl
sound-⊸r-1 (⊸r f) = refl
sound-⊸r-1 (Il f) = sound-⊸r-1 f
sound-⊸r-1 (⊸l f g) = refl ∘ refl ⊸ sound-⊸r-1 g
sound-⊸r-1 (ex f) = refl ∘ sound-⊸r-1 f

sound-⊸r⋆-1 : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma} → (f : S ∣ Γ ⊢ [ Δ ∣ C ])
  → sound (⊸r⋆-1 Δ f) ≐ sound f
sound-⊸r⋆-1 [] f = refl
sound-⊸r⋆-1 {Γ = Γ} (A ∷ Δ) f = sound-⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ (⊸r-1 f) ∙ sound-⊸r-1 f

-- ====================================================================

-- The cmplt function applied to L⋆ and [ Γ ∣ s ]f

cmplt-L⋆ : (Δ : Cxt) {A C : Fma}
  → cmplt (L⋆ Δ {A}{C}) ≗ ⊸r {Γ = []} (⊸r⋆ Δ (⊸l (uf (⊸r⋆-1 Δ ax)) ax))
cmplt-L⋆ [] = ax⊸
cmplt-L⋆ (B ∷ Δ) =
  proof≗
    scut (cmplt (L⋆ Δ)) (⊸r (⊸r (⊸l (uf (⊸l (uf ax) ax)) ax)))
  ≗〈 cong-scut1 (cmplt-L⋆ Δ) 〉
    ⊸r (⊸r (scut (ccut [] (uf (⊸l (uf ax) ax)) (⊸r⋆ Δ (⊸l (uf (⊸r⋆-1 Δ ax)) ax)) refl) ax))  
  ≗〈 ⊸r (⊸r (≡-to-≗ (scut-unit _))) 〉 
    ⊸r (⊸r (ccut [] (uf (⊸l (uf ax) ax)) (⊸r⋆ Δ (⊸l (uf (⊸r⋆-1 Δ ax)) ax)) refl))  
  ≗〈 ⊸r (⊸r (ccut⊸r⋆ [] Δ  (uf (⊸l (uf ax) ax)) (⊸l (uf (⊸r⋆-1 Δ ax)) ax) refl refl)) 〉 
    ⊸r (⊸r (⊸r⋆ Δ (⊸l (uf (⊸l (uf ax) (⊸r⋆-1 Δ ax))) ax)))
  ≗〈 ⊸r (⊸r (cong⊸r⋆ Δ (⊸l (uf (~ (⊸r⋆-1⊸l Δ (uf ax) ax))) refl))) 〉 
    ⊸r (⊸r (⊸r⋆ Δ (⊸l (uf (⊸r⋆-1 Δ (⊸l (uf ax) ax))) ax)))
  qed≗

cmplt-s : ∀ Γ {A B C}
  → cmplt [ Γ ∣ s {A}{B}{C} ]f
       ≗ ⊸r⋆ Γ (⊸r (⊸r (ex {Γ = Γ} (⊸r-1 {Γ = Γ ∷ʳ A} (⊸r-1 (⊸r⋆-1 Γ ax))))))
cmplt-s [] = refl
cmplt-s (A' ∷ Γ) {A}{B}{C} = ⊸r
  (proof≗
     ⊸l (uf ax) (cmplt [ Γ ∣ s ]f)
   ≗〈 ⊸l refl (cmplt-s Γ) 〉 
     ⊸l (uf ax) (⊸r⋆ Γ (⊸r (⊸r (ex (⊸r-1 {Γ = Γ ∷ʳ A} (⊸r-1 (⊸r⋆-1 Γ ax)))))))
   ≗〈 ~ (⊸r⋆⊸l _ _ _) 〉 
     ⊸r⋆ Γ (⊸l (uf ax) (⊸r (⊸r (ex (⊸r-1 {Γ = Γ ∷ʳ A} (⊸r-1 (⊸r⋆-1 Γ ax)))))))
   ≗〈 cong⊸r⋆ Γ (~ (⊸r (⊸r⊸l {Γ = _ ∷ []}) ∙ ⊸r⊸l)) 〉 
     ⊸r⋆ Γ (⊸r (⊸r (⊸l (uf ax) (ex (⊸r-1 {Γ = Γ ∷ʳ A} (⊸r-1 (⊸r⋆-1 Γ ax)))))))
   ≗〈 cong⊸r⋆ Γ (⊸r (⊸r (~ ex⊸l₂))) 〉 
     ⊸r⋆ Γ (⊸r (⊸r (ex {Γ = A' ∷ Γ} (⊸l (uf ax) (⊸r-1 {Γ = Γ ∷ʳ A} (⊸r-1 (⊸r⋆-1 Γ ax)))))))
   ≗〈 refl 〉 
     ⊸r⋆ Γ (⊸r (⊸r (ex {Γ = A' ∷ Γ} (⊸r-1 (⊸r-1 (⊸l (uf ax) (⊸r⋆-1 Γ ax)))))))
   ≗〈 cong⊸r⋆ Γ (⊸r (⊸r (ex {Γ = A' ∷ Γ} (cong⊸r-1 (cong⊸r-1 (~ (⊸r⋆-1⊸l Γ _ _))))))) 〉 
     ⊸r⋆ Γ (⊸r (⊸r (ex {Γ = A' ∷ Γ} (⊸r-1 (⊸r-1 (⊸r⋆-1 Γ (⊸l (uf ax) ax)))))))
   qed≗)

-- ====================================================================

-- Proof that ∀ f. cmplt (sound f) ≗ IL? (⊸r⋆ Γ f)

cmpltsound : {S : Stp} → {Γ : Cxt} → {C : Fma} → (f : S ∣ Γ ⊢ C)
  → cmplt (sound f) ≗ Il? (⊸r⋆ Γ f) 
cmpltsound ax = refl
cmpltsound (uf f) =
  proof≗
    ⊸r (Il (uf (cmplt (sound f))))
  ≗〈 ⊸r (Il (uf (cmpltsound f))) 〉
    ⊸r (Il (uf (⊸r⋆ _ f)))
  ≗〈 ⊸rIl 〉
    Il (⊸r (uf (⊸r⋆ _ f)))
  ≗〈 Il (⊸r (~ (⊸r⋆uf _ _))) 〉
    Il (⊸r (⊸r⋆ _ (uf f)))
  qed≗
cmpltsound Ir = axI
cmpltsound {Γ = Γ} (⊸r {A = A} {B} f) =
  (cmpltsound f) ∙ (congIl? (⊸r⋆ass Γ (A ∷ []) f))
cmpltsound (Il f) =
  proof≗
    cmplt (sound f)
  ≗〈 cmpltsound f 〉
    Il (⊸r⋆ _ f)
  ≗〈 ~ (⊸r⋆Il _ _) 〉
    ⊸r⋆ _ (Il f)
  qed≗ 
cmpltsound (⊸l {Γ = Γ}{Δ}{A}{B}{C} f g) = 
  proof≗
    scut (⊸r (⊸l (uf ax) (cmplt (sound g)))) (scut (cmplt (L⋆ Γ)) (⊸l (scut Ir (cmplt (sound f))) ax)) 
  ≗〈 cong-scut2 (⊸r (⊸l (uf ax) (cmplt (sound g)))) (cong-scut2 (cmplt (L⋆ Γ)) (⊸l (cong-scut2 Ir (cmpltsound f)) refl)) 〉 
    scut (⊸r (⊸l (uf ax) (cmplt (sound g)))) (scut (cmplt (L⋆ Γ)) (⊸l (⊸r⋆ Γ f) ax))
  ≗〈 cong-scut2 (⊸r (⊸l (uf ax) (cmplt (sound g)))) (cong-scut1 (cmplt-L⋆ Γ)) 〉 
    scut (⊸r (⊸l (uf ax) (cmplt (sound g)))) (scut (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl) ax)
  ≗〈 cong-scut2 (⊸r (⊸l (uf ax) (cmplt (sound g)))) (≡-to-≗ (scut-unit (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl))) 〉 
    scut (⊸r (⊸l (uf ax) (cmplt (sound g)))) (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl)
  ≗〈 cong-scut2 (⊸r (⊸l (uf ax) (cmplt (sound g)))) (ccut⊸r⋆ [] Γ (⊸r⋆ Γ f) (⊸l (uf (⊸r⋆-1 Γ ax)) ax) refl refl) 〉 
    scut (⊸r (⊸l (uf ax) (cmplt (sound g)))) (⊸r⋆ Γ (⊸l (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)) ax))
  ≗〈 ≡-to-≗ (scut⊸r⊸r⋆ Γ (⊸l (uf ax) (cmplt (sound g))) (⊸l (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)) ax)) 〉 
    ⊸r⋆ Γ (⊸l (scut (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)) ax) (scut (cmplt (sound g)) ax))
  ≗〈 cong⊸r⋆ Γ (⊸l refl (≡-to-≗ (scut-unit _))) 〉 
    ⊸r⋆ Γ (⊸l (scut (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)) ax) (cmplt (sound g)))
  ≗〈 cong⊸r⋆ Γ (⊸l (≡-to-≗ (scut-unit _)) (cmpltsound g)) 〉 
    ⊸r⋆ Γ (⊸l (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)) (⊸r⋆ Δ g))
  ≗〈 cong⊸r⋆ Γ (⊸l (≡-to-≗ (scut⊸r⋆⊸r⋆-1 Γ f)) refl) 〉
    ⊸r⋆ Γ (⊸l f (⊸r⋆ Δ g))
  ≗〈 cong⊸r⋆ Γ (~ (⊸r⋆⊸l Δ f g)) 〉
    ⊸r⋆ Γ (⊸r⋆ Δ (⊸l f g))
  ≗〈 ~ (⊸r⋆ass Γ Δ (⊸l f g)) 〉
    ⊸r⋆ (Γ ++ Δ) (⊸l f g)
  qed≗
cmpltsound (ex {Γ = Γ}{Δ}{A = A}{B} f) =
  proof≗
    scut (cmplt (sound f)) (cmplt [ Γ ∣ s ]f)
  ≗〈 cong-scut1 (cmpltsound f) 〉
    scut (Il? (⊸r⋆ (Γ ++ A ∷ B ∷ Δ) f)) (cmplt [ Γ ∣ s ]f)
  ≗〈 ≡-to-≗ (scutIl? (⊸r⋆ (Γ ++ A ∷ B ∷ Δ) f) _) 〉
    Il? (scut (⊸r⋆ (Γ ++ A ∷ B ∷ Δ) f) (cmplt [ Γ ∣ s ]f))
  ≗〈 congIl? (cong-scut2 (⊸r⋆ (Γ ++ A ∷ B ∷ Δ) f) (cmplt-s Γ)) 〉
    Il? (scut (⊸r⋆ (Γ ++ A ∷ B ∷ Δ) f) (⊸r⋆ Γ (⊸r (⊸r (ex {Γ = Γ} (⊸r-1 {Γ = Γ ∷ʳ A} (⊸r-1 (⊸r⋆-1 Γ ax))))))))
  ≗〈 congIl? (scut⊸r⋆ Γ (⊸r⋆ (Γ ++ A ∷ B ∷ Δ) f) _ ∙ cong⊸r⋆ Γ (scut⊸r (⊸r⋆ (Γ ++ A ∷ B ∷ Δ) f) _ ∙ ⊸r (scut⊸r (⊸r⋆ (Γ ++ A ∷ B ∷ Δ) f) _))) 〉
    Il? (⊸r⋆ Γ (⊸r (⊸r (scut {Γ = []} (⊸r⋆ (Γ ++ A ∷ B ∷ Δ) f) (ex {Γ = Γ} (⊸r-1 {Γ = Γ ∷ʳ A} (⊸r-1 (⊸r⋆-1 Γ ax))))))))
  ≗〈 congIl? (cong⊸r⋆ Γ (⊸r (⊸r (scut-ex (⊸r⋆ (Γ ++ A ∷ B ∷ Δ) f))))) 〉
    Il? (⊸r⋆ Γ (⊸r (⊸r (ex (scut {Γ = []} (⊸r⋆ (Γ ++ A ∷ B ∷ Δ) f) (⊸r-1 {Γ = Γ ∷ʳ A} (⊸r-1 (⊸r⋆-1 Γ ax))))))))
  ≗〈 congIl? (cong⊸r⋆ Γ (⊸r (⊸r (ex (cong-scut1 (⊸r⋆ass Γ (A ∷ B ∷ Δ) f)))))) 〉
    Il? (⊸r⋆ Γ (⊸r (⊸r (ex (scut {Γ = []} (⊸r⋆ Γ (⊸r (⊸r (⊸r⋆ Δ f)))) (⊸r-1 {Γ = Γ ∷ʳ A} (⊸r-1 (⊸r⋆-1 Γ ax))))))))
  ≗〈 congIl? (cong⊸r⋆ Γ (⊸r (⊸r (ex (≡-to-≗ (scut⊸r-1 (⊸r⋆ Γ (⊸r (⊸r (⊸r⋆ Δ f)))) (⊸r-1 (⊸r⋆-1 Γ ax)))
                                      ∙ cong⊸r-1 {Γ = Γ ∷ʳ A} (≡-to-≗ (scut⊸r-1 (⊸r⋆ Γ (⊸r (⊸r (⊸r⋆ Δ f)))) (⊸r⋆-1 Γ ax))
                                      ∙ cong⊸r-1 (≡-to-≗ (scut⊸r⋆-1 Γ (⊸r⋆ Γ (⊸r (⊸r (⊸r⋆ Δ f)))) ax)))))))) 〉
    Il? (⊸r⋆ Γ (⊸r (⊸r (ex (⊸r-1 (⊸r-1 (⊸r⋆-1 Γ (scut {Γ = []} (⊸r⋆ Γ (⊸r (⊸r (⊸r⋆ Δ f)))) ax))))))))
  ≗〈 congIl? (cong⊸r⋆ Γ (⊸r (⊸r (ex (cong⊸r-1 {Γ = Γ ∷ʳ A} (cong⊸r-1 (cong⊸r⋆-1 Γ (≡-to-≗ (scut-unit (⊸r⋆ Γ (⊸r (⊸r (⊸r⋆ Δ f))))))))))))) 〉
    Il? (⊸r⋆ Γ (⊸r (⊸r (ex (⊸r-1 {Γ = Γ ∷ʳ A} (⊸r-1 (⊸r⋆-1 Γ (⊸r⋆ Γ (⊸r (⊸r (⊸r⋆ Δ f)))))))))))
  ≗〈 congIl? (cong⊸r⋆ Γ (⊸r (⊸r (ex (cong⊸r-1 {Γ = Γ ∷ʳ A} (cong⊸r-1 (≡-to-≗ (⊸r⋆-iso2 Γ _)))))))) 〉
    Il? (⊸r⋆ Γ (⊸r (⊸r (ex (⊸r⋆ Δ f)))))
  ≗〈 congIl? (cong⊸r⋆ Γ (⊸r (⊸r (ex⊸r⋆ Δ f)))) 〉
    Il? (⊸r⋆ Γ (⊸r (⊸r (⊸r⋆ Δ (ex f)))))
  ≗〈 congIl? (~ (⊸r⋆ass Γ (B ∷ A ∷ Δ) (ex f))) 〉
    Il? (⊸r⋆ (Γ ++ B ∷ A ∷ Δ) (ex f))
  qed≗

-- ====================================================================

-- Strong completeness and full adequacy

-- A stronger version of completeness

strcmplt :  {S : Stp} → {Γ : Cxt} → {A : Fma} → t S ⇒ [ Γ ∣ A ] → S ∣ Γ ⊢ A
strcmplt {Γ = Γ} f = Il-1? (⊸r⋆-1 Γ (cmplt f))

-- Proof that ∀ f. strcmplt (sound f) ≗ f

strcmpltsound : {S : Stp} → {Γ : Cxt} → {C : Fma} → (f : S ∣ Γ ⊢ C) → strcmplt (sound f) ≗ f
strcmpltsound {just A} {Γ} f =
  proof≗
    ⊸r⋆-1 Γ (cmplt (sound f))
  ≗〈 cong⊸r⋆-1 Γ (cmpltsound f) 〉
    ⊸r⋆-1 Γ (⊸r⋆ Γ f)
  ≗〈 ≡-to-≗ (⊸r⋆-iso2 Γ f) 〉
    f
  qed≗ 
strcmpltsound {nothing} {Γ} f = 
  proof≗
    Il-1 (⊸r⋆-1 Γ (cmplt (sound f)))
  ≗〈 congIl-1 (cong⊸r⋆-1 Γ (cmpltsound f)) 〉
    Il-1 (⊸r⋆-1 Γ (Il (⊸r⋆ Γ f)))
  ≗〈 congIl-1 (≡-to-≗ (⊸r⋆-1Il Γ (⊸r⋆ Γ f))) 〉
    ⊸r⋆-1 Γ (⊸r⋆ Γ f)
  ≗〈 ≡-to-≗ (⊸r⋆-iso2 Γ f) 〉
    f
  qed≗ 


open import Adequacy2

-- Proof that ∀ f. sound (strcmplt f) ≐ f

soundstrcmplt : {S : Stp} → {Γ : Cxt} → {C : Fma} → (f : t S ⇒ [ Γ ∣ C ])
  → sound (strcmplt {S}{Γ} f) ≐ f
soundstrcmplt {just A}{Γ} f = sound-⊸r⋆-1 Γ (cmplt f) ∙ soundcmplt f
soundstrcmplt {nothing}{Γ} f = 
  sound-Il-1 (⊸r⋆-1 Γ (cmplt f)) ∙ sound-⊸r⋆-1 Γ (cmplt f) ∙ (soundcmplt f)
