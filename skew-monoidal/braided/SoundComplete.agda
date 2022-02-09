{-# OPTIONS --rewriting #-}

module SoundComplete where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Bool
open import Data.Bool.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import SeqCalc
open import Fsk
open import Sound
open import Complete

-- ====================================================================

-- Proof that ∀ f. sound (cmplt f) ≐ f


[ex-fma-cxt] : (Λ : Cxt) → {S A : Fma} (b : Bool) → 
              [ S ∣ Λ ] ⊗ A ⇒ [ S ∣ A ∷ Λ ]
[ex-fma-cxt] [] b = id
[ex-fma-cxt] (B ∷ Λ) b = [ s b ∣ Λ ]f ∘ [ex-fma-cxt] Λ b

[ex-cxt-fma] : (Λ : Cxt) → {S A : Fma} (b : Bool) → 
              [ S ∣ A ∷ Λ ] ⇒ [ S ∣ Λ ] ⊗ A
[ex-cxt-fma] [] b = id
[ex-cxt-fma] (B ∷ Λ) b = [ex-cxt-fma] Λ b ∘ [ s b ∣ Λ ]f

[ex-cxt-fma]iso1 : (Λ : Cxt) → {S A : Fma} (b : Bool) →
                  [ex-cxt-fma] Λ {S}{A} b ∘ [ex-fma-cxt] Λ (not b) ≐ id
[ex-cxt-fma]iso1 [] b = lid
[ex-cxt-fma]iso1 (B ∷ Λ) b =
  ass ∙ (refl ∘ (~ ass ∙ (~ [∘∣ Λ ] _ _ ∙ [≐∣ Λ ] (ss _) ∙ [id∣ Λ ] ∘ refl)))
  ∙ (refl ∘ lid ∙ [ex-cxt-fma]iso1 Λ b)

[ex-cxt-fma]iso2 : (Λ : Cxt) → {S A : Fma} (b : Bool) →
                  [ex-fma-cxt] Λ {S}{A} b ∘ [ex-cxt-fma] Λ (not b) ≐ id
[ex-cxt-fma]iso2 [] b = lid
[ex-cxt-fma]iso2 (B ∷ Λ) b =
  ass ∙ (refl ∘ (~ ass ∙ ([ex-cxt-fma]iso2 Λ b ∘ refl)) ∙ (refl ∘ lid
  ∙ (~ [∘∣ Λ ] _ _ ∙ ([≐∣ Λ ] (ss _) ∙ [id∣ Λ ])))) 

n[ex-fma-cxt] : (Λ : Cxt) → {S T A : Fma} (b : Bool) → {f : S ⇒ T}
               → [ f ⊗ id ∣ Λ ]f ∘ [ex-fma-cxt] Λ {S}{A} b ≐ [ex-fma-cxt] Λ {T}{A} b ∘ [ f ∣ Λ ]f ⊗ id
n[ex-fma-cxt] [] b = ~ rid ∙ ~ lid
n[ex-fma-cxt] (B ∷ Λ) b {f = f} =
  proof≐
    [ f ⊗ id ⊗ id ∣ Λ ]f ∘ ([ s _ ∣ Λ ]f ∘ [ex-fma-cxt] Λ _)
  ≐⟨ ~ ass ⟩
    [ f ⊗ id ⊗ id ∣ Λ ]f ∘ [ s _ ∣ Λ ]f ∘ [ex-fma-cxt] Λ _
  ≐⟨ ~ [∘∣ Λ ] _ _ ∙ [≐∣ Λ ] (~ ns-b b) ∙ [∘∣ Λ ] _ _ ∘ refl ⟩
    [ s _ ∣ Λ ]f ∘ [ f ⊗ id ⊗ id ∣ Λ ]f ∘ [ex-fma-cxt] Λ _
  ≐⟨ ass ⟩
    [ s _ ∣ Λ ]f ∘ ([ f ⊗ id ⊗ id ∣ Λ ]f ∘ [ex-fma-cxt] Λ _)
  ≐⟨ refl ∘ n[ex-fma-cxt] Λ _ {f = f ⊗ id} ⟩
    [ s _ ∣ Λ ]f ∘ ([ex-fma-cxt] Λ _ ∘ [ f ⊗ id ∣ Λ ]f ⊗ id)
  ≐⟨ ~ ass ⟩
    [ s _ ∣ Λ ]f ∘ [ex-fma-cxt] Λ _ ∘ [ f ⊗ id ∣ Λ ]f ⊗ id
  qed≐


sψ : ∀ (Γ : Cxt) {S A C : Fma} b
  →  ψ (S ⊗ C) A Γ ∘ [ s b ∣ Γ ]f ∘ [ex-fma-cxt] Γ {S ⊗ A}{C} b
       ≐ s b ∘ ψ S A Γ ⊗ id 
sψ [] b = lid ∘ ~ f⊗id
sψ (A' ∷ Γ) {S}{A}{C} b =
  proof≐
    ψ (S ⊗ C) (A ⊗ A') Γ ∘ [ α ∣ Γ ]f ∘ [ s b ⊗ id ∣ Γ ]f ∘ ([ s b ∣ Γ ]f ∘ [ex-fma-cxt] Γ b)
  ≐⟨ ~ ass ∙ (ass ∙ ass ∙ (refl ∘ (refl ∘ ~ [∘∣ Γ ] _ _ ∙ (~ [∘∣ Γ ] _ _ ∙ [≐∣ Γ ] (~ ass)))) ∘ refl) ⟩
    ψ (S ⊗ C) (A ⊗ A') Γ ∘ [ α ∘ s b ⊗ id ∘ s b ∣ Γ ]f ∘ [ex-fma-cxt] Γ b
  ≐⟨ refl ∘ [≐∣ Γ ] (~ sα2-b _) ∘ refl ⟩
    ψ (S ⊗ C) (A ⊗ A') Γ ∘ [ s b ∘ α ⊗ id ∣ Γ ]f ∘ [ex-fma-cxt] Γ b
  ≐⟨ refl ∘ [∘∣ Γ ] _ _ ∙ ~ ass ∘ refl ∙ ass ⟩
    ψ (S ⊗ C) (A ⊗ A') Γ ∘ [ s b ∣ Γ ]f ∘ ([ α ⊗ id ∣ Γ ]f ∘ [ex-fma-cxt] Γ b)
  ≐⟨ refl ∘ n[ex-fma-cxt] Γ b ⟩
    ψ (S ⊗ C) (A ⊗ A') Γ ∘ [ s b ∣ Γ ]f ∘ ([ex-fma-cxt] Γ b ∘ [ α ∣ Γ ]f ⊗ id)
  ≐⟨ ~ ass ⟩
    ψ (S  ⊗ C) (A ⊗ A') Γ ∘ [ s b ∣ Γ ]f ∘ [ex-fma-cxt] Γ b ∘ [ α ∣ Γ ]f ⊗ id
  ≐⟨ sψ Γ {S}{A ⊗ A'}{C} b ∘ refl ⟩
    s b ∘ ψ S (A ⊗ A') Γ ⊗ id ∘ [ α ∣ Γ ]f ⊗ id
  ≐⟨ ass ∙ (refl ∘ (~ f⊗∘ ∙ refl ⊗ lid)) ⟩
    s b ∘ (ψ S (A ⊗ A') Γ ∘ [ α ∣ Γ ]f) ⊗ id
  qed≐ 


sφ' : ∀ (Γ Δ : Cxt) {S A : Fma} b
  → φ' S (Δ ++ A ∷ []) Γ ∘ [ex-fma-cxt] Γ b ≐ s b ∘ φ' S Δ Γ ⊗ id
sφ' Γ Δ {S}{A} b =
  proof≐
    ψ ([ _ ∣ Δ ] ⊗ _) I Γ ∘ [ ρ  ∣ Γ ]f ∘ [ex-fma-cxt] Γ b
  ≐⟨ refl ∘ [≐∣ Γ ] (~ sρ b) ∘ refl ⟩
    ψ ([ _ ∣ Δ ] ⊗ _) I Γ ∘ [ s b ∘ ρ ⊗ id ∣ Γ ]f ∘ [ex-fma-cxt] Γ b
  ≐⟨ refl ∘ [∘∣ Γ ] _ _ ∘ refl ∙ ass ⟩
    ψ ([ _ ∣ Δ ] ⊗ _) I Γ ∘ ([ s b ∣ Γ ]f ∘ [ ρ ⊗ id ∣ Γ ]f ∘ [ex-fma-cxt] Γ b)
  ≐⟨ refl ∘ (ass ∙ (refl ∘ n[ex-fma-cxt] Γ b)) ∙ (~ ass ∙ ~ ass) ⟩
    ψ ([ _ ∣ Δ ] ⊗ _) I Γ ∘ [ s b ∣ Γ ]f ∘ [ex-fma-cxt] Γ b ∘ [ ρ ∣ Γ ]f ⊗ id
  ≐⟨ sψ Γ b ∘ refl ⟩
    s b ∘ ψ [ _ ∣ Δ ] I Γ ⊗ id ∘ [ ρ ∣ Γ ]f ⊗ id
  ≐⟨ ass ∙ (refl ∘ (~ f⊗∘ ∙ refl ⊗ lid)) ⟩
    s b ∘ (ψ [ _ ∣ Δ ] I Γ ∘ [ ρ ∣ Γ ]f) ⊗ id
  qed≐

sφ'2 : ∀ (Γ Δ : Cxt) {S A : Fma} b
  → φ' S Γ Δ ⊗ id ∘ [ex-cxt-fma] Δ b ≐ s b ∘ φ' S (Γ ++ A ∷ []) Δ
sφ'2 Γ Δ {S}{A} b =
  proof≐
    φ' S Γ Δ ⊗ id ∘ [ex-cxt-fma] Δ b
  ≐⟨ ~ lid ∘ refl ⟩
    id ∘ φ' S Γ Δ ⊗ id ∘ [ex-cxt-fma] Δ b
  ≐⟨ ~ ss _ ∘ refl ∘ refl ⟩
    s _ ∘ s _ ∘ φ' S Γ Δ ⊗ id ∘ [ex-cxt-fma] Δ b
  ≐⟨ ass ∘ refl ⟩
    s _ ∘ (s _ ∘ φ' S Γ Δ ⊗ id) ∘ [ex-cxt-fma] Δ b
  ≐⟨ refl ∘ ~ sφ' Δ Γ _ ∘ refl ⟩ 
    s _ ∘ (φ' S (Γ ++ A ∷ []) Δ ∘ [ex-fma-cxt] Δ _) ∘ [ex-cxt-fma] Δ b
  ≐⟨ ~ ass ∘ refl ∙ ass ⟩
    s _ ∘ φ' S (Γ ++ A ∷ []) Δ ∘ ([ex-fma-cxt] Δ _ ∘ [ex-cxt-fma] Δ b)
  ≐⟨ refl ∘ (refl ∘ refl≐' (cong ([ex-cxt-fma] Δ) (sym (not-involutive b))) ∙ [ex-cxt-fma]iso2 Δ (not b) ) ⟩
    s _ ∘ φ' S (Γ ++ A ∷ []) Δ ∘ id
  ≐⟨ ~ rid ⟩
    s _ ∘ φ' S (Γ ++ A ∷ []) Δ
  qed≐

soundex-fma-cxt : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma} (b : Bool) → 
              (f : S ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C) →
                sound (ex-fma-cxt {S}{Γ}{Δ} Λ b f) ≐
                  sound f ∘ [ [ex-fma-cxt] Λ b ∣ Δ ]f
soundex-fma-cxt {S} {Γ} {Δ} [] b f = rid ∙ (refl ∘ ~ [id∣ Δ ])
soundex-fma-cxt {S} {Γ} {Δ} (B ∷ Λ) b f =
  proof≐
    sound (ex-fma-cxt {S} {Γ ++ B ∷ []} {Δ} Λ b (ex b f))
  ≐⟨ soundex-fma-cxt {S} {Γ ++ B ∷ []} {Δ} Λ b (ex b f) ⟩
    sound f ∘ [ [ s b ∣ Λ ]f ∣ Δ ]f ∘ [ [ex-fma-cxt] Λ b ∣ Δ ]f
  ≐⟨ ass ⟩ 
    sound f ∘ ([ [ s b ∣ Λ ]f ∣ Δ ]f ∘ [ [ex-fma-cxt] Λ b ∣ Δ ]f)
  ≐⟨ refl ∘ ~ ([∘∣ Δ ] _ _) ⟩ 
    sound f ∘ [ [ s b ∣ Λ ]f ∘ [ex-fma-cxt] Λ b ∣ Δ ]f
  qed≐

soundex-cxt-fma : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma} (b : Bool) → 
              (f : S ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C) →
                sound (ex-cxt-fma {S}{Γ}{Δ} Λ b f) ≐
                  sound f ∘ [ [ex-cxt-fma] Λ b ∣ Δ ]f
soundex-cxt-fma {S} {Γ} {Δ} [] b f = rid ∙ (refl ∘ ~ [id∣ Δ ])
soundex-cxt-fma {S} {Γ} {Δ} (B ∷ Λ) b f =
  proof≐
    sound (ex-cxt-fma {S} {Γ ++ B ∷ []} {Δ} Λ b f) ∘ [ [ s b ∣ Λ ]f ∣ Δ ]f
  ≐⟨ soundex-cxt-fma {S}{Γ ++ B ∷ []} {Δ} Λ b f ∘ refl ⟩
    sound f ∘ [ [ex-cxt-fma] Λ b ∣ Δ ]f ∘ [ [ s b ∣ Λ ]f ∣ Δ ]f
  ≐⟨ ass ⟩
    sound f ∘ ([ [ex-cxt-fma] Λ b ∣ Δ ]f ∘ [ [ s b ∣ Λ ]f ∣ Δ ]f)
  ≐⟨ refl ∘ ~ [∘∣ Δ ] _ _ ⟩
    sound f ∘ [ [ex-cxt-fma] Λ b ∘ [ s b ∣ Λ ]f ∣ Δ ]f
  qed≐

[scut] : {S : Stp} → {Γ Δ : Cxt} → {A C : Fma} → 
           [ A ∣ Δ ] ⇒ C → 〈 S ∣ Γ 〉 ⇒ A  → 〈 S ∣ Γ ++ Δ 〉 ⇒ C
[scut] {Δ = Δ} g f = g ∘ [ f ∣ Δ ]f 

[ccut] : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
         〈  T ∣ Δ 〉  ⇒ C  → [ I ∣ Γ ] ⇒ A →  Δ ≡ Δ₀ ++ A ∷ Δ' →
                                         〈 T ∣ Δ₀ ++ Γ ++ Δ' 〉 ⇒ C
[ccut] {T} {Γ} Δ₀ {Δ'} g f refl = g ∘ [ id ⊗ f ∘ φ T Δ₀ Γ ∣ Δ' ]f 


soundscut : {S : Stp} → {Γ : Cxt} → (Δ' : Cxt) {A C : Fma} → 
     (f : S ∣ Γ ⊢ A) → (g : just A ∣ Δ' ⊢ C) → 
               sound (scut f g) ≐ [scut] {S} {Γ} {Δ'} (sound g) (sound f)                 
soundccut : {T : Stp} → {Γ Δ : Cxt} →  (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma}  → 
     (f : nothing ∣ Γ ⊢ A) → (g : T ∣ Δ ⊢ C) → (p : Δ ≡ Δ₀ ++ A ∷ Δ') →
            sound (ccut Δ₀ f g p) ≐ [ccut] {T} {Γ} Δ₀ (sound g) (sound f) p

soundscut Δ ax g = rid ∙ (refl ∘ ~ [id∣ Δ ])
soundscut Δ (uf {Γ} f) g =
  proof≐
    sound (scut f g) ∘ [ l ∣ Γ ++ Δ ]f
  ≐⟨ soundscut Δ f g ∘ refl ⟩
    sound g ∘ [ sound f ∣ Δ ]f ∘ [ l ∣ Γ ++ Δ ]f
  ≐⟨ ass ⟩
    sound g ∘ ([ sound f ∣ Δ ]f ∘ [ [ l ∣ Γ ]f ∣ Δ ]f)
  ≐⟨ refl ∘ ~ [∘∣ Δ ] (sound f) [ l ∣ Γ ]f ⟩
    sound g ∘ [ sound f ∘ [ l ∣ Γ ]f ∣ Δ ]f
  qed≐
soundscut Δ (ex {Γ = Γ}{Λ} b f) g =
  proof≐
    sound (scut f g) ∘ [ s b ∣ Λ ++ Δ ]f
  ≐⟨ soundscut Δ f g ∘ refl ⟩ 
    sound g ∘ [ sound f ∣ Δ ]f ∘ [ s b ∣ Λ ++ Δ ]f
  ≐⟨ ass ⟩ 
    sound g ∘ ([ sound f ∣ Δ ]f ∘ [ [ s b ∣ Λ ]f ∣ Δ ]f)
  ≐⟨ refl ∘ ~ [∘∣ Δ ] (sound f) [ s b ∣ Λ ]f ⟩ 
    sound g ∘ [ sound f ∘ [ s b ∣ Λ ]f ∣ Δ ]f
  qed≐
soundscut .[] Ir ax = rid
soundscut ._ Ir (ex {Γ = Γ}{Δ} b g) =
  proof≐
    sound (scut Ir g) ∘ [ s b ∣ Δ ]f
  ≐⟨ soundscut _ Ir g ∘ refl ⟩ 
    sound g ∘ [ id ∣ Γ ++ _ ∷ _ ∷ Δ ]f ∘ [ s b ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (([id∣ Γ ] ⊗ refl ∙ f⊗id) ⊗ refl ∙ f⊗id) ∙ (refl ∘ [id∣ Δ ] ∙ ~ rid) ∘ refl ⟩ 
    sound g ∘ [ s b ∣ Δ ]f
  ≐⟨ rid ∙ (refl ∘ (~ [id∣ Δ ] ∙ [≐∣ Δ ] (~ f⊗id ∙ (~ f⊗id ∙ (~ [id∣ Γ ]) ⊗ refl) ⊗ refl))) ⟩ 
    sound g ∘ [ s b ∣ Δ ]f ∘ [ [ id ∣ Γ ]f ⊗ id ⊗ id ∣ Δ ]f
  qed≐
soundscut ._ Ir (⊗r {Γ = Γ}{Δ} g g') =
  proof≐
    sound (scut Ir g) ⊗ sound g' ∘ φ' I Γ Δ
  ≐⟨ soundscut Γ Ir g ⊗ refl ∘ refl ⟩
    (sound g ∘ [ id ∣ Γ ]f) ⊗ sound g' ∘ φ' I Γ Δ
  ≐⟨ (refl ∘ [id∣ Γ ] ∙ ~ rid) ⊗ refl ∘ refl ⟩
    sound g ⊗ sound g' ∘ φ' I Γ Δ
  ≐⟨ rid ∙ (refl ∘ ~ [id∣ Γ ++ Δ ]) ⟩
    sound g ⊗ sound g' ∘ φ' I Γ Δ ∘ [ [ id ∣ Γ ]f ∣ Δ ]f
  qed≐
soundscut Δ Ir (Il g) = rid ∙ (refl ∘ ~ [id∣ Δ ])
soundscut .[] (⊗r f f') ax = ~ lid
soundscut ._ (⊗r {Γ = Γ}{Δ}{A'}{B'} f f') (ex {Γ = Γ'}{Δ'}{A}{B} b g) =
  proof≐
    sound (scut (⊗r f f') g) ∘ [ s b ∣ Δ' ]f
  ≐⟨ soundscut (Γ' ++ A ∷ B ∷ Δ') (⊗r f f') g ∘ refl ⟩ 
    sound g ∘ [ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ∣ A ∷ B ∷ Δ' ]f ∘ [ s b ∣ Δ' ]f
  ≐⟨ ass ⟩ 
    sound g ∘ ([ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ⊗ id ⊗ id ∣ Δ' ]f ∘ [ s b ∣ Δ' ]f)
  ≐⟨ refl ∘ ~ ([∘∣ Δ' ] _ _) ⟩ 
    sound g ∘ [ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ⊗ id ⊗ id ∘ s b ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] (~ ns-b b) ⟩ 
    sound g ∘ [ s b ∘ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ⊗ id ⊗ id ∣ Δ' ]f
  ≐⟨ refl ∘ [∘∣ Δ' ] _ _ ⟩ 
    sound g ∘ ([ s b ∣ Δ' ]f ∘ [ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ⊗ id ⊗ id ∣ Δ' ]f)
  ≐⟨ ~ ass ⟩ 
    sound g ∘ [ s b ∣ Δ' ]f ∘ [ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ∣ B ∷ A ∷ Δ' ]f
  qed≐
soundscut ._ (⊗r {Γ = Γ}{Δ} f f') (⊗r {Γ = Γ'}{Δ'} g g') =
  proof≐
    sound (scut (⊗r f f') g) ⊗ sound g' ∘ φ' _ (Γ ++ Δ ++ Γ') Δ'
  ≐⟨ soundscut Γ' (⊗r f f') g ⊗ rid ∘ refl ⟩ 
    (sound g ∘ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f) ⊗ (sound g' ∘ id) ∘ φ' _ (Γ ++ Δ ++ Γ') Δ'
  ≐⟨ f⊗∘ ∘ refl ⟩ 
    sound g ⊗ sound g' ∘ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ⊗ id ∘ φ' _ (Γ ++ Δ ++ Γ') Δ'
  ≐⟨ ass ⟩ 
    sound g ⊗ sound g' ∘ ([ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ⊗ id ∘ φ' _ (Γ ++ Δ ++ Γ') Δ')
  ≐⟨ refl ∘ nφ' Γ' Δ' _ ⟩ 
    sound g ⊗ sound g' ∘ (φ' _ Γ' Δ' ∘ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ++ Δ' ]f)
  ≐⟨ ~ ass ⟩ 
    sound g ⊗ sound g' ∘ φ' _ Γ' Δ' ∘ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ++ Δ' ]f
  qed≐
soundscut Δ (⊗r {Γ = Γ'}{Δ'} f f') (⊗l g) =
  proof≐
    sound (scut f (ccut [] f' g refl))
  ≐⟨ soundscut (Δ' ++ Δ) f (ccut [] f' g refl) ⟩
    sound (ccut [] f' g refl) ∘ [ sound f ∣ Δ' ++ Δ ]f
  ≐⟨ soundccut [] f' g refl ∘ refl ⟩
    sound g ∘ [ id ⊗ sound f' ∘ φ' _ [] Δ' ∣ Δ ]f ∘ [ [ sound f ∣ Δ' ]f ∣ Δ ]f
  ≐⟨ ass ⟩
    sound g ∘ ([ id ⊗ sound f' ∘ φ' _ [] Δ' ∣ Δ ]f ∘ [ [ sound f ∣ Δ' ]f ∣ Δ ]f)
  ≐⟨ refl ∘ ~ [∘∣ Δ ] _ _ ⟩
    sound g ∘ [ id ⊗ sound f' ∘ φ' _ [] Δ' ∘ [ sound f ∣ Δ' ]f ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] ass ⟩
    sound g ∘ [ id ⊗ sound f' ∘ (φ' _ [] Δ' ∘ [ sound f ∣ Δ' ]f) ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ ~ (nφ' [] Δ' (sound f))) ⟩
    sound g ∘ [ id ⊗ sound f' ∘ (sound f ⊗ id ∘ φ' _ [] Δ') ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ ass) ⟩
    sound g ∘ [ id ⊗ sound f' ∘ sound f ⊗ id ∘ φ' _ [] Δ' ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ f⊗∘ ∘ refl) ⟩
    sound g ∘ [ (id ∘ sound f) ⊗ (sound f' ∘ id) ∘ φ' _ [] Δ' ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (lid ⊗ (~ rid) ∘ refl) ⟩
    sound g ∘ [ sound f ⊗ sound f' ∘ φ' _ Γ' Δ' ∣ Δ ]f
  qed≐  
soundscut Δ (Il f) g = soundscut Δ f g
soundscut Δ (⊗l f) g = soundscut Δ f g

soundccut Δ₀ f ax p = ⊥-elim ([]disj∷ Δ₀ p)
soundccut Δ₀ f (uf g) p with  cases∷ Δ₀ p
soundccut {Γ = Γ} .[] f (uf {Γ = Δ} g) refl | inj₁ (refl , refl , refl) =
  proof≐
    sound (scut f g)
  ≐⟨ soundscut Δ f g ⟩
    sound g ∘ [ sound f ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] rid ⟩
    sound g ∘ [ sound f ∘ id ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ ~ lφ' Γ) ⟩
    sound g ∘ [ sound f ∘ (l ∘ φ nothing [] Γ) ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ ass) ⟩
    sound g ∘ [ sound f ∘ l ∘ φ nothing [] Γ ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ nl ∘ refl) ⟩
    sound g ∘ [ l ∘ id ⊗ sound f ∘ φ nothing [] Γ ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] ass ⟩
    sound g ∘ [ l ∘ (id ⊗ sound f ∘ φ nothing [] Γ) ∣ Δ ]f
  ≐⟨ refl ∘ [∘∣ Δ ] _ _ ⟩
    sound g ∘ ([ l ∣ Δ ]f ∘ [ id ⊗ sound f ∘ φ nothing [] Γ ∣ Δ ]f)
  ≐⟨ ~ ass ⟩
    sound g ∘ [ l ∣ Δ ]f ∘ [ id ⊗ sound f ∘ φ nothing [] Γ ∣ Δ ]f
  qed≐
soundccut {Γ = Γ} .(_ ∷ Γ₀) {Δ'} f (uf g) refl | inj₂ (Γ₀ , refl , refl) =
  proof≐
    sound (ccut Γ₀ f g refl) ∘ [ [ [ l ∣ Γ₀ ]f ∣ Γ ]f ∣ Δ' ]f
  ≐⟨ soundccut Γ₀ f g refl ∘ refl ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ ∣ Δ' ]f ∘ [ [ [ l ∣ Γ₀ ]f ∣ Γ ]f ∣ Δ' ]f
  ≐⟨ ass ⟩ 
    sound g ∘ ([ id ⊗ sound f ∘ φ' _ Γ₀ Γ ∣ Δ' ]f ∘ [ [ [ l ∣ Γ₀ ]f ∣ Γ ]f ∣ Δ' ]f)
  ≐⟨ refl ∘ ~ [∘∣ Δ' ] _ _ ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ ∘ [ [ l ∣ Γ₀ ]f ∣ Γ ]f ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] ass ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ (φ' _ Γ₀ Γ ∘ [ [ l ∣ Γ₀ ]f ∣ Γ ]f) ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] (refl ∘ ~ nφ' Γ₀ Γ _ ) ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ ([ l ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Γ) ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] (~ ass) ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ [ l ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Γ ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] (id⊗swap ∘ refl) ⟩ 
    sound g ∘ [ [ l ∣ Γ₀ ]f ⊗ id ∘ id ⊗ sound f ∘ φ' _ Γ₀ Γ ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] ass ⟩ 
    sound g ∘ [ [ l ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ φ' _ Γ₀ Γ) ∣ Δ' ]f
  ≐⟨ refl ∘ [∘∣ Δ' ] _ _ ⟩ 
    sound g ∘ ([ [ l ∣ Γ₀ ]f ⊗ id ∣ Δ' ]f ∘ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ ∣ Δ' ]f)
  ≐⟨ ~ ass ⟩ 
    sound g ∘ [ [ l ∣ Γ₀ ]f ⊗ id ∣ Δ' ]f ∘ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ ∣ Δ' ]f
  qed≐
soundccut Δ₀ {Δ'} f (ex {Γ = Γ} {Δ} b g) p with cases++2 Δ₀ Γ Δ' Δ p
soundccut {Γ = Γ} Δ₀ {_} f (ex {Γ = _} {Δ} b g) refl | inj₁ (Γ₀ , refl , refl) =
  proof≐
    sound (ccut Δ₀ f g refl) ∘ [ s b ∣ Δ ]f
  ≐⟨ soundccut Δ₀ f g refl ∘ refl ⟩
    sound g ∘ [ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Δ ]f ∘ [ s b ∣ Δ ]f
  ≐⟨ ass ⟩
    sound g ∘ ([ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Δ ]f ∘ [ s b ∣ Δ ]f)
  ≐⟨ refl ∘ ~ [∘∣ Δ ] _ _ ⟩
    sound g ∘ [ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ⊗ id ∘ s b ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ ns-b b) ⟩
    sound g ∘ [ s b ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Δ ]f
  ≐⟨ refl ∘ [∘∣ Δ ] _ _ ⟩
    sound g ∘ ([ s b ∣ Δ ]f ∘ [ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Δ ]f)
  ≐⟨ ~ ass ⟩
    sound g ∘ [ s b ∣ Δ ]f ∘ [ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Δ ]f
  qed≐
soundccut {Γ = Γ₁} ._ {Δ'} f (ex {Γ = Γ} {A = A}{B} b g) refl | inj₂ (inj₁ (Γ₀ , refl , refl)) =
  proof≐
    sound (ccut (Γ ++ A ∷ B ∷ Γ₀) f g refl) ∘ [ [ [ s b ∣ Γ₀ ]f ∣ Γ₁ ]f ∣ Δ' ]f
  ≐⟨ soundccut (Γ ++ A ∷ B ∷ Γ₀) f g refl ∘ refl ⟩ 
    sound g ∘  [ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f ∘ [ [ [ s b ∣ Γ₀ ]f ∣ Γ₁ ]f ∣ Δ' ]f
  ≐⟨ ass ⟩ 
    sound g ∘  ([ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f ∘ [ [ [ s b ∣ Γ₀ ]f ∣ Γ₁ ]f ∣ Δ' ]f)
  ≐⟨ refl ∘ ~ [∘∣ Δ' ] _ _ ⟩ 
    sound g ∘  [ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∘ [ [ s b ∣ Γ₀ ]f ∣ Γ₁ ]f ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] ass ⟩ 
    sound g ∘  [ id ⊗ sound f ∘ (φ' _ Γ₀ Γ₁ ∘ [ [ s b ∣ Γ₀ ]f ∣ Γ₁ ]f) ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] (refl ∘ ~ nφ' Γ₀ Γ₁ (s _)) ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ ([ s b ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Γ₁) ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] (~ ass) ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ [ s b ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] (id⊗swap ∘ refl) ⟩ 
    sound g ∘ [ [ s b ∣ Γ₀ ]f ⊗ id ∘ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f
  ≐⟨ refl ∘ [≐∣ Δ' ] ass ⟩ 
    sound g ∘ [ [ s b ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ φ' _ Γ₀ Γ₁) ∣ Δ' ]f
  ≐⟨ refl ∘ [∘∣ Δ' ] _ _ ⟩ 
    sound g ∘ ([ [ s b ∣ Γ₀ ]f ⊗ id ∣ Δ' ]f ∘ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f)
  ≐⟨ ~ ass ⟩ 
    sound g ∘ [ [ s b ∣ Γ₀ ]f ⊗ id ∣ Δ' ]f ∘ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f
  qed≐
soundccut {Γ = Γ} Δ₀ f (ex {Γ = .Δ₀} {Δ} b g) refl | inj₂ (inj₂ (inj₁ (refl , refl , refl))) =
  proof≐
    sound (ex-fma-cxt Γ b (ccut (Δ₀ ++ _ ∷ []) f g refl))
  ≐⟨ soundex-fma-cxt Γ b (ccut (Δ₀ ++ _ ∷ []) f g refl) ⟩ 
    sound (ccut (Δ₀ ++ _ ∷ []) f g refl) ∘ [ [ex-fma-cxt] Γ b ∣ Δ ]f
  ≐⟨ soundccut (Δ₀ ++ _ ∷ []) f g refl ∘ refl ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ φ' _ (Δ₀ ++ _ ∷ []) Γ ∣ Δ ]f ∘ [ [ex-fma-cxt] Γ b ∣ Δ ]f
  ≐⟨ ass ⟩ 
    sound g ∘ ([ id ⊗ sound f ∘ φ' _ (Δ₀ ++ _ ∷ []) Γ ∣ Δ ]f ∘ [ [ex-fma-cxt] Γ b ∣ Δ ]f)
  ≐⟨ refl ∘ ~ [∘∣ Δ ] _ _ ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ φ' _ (Δ₀ ++ _ ∷ []) Γ ∘ [ex-fma-cxt] Γ b ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] ass ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ (φ' _ (Δ₀ ++ _ ∷ []) Γ ∘ [ex-fma-cxt] Γ b) ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ sφ' Γ Δ₀ b) ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ (s b ∘ φ' _ Δ₀ Γ ⊗ id) ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ ass) ⟩ 
    sound g ∘ [ id ⊗ sound f ∘ s b ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] ((~ f⊗id) ⊗ refl ∘ refl ∘ refl) ⟩ 
    sound g ∘ [ (id ⊗ id) ⊗ sound f ∘ s b ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ ns-b b ∘ refl) ⟩ 
    sound g ∘ [ s b ∘ (id ⊗ sound f) ⊗ id ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (ass ∙ (refl ∘ (~ f⊗∘ ∙ refl ⊗ lid))) ⟩ 
    sound g ∘ [ s b ∘ (id ⊗ sound f ∘ φ' _ Δ₀ Γ) ⊗ id ∣ Δ ]f
  ≐⟨ refl ∘ [∘∣ Δ ] _ _ ⟩ 
    sound g ∘ ([ s b ∣ Δ ]f ∘ [ (id ⊗ sound f ∘ φ' _ Δ₀ Γ) ⊗ id ∣ Δ ]f)
  ≐⟨ ~ ass ⟩ 
    sound g ∘ [ s b ∣ Δ ]f ∘ [ (id ⊗ sound f ∘ φ' _ Δ₀ Γ) ⊗ id ∣ Δ ]f
  qed≐
soundccut {Γ = Γ₁}._ f (ex {Γ = Γ} {Δ} b g) refl | inj₂ (inj₂ (inj₂ (refl , refl , refl))) =
  proof≐
    sound (ex-cxt-fma Γ₁ b (ccut Γ f g refl))
  ≐⟨ soundex-cxt-fma Γ₁ b (ccut Γ f g refl) ⟩
    sound (ccut Γ f g refl) ∘ [ [ex-cxt-fma] Γ₁ b ∣ Δ ]f
  ≐⟨ soundccut Γ f g refl ∘ refl ⟩
    sound g ∘ [ (id ⊗ sound f ∘ φ' _ Γ Γ₁) ⊗ id ∣ Δ ]f ∘ [ [ex-cxt-fma] Γ₁ b ∣ Δ ]f
  ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _) ⟩
    sound g ∘ [ (id ⊗ sound f ∘ φ' _ Γ Γ₁) ⊗ id ∘ [ex-cxt-fma] Γ₁ b ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (refl ⊗ rid ∙ f⊗∘ ∘ refl ∙ ass) ⟩
    sound g ∘ [ id ⊗ sound f ⊗ id ∘ (φ' _ Γ Γ₁ ⊗ id ∘ [ex-cxt-fma] Γ₁ b) ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ sφ'2 Γ Γ₁ b) ⟩
    sound g ∘ [ id ⊗ sound f ⊗ id ∘ (s b ∘ φ' _ (Γ ++ _ ∷ []) Γ₁) ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ ass) ⟩
    sound g ∘ [ id ⊗ sound f ⊗ id ∘ s b ∘ φ' _ (Γ ++ _ ∷ []) Γ₁ ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (~ ns-b b ∘ refl) ⟩
    sound g ∘ [ s b ∘ id ⊗ id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ []) Γ₁ ∣ Δ ]f
  ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ f⊗id ⊗ refl ∘ refl) ⟩
    sound g ∘ [ s b ∘ id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ []) Γ₁ ∣ Δ ]f
  ≐⟨ refl ∘ ([≐∣ Δ ] ass ∙ [∘∣ Δ ] _ _) ∙ ~ ass ⟩
    sound g ∘ [ s b ∣ Δ ]f ∘ [ id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ []) Γ₁ ∣ Δ ]f
  qed≐
soundccut Δ₀ f Ir p = ⊥-elim ([]disj∷ Δ₀ p)
soundccut Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
soundccut {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) =
  proof≐
    sound (ccut Δ₀ f g refl) ⊗ sound g' ∘ φ' _ Γ₀ Δ
  ≐⟨ soundccut Δ₀ f g refl ⊗ refl ∘ refl ⟩ 
    (sound g ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f) ⊗ sound g' ∘ φ' _ Γ₀ Δ
  ≐⟨ refl ⊗ rid ∙ f⊗∘ ∘ refl ⟩ 
    sound g ⊗ sound g' ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Δ
  ≐⟨ refl ∘ refl ∙ ass ⟩ 
    sound g ⊗ sound g' ∘ ([ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Δ)
  ≐⟨ refl ∘ nφ' Γ₀ Δ (id ⊗ sound f ∘ φ' _ Δ₀ Γ) ⟩ 
    sound g ⊗ sound g' ∘ (φ' _ Γ₀ Δ ∘ [ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ∣ Δ ]f)
  ≐⟨ ~ ass ⟩ 
    sound g ⊗ sound g' ∘ φ' _ Γ₀ Δ ∘ [ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ∣ Δ ]f
  qed≐
soundccut {Γ = Γ₁} .(Γ ++ Γ₀) {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) =
  proof≐
    sound g ⊗ sound (ccut Γ₀ f g' refl) ∘ φ' _ Γ (Γ₀ ++ Γ₁ ++ Δ')
  ≐⟨ refl ⊗ soundccut Γ₀ f g' refl ∘ refl ⟩ 
    sound g ⊗ (sound g' ∘ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f) ∘ φ' _ Γ (Γ₀ ++ Γ₁ ++ Δ')
  ≐⟨ rid ⊗ refl ∙ f⊗∘ ∘ refl ⟩ 
    sound g ⊗ sound g' ∘ id ⊗ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f ∘ φ' _ Γ (Γ₀ ++ Γ₁ ++ Δ')
  ≐⟨ refl ∘ (refl ⊗ [∘∣ Δ' ] _ _ ∙ (rid ⊗ refl ∙ f⊗∘)) ∙ ~ ass ∘ refl ∙ ass ⟩ 
    sound g ⊗ sound g' ∘ id ⊗ [ id ⊗ sound f ∣ Δ' ]f ∘ (id ⊗ [ φ' _ Γ₀ Γ₁ ∣ Δ' ]f ∘ φ' _ Γ (Γ₀ ++ Γ₁ ++ Δ'))
  ≐⟨ refl ∘ assφ' Γ Γ₀ Γ₁ Δ' ⟩ 
    sound g ⊗ sound g' ∘ id ⊗ [ id ⊗ sound f ∣ Δ' ]f ∘ (φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ φ' _ (Γ ++ Γ₀) Γ₁ ∣ Δ' ]f)
  ≐⟨ ~ ass ∙ (ass ∘ refl) ⟩ 
    sound g ⊗ sound g' ∘ (id ⊗ [ id ⊗ sound f ∣ Δ' ]f ∘ φ' _ Γ (Γ₀ ++ _ ∷ Δ')) ∘ [ φ' _ (Γ ++ Γ₀) Γ₁ ∣ Δ' ]f
  ≐⟨ refl ∘ nφ'2 Γ Γ₀ Δ' (sound f) ∘ refl ⟩ 
    sound g ⊗ sound g' ∘ (φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ id ⊗ sound f ∣ Δ' ]f) ∘ [ φ' _ (Γ ++ Γ₀) Γ₁ ∣ Δ' ]f
  ≐⟨ ~ ass ∘ refl ∙ ass ∙ (refl ∘ ~ [∘∣ Δ' ] _ _)  ⟩ 
    sound g ⊗ sound g' ∘ φ' _ Γ (Γ₀ ++ _ ∷ Δ') ∘ [ id ⊗ sound f ∘ φ' _ (Γ ++ Γ₀) Γ₁ ∣ Δ' ]f
  qed≐
soundccut Δ₀ f (Il g) refl = soundccut Δ₀ f g refl
soundccut Δ₀ f (⊗l g) refl = soundccut (_ ∷ Δ₀) f g refl


soundcmplt : {A B : Fma} (f : A ⇒ B)
  → sound (cmplt f) ≐ f
soundcmplt id = refl
soundcmplt (f ∘ g) =
  soundscut [] (cmplt g) (cmplt f)
  ∙ (soundcmplt f ∘ soundcmplt g)
soundcmplt (f ⊗ g) =
  soundcmplt f ⊗ (soundcmplt g ∘ refl) ∘ refl
  ∙ (rid ⊗ refl ∙ f⊗∘ ∘ refl)
  ∙ ass
  ∙ (refl ∘ (refl ∘ (lid ∘ refl) ∙ (~ ass ∙ ~ lαρ)))
  ∙ ~ rid
soundcmplt l = lid
soundcmplt ρ = f⊗id ∘ refl ∙ (lid ∙ lid)
soundcmplt α =
  proof≐
    id ⊗ (id ⊗ (id ∘ l) ∘ (id ∘ α ∘ ρ ⊗ id) ∘ l ⊗ id) ∘ (id ∘ α ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id)
  ≐⟨ refl ⊗ (~ ass ∙ (~ ass ∙ (~ rid ∙ refl ⊗ lid ∘ refl) ∘ refl) ∘ refl) ∘ (lid ∘ refl ∘ refl) ⟩
    id ⊗ (id ⊗ l ∘ α ∘ ρ ⊗ id ∘ l ⊗ id) ∘ (α ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id)
  ≐⟨ refl ⊗ (~ lαρ ∘ refl ∙ lid) ∘ refl ⟩
    id ⊗ (l ⊗ id) ∘ (α ∘ α ⊗ id ∘ (ρ ⊗ id) ⊗ id)
  ≐⟨ ~ ass ∙ (~ ass ∘ refl) ⟩
    id ⊗ (l ⊗ id) ∘ α ∘ α ⊗ id ∘ (ρ ⊗ id) ⊗ id
  ≐⟨ ~ nα ∘ refl ∘ refl ⟩
    α ∘ (id ⊗ l) ⊗ id ∘ α ⊗ id ∘ (ρ ⊗ id) ⊗ id
  ≐⟨ ass ∙ (refl ∘ (~ f⊗∘ ∙ refl ⊗ lid) ∙ (ass ∙ (refl ∘ (~ f⊗∘ ∙ (~ ass) ⊗ lid)))) ⟩
    α ∘ (id ⊗ l ∘ α ∘ ρ ⊗ id) ⊗ id
  ≐⟨ refl ∘ (~ lαρ) ⊗ refl ∙ (refl ∘ f⊗id) ∙ ~ rid ⟩
    α
  qed≐
soundcmplt (s b) =
  proof≐
    (id ⊗ (id ∘ l) ∘ (id ∘ α ∘ ρ ⊗ id)) ⊗ (id ∘ l) ∘ (id ∘ α ∘ ρ ⊗ id) ∘ s b
  ≐⟨ ~ ass ∙ (~ ass ∙ (~ rid ∙ ((refl ⊗ lid ∘ (lid ∘ refl)) ⊗ lid ∙ (~ ass) ⊗ refl) ∘ refl) ∘ refl) ∘ refl ⟩ 
    (id ⊗ l ∘ α ∘ ρ ⊗ id) ⊗ l ∘ α ∘ ρ ⊗ id ∘ s b
  ≐⟨ (~ lαρ) ⊗ refl ∘ refl ∘ refl ∘ refl ⟩ 
    id ⊗ l ∘ α ∘ ρ ⊗ id ∘ s b
  ≐⟨ ~ (lαρ ∘ refl) ⟩ 
    id ∘ s b
  ≐⟨ lid ⟩ 
    s b
  qed≐


