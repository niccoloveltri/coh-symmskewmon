{-# OPTIONS --rewriting #-}

module SoundComplete where

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
open import Sound
open import Complete

-- ====================================================================

-- Proof that ∀ f. sound (cmplt f) ≐ f


[ex-fma-cxt] : (Λ : Cxt) → {S A : Fma} → 
              [ S ∣ Λ ] ⊗ A ⇒ [ S ∣ A ∷ Λ ]
[ex-fma-cxt] [] = id
[ex-fma-cxt] (B ∷ Λ) = [ s ∣ Λ ]f ∘ [ex-fma-cxt] Λ

[ex-cxt-fma] : (Λ : Cxt) → {S A : Fma} → 
              [ S ∣ A ∷ Λ ] ⇒ [ S ∣ Λ ] ⊗ A
[ex-cxt-fma] [] = id
[ex-cxt-fma] (B ∷ Λ) = [ex-cxt-fma] Λ ∘ [ s ∣ Λ ]f

n[ex-fma-cxt] : (Λ : Cxt) → {S T A : Fma} → {f : S ⇒ T}
               → [ f ⊗ id ∣ Λ ]f ∘ [ex-fma-cxt] Λ {S}{A} ≐ [ex-fma-cxt] Λ {T}{A} ∘ [ f ∣ Λ ]f ⊗ id
n[ex-fma-cxt] [] = ~ rid ∙ ~ lid
n[ex-fma-cxt] (B ∷ Λ) {f = f} =
  proof≐
    [ f ⊗ id ⊗ id ∣ Λ ]f ∘ ([ s ∣ Λ ]f ∘ [ex-fma-cxt] Λ)
  ≐⟨ ~ ass ⟩
    [ f ⊗ id ⊗ id ∣ Λ ]f ∘ [ s ∣ Λ ]f ∘ [ex-fma-cxt] Λ
  ≐⟨ ~ [∘∣ Λ ] _ _ ∙ [≐∣ Λ ] (~ ns) ∙ [∘∣ Λ ] _ _ ∘ refl ⟩
    [ s ∣ Λ ]f ∘ [ f ⊗ id ⊗ id ∣ Λ ]f ∘ [ex-fma-cxt] Λ
  ≐⟨ ass ⟩
    [ s ∣ Λ ]f ∘ ([ f ⊗ id ⊗ id ∣ Λ ]f ∘ [ex-fma-cxt] Λ)
  ≐⟨ refl ∘ n[ex-fma-cxt] Λ {f = f ⊗ id} ⟩
    [ s ∣ Λ ]f ∘ ([ex-fma-cxt] Λ ∘ [ f ⊗ id ∣ Λ ]f ⊗ id)
  ≐⟨ ~ ass ⟩
    [ s ∣ Λ ]f ∘ [ex-fma-cxt] Λ ∘ [ f ⊗ id ∣ Λ ]f ⊗ id
  qed≐

[ex-cxt-fma]iso1 : (Λ : Cxt) → {S A : Fma} →
                  [ex-cxt-fma] Λ {S}{A} ∘ [ex-fma-cxt] Λ ≐ id
[ex-cxt-fma]iso1 [] = lid
[ex-cxt-fma]iso1 (B ∷ Λ) =
  ass ∙ (refl ∘ (~ ass ∙ (~ [∘∣ Λ ] _ _ ∙ [≐∣ Λ ] ss ∙ [id∣ Λ ] ∘ refl)))
  ∙ (refl ∘ lid ∙ [ex-cxt-fma]iso1 Λ)

[ex-cxt-fma]iso2 : (Λ : Cxt) → {S A : Fma} →
                  [ex-fma-cxt] Λ {S}{A} ∘ [ex-cxt-fma] Λ ≐ id
[ex-cxt-fma]iso2 [] = lid
[ex-cxt-fma]iso2 (B ∷ Λ) =
  ass ∙ (refl ∘ (~ ass ∙ ([ex-cxt-fma]iso2 Λ ∘ refl)) ∙ (refl ∘ lid
  ∙ (~ [∘∣ Λ ] _ _ ∙ ([≐∣ Λ ] ss ∙ [id∣ Λ ])))) 

sψ : (Γ : Cxt) {S A C : Fma}
  →  ψ (S ⊗ C) A Γ ∘ [ s ∣ Γ ]f ∘ [ex-fma-cxt] Γ {S ⊗ A}{C}
       ≐ s ∘ ψ S A Γ ⊗ id 
sψ [] = lid ∘ ~ f⊗id
sψ (A' ∷ Γ) {S}{A}{C} =
  proof≐
    ψ (S ⊗ C) (A ⊗ A') Γ ∘ [ α ∣ Γ ]f ∘ [ s ⊗ id ∣ Γ ]f ∘ ([ s ∣ Γ ]f ∘ [ex-fma-cxt] Γ)
  ≐⟨ ~ ass ∙ (ass ∙ ass ∙ (refl ∘ (refl ∘ ~ [∘∣ Γ ] _ _ ∙ (~ [∘∣ Γ ] _ _ ∙ [≐∣ Γ ] (~ ass)))) ∘ refl) ⟩
    ψ (S ⊗ C) (A ⊗ A') Γ ∘ [ α ∘ s ⊗ id ∘ s ∣ Γ ]f ∘ [ex-fma-cxt] Γ
  ≐⟨ refl ∘ [≐∣ Γ ] (~ sα2) ∘ refl ⟩
    ψ (S ⊗ C) (A ⊗ A') Γ ∘ [ s ∘ α ⊗ id ∣ Γ ]f ∘ [ex-fma-cxt] Γ
  ≐⟨ refl ∘ [∘∣ Γ ] _ _ ∙ ~ ass ∘ refl ∙ ass ⟩
    ψ (S ⊗ C) (A ⊗ A') Γ ∘ [ s ∣ Γ ]f ∘ ([ α ⊗ id ∣ Γ ]f ∘ [ex-fma-cxt] Γ)
  ≐⟨ refl ∘ n[ex-fma-cxt] Γ ⟩
    ψ (S ⊗ C) (A ⊗ A') Γ ∘ [ s ∣ Γ ]f ∘ ([ex-fma-cxt] Γ ∘ [ α ∣ Γ ]f ⊗ id)
  ≐⟨ ~ ass ⟩
    ψ (S  ⊗ C) (A ⊗ A') Γ ∘ [ s ∣ Γ ]f ∘ [ex-fma-cxt] Γ ∘ [ α ∣ Γ ]f ⊗ id
  ≐⟨ sψ Γ {S}{A ⊗ A'}{C} ∘ refl ⟩
    s ∘ ψ S (A ⊗ A') Γ ⊗ id ∘ [ α ∣ Γ ]f ⊗ id
  ≐⟨ ass ∙ (refl ∘ (~ f⊗∘ ∙ refl ⊗ lid)) ⟩
    s ∘ (ψ S (A ⊗ A') Γ ∘ [ α ∣ Γ ]f) ⊗ id
  qed≐ 


sφ' : (Γ Δ : Cxt) {S A : Fma}
  → φ' S (Δ ++ A ∷ []) Γ ∘ [ex-fma-cxt] Γ ≐ s ∘ φ' S Δ Γ ⊗ id
sφ' Γ Δ {S}{A} =
  proof≐
    ψ ([ _ ∣ Δ ] ⊗ _) I Γ ∘ [ ρ  ∣ Γ ]f ∘ [ex-fma-cxt] Γ
  ≐⟨ refl ∘ [≐∣ Γ ] (~ sρ) ∘ refl ⟩
    ψ ([ _ ∣ Δ ] ⊗ _) I Γ ∘ [ s ∘ ρ ⊗ id ∣ Γ ]f ∘ [ex-fma-cxt] Γ
  ≐⟨ refl ∘ [∘∣ Γ ] _ _ ∘ refl ∙ ass ⟩
    ψ ([ _ ∣ Δ ] ⊗ _) I Γ ∘ ([ s ∣ Γ ]f ∘ [ ρ ⊗ id ∣ Γ ]f ∘ [ex-fma-cxt] Γ)
  ≐⟨ refl ∘ (ass ∙ (refl ∘ n[ex-fma-cxt] Γ)) ∙ (~ ass ∙ ~ ass) ⟩
    ψ ([ _ ∣ Δ ] ⊗ _) I Γ ∘ [ s ∣ Γ ]f ∘ [ex-fma-cxt] Γ ∘ [ ρ ∣ Γ ]f ⊗ id
  ≐⟨ sψ Γ ∘ refl ⟩
    s ∘ ψ [ _ ∣ Δ ] I Γ ⊗ id ∘ [ ρ ∣ Γ ]f ⊗ id
  ≐⟨ ass ∙ (refl ∘ (~ f⊗∘ ∙ refl ⊗ lid)) ⟩
    s ∘ (ψ [ _ ∣ Δ ] I Γ ∘ [ ρ ∣ Γ ]f) ⊗ id
  qed≐

sφ'2 : (Γ Δ : Cxt) {S A : Fma}
  → φ' S Γ Δ ⊗ id ∘ [ex-cxt-fma] Δ ≐ s ∘ φ' S (Γ ++ A ∷ []) Δ
sφ'2 Γ Δ {S}{A} =
  proof≐
    φ' S Γ Δ ⊗ id ∘ [ex-cxt-fma] Δ
  ≐⟨ ~ lid ∘ refl ⟩
    id ∘ φ' S Γ Δ ⊗ id ∘ [ex-cxt-fma] Δ
  ≐⟨ ~ ss ∘ refl ∘ refl ⟩
    s ∘ s ∘ φ' S Γ Δ ⊗ id ∘ [ex-cxt-fma] Δ
  ≐⟨ ass ∘ refl ⟩
    s ∘ (s ∘ φ' S Γ Δ ⊗ id) ∘ [ex-cxt-fma] Δ
  ≐⟨ refl ∘ ~ sφ' Δ Γ ∘ refl ⟩
    s ∘ (φ' S (Γ ++ A ∷ []) Δ ∘ [ex-fma-cxt] Δ) ∘ [ex-cxt-fma] Δ
  ≐⟨ ~ ass ∘ refl ∙ ass ⟩
    s ∘ φ' S (Γ ++ A ∷ []) Δ ∘ ([ex-fma-cxt] Δ ∘ [ex-cxt-fma] Δ)
  ≐⟨ refl ∘ [ex-cxt-fma]iso2 Δ ⟩
    s ∘ φ' S (Γ ++ A ∷ []) Δ ∘ id
  ≐⟨ ~ rid ⟩
    s ∘ φ' S (Γ ++ A ∷ []) Δ
  qed≐

soundex-fma-cxt : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma} → 
              (f : S ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C) →
                sound (ex-fma-cxt {S}{Γ}{Δ} Λ f) ≐
                  sound f ∘ [ [ex-fma-cxt] Λ ∣ Δ ]f
soundex-fma-cxt {S} {Γ} {Δ} [] f = rid ∙ (refl ∘ ~ [id∣ Δ ])
soundex-fma-cxt {S} {Γ} {Δ} (B ∷ Λ) f =
  proof≐
    sound (ex-fma-cxt {S} {Γ ++ B ∷ []} {Δ} Λ (ex f))
  ≐⟨ soundex-fma-cxt {S} {Γ ++ B ∷ []} {Δ} Λ (ex f) ⟩
    sound f ∘ [ [ s ∣ Λ ]f ∣ Δ ]f ∘ [ [ex-fma-cxt] Λ ∣ Δ ]f
  ≐⟨ ass ⟩ 
    sound f ∘ ([ [ s ∣ Λ ]f ∣ Δ ]f ∘ [ [ex-fma-cxt] Λ ∣ Δ ]f)
  ≐⟨ refl ∘ ~ ([∘∣ Δ ] _ _) ⟩ 
    sound f ∘ [ [ s ∣ Λ ]f ∘ [ex-fma-cxt] Λ ∣ Δ ]f
  qed≐

soundex-cxt-fma : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma} → 
              (f : S ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C) →
                sound (ex-cxt-fma {S}{Γ}{Δ} Λ f) ≐
                  sound f ∘ [ [ex-cxt-fma] Λ ∣ Δ ]f
soundex-cxt-fma {S} {Γ} {Δ} [] f = rid ∙ (refl ∘ ~ [id∣ Δ ])
soundex-cxt-fma {S} {Γ} {Δ} (B ∷ Λ) f =
  proof≐
    sound (ex-cxt-fma {S} {Γ ++ B ∷ []} {Δ} Λ f) ∘ [ [ s ∣ Λ ]f ∣ Δ ]f
  ≐⟨ soundex-cxt-fma {S}{Γ ++ B ∷ []} {Δ} Λ f ∘ refl ⟩
    sound f ∘ [ [ex-cxt-fma] Λ ∣ Δ ]f ∘ [ [ s ∣ Λ ]f ∣ Δ ]f
  ≐⟨ ass ⟩
    sound f ∘ ([ [ex-cxt-fma] Λ ∣ Δ ]f ∘ [ [ s ∣ Λ ]f ∣ Δ ]f)
  ≐⟨ refl ∘ ~ [∘∣ Δ ] _ _ ⟩
    sound f ∘ [ [ex-cxt-fma] Λ ∘ [ s ∣ Λ ]f ∣ Δ ]f
  qed≐

[scut] : {S : Stp} → {Γ Δ : Cxt} → {A C : Fma} → 
           [ A ∣ Δ ] ⇒ C → 〈 S ∣ Γ 〉 ⇒ A  → 〈 S ∣ Γ ++ Δ 〉 ⇒ C
[scut] {Δ = Δ} g f = g ∘ [ f ∣ Δ ]f 

[ccut] : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
         〈  T ∣ Δ 〉  ⇒ C  → [ I ∣ Γ ] ⇒ A →  Δ ≡ Δ₀ ++ A ∷ Δ' →
                                         〈 T ∣ Δ₀ ++ Γ ++ Δ' 〉 ⇒ C
[ccut] {T} {Γ} Δ₀ {Δ'} g f refl = g ∘ [ id ⊗ f ∘ φ T Δ₀ Γ ∣ Δ' ]f 

  
mutual
  soundscut : {S : Stp} → {Γ : Cxt} → (Δ' : Cxt) {A C : Fma} → 
       (f : S ∣ Γ ⊢ A) → (g : just A ∣ Δ' ⊢ C) → 
                 sound (scut f g) ≐ [scut] {S} {Γ} {Δ'} (sound g) (sound f)                 
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
  soundscut Δ (ex {Γ = Γ}{Λ} f) g =
    proof≐
      sound (scut f g) ∘ [ s ∣ Λ ++ Δ ]f
    ≐⟨ soundscut Δ f g ∘ refl ⟩ 
      sound g ∘ [ sound f ∣ Δ ]f ∘ [ s ∣ Λ ++ Δ ]f
    ≐⟨ ass ⟩ 
      sound g ∘ ([ sound f ∣ Δ ]f ∘ [ [ s ∣ Λ ]f ∣ Δ ]f)
    ≐⟨ refl ∘ ~ [∘∣ Δ ] (sound f) [ s ∣ Λ ]f ⟩ 
      sound g ∘ [ sound f ∘ [ s ∣ Λ ]f ∣ Δ ]f
    qed≐
  soundscut .[] Ir ax = rid
  soundscut ._ Ir (ex {Γ = Γ}{Δ} g) =
    proof≐
      sound (scut Ir g) ∘ [ s ∣ Δ ]f
    ≐⟨ soundscut _ Ir g ∘ refl ⟩ 
      sound g ∘ [ id ∣ Γ ++ _ ∷ _ ∷ Δ ]f ∘ [ s ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (([id∣ Γ ] ⊗ refl ∙ f⊗id) ⊗ refl ∙ f⊗id) ∙ (refl ∘ [id∣ Δ ] ∙ ~ rid) ∘ refl ⟩ 
      sound g ∘ [ s ∣ Δ ]f
    ≐⟨ rid ∙ (refl ∘ (~ [id∣ Δ ] ∙ [≐∣ Δ ] (~ f⊗id ∙ (~ f⊗id ∙ (~ [id∣ Γ ]) ⊗ refl) ⊗ refl))) ⟩ 
      sound g ∘ [ s ∣ Δ ]f ∘ [ [ id ∣ Γ ]f ⊗ id ⊗ id ∣ Δ ]f
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
  soundscut ._ (⊗r {Γ = Γ}{Δ}{A'}{B'} f f') (ex {Γ = Γ'}{Δ'}{A}{B} g) =
    proof≐
      sound (scut (⊗r f f') g) ∘ [ s ∣ Δ' ]f
    ≐⟨ soundscut (Γ' ++ A ∷ B ∷ Δ') (⊗r f f') g ∘ refl ⟩ 
      sound g ∘ [ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ∣ A ∷ B ∷ Δ' ]f ∘ [ s ∣ Δ' ]f
    ≐⟨ ass ⟩ 
      sound g ∘ ([ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ⊗ id ⊗ id ∣ Δ' ]f ∘ [ s ∣ Δ' ]f)
    ≐⟨ refl ∘ ~ ([∘∣ Δ' ] _ _) ⟩ 
      sound g ∘ [ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ⊗ id ⊗ id ∘ s ∣ Δ' ]f
    ≐⟨ refl ∘ [≐∣ Δ' ] (~ ns) ⟩ 
      sound g ∘ [ s ∘ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ⊗ id ⊗ id ∣ Δ' ]f
    ≐⟨ refl ∘ [∘∣ Δ' ] _ _ ⟩ 
      sound g ∘ ([ s ∣ Δ' ]f ∘ [ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ⊗ id ⊗ id ∣ Δ' ]f)
    ≐⟨ ~ ass ⟩ 
      sound g ∘ [ s ∣ Δ' ]f ∘ [ [ sound f ⊗ sound f' ∘ φ' _ Γ Δ ∣ Γ' ]f ∣ B ∷ A ∷ Δ' ]f
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

  soundccut : {T : Stp} → {Γ Δ : Cxt} →  (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma}  → 
       (f : nothing ∣ Γ ⊢ A) → (g : T ∣ Δ ⊢ C) → (p : Δ ≡ Δ₀ ++ A ∷ Δ') →
              sound (ccut Δ₀ f g p) ≐ [ccut] {T} {Γ} Δ₀ (sound g) (sound f) p
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
  soundccut Δ₀ {Δ'} f (ex {Γ = Γ} {Δ} g) p with cases++2 Δ₀ Γ Δ' Δ p
  soundccut {Γ = Γ} Δ₀ {_} f (ex {Γ = _} {Δ} g) refl | inj₁ (Γ₀ , refl , refl) =
    proof≐
      sound (ccut Δ₀ f g refl) ∘ [ s ∣ Δ ]f
    ≐⟨ soundccut Δ₀ f g refl ∘ refl ⟩
      sound g ∘ [ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Δ ]f ∘ [ s ∣ Δ ]f
    ≐⟨ ass ⟩
      sound g ∘ ([ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Δ ]f ∘ [ s ∣ Δ ]f)
    ≐⟨ refl ∘ ~ [∘∣ Δ ] _ _ ⟩
      sound g ∘ [ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ⊗ id ∘ s ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (~ ns) ⟩
      sound g ∘ [ s ∘ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Δ ]f
    ≐⟨ refl ∘ [∘∣ Δ ] _ _ ⟩
      sound g ∘ ([ s ∣ Δ ]f ∘ [ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Δ ]f)
    ≐⟨ ~ ass ⟩
      sound g ∘ [ s ∣ Δ ]f ∘ [ [ id ⊗ sound f ∘ φ' _ Δ₀ Γ ∣ Γ₀ ]f ⊗ id ⊗ id ∣ Δ ]f
    qed≐
  soundccut {Γ = Γ₁} ._ {Δ'} f (ex {Γ = Γ} {A = A}{B} g) refl | inj₂ (inj₁ (Γ₀ , refl , refl)) =
    proof≐
      sound (ccut (Γ ++ A ∷ B ∷ Γ₀) f g refl) ∘ [ [ [ s ∣ Γ₀ ]f ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ soundccut (Γ ++ A ∷ B ∷ Γ₀) f g refl ∘ refl ⟩ 
      sound g ∘  [ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f ∘ [ [ [ s ∣ Γ₀ ]f ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ ass ⟩ 
      sound g ∘  ([ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f ∘ [ [ [ s ∣ Γ₀ ]f ∣ Γ₁ ]f ∣ Δ' ]f)
    ≐⟨ refl ∘ ~ [∘∣ Δ' ] _ _ ⟩ 
      sound g ∘  [ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∘ [ [ s ∣ Γ₀ ]f ∣ Γ₁ ]f ∣ Δ' ]f
    ≐⟨ refl ∘ [≐∣ Δ' ] ass ⟩ 
      sound g ∘  [ id ⊗ sound f ∘ (φ' _ Γ₀ Γ₁ ∘ [ [ s ∣ Γ₀ ]f ∣ Γ₁ ]f) ∣ Δ' ]f
    ≐⟨ refl ∘ [≐∣ Δ' ] (refl ∘ ~ nφ' Γ₀ Γ₁ s) ⟩ 
      sound g ∘ [ id ⊗ sound f ∘ ([ s ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Γ₁) ∣ Δ' ]f
    ≐⟨ refl ∘ [≐∣ Δ' ] (~ ass) ⟩ 
      sound g ∘ [ id ⊗ sound f ∘ [ s ∣ Γ₀ ]f ⊗ id ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f
    ≐⟨ refl ∘ [≐∣ Δ' ] (id⊗swap ∘ refl) ⟩ 
      sound g ∘ [ [ s ∣ Γ₀ ]f ⊗ id ∘ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f
    ≐⟨ refl ∘ [≐∣ Δ' ] ass ⟩ 
      sound g ∘ [ [ s ∣ Γ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ φ' _ Γ₀ Γ₁) ∣ Δ' ]f
    ≐⟨ refl ∘ [∘∣ Δ' ] _ _ ⟩ 
      sound g ∘ ([ [ s ∣ Γ₀ ]f ⊗ id ∣ Δ' ]f ∘ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f)
    ≐⟨ ~ ass ⟩ 
      sound g ∘ [ [ s ∣ Γ₀ ]f ⊗ id ∣ Δ' ]f ∘ [ id ⊗ sound f ∘ φ' _ Γ₀ Γ₁ ∣ Δ' ]f
    qed≐
  soundccut {Γ = Γ} Δ₀ f (ex {Γ = .Δ₀} {Δ} g) refl | inj₂ (inj₂ (inj₁ (refl , refl , refl))) =
    proof≐
      sound (ex-fma-cxt Γ (ccut (Δ₀ ++ _ ∷ []) f g refl))
    ≐⟨ soundex-fma-cxt Γ (ccut (Δ₀ ++ _ ∷ []) f g refl) ⟩ 
      sound (ccut (Δ₀ ++ _ ∷ []) f g refl) ∘ [ [ex-fma-cxt] Γ ∣ Δ ]f
    ≐⟨ soundccut (Δ₀ ++ _ ∷ []) f g refl ∘ refl ⟩ 
      sound g ∘ [ id ⊗ sound f ∘ φ' _ (Δ₀ ++ _ ∷ []) Γ ∣ Δ ]f ∘ [ [ex-fma-cxt] Γ ∣ Δ ]f
    ≐⟨ ass ⟩ 
      sound g ∘ ([ id ⊗ sound f ∘ φ' _ (Δ₀ ++ _ ∷ []) Γ ∣ Δ ]f ∘ [ [ex-fma-cxt] Γ ∣ Δ ]f)
    ≐⟨ refl ∘ ~ [∘∣ Δ ] _ _ ⟩ 
      sound g ∘ [ id ⊗ sound f ∘ φ' _ (Δ₀ ++ _ ∷ []) Γ ∘ [ex-fma-cxt] Γ ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] ass ⟩ 
      sound g ∘ [ id ⊗ sound f ∘ (φ' _ (Δ₀ ++ _ ∷ []) Γ ∘ [ex-fma-cxt] Γ) ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ sφ' Γ Δ₀) ⟩ 
      sound g ∘ [ id ⊗ sound f ∘ (s ∘ φ' _ Δ₀ Γ ⊗ id) ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (~ ass) ⟩ 
      sound g ∘ [ id ⊗ sound f ∘ s ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] ((~ f⊗id) ⊗ refl ∘ refl ∘ refl) ⟩ 
      sound g ∘ [ (id ⊗ id) ⊗ sound f ∘ s ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (~ ns ∘ refl) ⟩ 
      sound g ∘ [ s ∘ (id ⊗ sound f) ⊗ id ∘ φ' _ Δ₀ Γ ⊗ id ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (ass ∙ (refl ∘ (~ f⊗∘ ∙ refl ⊗ lid))) ⟩ 
      sound g ∘ [ s ∘ (id ⊗ sound f ∘ φ' _ Δ₀ Γ) ⊗ id ∣ Δ ]f
    ≐⟨ refl ∘ [∘∣ Δ ] _ _ ⟩ 
      sound g ∘ ([ s ∣ Δ ]f ∘ [ (id ⊗ sound f ∘ φ' _ Δ₀ Γ) ⊗ id ∣ Δ ]f)
    ≐⟨ ~ ass ⟩ 
      sound g ∘ [ s ∣ Δ ]f ∘ [ (id ⊗ sound f ∘ φ' _ Δ₀ Γ) ⊗ id ∣ Δ ]f
    qed≐
  soundccut {Γ = Γ₁}._ f (ex {Γ = Γ} {Δ} g) refl | inj₂ (inj₂ (inj₂ (refl , refl , refl))) =
    proof≐
      sound (ex-cxt-fma Γ₁ (ccut Γ f g refl))
    ≐⟨ soundex-cxt-fma Γ₁ (ccut Γ f g refl) ⟩
      sound (ccut Γ f g refl) ∘ [ [ex-cxt-fma] Γ₁ ∣ Δ ]f
    ≐⟨ soundccut Γ f g refl ∘ refl ⟩
      sound g ∘ [ (id ⊗ sound f ∘ φ' _ Γ Γ₁) ⊗ id ∣ Δ ]f ∘ [ [ex-cxt-fma] Γ₁ ∣ Δ ]f
    ≐⟨ ass ∙ (refl ∘ ~ [∘∣ Δ ] _ _) ⟩
      sound g ∘ [ (id ⊗ sound f ∘ φ' _ Γ Γ₁) ⊗ id ∘ [ex-cxt-fma] Γ₁ ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (refl ⊗ rid ∙ f⊗∘ ∘ refl ∙ ass) ⟩
      sound g ∘ [ id ⊗ sound f ⊗ id ∘ (φ' _ Γ Γ₁ ⊗ id ∘ [ex-cxt-fma] Γ₁) ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ sφ'2 Γ Γ₁) ⟩
      sound g ∘ [ id ⊗ sound f ⊗ id ∘ (s ∘ φ' _ (Γ ++ _ ∷ []) Γ₁) ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (~ ass) ⟩
      sound g ∘ [ id ⊗ sound f ⊗ id ∘ s ∘ φ' _ (Γ ++ _ ∷ []) Γ₁ ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (~ ns ∘ refl) ⟩
      sound g ∘ [ s ∘ id ⊗ id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ []) Γ₁ ∣ Δ ]f
    ≐⟨ refl ∘ [≐∣ Δ ] (refl ∘ f⊗id ⊗ refl ∘ refl) ⟩
      sound g ∘ [ s ∘ id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ []) Γ₁ ∣ Δ ]f
    ≐⟨ refl ∘ ([≐∣ Δ ] ass ∙ [∘∣ Δ ] _ _) ∙ ~ ass ⟩
      sound g ∘ [ s ∣ Δ ]f ∘ [ id ⊗ sound f ∘ φ' _ (Γ ++ _ ∷ []) Γ₁ ∣ Δ ]f
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
soundcmplt s =
  proof≐
    (id ⊗ (id ∘ l) ∘ (id ∘ α ∘ ρ ⊗ id)) ⊗ (id ∘ l) ∘ (id ∘ α ∘ ρ ⊗ id) ∘ s
  ≐⟨ ~ ass ∙ (~ ass ∙ (~ rid ∙ ((refl ⊗ lid ∘ (lid ∘ refl)) ⊗ lid ∙ (~ ass) ⊗ refl) ∘ refl) ∘ refl) ∘ refl ⟩ 
    (id ⊗ l ∘ α ∘ ρ ⊗ id) ⊗ l ∘ α ∘ ρ ⊗ id ∘ s
  ≐⟨ (~ lαρ) ⊗ refl ∘ refl ∘ refl ∘ refl ⟩ 
    id ⊗ l ∘ α ∘ ρ ⊗ id ∘ s
  ≐⟨ ~ (lαρ ∘ refl) ⟩ 
    id ∘ s
  ≐⟨ lid ⟩ 
    s
  qed≐

