module UniversalProperty where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Fsk
open import Utilities

-- a useful lemmata about equality
subst₂subst₂ : {X Y : Set} (P : X → Y → Set)
  → {x x' x'' : X} {y y' y'' : Y}
  → (p : x ≡ x') (p' : x' ≡ x'')
  → (q : y ≡ y') (q' : y' ≡ y'')
  → (z : P x y)
  → subst₂ P (trans p p') (trans q q') z
           ≡ subst₂ P p' q' (subst₂ P p q z)
subst₂subst₂ P refl refl refl refl z = refl

-- =======================================================================

-- Fsk(At) is the free skew monoidal category on At.

-- =======================================================================

-- the type of skew monoidal categories.

record SymSkMonCat : Set₁ where
  field
-- -- objects  
    Obj : Set
    𝕀 : Obj
    M₀ : Obj → Obj → Obj

-- -- morphisms
    Hom : Obj → Obj → Set
    Id : {B : Obj} → Hom B B
    Comp : {D B C : Obj} → Hom B C → Hom D B → Hom D C
    M₁ : {E B C D : Obj} → Hom E B → Hom C D → Hom (M₀ E C) (M₀ B D)
    L : {B : Obj} → Hom (M₀ 𝕀 B) B
    R : {B : Obj} → Hom B (M₀ B 𝕀)
    A : {D B C : Obj} → Hom (M₀ (M₀ D B) C) (M₀ D (M₀ B C))
    S : {D B C : Obj} → Hom (M₀ (M₀ D B) C) (M₀ (M₀ D C) B)

-- -- equalities
    Eq : {A B : Obj} → Hom A B → Hom A B → Set
    Refl : {C B : Obj} {f : Hom C B} → Eq f f
    Sym : {C B : Obj} {f g : Hom C B} → Eq f g → Eq g f
    Trans : {C B : Obj} {f g h : Hom C B} → Eq f g → Eq g h → Eq f h
    CompEq : {D B C : Obj} {f g : Hom B C} {h k : Hom D B} →
                           Eq f g → Eq h k → Eq (Comp f h) (Comp g k)
    M₁Eq : {E B C D : Obj} {f g : Hom E C} {h k : Hom B D} →
                           Eq f g → Eq h k → Eq (M₁ f h) (M₁ g k)
    Lid : {C B : Obj} {f : Hom C B} → Eq (Comp Id f) f
    Rid : {C B : Obj} {f : Hom C B} → Eq f (Comp f Id)
    Ass : {E B C D : Obj} {f : Hom C D} {g : Hom B C} {h : Hom E B}
         → Eq (Comp (Comp f g) h) (Comp f (Comp g h))
    fM₁Id : {C B : Obj} → Eq (M₁ (Id {C}) (Id {B})) Id
    fM₁Comp : {G B C D E F : Obj} {f : Hom G C} {g : Hom B D} {h : Hom C E} {k : Hom D F} →  
                      Eq (M₁ (Comp h f) (Comp k g)) (Comp (M₁ h k) (M₁ f g))
    nL : {B C : Obj} {f : Hom B C} → Eq (Comp L (M₁ Id f)) (Comp f L)
    nR : {B C : Obj} {f : Hom B C} → Eq (Comp R f) (Comp (M₁ f Id) R)
    nA : {G B C D E F : Obj} {f : Hom G D} {g : Hom B E} {h : Hom C F} → 
                         Eq (Comp A (M₁ (M₁ f g) h)) (Comp (M₁ f (M₁ g h)) A)
    nS : {G B C D E F : Obj} {f : Hom G D} {g : Hom B E} {h : Hom C F} → 
                         Eq (Comp S (M₁ (M₁ f g) h)) (Comp (M₁ (M₁ f h) g) S)
    LR : Eq (Comp L R) Id 
    LAR : {B C : Obj} → Eq Id (Comp (Comp (M₁ (Id {B}) L) A) (M₁ R (Id {C})))
    LA :  {B C : Obj} → Eq (Comp L A) (M₁ (L {B}) (Id {C}))
    AR : {B C : Obj} → Eq (Comp A R) (M₁ (Id {B}) (R {C}))
    AAA : {E B C D : Obj} → 
      Eq (Comp A A) (Comp (M₁ (Id {E}) (A {B}{C}{D})) (Comp A (M₁ A Id)))
    SSS : {E B C D : Obj} → 
      Eq (Comp (Comp (M₁ S Id) S) (M₁ S Id)) (Comp (Comp S (M₁ S Id)) (S {M₀ E B}{C}{D}))
    SA1 : {E B C D : Obj} →
      Eq (Comp S (A {M₀ E B}{C}{D})) (Comp (Comp (M₁ A Id) S) (M₁ S Id))
    SA2 : {E B C D : Obj} →
      Eq (Comp S (M₁ A Id)) (Comp (Comp A (M₁ S Id)) (S {M₀ E B}{C}{D}))
    SA3 : {E B C D : Obj} →
      Eq (Comp (Comp A (M₁ A Id)) (S {M₀ E B}{C}{D})) (Comp (Comp (M₁ Id S) A) (M₁ A Id))
    SS : {E B C : Obj} →
      Eq (Comp S S) (Id {M₀ (M₀ E B) C})

open SymSkMonCat


-- the categorical calculus defines a symmetryc skew monoidal category

Fsk : SymSkMonCat
Fsk = record {
    Obj = Fma ;
    Hom = _⇒_ ; 
    Eq = _≐_ ;     
    𝕀 = I ; 
    M₀ = _⊗_ ;     
    Id = id ; 
    Comp = _∘_ ;
    M₁ = _⊗_ ; 
    L = l ;
    R = ρ ; 
    A = α ;
    S = s ;
    Refl = refl ;
    Sym = ~_  ; 
    Trans = _∙_ ;
    CompEq = _∘_ ;
    M₁Eq = _⊗_ ;
    Lid = lid ;
    Rid = rid ;
    Ass = ass ; 
    fM₁Id = f⊗id ; 
    fM₁Comp = f⊗∘ ;
    nL = nl ; 
    nR = nρ ; 
    nA = nα ;
    nS = ns ;
    LR = lρ ; 
    LAR = lαρ ; 
    LA = lα ; 
    AR = αρ ; 
    AAA = ααα ;
    SSS = sss ;
    SA1 = sα1 ;
    SA2 = sα2 ;
    SA3 = sα3 ;
    SS = ss
    }


-- =======================================================================

-- the type of strict symm. monoidal functors.

record SymMonFun (ℂ 𝔻 : SymSkMonCat) : Set₁ where
  field
-- -- action on objects, morphisms and equalities  
    F₀ : Obj ℂ → Obj 𝔻
    F₁ : ∀{B C} → Hom ℂ B C → Hom 𝔻 (F₀ B) (F₀ C)
    FEq : ∀{B C} {f g : Hom ℂ B C} → Eq ℂ f g → Eq 𝔻 (F₁ f) (F₁ g)
-- -- functor laws    
    FId : ∀{B} → Eq 𝔻 (F₁ (Id ℂ {B})) (Id 𝔻)
    FComp : ∀{B C D} {g : Hom ℂ C D} {f : Hom ℂ B C} →
           Eq 𝔻 (F₁ (Comp ℂ g f)) (Comp 𝔻 (F₁ g) (F₁ f))
-- -- monoidal functor laws         
    F𝕀 : F₀ (𝕀 ℂ) ≡ 𝕀 𝔻
    FM₀ : ∀{B C} → F₀ (M₀ ℂ B C) ≡ M₀ 𝔻 (F₀ B) (F₀ C)
    FM₁ : ∀{E B C D} {f : Hom ℂ E B} {g : Hom ℂ C D}
      → Eq 𝔻 (subst₂ (Hom 𝔻) FM₀ FM₀ (F₁ (M₁ ℂ f g)))
               (M₁ 𝔻 (F₁ f) (F₁ g))
    FL : ∀{B}
      → Eq 𝔻 (subst₂ (Hom 𝔻) (trans FM₀ (cong (λ x → M₀ 𝔻 x (F₀ B)) F𝕀))
                                refl
                                (F₁ (L ℂ {B})))
              (L 𝔻)
    FR : ∀{B}
      → Eq 𝔻 (subst₂ (Hom 𝔻) refl
                                (trans FM₀ (cong (M₀ 𝔻 (F₀ B)) F𝕀))
                                (F₁ (R ℂ {B})))
              (R 𝔻)
    FA : ∀{E B C}
      → Eq 𝔻 (subst₂ (Hom 𝔻) (trans FM₀ (cong (λ x → M₀ 𝔻 x (F₀ C)) FM₀))
                               (trans FM₀ (cong (M₀ 𝔻 (F₀ E)) FM₀))
                               (F₁ (A ℂ {E}{B}{C})))
               (A 𝔻) 
    FS : ∀{E B C}
      → Eq 𝔻 (subst₂ (Hom 𝔻) (trans FM₀ (cong (λ x → M₀ 𝔻 x (F₀ C)) FM₀))
                               (trans FM₀ ((cong (λ x → M₀ 𝔻 x (F₀ B)) FM₀)))
                               (F₁ (S ℂ {E}{B}{C})))
               (S 𝔻) 
open SymMonFun   

-- equality of strict symm. monoidal functors
record EqFun {ℂ 𝔻 : SymSkMonCat} (F G : SymMonFun ℂ 𝔻) : Set where
  field
    Eq₀ : ∀ B → F₀ F B ≡ F₀ G B
    Eq₁ : ∀{B C} (f : ℂ .Hom B C)
      → Eq 𝔻 (subst₂ (Hom 𝔻) (Eq₀ B) (Eq₀ C) (F₁ F f))
               (F₁ G f)
open EqFun

-- existence of a strict symm. monoidal functor between Fsk and
-- any other symm. skew monoidal category 𝔻 with γ : At → 𝔻
module Exists (𝔻 : SymSkMonCat) (γ : At → Obj 𝔻) where

  𝔽₀ : Fma → Obj 𝔻
  𝔽₀ (` X) = γ X
  𝔽₀ I = 𝕀 𝔻
  𝔽₀ (B ⊗ C) = M₀ 𝔻 (𝔽₀ B) (𝔽₀ C)

  𝔽₁ : {B C : Fma} → B ⇒ C → Hom 𝔻 (𝔽₀ B) (𝔽₀ C)
  𝔽₁ id = Id 𝔻
  𝔽₁ (f ∘ f₁) = Comp 𝔻 (𝔽₁ f) (𝔽₁ f₁)
  𝔽₁ (f ⊗ f₁) = M₁ 𝔻 (𝔽₁ f) (𝔽₁ f₁)
  𝔽₁ l = L 𝔻
  𝔽₁ ρ = R 𝔻
  𝔽₁ α = A 𝔻
  𝔽₁ s = S 𝔻

  𝔽Eq : {B C : Fma} {f g : B ⇒ C} →
        f ≐ g → Eq 𝔻 (𝔽₁ f) (𝔽₁ g)
  𝔽Eq refl = Refl 𝔻
  𝔽Eq (~ p) = Sym 𝔻 (𝔽Eq p)
  𝔽Eq (p ∙ p₁) = Trans 𝔻 (𝔽Eq p) (𝔽Eq p₁)
  𝔽Eq (p ∘ p₁) = CompEq 𝔻 (𝔽Eq p) (𝔽Eq p₁)
  𝔽Eq (p ⊗ p₁) = M₁Eq 𝔻 (𝔽Eq p) (𝔽Eq p₁)
  𝔽Eq lid = Lid 𝔻
  𝔽Eq rid = Rid 𝔻
  𝔽Eq ass = Ass 𝔻
  𝔽Eq f⊗id = fM₁Id 𝔻
  𝔽Eq f⊗∘ = fM₁Comp 𝔻
  𝔽Eq nl = nL 𝔻
  𝔽Eq nρ = nR 𝔻
  𝔽Eq nα = nA 𝔻
  𝔽Eq ns = nS 𝔻
  𝔽Eq lρ = LR 𝔻
  𝔽Eq lαρ = LAR 𝔻
  𝔽Eq lα = LA 𝔻
  𝔽Eq αρ = AR 𝔻
  𝔽Eq ααα = AAA 𝔻
  𝔽Eq sss = SSS 𝔻
  𝔽Eq sα1 = SA1 𝔻
  𝔽Eq sα2 = SA2 𝔻
  𝔽Eq sα3 = SA3 𝔻
  𝔽Eq ss = SS 𝔻

  𝔽 : SymMonFun Fsk 𝔻
  𝔽 = record
        { F₀ = 𝔽₀
        ; F₁ = 𝔽₁
        ; FEq = 𝔽Eq
        ; FId = Refl 𝔻
        ; FComp = Refl 𝔻
        ; F𝕀 = refl
        ; FM₀ = refl
        ; FM₁ = Refl 𝔻
        ; FL = Refl 𝔻
        ; FR = Refl 𝔻
        ; FA = Refl 𝔻
        ; FS = Refl 𝔻
        }


-- uniqueness of such strict symm. monoidal functor
module Unique (𝔻 : SymSkMonCat)
              (γ : At → Obj 𝔻)
              (G : SymMonFun Fsk 𝔻)
              (p : {X : At} → F₀ G (` X) ≡ γ X)
              where

  open Exists 𝔻 γ

  EqRefl : ∀{S B} {f g : Hom 𝔻 S B}
    → f ≡ g  → Eq 𝔻 f g
  EqRefl refl = Refl 𝔻

  EqSubst : ∀{S S' B B'} {f g : Hom 𝔻 S B}
    → (p : S ≡ S') (q : B ≡ B')
    → Eq 𝔻 f g 
    → Eq 𝔻 (subst₂ (Hom 𝔻) p q f) (subst₂ (Hom 𝔻) p q g)
  EqSubst refl refl r = r

  EqSubst₂ : ∀{S S' B B'} {f : Hom 𝔻 S B}
    → (p p' : S ≡ S') (q q' : B ≡ B')
    → Eq 𝔻 (subst₂ (Hom 𝔻) p q f) (subst₂ (Hom 𝔻) p' q' f)
  EqSubst₂ refl refl refl refl = Refl 𝔻

  EqSubstId : ∀{B B'} (q : B ≡ B')
    → Eq 𝔻 (subst₂ (Hom 𝔻) q q (Id 𝔻)) (Id 𝔻)
  EqSubstId refl = Refl 𝔻

  EqSubstComp : ∀{S S' B B' C C'} {f : Hom 𝔻 S B}{g : Hom 𝔻 B C}
    → (p : S ≡ S') (q : B ≡ B') (r : C ≡ C')
    → Eq 𝔻 (subst₂ (Hom 𝔻) p r (Comp 𝔻 g f))
            (Comp 𝔻 (subst₂ (Hom 𝔻) q r g)
                     (subst₂ (Hom 𝔻) p q f))
  EqSubstComp refl refl refl = Refl 𝔻

  EqSubstM₀ : ∀{A A' B B' C C' D D'} {f : Hom 𝔻 A B}{g : Hom 𝔻 C D}
    → (p : A ≡ A') (q : B ≡ B') (r : C ≡ C') (s : D ≡ D')
    → Eq 𝔻 (subst₂ (Hom 𝔻) (cong₂ (M₀ 𝔻) p r) (cong₂ (M₀ 𝔻) q s) (M₁ 𝔻 f g))
             (M₁ 𝔻 (subst₂ (Hom 𝔻) p q f) (subst₂ (Hom 𝔻) r s g))
  EqSubstM₀ refl refl refl refl = Refl 𝔻

  EqSubstL : ∀{B B'} (p : B ≡ B')
    → Eq 𝔻 (subst₂ (Hom 𝔻) (cong (M₀ 𝔻 (𝕀 𝔻)) p) p (L 𝔻)) (L 𝔻)
  EqSubstL refl = Refl 𝔻

  EqSubstR : ∀{B B'} (p : B ≡ B')
    → Eq 𝔻 (subst₂ (Hom 𝔻) p (cong (λ x → M₀ 𝔻 x (𝕀 𝔻)) p) (R 𝔻)) (R 𝔻)
  EqSubstR refl = Refl 𝔻

  EqSubstA : ∀{E E' B B' C C'} (p : E ≡ E') (q : B ≡ B') (r : C ≡ C')
    → Eq 𝔻 (subst₂ (Hom 𝔻) (cong₂ (M₀ 𝔻) (cong₂ (M₀ 𝔻) p q) r) (cong₂ (M₀ 𝔻) p (cong₂ (M₀ 𝔻) q r)) (A 𝔻)) (A 𝔻)
  EqSubstA refl refl refl = Refl 𝔻

  EqSubstS : ∀{E E' B B' C C'} (p : E ≡ E') (q : B ≡ B') (r : C ≡ C')
    → Eq 𝔻 (subst₂ (Hom 𝔻) (cong₂ (M₀ 𝔻) (cong₂ (M₀ 𝔻) p q) r) (cong₂ (M₀ 𝔻) (cong₂ (M₀ 𝔻) p r) q) (S 𝔻)) (S 𝔻)
  EqSubstS refl refl refl = Refl 𝔻

  𝔽Eq₀ : (B : Fma) → F₀ G B ≡ 𝔽₀ B
  𝔽Eq₀ (` X) = p
  𝔽Eq₀ I = F𝕀 G
  𝔽Eq₀ (B ⊗ C) = trans (FM₀ G) (cong₂ (M₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ C))

  𝔽Eq₁ : ∀{B C} (f : B ⇒ C)
    → Eq 𝔻 (subst₂ (Hom 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ C) (F₁ G f)) (𝔽₁ f)
  𝔽Eq₁ (id {B}) =
    Trans 𝔻 (EqSubst (𝔽Eq₀ B) (𝔽Eq₀ B) (FId G)) (EqSubstId (𝔽Eq₀ B))
  𝔽Eq₁ (_∘_ {S}{B}{C} f g) =
    Trans 𝔻 (Trans 𝔻 (EqSubst (𝔽Eq₀ S) (𝔽Eq₀ C) (FComp G))
                       (EqSubstComp (𝔽Eq₀ S) (𝔽Eq₀ B) (𝔽Eq₀ C)))
             (CompEq 𝔻 (𝔽Eq₁ f) (𝔽Eq₁ g))
  𝔽Eq₁ (_⊗_ {A}{B}{C}{D} f g) =
    Trans 𝔻 (Trans 𝔻 (Trans 𝔻 (subst (Eq 𝔻 _) (subst₂subst₂ (Hom 𝔻) (FM₀ G) r (FM₀ G) r' _)
                                                               (EqSubst₂ q (trans (FM₀ G) r) q' (trans (FM₀ G) r')))
                                 (EqSubst _ _ (FM₁ G)))
                       (EqSubstM₀ (𝔽Eq₀ A) (𝔽Eq₀ B) (𝔽Eq₀ C) (𝔽Eq₀ D)))
             (M₁Eq 𝔻 (𝔽Eq₁ f) (𝔽Eq₁ g))
    where
      q = trans (FM₀ G) (cong₂ (M₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ C))
      q' = trans (FM₀ G) (cong₂ (M₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ D))
      r = cong₂ (M₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ C)
      r' = cong₂ (M₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ D)             
  𝔽Eq₁ (l {B}) =
    Trans 𝔻 (EqRefl (trans (cong (λ z → subst₂ (Hom 𝔻) z (𝔽Eq₀ B) (F₁ G l)) uip)
                            (subst₂subst₂ (Hom 𝔻) _ (cong (M₀ 𝔻 (𝕀 𝔻)) (𝔽Eq₀ B)) _ (𝔽Eq₀ B) (F₁ G l))))
             (Trans 𝔻 (EqSubst _ _ (FL G))
                       (EqSubstL (𝔽Eq₀ B)))
  𝔽Eq₁ (ρ {B}) =
    Trans 𝔻 (EqRefl (trans (cong₂ (λ x y → subst₂ (Hom 𝔻) x y (F₁ G ρ)) uip uip)
                            (subst₂subst₂ (Hom 𝔻) _ (𝔽Eq₀ B) _ (cong (λ x → M₀ 𝔻 x (𝕀 𝔻)) (𝔽Eq₀ B)) (F₁ G ρ))))
             (Trans 𝔻 (EqSubst _ _ (FR G))
                       (EqSubstR (𝔽Eq₀ B)))
  𝔽Eq₁ (α {B}{C}{D}) =
    Trans 𝔻 (EqRefl (trans (cong₂ (λ x y → subst₂ (Hom 𝔻) x y (F₁ G α)) uip uip)
                            (subst₂subst₂ (Hom 𝔻) _ (cong₂ (M₀ 𝔻) (cong₂ (M₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ C)) (𝔽Eq₀ D)) _ (cong₂ (M₀ 𝔻) (𝔽Eq₀ B) (cong₂ (M₀ 𝔻) (𝔽Eq₀ C) (𝔽Eq₀ D))) (F₁ G α))))
             (Trans 𝔻 (EqSubst _ _ (FA G))
                       (EqSubstA (𝔽Eq₀ B) (𝔽Eq₀ C) (𝔽Eq₀ D)))
  𝔽Eq₁ (s {B}{C}{D}) =
    Trans 𝔻 (EqRefl (trans (cong₂ (λ x y → subst₂ (Hom 𝔻) x y (F₁ G s)) uip uip)
                            (subst₂subst₂ (Hom 𝔻) _ (cong₂ (M₀ 𝔻) (cong₂ (M₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ C)) (𝔽Eq₀ D)) _ (cong₂ (M₀ 𝔻) (cong₂ (M₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ D)) (𝔽Eq₀ C)) (F₁ G s))))
             (Trans 𝔻 (EqSubst _ _ (FS G))
                       (EqSubstS (𝔽Eq₀ B) (𝔽Eq₀ C) (𝔽Eq₀ D)))

  𝔽-uniq : EqFun G 𝔽
  𝔽-uniq = record { Eq₀ = 𝔽Eq₀ ; Eq₁ = 𝔽Eq₁ }


-- the predicate characterizing the free symm. skew monoidal category
record FreeSymSkMonCat (ℂ : SymSkMonCat) : Set₁ where
  field
    η : At → Obj ℂ
    F : ∀ 𝔻 (γ : At → Obj 𝔻) → SymMonFun ℂ 𝔻
    comm : ∀ 𝔻 γ {X : At} → F₀ (F 𝔻 γ) (η X) ≡ γ X
    uniq : ∀ 𝔻 γ (G : SymMonFun ℂ 𝔻) →
      ({X : At} → F₀ G (η X) ≡ γ X) → EqFun G (F 𝔻 γ)

-- Wrapping up: Fsk satisfies this universal property
Fsk-univ : FreeSymSkMonCat Fsk
Fsk-univ = record
  { η = `
  ; F = Exists.𝔽
  ; comm = λ _ _ → refl
  ; uniq = Unique.𝔽-uniq
  }


