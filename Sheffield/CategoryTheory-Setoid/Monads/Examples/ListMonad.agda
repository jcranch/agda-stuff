module Sheffield.CategoryTheory-Setoid.Monads.Examples.ListMonad where

open import Data.List
open import Function.Equality
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Examples.Sets
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Monads
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.SetoidFunction


module list-setoids {ℓ ℓ′ : Level} (S : Setoid ℓ ℓ′) where

  open Setoid S

  infix 4 _≈ˡ_

  data _≈ˡ_ : Rel (List Carrier) (ℓ ⊔ ℓ′) where
    ≈ˡ-nil : [] ≈ˡ []
    ≈ˡ-cons : {h₁ h₂ : Carrier} {t₁ t₂ : List Carrier} → h₁ ≈ h₂ → t₁ ≈ˡ t₂ → (h₁ ∷ t₁) ≈ˡ (h₂ ∷ t₂)

  ≈ˡ-refl : {l : List Carrier} → l ≈ˡ l
  ≈ˡ-refl {[]} = ≈ˡ-nil
  ≈ˡ-refl {x ∷ xs} = ≈ˡ-cons refl ≈ˡ-refl

  ≈ˡ-sym : {l₁ l₂ : List Carrier} → l₁ ≈ˡ l₂ → l₂ ≈ˡ l₁
  ≈ˡ-sym ≈ˡ-nil = ≈ˡ-nil
  ≈ˡ-sym (≈ˡ-cons h t) = ≈ˡ-cons (sym h) (≈ˡ-sym t)

  ≈ˡ-trans : {l₁ l₂ l₃ : List Carrier} → l₁ ≈ˡ l₂ → l₂ ≈ˡ l₃ → l₁ ≈ˡ l₃
  ≈ˡ-trans ≈ˡ-nil ≈ˡ-nil = ≈ˡ-nil
  ≈ˡ-trans (≈ˡ-cons h′ t′) (≈ˡ-cons h t) = ≈ˡ-cons (trans h′ h) (≈ˡ-trans t′ t)

  ≈ˡ-map-id : (l : List Carrier) → map (λ x → x) l ≈ˡ l
  ≈ˡ-map-id [] = ≈ˡ-nil
  ≈ˡ-map-id (h ∷ t) = ≈ˡ-cons refl (≈ˡ-map-id t)

  -- left unit is obvious
  ≈ˡ-r-unit : (l : List Carrier) → (l ++ []) ≈ˡ l
  ≈ˡ-r-unit [] = ≈ˡ-nil
  ≈ˡ-r-unit (h ∷ t) = ≈ˡ-cons refl (≈ˡ-r-unit t)

  ≈ˡ-concat-single : {l₁ l₂ : List Carrier} → l₁ ≈ˡ l₂ → concat (map (λ x → x ∷ []) l₁) ≈ˡ l₂
  ≈ˡ-concat-single ≈ˡ-nil = ≈ˡ-nil
  ≈ˡ-concat-single (≈ˡ-cons h t) = ≈ˡ-cons h (≈ˡ-concat-single t)

  listSetoid : Setoid ℓ (ℓ ⊔ ℓ′)
  listSetoid = record {
    Carrier = List Carrier ;
    _≈_ = _≈ˡ_ ;
    isEquivalence = record {
      refl = ≈ˡ-refl;
      sym = ≈ˡ-sym;
      trans = ≈ˡ-trans } }

open list-setoids public


private
  ≈ˡ-map : {ℓ ℓ′ : Level} {S₁ S₂ : Setoid ℓ ℓ′} (f : S₁ ⟶ S₂) {A B : List (Setoid.Carrier S₁)} → _≈ˡ_ S₁ A B → _≈ˡ_ S₂ (map (_⟨$⟩_ f) A) (map (_⟨$⟩_ f) B)
  ≈ˡ-map f ≈ˡ-nil = ≈ˡ-nil
  ≈ˡ-map f (≈ˡ-cons h≈ t≈) = ≈ˡ-cons (cong f h≈) (≈ˡ-map f t≈)

  ≈ˡ-map′ : {ℓ ℓ′ : Level} {S₁ S₂ : Setoid ℓ ℓ′} (f g : S₁ ⟶ S₂) {A B : List (Setoid.Carrier S₁)} → Setoid._≈_ (S₁ ⇨ S₂) f g → _≈ˡ_ S₁ A B → _≈ˡ_ S₂ (map (_⟨$⟩_ f) A) (map (_⟨$⟩_ g) B)
  ≈ˡ-map′ _ _ f≈g ≈ˡ-nil = ≈ˡ-nil
  ≈ˡ-map′ f g f≈g (≈ˡ-cons h≈ t≈) = ≈ˡ-cons (f≈g h≈) (≈ˡ-map′ f g f≈g t≈)

  ≈ˡ-map-compose : {ℓ ℓ′ : Level} {S₁ S₂ S₃ : Setoid ℓ ℓ′} (g : S₂ ⟶ S₃) (f : S₁ ⟶ S₂) {l₁ l₂ : List (Setoid.Carrier S₁)} → _≈ˡ_ S₁ l₁ l₂ → _≈ˡ_ S₃ (map (_⟨$⟩_ (g ∘ f)) l₁) (map (_⟨$⟩_ g) (map (_⟨$⟩_ f) l₂))
  ≈ˡ-map-compose g f ≈ˡ-nil = ≈ˡ-nil
  ≈ˡ-map-compose g f (≈ˡ-cons h≈ t≈) = ≈ˡ-cons (cong g (cong f h≈)) (≈ˡ-map-compose g f t≈)

  ≈ˡ-concat : {ℓ ℓ′ : Level} {S : Setoid ℓ ℓ′} {ll₁ ll₂ : List (List (Setoid.Carrier S))} → _≈ˡ_ (listSetoid S) ll₁ ll₂ → _≈ˡ_ S (concat ll₁) (concat ll₂)
  ≈ˡ-concat ≈ˡ-nil = ≈ˡ-nil
  ≈ˡ-concat (≈ˡ-cons ≈ˡ-nil tl) = ≈ˡ-concat tl
  ≈ˡ-concat (≈ˡ-cons (≈ˡ-cons h t) tl) = ≈ˡ-cons h (≈ˡ-concat (≈ˡ-cons t tl))

  ≈ˡ-concat-map : {ℓ ℓ′ : Level} {S₁ S₂ : Setoid ℓ ℓ′} (f : S₁ ⟶ S₂) {ll₁ ll₂ : List (List (Setoid.Carrier S₁))} → _≈ˡ_ (listSetoid S₁) ll₁ ll₂ → _≈ˡ_ S₂ (concat (map (map (_⟨$⟩_ f)) ll₁)) (map (_⟨$⟩_ f) (concat ll₂))
  ≈ˡ-concat-map f ≈ˡ-nil = ≈ˡ-nil
  ≈ˡ-concat-map f (≈ˡ-cons ≈ˡ-nil tl) = ≈ˡ-concat-map f tl
  ≈ˡ-concat-map f (≈ˡ-cons (≈ˡ-cons h t) tl) = ≈ˡ-cons (cong f h) (≈ˡ-concat-map f (≈ˡ-cons t tl))

  ≈ˡ-concat-assoc : {ℓ ℓ′ : Level} {S : Setoid ℓ ℓ′} {L₁ L₂ : List (List (List (Setoid.Carrier S)))} → _≈ˡ_ (listSetoid (listSetoid S)) L₁ L₂ → _≈ˡ_ S (concat (map concat L₁)) (concat (concat (map (map (λ x → x)) L₂)))
  ≈ˡ-concat-assoc ≈ˡ-nil = ≈ˡ-nil
  ≈ˡ-concat-assoc (≈ˡ-cons ≈ˡ-nil ttt) = ≈ˡ-concat-assoc ttt
  ≈ˡ-concat-assoc (≈ˡ-cons (≈ˡ-cons ≈ˡ-nil tt) ttt) = ≈ˡ-concat-assoc (≈ˡ-cons tt ttt)
  ≈ˡ-concat-assoc (≈ˡ-cons (≈ˡ-cons (≈ˡ-cons h t) tt) ttt) = ≈ˡ-cons h (≈ˡ-concat-assoc (≈ˡ-cons (≈ˡ-cons t tt) ttt))




listMonad : {ℓ : Level} → Monad (Setoids {ℓ} {ℓ})
listMonad = record {
  T = record {
    obj = listSetoid ;
    hom = λ {x} {y} → record {
      _⟨$⟩_ = λ F → record {
        _⟨$⟩_ = map (_⟨$⟩_ F);
        cong = ≈ˡ-map F } ;
      cong = λ {f₁} {f₂} f≈ e≈ → ≈ˡ-map′ f₁ f₂ f≈ e≈ } ;
    id = λ S {ℓ₁} {ℓ₂} e → ≈ˡ-trans S (≈ˡ-map-id S ℓ₁) e ;
    compose = λ G F e → ≈ˡ-map-compose G F e } ;
  μ = record {
    component = λ S → record {
      _⟨$⟩_ = concat ;
      cong = ≈ˡ-concat } ;
    naturality = λ {S₁} {S₂} f {ll₁} {ll₂} r → ≈ˡ-concat-map f r } ;
  ε = record {
    component = λ S → record {
      _⟨$⟩_ = λ x → x ∷ [] ;
      cong = λ e → ≈ˡ-cons e ≈ˡ-nil } ;
    naturality = λ {S₁} {S₂} f {x} {y} r → ≈ˡ-cons (cong f r) ≈ˡ-nil } ;
  unit-l = λ S {l₁} e → ≈ˡ-trans S (≈ˡ-r-unit S l₁) e ;
  unit-r = λ S {l₁} {l₂} e → ≈ˡ-concat-single S e ;
  assoc = λ S {L₁} {L₂} r → ≈ˡ-concat-assoc r }