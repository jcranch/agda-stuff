module Paths where

open import Level
open import Relation.Binary.PropositionalEquality

open import Categories
open import Functors

module paths {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) where

  open Category C renaming (_•_ to _•′_)

  data Path : obj → obj → Set (ℓ ⊔ ℓ′)  where
    nil : (x : obj) → Path x x
    cons : {x y z : obj} → Path y z → hom x y → Path x z

  composite : {x y : obj} → Path x y → hom x y
  composite (nil x) = id x
  composite (cons P f) = composite P •′ f
  
  _≈_  : {x y : obj} (P Q : Path x y) → Set ℓ′
  P ≈ Q = composite P ≡ composite Q

  infix 5 [[_
  [[_ = λ {x} {y} → composite {x} {y}
  infix 6 _•_
  _•_ = λ {x} {y} {z} → cons {x} {y} {z}
  ]] = nil

  infixl 5 _++_
  _++_ : {x y z : obj} → Path y z → Path x y → Path x z
  P ++ (nil x) = P
  P ++ cons Q f = cons (P ++ Q) f

  composite-++ : {x y z : obj} (Q : Path y z) (P : Path x y) → composite (Q ++ P) ≡ composite Q •′ composite P
  composite-++ Q (nil x) = sym (id-r (composite Q))
  composite-++ Q (cons P f) = trans (cong (λ α → α •′ f) (composite-++ Q P)) (sym (assoc (composite Q) (composite P) f))

  infixl 4 _≈_
  ≈-cong : {x x′ y′ y : obj} {R : Path y′ y} {Q₁ Q₂ : Path x′ y′} {P : Path x x′} → Q₁ ≈ Q₂ → R ++ Q₁ ++ P ≈ R ++ Q₂ ++ P
  ≈-cong {_} {_} {_} {_} {R} {Q₁} {Q₂} {P} e = begin
    composite (R ++ Q₁ ++ P)
      ≡⟨ composite-++ (R ++ Q₁) P ⟩
    composite (R ++ Q₁) •′ composite P
      ≡⟨ cong (λ x → x •′ composite P) (composite-++ R Q₁) ⟩
    composite R •′ composite Q₁ •′ composite P
      ≡⟨ cong (λ x → composite R •′ x •′ composite P) e ⟩
    composite R •′ composite Q₂ •′ composite P
      ≡⟨ cong (λ x → x •′ composite P) (sym (composite-++ R Q₂)) ⟩
    composite (R ++ Q₂) •′ composite P
      ≡⟨ sym (composite-++ (R ++ Q₂) P) ⟩
    composite (R ++ Q₂ ++ P) ∎ where open ≡-Reasoning

  pathCategory : Category {ℓ} {ℓ ⊔ ℓ′}
  pathCategory = makeCat obj Path nil _++_ id-l′ id-r′ assoc′ where
    id-l′ : {x y : obj} (f : Path x y) → nil y ++ f ≡ f
    id-l′ (nil x) = refl
    id-l′ (cons P f) = cong (λ a → cons a f) (id-l′ P)

    id-r′ : {x y : obj} (f : Path x y) → f ++ nil x ≡ f
    id-r′ f = refl

    assoc′ : {w x y z : obj} (h : Path y z) (g : Path x y) (f : Path w x) → h ++ (g ++ f) ≡ (h ++ g) ++ f
    assoc′ R Q (nil x) = refl
    assoc′ R Q (cons P f) = cong (λ P' → cons P' f) (assoc′ R Q P)

  composition : Functor pathCategory C
  composition = makeFunctor (λ z → z) composite (λ _ → refl) composite-++

open paths

