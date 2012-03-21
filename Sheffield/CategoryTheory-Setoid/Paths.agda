module Sheffield.CategoryTheory-Setoid.Paths where

open import Level

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors

module paths {ℓ ℓ′ ℓ″ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) where

  open Category C renaming (_≈_ to _≈′_ ; _•_ to _•′_)

  data Path : obj → obj → Set (ℓ ⊔ ℓ′ ⊔ ℓ″) where
    _•_ : {x y z : obj} → homset y z → Path x y → Path x z
    finish : {x : obj} → Path x x

  composite : {x y : obj} → Path x y → homset x y
  composite (finish {x}) = id x
  composite (f • P) = f •′ composite P

  infix 4 _≈_
  _≈_  : {x y : obj} (P Q : Path x y) → Set ℓ″
  P ≈ Q = composite P ≈′ composite Q

  infixr 5 _++_
  _++_ : {x y z : obj} → Path y z → Path x y → Path x z
  finish ++ Q = Q
  (f • P) ++ Q = f • (P ++ Q)

  composite-++ : {x y z : obj} (Q : Path y z) (P : Path x y) → composite (Q ++ P) ≈′ composite Q •′ composite P
  composite-++ (f • Q) P = ≈-trans (•-cong ≈-refl (composite-++ Q P)) (≈-sym (assoc _ _ _))
  composite-++ finish P = ≈-sym (id-l _)

  ++-cong : {x y z : obj} {Q₁ Q₂ : Path y z} {P₁ P₂ : Path x y} → Q₁ ≈ Q₂ → P₁ ≈ P₂ → Q₁ ++ P₁ ≈ Q₂ ++ P₂
  ++-cong {_} {_} {_} {Q₁} {Q₂} {P₁} {P₂} eQ eP = begin
    composite (Q₁ ++ P₁)
      ≈⟨ composite-++ Q₁ P₁ ⟩
    composite Q₁ •′ composite P₁
      ≈⟨ •-cong eQ eP ⟩
    composite Q₂ •′ composite P₂
      ≈⟨ ≈-sym (composite-++ Q₂ P₂) ⟩
    composite (Q₂ ++ P₂) ∎ where open ≈-Reasoning _ _

  ++-assoc : {w x y z : obj} (R : Path y z) (Q : Path x y) (P : Path w x) → (R ++ Q) ++ P ≈ R ++ (Q ++ P)
  ++-assoc R Q P = begin
    composite ((R ++ Q) ++ P)
      ≈⟨ composite-++ (R ++ Q) P ⟩
    composite (R ++ Q) •′ composite P
      ≈⟨ •-cong (composite-++ R Q) ≈-refl ⟩
    (composite R •′ composite Q) •′ composite P
      ≈⟨ assoc _ _ _ ⟩
    composite R •′ (composite Q •′ composite P)
      ≈⟨ •-cong ≈-refl (≈-sym (composite-++ Q P)) ⟩
    composite R •′ (composite (Q ++ P))
      ≈⟨ ≈-sym (composite-++ R (Q ++ P)) ⟩
    composite (R ++ (Q ++ P)) ∎ where open ≈-Reasoning _ _

  pathCategory : Category {ℓ} {ℓ ⊔ ℓ′ ⊔ ℓ″} {ℓ″}
  pathCategory = record {
    obj = obj;
    hom = λ x y → record {
      Carrier = Path x y;
      _≈_ = _≈_;
      isEquivalence = record {
        refl = ≈-refl;
        sym = ≈-sym;
        trans = ≈-trans } };
    id = λ x → finish;
    compose = record {
      _⟨$⟩_ = λ Q → record {
        _⟨$⟩_ = _++_ Q;
        cong = λ {P₁} {P₂} eP → ++-cong {Q₁ = Q} {Q₂ = Q} {P₁ = P₁} {P₂ = P₂} ≈-refl eP };
      cong = λ {Q₁} {Q₂} eQ {P₁} {P₂} eP → ++-cong {Q₁ = Q₁} {Q₂ = Q₂} {P₁ = P₁} {P₂ = P₂} eQ eP };
    id-l = λ f → ≈-refl;
    id-r = λ f → ≈-trans (composite-++ f finish) (id-r _);
    assoc = ++-assoc }

  composition : Functor pathCategory C
  composition = record {
    obj = λ z → z ;
    hom = record {
      _⟨$⟩_ = composite ;
      cong = λ x → x } ;
    id = λ x → ≈-refl ;
    compose = λ g f → composite-++ g f }
