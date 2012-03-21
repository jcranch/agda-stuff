module Sheffield.CategoryTheory-Setoid.SetoidFunction where

open import Function.Equality
open import Level
open import Relation.Binary


setoid-lift : {c c′ ℓ ℓ′ : Level} → Setoid c ℓ → Setoid (c ⊔ c′) (ℓ ⊔ ℓ′)
setoid-lift {c} {c′} {ℓ} {ℓ′} S = record {
  Carrier = Lift {c} {c′} (Setoid.Carrier S);
  _≈_ = λ x y → Lift {ℓ} {ℓ′} (Setoid._≈_ S (Lift.lower x) (Lift.lower y));
  isEquivalence = record {
    refl = λ {x} → lift (Setoid.refl S);
    sym = λ {x} {y} r → lift (Setoid.sym S (Lift.lower r));
    trans = λ {x} {y} {z} r s → lift (Setoid.trans S (Lift.lower r) (Lift.lower s)) } }


Γ = λ {x} {y} → Setoid.Carrier {x} {y}


flip : {c₁ ℓ₁ c₂ ℓ₂ c₃ ℓ₃ : Level}
  {A : Setoid c₁ ℓ₁} {B : Setoid c₂ ℓ₂} {C : Setoid c₃ ℓ₃} →
  (A ⇨ B ⇨ C) ⟶ (B ⇨ A ⇨ C)
flip {A = A} {B} {C} = record {
  _⟨$⟩_ = λ f → record {
    _⟨$⟩_ = λ b → record {
      _⟨$⟩_ = λ a → f ⟨$⟩ a ⟨$⟩ b ;
      cong = λ {a₁} {a₂} a₁≈a₂ → cong f a₁≈a₂ (Setoid.refl B) } ;
    cong = λ {b₁} {b₂} b₁≈b₂ {a₁} {a₂} a₁≈a₂ → cong f a₁≈a₂ b₁≈b₂ } ; 
  cong = λ f₁≈f₂ e e′ → f₁≈f₂ e′ e }


data ⊤ {ℓ : Level} : Set ℓ where
  tt : ⊤


indiscreteSetoid : {ℓ ℓ′ : Level} → Set ℓ → Setoid ℓ ℓ′
indiscreteSetoid A = record {
  Carrier = A;
  _≈_ = λ _ _ → ⊤;
  isEquivalence = record {
    refl = λ {_} → tt;
    sym = λ _ → tt;
    trans = λ _ _ → tt } }