module Sheffield.CategoryTheory-Setoid.SetoidProduct where

open import Data.Product renaming (_×_ to _✶_ ; proj₁ to proj′₁ ; proj₂ to proj′₂)
open import Function.Equality
open import Level
open import Relation.Binary


module products-of-equivalences {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {_≈₁_ : Rel A ℓ′₁} {_≈₂_ : Rel B ℓ′₂} (e₁ : IsEquivalence _≈₁_) (e₂ : IsEquivalence _≈₂_) where

  _≈_ : Rel (A ✶ B) (ℓ′₁ ⊔ ℓ′₂)
  _≈_ (a , b) (c , d) = a ≈₁ c ✶ b ≈₂ d

  refl : {x : A ✶ B} → x ≈ x
  refl {a , b} = IsEquivalence.refl e₁ , IsEquivalence.refl e₂

  sym : {x y : A ✶ B} → x ≈ y → y ≈ x
  sym (r₁ , r₂) = IsEquivalence.sym e₁ r₁ , IsEquivalence.sym e₂ r₂

  trans : {x y z : A ✶ B} → x ≈ y → y ≈ z → x ≈ z
  trans (r₁ , r₂) (s₁ , s₂) = IsEquivalence.trans e₁ r₁ s₁ , IsEquivalence.trans e₂ r₂ s₂

  isEquivalence : IsEquivalence _≈_
  isEquivalence = record {
    refl = refl ;
    sym = sym ;
    trans = trans }


infixl 7 _×_
_×_ : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level} → Setoid ℓ₁ ℓ′₁ → Setoid ℓ₂ ℓ′₂ → Setoid (ℓ₁ ⊔ ℓ₂) (ℓ′₁ ⊔ ℓ′₂)
S × T = record {
  Carrier = Setoid.Carrier S ✶ Setoid.Carrier T ;
  _≈_ = _≈_ ;
  isEquivalence = isEquivalence } where
  open products-of-equivalences (Setoid.isEquivalence S) (Setoid.isEquivalence T)


proj₁ : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level} {S : Setoid ℓ₁ ℓ′₁} {T : Setoid ℓ₂ ℓ′₂} → S × T ⟶ S
proj₁ = record {
  _⟨$⟩_ = proj′₁ ;
  cong = proj′₁ }


proj₂ : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level} {S : Setoid ℓ₁ ℓ′₁} {T : Setoid ℓ₂ ℓ′₂} → S × T ⟶ T
proj₂ = record {
  _⟨$⟩_ = proj′₂ ;
  cong = proj′₂ }


infixl 5 _⊕_
_⊕_ : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ ℓ₄ ℓ′₄ : Level}
  {S₁ : Setoid ℓ₁ ℓ′₁} {T₁ : Setoid ℓ₂ ℓ′₂}
  {S₂ : Setoid ℓ₃ ℓ′₃} {T₂ : Setoid ℓ₄ ℓ′₄} →
  S₁ ⟶ S₂ → T₁ ⟶ T₂ → S₁ × T₁ ⟶ S₂ × T₂
f ⊕ g = record {
  _⟨$⟩_ = λ x → f ⟨$⟩ (proj′₁ x) , g ⟨$⟩ (proj′₂ x) ;
  cong = λ x → cong f (proj′₁ x) , cong g (proj′₂ x) }
