module Sheffield.SimplicialSets.Simplicial where

open import Data.Fin hiding (zero)
open import Data.Nat hiding (_≤_ ; zero ; _⊔_)
open import Function renaming (id to f-id)
open import Level
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors.Category



module ordered-maps where

  IsOrdered : {m n : ℕ} → (Fin m → Fin n) → Set zero
  IsOrdered {m} {n} f = (i j : Fin m) → i ≤ j → f i ≤ f j

  record Ordered (m n : ℕ) : Set zero where
    constructor ord
    field
      map : Fin m → Fin n
      isOrdered : IsOrdered map

  _≈_ : {m n : ℕ} → Ordered m n → Ordered m n → Set zero
  _≈_ {m} (ord f f₀) (ord g g₀) = (i : Fin m) → f i ≡ g i

  id : {n : ℕ} → Ordered n n
  id {n} = ord f-id (λ _ _ → f-id)

  compose : {l m n : ℕ} → Ordered m n → Ordered l m → Ordered l n
  compose (ord g g₀) (ord f f₀) = ord (g ∘ f) (λ i j e → g₀ (f i) (f j) (f₀ i j e))

  compose-≈ : {l m n : ℕ} (g₁ g₂ : Ordered m n) (f₁ f₂ : Ordered l m) → g₁ ≈ g₂ → f₁ ≈ f₂ → compose g₁ f₁ ≈ compose g₂ f₂
  compose-≈ g₁ g₂ f₁ f₂ eg ef i = trans (cong (Ordered.map g₁) (ef i)) (eg (Ordered.map f₂ i))

open ordered-maps



Δ : Category {zero} {zero} {zero}
Δ = record {
  obj = ℕ ;
  hom = λ m n → record {
    Carrier = Ordered m n;
    _≈_ = _≈_;
    isEquivalence = record {
      refl = λ _ → refl;
      sym = λ e x → sym (e x);
      trans = λ e₁ e₂ x → trans (e₁ x) (e₂ x) } } ;
  id = λ n → ord (λ z → z) (λ _ _ z → z) ;
  compose = record {
    _⟨$⟩_ = λ g → record {
      _⟨$⟩_ = compose g;
      cong = λ {f₁} {f₂} e → compose-≈ g g f₁ f₂ (λ _ → refl) e } ;
    cong = λ {g₁} {g₂} eg {f₁} {f₂} ef → compose-≈ g₁ g₂ f₁ f₂ eg ef } ;
  id-l = λ _ _ → refl ;
  id-r = λ _ _ → refl ;
  assoc = λ _ _ _ _ → refl }



simplicial : {ℓ ℓ′ ℓ″ : Level} → Category {ℓ} {ℓ′} {ℓ″} → Category {ℓ ⊔ ℓ′ ⊔ ℓ″} {ℓ ⊔ ℓ′ ⊔ ℓ″} {ℓ″}
simplicial C = Functors (opposite Δ) C