module AbelianCategories.AbEnriched where

open import Algebra
open import Algebra.Structures
open import Data.Product using (proj₁ ; proj₂)
open import Function hiding (id)
open import Level
import Relation.Binary.EqReasoning
open import Relation.Binary.PropositionalEquality hiding (setoid ; sym)

open import Categories


module AdditiveNotation {c ℓ : Level} (A : CommutativeMonoid c ℓ) where
  open CommutativeMonoid A public renaming (_∙_ to _+_ ; ε to O)

module AdditiveNotation′ {c ℓ : Level} (A : AbelianGroup c ℓ) where
  open AbelianGroup A public renaming (_∙_ to _+_ ; _⁻¹ to −_ ; ε to O)


private
  ∣_∣ : {c ℓ : Level} → CommutativeMonoid c ℓ → Set c
  ∣_∣ = CommutativeMonoid.Carrier

  ∣_∣′ : {c ℓ : Level} → AbelianGroup c ℓ → Set c
  ∣_∣′ = AbelianGroup.Carrier


record IsBilinear {c₁ ℓ₁ c₂ ℓ₂ c ℓ : Level}
  {A₁ : CommutativeMonoid c₁ ℓ₁}
  {A₂ : CommutativeMonoid c₂ ℓ₂}
  {A  : CommutativeMonoid c  ℓ }
  (⟨_,_⟩ : ∣ A₁ ∣ → ∣ A₂ ∣ → ∣ A ∣) : Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂ ⊔ c ⊔ ℓ) where

  constructor makeBilinear

  open AdditiveNotation A₁ hiding (_≈_) renaming (_+_ to _+₁_ ; O to O₁)
  open AdditiveNotation A₂ hiding (_≈_) renaming (_+_ to _+₂_ ; O to O₂)
  open AdditiveNotation A

  field
    0-left : (y : ∣ A₂ ∣) → ⟨ O₁ , y ⟩ ≈ O
    0-right : (x : ∣ A₁ ∣) → ⟨ x , O₂ ⟩ ≈ O
    +-left : (x x′ : ∣ A₁ ∣) (y : ∣ A₂ ∣) → ⟨ x +₁ x′ , y ⟩ ≈ ⟨ x , y ⟩ + ⟨ x′ , y ⟩
    +-right : (x : ∣ A₁ ∣) (y y′ : ∣ A₂ ∣) → ⟨ x , y +₂ y′ ⟩ ≈ ⟨ x , y ⟩ + ⟨ x , y′ ⟩


-- a bilinear map A₁ x A₂ → A gives one A₂ x A₁ → A
flip-bilinear : {c₁ ℓ₁ c₂ ℓ₂ c ℓ : Level}
  {A₁ : CommutativeMonoid c₁ ℓ₁}
  {A₂ : CommutativeMonoid c₂ ℓ₂}
  {A  : CommutativeMonoid c  ℓ }
  {μ : ∣ A₁ ∣ → ∣ A₂ ∣ → ∣ A ∣} →
  IsBilinear {c₁} {ℓ₁} {c₂} {ℓ₂} {c} {ℓ} {A₁} {A₂} {A} μ →
  IsBilinear {c₂} {ℓ₂} {c₁} {ℓ₁} {c} {ℓ} {A₂} {A₁} {A} (flip μ)
flip-bilinear (makeBilinear 0-left 0-right +-left +-right) =
               makeBilinear 0-right 0-left (λ x x′ y → +-right y x x′) (λ x y y′ → +-left y y′ x)


{-
module left-minus-axiom {c₁ ℓ₁ c₂ ℓ₂ c ℓ : Level}
  {A₁ : AbelianGroup c₁ ℓ₁}
  {A₂ : CommutativeMonoid c₂ ℓ₂}
  {A  : AbelianGroup c ℓ }
  {⟨_,_⟩ : ∣ A₁ ∣′ → ∣ A₂ ∣ → ∣ A ∣′}
  (ib : IsBilinear {c₁} {ℓ₁} {c₂} {ℓ₂} {c} {ℓ} {AbelianGroup.commutativeMonoid A₁} {A₂} {AbelianGroup.commutativeMonoid A} ⟨_,_⟩) where

  open AdditiveNotation′ A₁ hiding (_≈_ ; setoid ; sym ; ∙-cong ; refl) renaming (_+_ to _+₁_ ; −_ to −₁_ ; O to O₁ ; identity to identity₁ ; inverse to inverse₁)
  open AdditiveNotation  A₂ hiding (_≈_ ; setoid ; sym ; ∙-cong ; refl) renaming (_+_ to _+₂_ ; O to O₂ ; identity to identity₂)
  open AdditiveNotation′ A

  −-left : (x : ∣ A₁ ∣′) (y : ∣ A₂ ∣) → ⟨ −₁ x , y ⟩ ≈ − ⟨ x , y ⟩
  −-left x y = begin
    ⟨ −₁ x , y ⟩
      ≈⟨ sym (proj₁ identity ⟨ −₁ x , y ⟩) ⟩
    O + ⟨ −₁ x , y ⟩
      ≈⟨ {!∙-cong ? refl!} ⟩ -- ? is built from "proj₁ inverse"
    ((− ⟨ x , y ⟩) + ⟨ x , y ⟩) + ⟨ −₁ x , y ⟩
      ≈⟨ {!!} ⟩
    (− ⟨ x , y ⟩) + (⟨ x , y ⟩ + ⟨ −₁ x , y ⟩)
      ≈⟨ {!!} ⟩
    (− ⟨ x , y ⟩) + ⟨ x +₁ (−₁ x) , y ⟩
      ≈⟨ {!!} ⟩
    (− ⟨ x , y ⟩) + ⟨ O₁ , y ⟩
      ≈⟨ {!!} ⟩
    (− ⟨ x , y ⟩) + O
      ≈⟨ {!!} ⟩
    − ⟨ x , y ⟩ ∎ where open Relation.Binary.EqReasoning setoid

open left-minus-axiom public
-}


-- similarly... or maybe using flip
-- −-right : (x : A₁) (y : A₂) → ⟨ x , −₂ y ⟩ ≡ − ⟨ x , y ⟩



record AbelianEnrichment {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) : Set (ℓ ⊔ ℓ′) where

  open Category C

  field
    _+_ : {x y : obj} → hom x y → hom x y → hom x y
    O : {x y : obj} → hom x y
    −_ : {x y : obj} → hom x y → hom x y
    isAbelianGroup : (x y : obj) → IsAbelianGroup _≡_ (_+_ {x} {y}) O −_

  HomAbelianGroup : (x y : obj) → AbelianGroup ℓ′ ℓ′
  HomAbelianGroup x y = record {
    Carrier = hom x y ;
    isAbelianGroup = isAbelianGroup x y
    }

  HomCommutativeMonoid : (x y : obj) → CommutativeMonoid ℓ′ ℓ′
  HomCommutativeMonoid x y = AbelianGroup.commutativeMonoid (HomAbelianGroup x y)

  field
    isBilinear : {x y z : obj} → IsBilinear {A₁ = HomCommutativeMonoid y z} {A₂ = HomCommutativeMonoid x y} {A = HomCommutativeMonoid x z} _•_


module endomorphisms-ring {ℓ ℓ′ : Level} {C : Category {ℓ} {ℓ′}} (E : AbelianEnrichment C) where

  open import Data.Product

  open Category C
  open AbelianEnrichment E

  endomorphismRing : (x : Category.obj C) → IsRing _≡_ _+_ _•_ −_ O (id x)
  endomorphismRing x = record {
    +-isAbelianGroup = AbelianEnrichment.isAbelianGroup E x x ;
    *-isMonoid = endomorphismMonoid {ℓ} {ℓ′} {C} x ;
    distrib = IsBilinear.+-right isBilinear ,′ (λ a b c → IsBilinear.+-left isBilinear b c a) }

open endomorphisms-ring public
