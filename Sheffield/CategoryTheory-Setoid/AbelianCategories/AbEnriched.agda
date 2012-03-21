module Sheffield.CategoryTheory-Setoid.AbelianCategories.AbEnriched where

open import Algebra
open import Algebra.Structures
import Algebra.FunctionProperties as Props
open import Data.Product using (_,′_ ; proj₁ ; proj₂)
open import Function.Equality hiding (id)
open import Level
open import Relation.Binary
import Relation.Binary.EqReasoning as EqReasoning

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.SetoidFunction



module AdditiveNotation {c ℓ : Level} (A : CommutativeMonoid c ℓ) where
  open CommutativeMonoid A public renaming (_∙_ to _+_ ; ε to O)

module AdditiveNotation′ {c ℓ : Level} (A : AbelianGroup c ℓ) where
  open AbelianGroup A public renaming (_∙_ to _+_ ; _⁻¹ to −_ ; ε to O)



module pairing-context {c₁ ℓ₁ c₂ ℓ₂ c ℓ : Level}
  (A₁ : CommutativeMonoid c₁ ℓ₁)
  (A₂ : CommutativeMonoid c₂ ℓ₂)
  (A  : CommutativeMonoid c  ℓ ) where

  private
    ∣A₁∣ = CommutativeMonoid.setoid A₁
    ∣A₂∣ = CommutativeMonoid.setoid A₂
    ∣A∣  = CommutativeMonoid.setoid A

  Pairing = ∣A₁∣ ⟶ ∣A₂∣ ⇨ ∣A∣

  record IsBilinear (pairing : Pairing) : Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂ ⊔ c ⊔ ℓ) where
    constructor makeBilinear

    ⟨_,_⟩ : Γ ∣A₁∣ → Γ ∣A₂∣ → Γ ∣A∣
    ⟨_,_⟩ x y = pairing ⟨$⟩ x ⟨$⟩ y

    open AdditiveNotation A₁ hiding (_≈_) renaming (_+_ to _+₁_ ; O to O₁)
    open AdditiveNotation A₂ hiding (_≈_) renaming (_+_ to _+₂_ ; O to O₂)
    open AdditiveNotation A

    field
      0-left : (y : Γ ∣A₂∣) → ⟨ O₁ , y ⟩ ≈ O
      0-right : (x : Γ ∣A₁∣) → ⟨ x , O₂ ⟩ ≈ O
      +-left : (x x′ : Γ ∣A₁∣) (y : Γ ∣A₂∣) → ⟨ x +₁ x′ , y ⟩ ≈ ⟨ x , y ⟩ + ⟨ x′ , y ⟩
      +-right : (x : Γ ∣A₁∣) (y y′ : Γ ∣A₂∣) → ⟨ x , y +₂ y′ ⟩ ≈ ⟨ x , y ⟩ + ⟨ x , y′ ⟩



module flipping-bilinear {c₁ ℓ₁ c₂ ℓ₂ c ℓ : Level}
  {A₁ : CommutativeMonoid c₁ ℓ₁}
  {A₂ : CommutativeMonoid c₂ ℓ₂}
  {A  : CommutativeMonoid c  ℓ } where

  open pairing-context

  -- a bilinear map A₁ x A₂ → A gives one A₂ x A₁ → A
  flip-bilinear : {μ : Pairing A₁ A₂ A} → IsBilinear A₁ A₂ A μ →  IsBilinear A₂ A₁ A (flip ⟨$⟩ μ)
  flip-bilinear (makeBilinear 0-left 0-right +-left +-right) = makeBilinear 0-right 0-left (λ x x′ y → +-right y x x′) (λ x y y′ → +-left y y′ x)



record AbelianEnrichment {ℓ ℓ′ ℓ″ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) : Set (ℓ ⊔ ℓ′ ⊔ ℓ″) where

  open Category C

  field
    _+_ : {x y : obj} → homset x y → homset x y → homset x y
    O : {x y : obj} → homset x y
    −_ : {x y : obj} → homset x y → homset x y
    comm : {x y : obj} → Props.Commutative (_≈_ {x} {y}) (_+_ {x} {y})
    inverse : {x y : obj} → Props.Inverse (_≈_ {x} {y}) (O {x} {y}) (−_ {x} {y}) (_+_ {x} {y})
    −-cong : {x y : obj} → _Preserves_⟶_ (−_ {x} {y}) (_≈_ {x} {y}) (_≈_ {x} {y})
    identity : {x y : obj} → Props.Identity (_≈_ {x} {y}) (O {x} {y}) (_+_ {x} {y})
    +-assoc : {x y : obj} → Props.Associative (_≈_ {x} {y}) (_+_ {x} {y})
    +-cong : {x y : obj} → _Preserves₂_⟶_⟶_ (_+_ {x} {y}) (_≈_ {x} {y}) (_≈_ {x} {y}) (_≈_ {x} {y})

  isAbelianGroup : (x y : obj) → IsAbelianGroup _≈_ (_+_ {x} {y}) O −_
  isAbelianGroup x y = record {
    isGroup = record {
      isMonoid = record {
        isSemigroup = record {
          isEquivalence = Setoid.isEquivalence (hom x y);
          assoc = +-assoc;
          ∙-cong = +-cong };
        identity = identity };
      inverse = inverse;
      ⁻¹-cong = −-cong };
    comm = comm }

  HomAbelianGroup : (x y : obj) → AbelianGroup ℓ′ ℓ″
  HomAbelianGroup x y = record {
    Carrier = homset x y ;
    isAbelianGroup = isAbelianGroup x y }

  HomCommutativeMonoid : (x y : obj) → CommutativeMonoid ℓ′ ℓ″
  HomCommutativeMonoid x y = AbelianGroup.commutativeMonoid (HomAbelianGroup x y)

  field
    isBilinear : {x y z : obj} → pairing-context.IsBilinear (HomCommutativeMonoid y z) (HomCommutativeMonoid x y) (HomCommutativeMonoid x z) (compose {x} {y} {z})

  module bilinearity {x y z : obj} where
    open pairing-context.IsBilinear (HomCommutativeMonoid y z) (HomCommutativeMonoid x y) (HomCommutativeMonoid x z) (isBilinear {x} {y} {z}) public
  open bilinearity public


module endomorphisms-ring {ℓ ℓ′ ℓ″ : Level} {C : Category {ℓ} {ℓ′} {ℓ″}} (E : AbelianEnrichment C) where

  open Category C
  open AbelianEnrichment E

  endomorphismRing : (x : Category.obj C) → IsRing (_≈_ {x} {x}) _+_ _•_ −_ O (id x)
  endomorphismRing x = record {
    +-isAbelianGroup = AbelianEnrichment.isAbelianGroup E x x ;
    *-isMonoid = endomorphismMonoid {ℓ} {ℓ′} {ℓ″} {C} x ;
    distrib = (λ a b₁ b₂ → +-right a b₁ b₂) ,′ (λ b a₁ a₂ → +-left a₁ a₂ b) }

open endomorphisms-ring public



module minus-axioms-outer {c₁ ℓ₁ c₂ ℓ₂ c ℓ : Level}
  {A₁ : AbelianGroup c₁ ℓ₁}
  {A₂ : AbelianGroup c₂ ℓ₂}
  {A  : AbelianGroup c ℓ } where

  private
    M₁ = AbelianGroup.commutativeMonoid A₁
    M₂ = AbelianGroup.commutativeMonoid A₂
    M = AbelianGroup.commutativeMonoid A
    ∣A₁∣ = CommutativeMonoid.setoid M₁
    ∣A₂∣ = CommutativeMonoid.setoid M₂
    ∣A∣  = CommutativeMonoid.setoid M

  open pairing-context M₁ M₂ M
  open AdditiveNotation′ A₁ hiding (_≈_ ; setoid ; sym ; ∙-cong ; assoc) renaming (_+_ to _+₁_ ; −_ to −₁_ ; O to O₁ ; identity to identity₁ ; inverse to inverse₁ ; refl to refl₁)
  open AdditiveNotation′ A₂ hiding (_≈_ ; setoid ; sym ; ∙-cong ; assoc) renaming (_+_ to _+₂_ ; −_ to −₂_ ; O to O₂ ; identity to identity₂ ; inverse to inverse₂ ; refl to refl₂)
  open AdditiveNotation′ A

  module minus-axioms-inner {pairing : Pairing} (isBilinear : IsBilinear pairing) where
    open IsBilinear isBilinear
    open EqReasoning ∣A∣

    −-left : (x : Γ ∣A₁∣) (y : Γ ∣A₂∣) → ⟨ −₁ x , y ⟩ ≈ − ⟨ x , y ⟩
    −-left x y = begin
      ⟨ −₁ x , y ⟩
        ≈⟨ sym (proj₁ identity _) ⟩
      O + ⟨ −₁ x , y ⟩
        ≈⟨ ∙-cong (sym (proj₁ inverse _)) refl ⟩
      ((− ⟨ x , y ⟩) + ⟨ x , y ⟩) + ⟨ −₁ x , y ⟩
        ≈⟨ assoc _ _ _ ⟩
      (− ⟨ x , y ⟩) + (⟨ x , y ⟩ + ⟨ −₁ x , y ⟩)
        ≈⟨ ∙-cong refl (sym (+-left _ _ _)) ⟩
      (− ⟨ x , y ⟩) + ⟨ x +₁ (−₁ x) , y ⟩
        ≈⟨ ∙-cong refl (cong pairing (proj₂ inverse₁ x) refl₂) ⟩
      (− ⟨ x , y ⟩) + ⟨ O₁ , y ⟩
        ≈⟨ ∙-cong refl (0-left _) ⟩
      (− ⟨ x , y ⟩) + O
        ≈⟨ proj₂ identity _ ⟩
      − ⟨ x , y ⟩ ∎

    −-right : (x : Γ ∣A₁∣) (y : Γ ∣A₂∣) → ⟨ x , −₂ y ⟩ ≈ − ⟨ x , y ⟩
    −-right x y = begin
      ⟨ x , −₂ y ⟩
        ≈⟨ sym (proj₂ identity _) ⟩
      ⟨ x , −₂ y ⟩ + O
        ≈⟨ ∙-cong refl (sym (proj₂ inverse _)) ⟩
      ⟨ x , −₂ y ⟩ + (⟨ x , y ⟩ + (− ⟨ x , y ⟩))
        ≈⟨ sym (assoc _ _ _) ⟩
      (⟨ x , −₂ y ⟩ + ⟨ x , y ⟩) + (− ⟨ x , y ⟩)
        ≈⟨ ∙-cong (sym (+-right _ _ _)) refl ⟩
      ⟨ x , (−₂ y) +₂ y ⟩ + (− ⟨ x , y ⟩)
        ≈⟨ ∙-cong (cong pairing refl₁ (proj₁ inverse₂ y)) refl ⟩
      ⟨ x , O₂ ⟩ + (− ⟨ x , y ⟩)
        ≈⟨ ∙-cong (0-right _) refl ⟩
      O + (− ⟨ x , y ⟩)
        ≈⟨ proj₁ identity _ ⟩
      − ⟨ x , y ⟩ ∎


