module Sheffield.CategoryTheory-Set.NaturalTransformations.Equality where


open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_ ; refl)

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.NaturalTransformations


infix 4 _≡₂_
_≡₂_ : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level}
       {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
       {F G : Functor C D} → Rel (NatTrans F G) (ℓ₁ ⊔ ℓ′₂)
_≡₂_ {_} {_} {_} {_} {C} (makeNatTrans component _) (makeNatTrans component' _) = (x : Category.obj C) → component x ≡ component' x


≡₂-refl : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level}
         {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
         {F G : Functor C D} {Θ : NatTrans F G} → Θ ≡₂ Θ
≡₂-refl x = refl


≡₂-sym : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level}
         {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
         {F G : Functor C D}
         {Φ Ψ : NatTrans F G} → Φ ≡₂ Ψ → Ψ ≡₂ Φ
≡₂-sym E x = PropEq.sym (E x) 


≡₂-trans : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level}
         {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
         {F G : Functor C D}
         {Θ Φ Ψ : NatTrans F G} →
         Θ ≡₂ Φ → Φ ≡₂ Ψ → Θ ≡₂ Ψ
≡₂-trans E₁ E₂ x = PropEq.trans (E₁ x) (E₂ x)


≡₂-isEquivalence : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level}
         {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
         {F G : Functor C D} → IsEquivalence (_≡₂_ {F = F} {G = G})
≡₂-isEquivalence {ℓ₁} {ℓ₂} {ℓ′₁} {ℓ′₂} {C} {D} {F} {G} = record {
  refl  = λ {Θ : NatTrans F G} → ≡₂-refl {Θ = Θ} ;
  sym   = λ {Φ Ψ : NatTrans F G} e → ≡₂-sym {Φ = Φ} {Ψ = Ψ} e ; 
  trans = λ {Θ Φ Ψ : NatTrans F G} e₁ e₂ → ≡₂-trans {Θ = Θ} {Φ = Φ} {Ψ = Ψ} e₁ e₂ }


NaturalTransformations : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level}
         {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
         (F G : Functor C D) → Setoid (ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₁ ⊔ ℓ′₂) (ℓ₁ ⊔ ℓ′₂)
NaturalTransformations F G = record {
  Carrier       = NatTrans F G ;
  _≈_           = _≡₂_ ;
  isEquivalence = ≡₂-isEquivalence }
