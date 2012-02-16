module Sheffield.CategoryTheory-Set.Limits.Product where

open import Data.Product renaming (proj₁ to pr₁ ; proj₂ to pr₂ ; _×_ to _*_)
open import Data.Sum using (inj₁ ; inj₂ ; _⊎_ ; [_,_]′)
open import Data.Unit using (⊤ ; tt)
open import Level
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Set.Limits
open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Categories.Diagrams
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.Misc
open import Sheffield.CategoryTheory-Set.NaturalTransformations
open import Sheffield.CategoryTheory-Set.NaturalTransformations.Equality



module product-context {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁})
  (x y x×y : Category.obj C)
  (π₁ : Category.hom C x×y x) (π₂ : Category.hom C x×y y) where 

  open Category C

  IsProduct : Set (ℓ₁ ⊔ ℓ′₁)
  IsProduct = IsLimit F x×y Θ where
    F : Functor 2points C
    F = 2points-functor x y

    Θ : NatTrans (constFunctor 2points C x×y) F
    Θ = 2points-nat-trans (constFunctor 2points C x×y) F π₁ π₂


  record IsProduct-lowbrow : Set (ℓ₁ ⊔ ℓ′₁) where
    constructor make-product
    field
      product-factorisation : {a : obj} (f₁ : hom a x) (f₂ : hom a y) → existsUnique (hom a x×y) _≡_ (λ f → (π₁ • f ≡ f₁) * (π₂ • f ≡ f₂))


  induced-product-map : IsProduct-lowbrow → {a : obj} → hom a x →  hom a y → hom a x×y
  induced-product-map (make-product φ) f₁ f₂ = existsUnique.witness (φ f₁ f₂)


  product↑ : IsProduct-lowbrow → IsProduct
  product↑ (make-product P) = make-Limit M where
    M : (a : obj) (Ψ : NatTrans _ _) → existsUnique _ _ _
    M a Ψ = makeUnique f s u where
      e = P (NatTrans.component Ψ (inj₁ tt)) (NatTrans.component Ψ (inj₂ tt))
      f = existsUnique.witness e
      s : Ψ ≡₂ (2points-nat-trans (constFunctor 2points C x×y) (2points-functor x y) π₁ π₂) •̂ constNatTrans f
      s (inj₁ tt) = sym (pr₁ (existsUnique.satisfaction e))
      s (inj₂ tt) = sym (pr₂ (existsUnique.satisfaction e))
      u : (g : hom a x×y) → Ψ ≡₂ (2points-nat-trans (constFunctor 2points C x×y) (2points-functor x y) π₁ π₂) •̂ constNatTrans g → g ≡ f
      u g E = existsUnique.uniqueness e g (sym (E (inj₁ tt)) ,′ sym (E (inj₂ tt)))

  product↓ : IsProduct → IsProduct-lowbrow
  product↓ (make-Limit M) = make-product P where
    P : {a : obj} (f₁ : hom a x) (f₂ : hom a y) → existsUnique _ _ _
    P {a} f₁ f₂ = makeUnique f (s₁ ,′ s₂) u where
      e = M a (2points-nat-trans (constFunctor 2points C a) (2points-functor x y) f₁ f₂)
      f = existsUnique.witness e
      s₁ = sym (existsUnique.satisfaction e (inj₁ tt))
      s₂ = sym (existsUnique.satisfaction e (inj₂ tt))
      u : (g : hom a x×y) → (π₁ • g ≡ f₁) * (π₂ • g ≡ f₂) → g ≡ f
      u g E = existsUnique.uniqueness e g k where
        k : (2points-nat-trans (constFunctor 2points C a) (2points-functor x y) f₁ f₂) ≡₂ (2points-nat-trans (constFunctor 2points C x×y) (2points-functor x y) π₁ π₂) •̂ constNatTrans g
        k (inj₁ tt) = sym (pr₁ E)
        k (inj₂ tt) = sym (pr₂ E)

open product-context public

IsCoproduct : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) (x y x⊔y : Category.obj C) (i₁ : Category.hom C x x⊔y) (i₂ : Category.hom C y x⊔y) → Set (ℓ₁ ⊔ ℓ′₁)
IsCoproduct C = IsProduct (opposite C)

IsCoproduct-lowbrow : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) (x y x⊔y : Category.obj C) (i₁ : Category.hom C x x⊔y) (i₂ : Category.hom C y x⊔y) → Set (ℓ₁ ⊔ ℓ′₁)
IsCoproduct-lowbrow C = IsProduct-lowbrow (opposite C)



record Product {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) (x y : Category.obj C) : Set (ℓ₁ ⊔ ℓ′₁) where
  field
    _×_ : Category.obj C
    proj₁ : Category.hom C _×_ x
    proj₂ : Category.hom C _×_ y
    isProduct : IsProduct-lowbrow C x y _×_ proj₁ proj₂

Coproduct : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) (x y : Category.obj C) → Set (ℓ₁ ⊔ ℓ′₁)
Coproduct C = Product (opposite C)



HasProducts : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) → Set (ℓ₁ ⊔ ℓ′₁)
HasProducts C = (x y : Category.obj C) → Product C x y

HasCoproducts : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) → Set (ℓ₁ ⊔ ℓ′₁)
HasCoproducts C = HasProducts (opposite C)
