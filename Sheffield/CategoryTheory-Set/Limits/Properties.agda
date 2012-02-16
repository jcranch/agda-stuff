module Sheffield.CategoryTheory-Set.Limits.Properties where

open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Categories.Equivalence
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.Functors.Composition
open import Sheffield.CategoryTheory-Set.Functors.Isomorphism
open import Sheffield.CategoryTheory-Set.Limits
open import Sheffield.CategoryTheory-Set.Misc
open import Sheffield.CategoryTheory-Set.NaturalTransformations
open import Sheffield.CategoryTheory-Set.NaturalTransformations.Equality


hom-between-limits : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level}
  {K : Category {ℓ₁} {ℓ′₁}} {C : Category {ℓ₂} {ℓ′₂}}
  (F G : Functor K C) (x y : Category.obj C)
  (Φ : NatTrans (constFunctor K C x) F) →
  (Ψ : NatTrans (constFunctor K C y) G) →
  IsLimit G y Ψ → NatTrans F G → Category.hom C x y

hom-between-limits F G x y Φ Ψ lim Θ = existsUnique.witness (IsLimit.factorisations lim x (Θ •̂ Φ))



module cone-composition {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level}
  {K : Category {ℓ₁} {ℓ′₁}} {C : Category {ℓ₂} {ℓ′₂}} {D : Category {ℓ₃} {ℓ′₃}}
  {F : Functor K C} {x : Category.obj C} (Φ : NatTrans (constFunctor K C x) F)
  (G : Functor C D) where

  open Category D
  open Category C renaming (_•_ to _•′_ ; id to id′ ; id-r to id-r′ ; obj to obj′ ; hom to hom′)

  private
    Φ₀ = NatTrans.component Φ
    Φ₁ = λ {x} {y} f → NatTrans.naturality Φ {x} {y} f
    F₀ = Functor.obj F
    G₀ = Functor.obj G
    G₁ = λ {x} {y} f → Functor.hom G {x} {y} f

  map-cone : NatTrans (constFunctor K D (Functor.obj G x)) (G ⊙ F)
  map-cone = makeNatTrans component naturality where
    component : (a : Category.obj K) → hom (G₀ x) (G₀ (F₀ a))
    component a = G₁ (Φ₀ a)
    naturality : {a b : Category.obj K} (f : Category.hom K a b) → component b • Functor.hom (constFunctor K D (Functor.obj G x)) f ≡ Functor.hom (G ⊙ F) f • component a
    naturality {a} {b} f = begin
      Functor.hom G (NatTrans.component Φ b) • id (Functor.obj G x)
        ≡⟨ id-r _ ⟩
      Functor.hom G (NatTrans.component Φ b)
        ≡⟨ cong (Functor.hom G) (sym (id-r′ _)) ⟩
      Functor.hom G (Category.compose C (NatTrans.component Φ b) (Category.id C x))
        ≡⟨ cong (Functor.hom G) (Φ₁ f) ⟩
      Functor.hom G (Functor.hom F f •′ NatTrans.component Φ a)
        ≡⟨ Functor.compose G _ _ ⟩
      Functor.hom G (Functor.hom F f) • Functor.hom G (NatTrans.component Φ a) ∎

open cone-composition public


{-
-- this should be stated and proved as a property of Kan extensions and simply derived for limits
module limits-equivalence {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level}
  {K : Category {ℓ₁} {ℓ′₁}} {C : Category {ℓ₂} {ℓ′₂}} {D : Category {ℓ₃} {ℓ′₃}}
  (F : Functor K C) (x : Category.obj C) (Φ : NatTrans (constFunctor K C x) F)
  (G : Functor C D) (G̃ : Equivalence G) (lim : IsLimit F x Φ) where

  open Category D
  open Category C renaming (_•_ to _•′_ ; id to id′ ; id-r to id-r′ ; obj to obj′ ; hom to hom′)
  open Equivalence G̃ renaming (F⁻¹ to G⁻¹)
  open IsLimit lim

  private
    Φ₀ = NatTrans.component Φ
    Φ₁ = λ {x} {y} f → NatTrans.naturality Φ {x} {y} f
    F₀ = Functor.obj F
    G₀ = Functor.obj G
    G₁ = λ {x} {y} f → Functor.hom G {x} {y} f
    G⁻¹₀ = Functor.obj G⁻¹

  Φ′ : NatTrans (constFunctor K D (G₀ x)) (G ⊙ F)
  Φ′ = map-cone Φ G

  unmap-cone : {a : obj} → NatTrans (constFunctor K D a) (G ⊙ F) → NatTrans (constFunctor K C (G⁻¹₀ a)) F
  unmap-cone Ψ = ⊙-unitor-l F •̂ (_≅₁_.obverse unit ⊙̂ idNatTrans F) •̂ ⊙-associator G⁻¹ G F •̂ map-cone Ψ G⁻¹

  cong-≅₀-limits : IsLimit (G ⊙ F) (Functor.obj G x) Φ′

  cong-≅₀-limits = make-Limit L where
    L : (a : obj) (Ψ : NatTrans (constFunctor K D a) (G ⊙ F)) → existsUnique (hom a (G₀ x)) _≡_ (λ f → Ψ ≡₂ Φ′ •̂ constNatTrans f)
    L a Ψ = makeUnique (G₁ (existsUnique.witness ε) • NatTrans.component (_≅₁_.inverse counit) a) (λ b → {!existsUnique.satisfaction ε b!}) {!!} where
      ε = factorisations (G⁻¹₀ a) (unmap-cone Ψ)

open limits-equivalence public
-}