module Sheffield.CategoryTheory-Setoid.Comma.InducedMaps where

open import Algebra.Structures
open import Data.Product
open import Function using (flip ; _∘_)
open import Function.Equality hiding (id ; _∘_)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Comma
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.SetoidFunction



module comma-category-naturality
  {ℓ₁₁ ℓ′₁₁ ℓ″₁₁ ℓ₂₁ ℓ′₂₁ ℓ″₂₁ ℓ₃₁ ℓ′₃₁ ℓ″₃₁ ℓ₁₂ ℓ′₁₂ ℓ″₁₂ ℓ₂₂ ℓ′₂₂ ℓ″₂₂ ℓ₃₂ ℓ′₃₂ ℓ″₃₂ : Level}
  {A₁ : Category {ℓ₁₁} {ℓ′₁₁} {ℓ″₁₁}} {A₂ : Category {ℓ₁₂} {ℓ′₁₂} {ℓ″₁₂}}
  {B₁ : Category {ℓ₂₁} {ℓ′₂₁} {ℓ″₂₁}} {B₂ : Category {ℓ₂₂} {ℓ′₂₂} {ℓ″₂₂}}
  {C₁ : Category {ℓ₃₁} {ℓ′₃₁} {ℓ″₃₁}} {C₂ : Category {ℓ₃₂} {ℓ′₃₂} {ℓ″₃₂}}
  (F₁ : Functor A₁ C₁) (G₁ : Functor B₁ C₁)
  (F₂ : Functor A₂ C₂) (G₂ : Functor B₂ C₂)
  (HA : Functor A₁ A₂) (HB : Functor B₁ B₂) (HC : Functor C₁ C₂)
  (Φ : NatTrans (F₂ ⊙ HA) (HC ⊙ F₁))
  (Ψ : NatTrans (HC ⊙ G₁) (G₂ ⊙ HB)) where

  open comma-category.comma-structure F₁ G₁ using () renaming ([_,_,_] to [_,_,_]₁ ; make-hom to make-hom₁)
  open comma-category.comma-structure F₂ G₂ using () renaming ([_,_,_] to [_,_,_]₂ ; make-hom to make-hom₂)

  open Category C₂
  open Category C₁ using () renaming (_•_ to _•′_)
  open Category (F₁ ↓ G₁) using () renaming (_≈_ to _≈¹_ ; _•_ to _•¹_)
  open Category (F₂ ↓ G₂) using () renaming (_≈_ to _≈²_ ; _•_ to _•²_)

  HA₀ = Functor.obj HA
  HB₀ = Functor.obj HB
  HA₁ = λ {a} {b} → Functor.homsets HA {a} {b}
  HB₁ = λ {a} {b} → Functor.homsets HB {a} {b}
  HC₁ = λ {a} {b} → Functor.homsets HC {a} {b}
  F₁₁ = λ {a} {b} → Functor.homsets F₁ {a} {b}
  F₂₁ = λ {a} {b} → Functor.homsets F₂ {a} {b}
  G₁₁ = λ {a} {b} → Functor.homsets G₁ {a} {b}
  G₂₁ = λ {a} {b} → Functor.homsets G₂ {a} {b}
  Φ₀ = NatTrans.component Φ
  Ψ₀ = NatTrans.component Ψ

  ↓-natural : Functor (F₁ ↓ G₁) (F₂ ↓ G₂)
  ↓-natural = makeFunctor obj′ hom′ id′ compose′ where
    obj′ : Category.obj (F₁ ↓ G₁) → Category.obj (F₂ ↓ G₂)
    obj′ [ x , y , f ]₁ = [ HA₀ x , HB₀ y , Ψ₀ y • HC₁ f • Φ₀ x ]₂

    homsets′ : {x y : Category.obj (F₁ ↓ G₁)} → Γ (Category.hom (F₁ ↓ G₁) x y) → Γ (Category.hom (F₂ ↓ G₂) (obj′ x) (obj′ y))
    homsets′ {[ x₁ , y₁ , f₁ ]₁} {[ x₂ , y₂ , f₂ ]₁} (make-hom₁ α β ε) = make-hom₂ (HA₁ α) (HB₁ β) e where
      e′ = begin
        HC₁ (G₁₁ β) • HC₁ f₁
          ≈⟨ ≈-sym (Functor.compose HC (G₁₁ β) f₁) ⟩
        HC₁ (G₁₁ β •′ f₁)
          ≈⟨ Functor.hom-cong HC ε ⟩
        HC₁ (f₂ •′ F₁₁ α)
          ≈⟨ Functor.compose HC f₂ (F₁₁ α) ⟩
        HC₁ f₂ • HC₁ (F₁₁ α) ∎ where open ≈-Reasoning _ _
      e = begin
        G₂₁ (HB₁ β) • (Ψ₀ y₁ • HC₁ f₁ • Φ₀ x₁)
          ≈⟨ ≈-sym (assoc _ _ _) ⟩
        (G₂₁ (HB₁ β) • Ψ₀ y₁) • (HC₁ f₁ • Φ₀ x₁)
          ≈⟨ •-cong (≈-sym (NatTrans.naturality Ψ β)) ≈-refl ⟩
        (Ψ₀ y₂ • HC₁ (G₁₁ β)) • (HC₁ f₁ • Φ₀ x₁)
          ≈⟨ assoc _ _ _ ⟩
        Ψ₀ y₂ • HC₁ (G₁₁ β) • (HC₁ f₁ • Φ₀ x₁)
          ≈⟨ •-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
        Ψ₀ y₂ • (HC₁ (G₁₁ β) • HC₁ f₁) • Φ₀ x₁
          ≈⟨ •-cong ≈-refl (•-cong e′ ≈-refl) ⟩
        Ψ₀ y₂ • (HC₁ f₂ • HC₁ (F₁₁ α)) • Φ₀ x₁
          ≈⟨ •-cong ≈-refl (assoc _ _ _) ⟩
        Ψ₀ y₂ • HC₁ f₂ • HC₁ (F₁₁ α) • Φ₀ x₁
          ≈⟨ ≈-sym (assoc _ _ _) ⟩
        (Ψ₀ y₂ • HC₁ f₂) • (HC₁ (F₁₁ α) • Φ₀ x₁)
          ≈⟨ •-cong ≈-refl (≈-sym (NatTrans.naturality Φ α)) ⟩
        (Ψ₀ y₂ • HC₁ f₂) • (Φ₀ x₂ • F₂₁ (HA₁ α))
          ≈⟨ ≈-sym (assoc _ _ _) ⟩
        ((Ψ₀ y₂ • HC₁ f₂) • Φ₀ x₂) • F₂₁ (HA₁ α)
          ≈⟨ •-cong (assoc _ _ _) ≈-refl ⟩
        (Ψ₀ y₂ • HC₁ f₂ • Φ₀ x₂) • F₂₁ (HA₁ α) ∎ where open ≈-Reasoning _ _
 
    hom′ : {x y : Category.obj (F₁ ↓ G₁)} → Category.hom (F₁ ↓ G₁) x y ⟶ Category.hom (F₂ ↓ G₂) (obj′ x) (obj′ y)
    hom′ {[ x₁ , y₁ , f₁ ]₁} {[ x₂ , y₂ , f₂ ]₁} = record {
      _⟨$⟩_ = homsets′ ;
      cong = λ e → Functor.hom-cong HA (proj₁ e) , Functor.hom-cong HB (proj₂ e) }

    id′ : (x : Category.obj (F₁ ↓ G₁)) → (hom′ ⟨$⟩ Category.id (F₁ ↓ G₁) x) ≈² (Category.id (F₂ ↓ G₂) (obj′ x))
    id′ [ f , g , e ]₁ = Functor.id HA _ , Functor.id HB _

    compose′ : {x y z : Category.obj (F₁ ↓ G₁)}
      (g : Γ (Category.hom (F₁ ↓ G₁) y z))
      (f : Γ (Category.hom (F₁ ↓ G₁) x y)) →
      hom′ ⟨$⟩ (g •¹ f) ≈² (hom′ ⟨$⟩ g) •² (hom′ ⟨$⟩ f)
    compose′ (make-hom₁ g₁ g₂ _) (make-hom₁ f₁ f₂ _) = Functor.compose HA g₁ f₁ , Functor.compose HB g₂ f₂

open comma-category-naturality public using (↓-natural)

-- one could also show that, given composable diagrams as above, the induced functors agree up to natural equality... but that seems like a tremendous amount of work
