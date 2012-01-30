module NaturalTransformations where

open import Level
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_ ; refl ; sym ; cong)
open PropEq.≡-Reasoning

open import Categories
open import Functors


record NatTrans {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} (F G : Functor C D) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₁ ⊔ ℓ′₂) where
  constructor makeNatTrans
  field
    component : (x : Category.obj C) → Category.hom D (Functor.obj F x) (Functor.obj G x)
    naturality : {x y : Category.obj C} (f : Category.hom C x y) → Category.compose D (component y) (Functor.hom F f) ≡ Category.compose D (Functor.hom G f) (component x)



module identity-natural-transformation {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} (F : Functor C D) where

  open Category D
  private
    obC = Category.obj C
    homC = Category.hom C
    F₀ = Functor.obj F
    F₁ = λ {x} {y} f → Functor.hom F {x} {y} f

  idNatTrans : NatTrans F F
  idNatTrans = makeNatTrans id-component id-naturality where
    id-component : (x : obC) → hom (F₀ x) (F₀ x)
    id-component x = id (F₀ x)
    id-naturality : {x y : obC} (f : homC x y) → id-component y • F₁ f ≡ F₁ f • id-component x
    id-naturality {x} {y} f = begin
      id (F₀ y) • F₁ f
        ≡⟨ id-l (F₁ f) ⟩
      F₁ f
        ≡⟨ sym (id-r (F₁ f)) ⟩
      F₁ f • id (F₀ x) ∎

open identity-natural-transformation public



module vertical-composition {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
  {F G H : Functor C D} where

  open Category D
  private
    obC = Category.obj C
    homC = Category.hom C
    F₀ = Functor.obj F
    F₁ = λ {x} {y} f → Functor.hom F {x} {y} f
    G₁ = λ {x} {y} f → Functor.hom G {x} {y} f
    H₀ = Functor.obj H
    H₁ = λ {x} {y} f → Functor.hom H {x} {y} f

  infixl 8 _•̂_
  _•̂_ : NatTrans G H → NatTrans F G → NatTrans F H
  makeNatTrans Φ Φ-naturality •̂ makeNatTrans Ψ Ψ-naturality = makeNatTrans component naturality where
    component : (x : obC) → hom (F₀ x) (H₀ x)
    component x = Φ x • Ψ x
    naturality : {x y : obC} (f : homC x y) → component y • F₁ f ≡ H₁ f • component x
    naturality {x} {y} (f) = begin
      (Φ y • Ψ y) • (F₁ f)
        ≡⟨ sym (assoc (Φ y) (Ψ y) (F₁ f)) ⟩
      Φ y • (Ψ y • F₁ f)
        ≡⟨ cong (λ a → Φ y • a) (Ψ-naturality f) ⟩
      Φ y • (G₁ f • Ψ x)
        ≡⟨ assoc (Φ y) (G₁ f) (Ψ x) ⟩
      (Φ y • G₁ f) • Ψ x
        ≡⟨ cong (λ a → a • Ψ x) (Φ-naturality f) ⟩
      (H₁ f • Φ x) • Ψ x
        ≡⟨ sym (assoc (H₁ f) (Φ x) (Ψ x)) ⟩
      H₁ f • (Φ x • Ψ x) ∎

open vertical-composition public


module horizontal-composition {ℓ₁ ℓ₂ ℓ₃ ℓ′₁ ℓ′₂ ℓ′₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {E : Category {ℓ₃} {ℓ′₃}}
  {H K : Functor D E} {F G : Functor C D} where

  open Category E
  open Category D renaming (_•_ to _•′_ ; assoc to assoc′ ; hom to hom′)
  private
    obC = Category.obj C
    homC = Category.hom C
    F₀ = Functor.obj F
    G₀ = Functor.obj G
    H₀ = Functor.obj H
    K₀ = Functor.obj K
    F₁ = λ {x} {y} f → Functor.hom F {x} {y} f
    G₁ = λ {x} {y} f → Functor.hom G {x} {y} f
    H₁ = λ {x} {y} f → Functor.hom H {x} {y} f
    K₁ = λ {x} {y} f → Functor.hom K {x} {y} f

  infixl 7 _⊙̂_
  _⊙̂_ : NatTrans H K → NatTrans F G → NatTrans (H ⊙ F) (K ⊙ G)
  makeNatTrans Ξ Ξ-naturality ⊙̂ makeNatTrans Θ Θ-naturality = makeNatTrans component naturality where
    component : (x : obC) → hom (H₀ (F₀ x)) (K₀ (G₀ x))
    component x = Ξ (Functor.obj G x) • Functor.hom H (Θ x)
    naturality : {x y : obC} (f : homC x y) → component y • H₁ (F₁ f) ≡ K₁ (G₁ f) • component x
    naturality {x} {y} (f) = begin
      (Ξ (G₀ y) • H₁ (Θ y)) • H₁ (F₁ f)
        ≡⟨ sym (assoc (Ξ (G₀ y)) (H₁ (Θ y)) (H₁ (F₁ f))) ⟩
      Ξ (G₀ y) • (H₁ (Θ y) • H₁ (F₁ f))
        ≡⟨ cong (λ a → Ξ (G₀ y) • a) (sym (Functor.compose H (Θ y) (F₁ f))) ⟩
      Ξ (G₀ y) • (H₁ (Θ y •′ F₁ f))
        ≡⟨ cong (λ a → Ξ (G₀ y) • H₁ a) (Θ-naturality f) ⟩
      Ξ (G₀ y) • (H₁ (G₁ f •′ Θ x))
        ≡⟨ cong (λ a → Ξ (G₀ y) • a) (Functor.compose H (G₁ f) (Θ x)) ⟩
      Ξ (G₀ y) • (H₁ (G₁ f) • H₁ (Θ x))
        ≡⟨ assoc (Ξ (G₀ y)) (H₁ (G₁ f)) (H₁ (Θ x)) ⟩
      (Ξ (G₀ y) • H₁ (G₁ f)) • H₁ (Θ x)
        ≡⟨ cong (λ a → a • H₁ (Θ x)) (Ξ-naturality (G₁ f)) ⟩
      (K₁ (G₁ f) • Ξ (G₀ x)) • H₁ (Θ x)
        ≡⟨ sym (assoc (K₁ (G₁ f)) (Ξ (G₀ x)) (H₁ (Θ x))) ⟩
      K₁ (G₁ f) • (Ξ (G₀ x) • H₁ (Θ x)) ∎

open horizontal-composition public


nat-trans-op : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {F G : Functor C D} (Θ : NatTrans F G) → NatTrans (functor-op G) (functor-op F)
nat-trans-op (makeNatTrans component naturality) = makeNatTrans component (λ f → sym (naturality f))