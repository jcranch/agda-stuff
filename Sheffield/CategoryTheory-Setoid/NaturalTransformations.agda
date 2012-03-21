module Sheffield.CategoryTheory-Setoid.NaturalTransformations where


open import Function.Equality renaming (_∘_ to _∘⁺_ ; id to id⁺)
open import Level
open import Relation.Binary


open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.SetoidFunction



record NatTrans {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F G : Functor C D) : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂) where
  constructor makeNatTrans
  open Category D
  open Category C renaming (hom to hom′ ; _≈_ to _≈′_ ; _•_ to _•′_)

  field
    component : (x : Category.obj C) → Γ (hom (Functor.obj F x) (Functor.obj G x))
    naturality : {x y : Category.obj C} (f : Γ (Category.hom C x y)) → component y • (Functor.hom F ⟨$⟩ f) ≈ (Functor.hom G ⟨$⟩ f) • component x






-- this lemma observes that the naturality condition is always satisfied for identity maps
module identity-naturality {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level}
  {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}}
  (F G : Functor C D) (x : Category.obj C)
  (φ : Category.homset D (Functor.obj F x) (Functor.obj G x)) where

  open Category D

  naturality-for-identities : φ • (Functor.hom F ⟨$⟩ Category.id C x) ≈ (Functor.hom G ⟨$⟩ Category.id C x) • φ
  naturality-for-identities = begin
    φ • (Functor.hom F ⟨$⟩ Category.id C x)
      ≈⟨ •-cong ≈-refl (Functor.id F x) ⟩
    φ • Category.id D (Functor.obj F x)
      ≈⟨ Category.id-r D φ ⟩
    φ
      ≈⟨ ≈-sym (Category.id-l D φ) ⟩
    Category.id D (Functor.obj G x) • φ
      ≈⟨ •-cong (≈-sym (Functor.id G x)) ≈-refl ⟩
    (Functor.hom G ⟨$⟩ Category.id C x) • φ ∎ where open ≈-Reasoning _ _

open identity-naturality public


module identity-natural-transformation {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F : Functor C D) where

  open Category D
  open Category C renaming (obj to obj′ ; homset to homset′ ; id to id′ ; _≈_ to _≈′_ ; _•_ to _•′_ ; id-l to id-l′ ; id-r to id-r′ ; ≈-sym to ≈-sym′)
  private
    obC = Category.obj C
    F₀ = Functor.obj F
    F₁ = λ {x} {y} f → Functor.hom F {x} {y} ⟨$⟩ f

  idNatTrans : NatTrans F F
  idNatTrans = makeNatTrans id-component id-naturality where
    id-component : (x : obj′) → homset (F₀ x) (F₀ x)
    id-component x = id (F₀ x)
    id-naturality : {x y : obj′} (f : homset′ x y) → id-component y • F₁ f ≈ F₁ f • id-component x
    id-naturality {x} {y} f = begin
      id (F₀ y) • F₁ f
        ≈⟨ id-l (F₁ f) ⟩
      F₁ f
        ≈⟨ ≈-sym (id-r (F₁ f)) ⟩
      F₁ f • id (F₀ x) ∎ where open Category.≈-Reasoning D _ _

open identity-natural-transformation public




module vertical-composition {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}}
  {F G H : Functor C D} where

  open Category D
  open Category C renaming (obj to obj′ ; homset to homset′ ; _•_ to _•′_ ; _≈_ to _≈′_ ; ≈-refl to ≈-refl′ ; ≈-sym to ≈-sym′ ; assoc to assoc′ ; •-cong to •-cong′)

  private
    F₀ = Functor.obj F
    F₁ = λ {x} {y} f → Functor.hom F {x} {y} ⟨$⟩ f
    G₁ = λ {x} {y} f → Functor.hom G {x} {y} ⟨$⟩ f
    H₀ = Functor.obj H
    H₁ = λ {x} {y} f → Functor.hom H {x} {y} ⟨$⟩ f

  infixr 8 _•̂_
  _•̂_ : NatTrans G H → NatTrans F G → NatTrans F H
  makeNatTrans Φ Φ-naturality •̂ makeNatTrans Ψ Ψ-naturality = makeNatTrans component naturality where
    component : (x : obj′) → homset (F₀ x) (H₀ x)
    component x = Φ x • Ψ x
    naturality : {x y : obj′} (f : homset′ x y) → component y • F₁ f ≈ H₁ f • component x
    naturality {x} {y} (f) = begin
      (Φ y • Ψ y) • (F₁ f)
        ≈⟨ assoc (Φ y) (Ψ y) (F₁ f) ⟩
      Φ y • (Ψ y • F₁ f)
        ≈⟨ •-cong ≈-refl (Ψ-naturality f) ⟩
      Φ y • (G₁ f • Ψ x)
        ≈⟨ ≈-sym (assoc (Φ y) (G₁ f) (Ψ x)) ⟩
      (Φ y • G₁ f) • Ψ x
        ≈⟨ •-cong (Φ-naturality f) ≈-refl ⟩
      (H₁ f • Φ x) • Ψ x
        ≈⟨ assoc (H₁ f) (Φ x) (Ψ x) ⟩
      H₁ f • (Φ x • Ψ x) ∎ where open Category.≈-Reasoning D _ _

open vertical-composition public



module horizontal-composition {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}}
  {H K : Functor D E} {F G : Functor C D} where

  open Category E
  open Category D using () renaming (_•_ to _•′_ ; assoc to assoc′ ; hom to hom′)
  open Category C using () renaming (obj to obj″ ; hom to hom″ ; homset to homset″)
  private
    F₀ = Functor.obj F
    G₀ = Functor.obj G
    H₀ = Functor.obj H
    K₀ = Functor.obj K
    F₁ = λ {x} {y} f → Functor.hom F {x} {y} ⟨$⟩ f
    G₁ = λ {x} {y} f → Functor.hom G {x} {y} ⟨$⟩ f
    H₁ = λ {x} {y} f → Functor.hom H {x} {y} ⟨$⟩ f
    K₁ = λ {x} {y} f → Functor.hom K {x} {y} ⟨$⟩ f

  infixr 7 _⊙̂_
  _⊙̂_ : NatTrans H K → NatTrans F G → NatTrans (H ⊙ F) (K ⊙ G)
  makeNatTrans Ξ Ξ-naturality ⊙̂ makeNatTrans Θ Θ-naturality = makeNatTrans component naturality where
    component : (x : obj″) → homset (H₀ (F₀ x)) (K₀ (G₀ x))
    component x = Ξ (G₀ x) • H₁ (Θ x)
    naturality : {x y : obj″} (f : homset″ x y) → component y • H₁ (F₁ f) ≈ K₁ (G₁ f) • component x
    naturality {x} {y} (f) = begin
      (Ξ (G₀ y) • H₁ (Θ y)) • H₁ (F₁ f)
        ≈⟨ assoc (Ξ (G₀ y)) (H₁ (Θ y)) (H₁ (F₁ f)) ⟩
      Ξ (G₀ y) • (H₁ (Θ y) • H₁ (F₁ f))
        ≈⟨ •-cong ≈-refl (≈-sym (Functor.compose H (Θ y) (F₁ f))) ⟩
      Ξ (G₀ y) • (H₁ (Θ y •′ F₁ f))
        ≈⟨ •-cong ≈-refl (Functor.hom-cong H (Θ-naturality f)) ⟩
      Ξ (G₀ y) • (H₁ (G₁ f •′ Θ x))
        ≈⟨ •-cong ≈-refl (Functor.compose H (G₁ f) (Θ x)) ⟩
      Ξ (G₀ y) • (H₁ (G₁ f) • H₁ (Θ x))
        ≈⟨ ≈-sym (assoc (Ξ (G₀ y)) (H₁ (G₁ f)) (H₁ (Θ x))) ⟩
      (Ξ (G₀ y) • H₁ (G₁ f)) • H₁ (Θ x)
        ≈⟨ •-cong (Ξ-naturality (G₁ f)) ≈-refl ⟩
      (K₁ (G₁ f) • Ξ (G₀ x)) • H₁ (Θ x)
        ≈⟨ assoc (K₁ (G₁ f)) (Ξ (G₀ x)) (H₁ (Θ x)) ⟩
      K₁ (G₁ f) • (Ξ (G₀ x) • H₁ (Θ x)) ∎ where open Category.≈-Reasoning E _ _

open horizontal-composition public



nat-trans-op : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {F G : Functor C D} (Θ : NatTrans F G) → NatTrans (functor-op G) (functor-op F)
nat-trans-op {D = D} (makeNatTrans component naturality) = makeNatTrans component (λ f → Category.≈-sym D (naturality f))


constNatTrans : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁}  {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {x y : Category.obj D} (f : Category.homset D x y) → NatTrans (constFunctor C D x) (constFunctor C D y)
constNatTrans {D = D} f = makeNatTrans (λ x → f) (λ g → Category.≈-trans D (Category.id-r D f) (Category.≈-sym D (Category.id-l D f)))
