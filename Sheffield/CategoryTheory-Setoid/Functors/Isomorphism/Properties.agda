module Sheffield.CategoryTheory-Setoid.Functors.Isomorphism.Properties where

open import Function.Equality hiding (id)
open import Level
open import Relation.Binary
import Relation.Binary.EqReasoning

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Properties


Iso₁-⊙-left : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} (G : Functor D E) (F F′ : Functor C D) {Θ : NatTrans F F′} (I : Isomorphism₁ Θ) → Isomorphism₁ (idNatTrans G ⊙̂ Θ)
Iso₁-⊙-left G F F′ {Θ = Θ} (make-Iso₁ Θ⁻¹ c₁ c₂) = make-Iso₁ (idNatTrans G ⊙̂ Θ⁻¹) e₁ e₂ where
  e₁ = begin
         (idNatTrans G ⊙̂ Θ⁻¹) •̂ (idNatTrans G ⊙̂ Θ)
           ≈⟨ interchange (idNatTrans G) (idNatTrans G) Θ⁻¹ Θ ⟩
         (idNatTrans G •̂ idNatTrans G) ⊙̂ (Θ⁻¹ •̂ Θ)
           ≈⟨ ⊙̂-cong (•̂-unit-l (idNatTrans G)) c₁ ⟩
         idNatTrans G ⊙̂ idNatTrans F
           ≈⟨ id⊙id≈₂id G F ⟩
         idNatTrans (G ⊙ F) ∎ where open Relation.Binary.EqReasoning NaturalTransformations
  e₂ = begin
         (idNatTrans G ⊙̂ Θ) •̂ (idNatTrans G ⊙̂ Θ⁻¹)
           ≈⟨ interchange (idNatTrans G) (idNatTrans G) Θ Θ⁻¹ ⟩
         (idNatTrans G •̂ idNatTrans G) ⊙̂ (Θ •̂ Θ⁻¹)
           ≈⟨ ⊙̂-cong (•̂-unit-l (idNatTrans G)) c₂ ⟩
         idNatTrans G ⊙̂ idNatTrans F′
           ≈⟨ id⊙id≈₂id G F′ ⟩
         idNatTrans (G ⊙ F′) ∎ where open Relation.Binary.EqReasoning NaturalTransformations

Iso₁-⊙-right : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} (G G′ : Functor D E) (F : Functor C D) {Θ : NatTrans G G′} (I : Isomorphism₁ Θ) → Isomorphism₁ (Θ ⊙̂ idNatTrans F)
Iso₁-⊙-right G G′ F {Θ = Θ} (make-Iso₁ Θ⁻¹ c₁ c₂) = make-Iso₁ (Θ⁻¹ ⊙̂ idNatTrans F) e₁ e₂ where
  e₁ = begin
         (Θ⁻¹ ⊙̂ idNatTrans F) •̂ (Θ ⊙̂ idNatTrans F)
           ≈⟨ interchange Θ⁻¹ Θ (idNatTrans F) (idNatTrans F) ⟩
         (Θ⁻¹ •̂ Θ) ⊙̂ (idNatTrans F •̂ idNatTrans F) 
           ≈⟨ ⊙̂-cong c₁ (•̂-unit-l (idNatTrans F)) ⟩
         idNatTrans G ⊙̂ idNatTrans F
           ≈⟨ id⊙id≈₂id G F ⟩
         idNatTrans (G ⊙ F) ∎ where open Relation.Binary.EqReasoning NaturalTransformations
  e₂ = begin
         (Θ ⊙̂ idNatTrans F) •̂ (Θ⁻¹ ⊙̂ idNatTrans F)
           ≈⟨ interchange Θ Θ⁻¹ (idNatTrans F) (idNatTrans F) ⟩
         (Θ •̂ Θ⁻¹) ⊙̂ (idNatTrans F •̂ idNatTrans F) 
           ≈⟨ ⊙̂-cong c₂ (•̂-unit-l (idNatTrans F)) ⟩
         idNatTrans G′ ⊙̂ idNatTrans F
           ≈⟨ id⊙id≈₂id G′ F ⟩
         idNatTrans (G′ ⊙ F) ∎ where open Relation.Binary.EqReasoning NaturalTransformations


-- functor isomorphisms yield category isomorphisms
module iso-to-iso {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level}
       {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} where

  open Iso D

  iso₁-iso : {F G : Functor C D} {Θ : NatTrans F G} (I : Isomorphism₁ Θ) (x : Category.obj C) → Isomorphism (NatTrans.component Θ x)
  iso₁-iso {Θ = Θ} (make-Iso₁ Θ⁻¹ (make-≈₂ c₁) (make-≈₂ c₂)) x = makeIso (NatTrans.component Θ⁻¹ x) (c₁ x) (c₂ x)

  ≅₁-≅ : {F G : Functor C D} → F ≅₁ G → (x : Category.obj C) → Functor.obj F x ≅ Functor.obj G x
  ≅₁-≅ (make-≅₁ obverse (make-Iso₁ reverse (make-≈₂ unit) (make-≈₂ counit))) x = Iso.make-≅ (NatTrans.component obverse x) (Iso.makeIso (NatTrans.component reverse x) (unit x) (counit x))

open iso-to-iso public




≅₁-⊙-left : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} (G : Functor D E) (F F′ : Functor C D) → F ≅₁ F′ → G ⊙ F ≅₁ G ⊙ F′
≅₁-⊙-left G F F′ (make-≅₁ Θ I) = make-≅₁ (idNatTrans G ⊙̂ Θ) (Iso₁-⊙-left G F F′ I)

≅₁-⊙-right : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} (G G′ : Functor D E) (F : Functor C D) → G ≅₁ G′ → G ⊙ F ≅₁ G′ ⊙ F
≅₁-⊙-right G G′ F (make-≅₁ Θ I) = make-≅₁ (Θ ⊙̂ idNatTrans F) (Iso₁-⊙-right G G′ F I)


const-≅₁-l : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}}
  (F : Functor C D) (x : Category.obj E) → constFunctor D E x ⊙ F ≅₁ constFunctor C E x
const-≅₁-l {C = C} {D = D} {E = E} (makeFunctor obj hom id compose) x = make-≅₁ Θ (make-Iso₁ Θ⁻¹ (make-≈₂ (λ _ → Category.id-l E (Category.id E x))) (make-≈₂ (λ _ → Category.id-l E (Category.id E x)))) where
  Θ : NatTrans (constFunctor D E x ⊙ makeFunctor obj hom id compose) (constFunctor C E x)
  Θ = makeNatTrans (λ _ → Category.id E x) (λ _ → Category.≈-refl E)
  Θ⁻¹ : NatTrans (constFunctor C E x) (constFunctor D E x ⊙ makeFunctor obj hom id compose)
  Θ⁻¹ = makeNatTrans (λ _ → Category.id E x) (λ _ → Category.≈-refl E)

const-≅₁-r : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}}
  (F : Functor D E) (x : Category.obj D) → F ⊙ constFunctor C D x ≅₁ constFunctor C E (Functor.obj F x)
const-≅₁-r {C = C} {D = D} {E = E} (makeFunctor obj hom id compose) x = make-≅₁ Θ (make-Iso₁ Θ⁻¹ (make-≈₂ (λ _ → Category.id-l E (Category.id E (obj x)))) (make-≈₂ (λ _ → Category.id-l E (Category.id E (obj x))))) where
  Θ : NatTrans (makeFunctor obj hom id compose ⊙ constFunctor C D x) (constFunctor C E (obj x))
  Θ = makeNatTrans (λ _ → Category.id E (obj x)) (λ _ → Category.•-cong E (Category.≈-refl E) (id x))
  Θ⁻¹ : NatTrans (constFunctor C E (obj x)) (makeFunctor obj hom id compose ⊙ constFunctor C D x)
  Θ⁻¹ = makeNatTrans (λ _ → Category.id E (obj x)) (λ _ → Category.•-cong E (Category.≈-sym E (id x)) (Category.≈-refl E))


≅₁-cong : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} {G₁ G₂ : Functor D E} {F₁ F₂ : Functor C D} → G₁ ≅₁ G₂ → F₁ ≅₁ F₂ → G₁ ⊙ F₁ ≅₁ G₂ ⊙ F₂
≅₁-cong {G₁ = G₁} {G₂} {F₁} {F₂} (make-≅₁ obverse′ (make-Iso₁ reverse′ unit′ counit′)) (make-≅₁ obverse (make-Iso₁ reverse unit counit)) = isomorphic₁ obv rev u c where
  obv = obverse′ ⊙̂ obverse
  rev = reverse′ ⊙̂ reverse
  u = begin
    (reverse′ ⊙̂ reverse) •̂ (obverse′ ⊙̂ obverse)
      ≈⟨ interchange reverse′ obverse′ reverse obverse ⟩
    (reverse′ •̂ obverse′) ⊙̂ (reverse •̂ obverse)
      ≈⟨ ⊙̂-cong unit′ unit ⟩
    idNatTrans G₁ ⊙̂ idNatTrans F₁
      ≈⟨ id⊙id≈₂id G₁ F₁ ⟩
    idNatTrans (G₁ ⊙ F₁) ∎ where open NatTrans-reasoning
  c = begin
    (obverse′ ⊙̂ obverse) •̂ (reverse′ ⊙̂ reverse)
      ≈⟨ interchange obverse′ reverse′ obverse reverse ⟩
    (obverse′ •̂ reverse′) ⊙̂ (obverse •̂ reverse)
      ≈⟨ ⊙̂-cong counit′ counit ⟩
    idNatTrans G₂ ⊙̂ idNatTrans F₂
      ≈⟨ id⊙id≈₂id G₂ F₂ ⟩
    idNatTrans (G₂ ⊙ F₂) ∎ where open NatTrans-reasoning


module images {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {F G : Functor C D} (e : F ≅₁ G) where

  private
    Φ = _≅₁_.obverse e
    Ψ = _≅₁_.reverse e
    Φ₀ = NatTrans.component Φ
    Ψ₀ = NatTrans.component Ψ
    u = _≈₂_.component-≈ (_≅₁_.unit e)
    c = _≈₂_.component-≈ (_≅₁_.counit e)

  open Category D
  open Iso D

  ≅₁-obj : (x : Category.obj C) → Functor.obj F x ≅ Functor.obj G x
  ≅₁-obj x = make-iso (NatTrans.component Φ x) (NatTrans.component Ψ x) (u x) (c x)


  ≅₁-hom : {x y : Category.obj C} → Category.hom D (Functor.obj F x) (Functor.obj F y) ⟶ Category.hom D (Functor.obj G x) (Functor.obj G y)
  ≅₁-hom {x} {y} = record {
    _⟨$⟩_ = λ f → NatTrans.component Φ y • f • NatTrans.component Ψ x;
    cong = λ {f} {g} e → •-cong ≈-refl (•-cong e ≈-refl) }

  ≅₁-hom-≈ : {x y : Category.obj C} (f : Category.homset C x y) → ≅₁-hom ⟨$⟩ (Functor.homsets F f) ≈ Functor.homsets G f
  ≅₁-hom-≈ {x} {y} f = begin
    Φ₀ y • Functor.homsets F f • Ψ₀ x
      ≈⟨ ≈-sym (assoc _ _ _) ⟩
    (Φ₀ y • Functor.homsets F f) • Ψ₀ x
      ≈⟨ •-cong (NatTrans.naturality Φ f) ≈-refl ⟩
    (Functor.homsets G f • Φ₀ x) • Ψ₀ x
      ≈⟨ assoc _ _ _ ⟩
    Functor.homsets G f • (Φ₀ x • Ψ₀ x)
      ≈⟨ •-cong ≈-refl (c x) ⟩
    Functor.homsets G f • id _
      ≈⟨ id-r _ ⟩
    Functor.homsets G f ∎ where open ≈-Reasoning _ _

  ≅₁-morphisms : {x y : Category.obj C} {f g : Category.homset C x y} → Functor.homsets F f ≈ Functor.homsets F g → Functor.homsets G f ≈ Functor.homsets G g
  ≅₁-morphisms {x} {y} {f} {g} e = begin
    Functor.homsets G f
      ≈⟨ ≈-sym (id-l _) ⟩
    id (Functor.obj G y) • Functor.homsets G f
      ≈⟨ •-cong (≈-sym (c y)) ≈-refl ⟩
    (NatTrans.component Φ y • NatTrans.component Ψ y) • Functor.homsets G f
      ≈⟨ assoc _ _ _ ⟩
    NatTrans.component Φ y • (NatTrans.component Ψ y • Functor.homsets G f)
      ≈⟨ •-cong ≈-refl (NatTrans.naturality Ψ f) ⟩
    NatTrans.component Φ y • (Functor.homsets F f • NatTrans.component Ψ x)
      ≈⟨ ≈-sym (assoc _ _ _) ⟩
    (NatTrans.component Φ y • Functor.homsets F f) • NatTrans.component Ψ x
      ≈⟨ •-cong (•-cong ≈-refl e) ≈-refl ⟩
    (NatTrans.component Φ y • Functor.homsets F g) • NatTrans.component Ψ x
      ≈⟨ •-cong (NatTrans.naturality Φ g) ≈-refl ⟩
    (Functor.homsets G g • NatTrans.component Φ x) • NatTrans.component Ψ x
      ≈⟨ assoc _ _ _ ⟩
    Functor.homsets G g • (NatTrans.component Φ x • NatTrans.component Ψ x)
      ≈⟨ •-cong ≈-refl (c x) ⟩
    Functor.homsets G g • id (Functor.obj G x)
      ≈⟨ id-r _ ⟩
    Functor.homsets G g ∎ where open ≈-Reasoning _ _

open images public
