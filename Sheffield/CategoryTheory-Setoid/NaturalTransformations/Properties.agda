module Sheffield.CategoryTheory-Setoid.NaturalTransformations.Properties where



open import Function.Equality hiding (id)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Composition
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality





module id-nat-trans {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}}
  {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}}
  {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}}
  (G : Functor D E)
  (F : Functor C D) where

  private
    G₀ = Functor.obj G
    F₀ = Functor.obj F
    G₁ = λ {x} {y} f → Functor.homsets G {x} {y} f

  open Category E
  open Category D hiding (_≈_ ; module ≈-Reasoning) renaming (id to id′ ; _•_ to _•′_)

  id⊙id≈₂id : idNatTrans G ⊙̂ idNatTrans F ≈₂ idNatTrans (G ⊙ F) 
  id⊙id≈₂id = make-≈₂ H where
    H : (x : Category.obj C) → id (G₀ (F₀ x)) • G₁ (id′ (F₀ x)) ≈ id (G₀ (F₀ x))
    H x = begin
      id (G₀ (F₀ x)) • G₁ (id′ (F₀ x))
        ≈⟨ Category.id-l E (G₁ (id′ (F₀ x))) ⟩
      G₁ (id′ (F₀ x))
        ≈⟨ Functor.id G (F₀ x) ⟩
      id (G₀ (F₀ x)) ∎ where open ≈-Reasoning _ _

open id-nat-trans public

module composition-unit {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level}
  {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}}
  {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}}
  {F G : Functor C D}
  (Θ : NatTrans F G) where

  open Category D
  private
    F₀ = Functor.obj F
    G₀ = Functor.obj G
    Θ₀ = NatTrans.component Θ
    F₁ = λ {x} {y} f → Functor.homsets F {x} {y} f

  •̂-unit-l : idNatTrans G •̂ Θ ≈₂ Θ
  •̂-unit-l = make-≈₂ H where
    H : (x : Category.obj C) → _ ≈ _
    H x = begin
      id (G₀ x) • Θ₀ x
        ≈⟨ id-l (Θ₀ x) ⟩
      Θ₀ x ∎ where open ≈-Reasoning _ _

  •̂-unit-r : Θ •̂ idNatTrans F ≈₂ Θ
  •̂-unit-r = make-≈₂ H where
    H : (x : Category.obj C) → _ ≈ _
    H x = begin
      Θ₀ x • id (F₀ x) 
        ≈⟨ id-r (Θ₀ x) ⟩
      Θ₀ x ∎ where open ≈-Reasoning _ _

  ⊙̂-unit-l : (⊙-unitor-l G •̂ (idNatTrans (idFunctor D) ⊙̂ Θ)) •̂ ⊙-unitor-l⁻¹ F ≈₂ Θ
  ⊙̂-unit-l = make-≈₂ H where
    H : (x : Category.obj C) → _ ≈ _
    H x = begin
      (id (G₀ x) • (id (G₀ x) • Θ₀ x)) • id (F₀ x)
        ≈⟨ id-r _ ⟩
      id (G₀ x) • (id (G₀ x) • Θ₀ x)
        ≈⟨ id-l _ ⟩
      id (G₀ x) • Θ₀ x
        ≈⟨ id-l _ ⟩
      Θ₀ x ∎ where open ≈-Reasoning _ _

  ⊙̂-unit-r : (⊙-unitor-r G •̂ (Θ ⊙̂ idNatTrans (idFunctor C))) •̂ ⊙-unitor-r⁻¹ F ≈₂ Θ
  ⊙̂-unit-r = make-≈₂ H where
    H : (x : Category.obj C) → _ ≈ _
    H x = begin
      (id (G₀ x) • (Θ₀ x • F₁ (Category.id C x))) • id (F₀ x)
        ≈⟨ id-r _ ⟩
      id (G₀ x) • (Θ₀ x • F₁ (Category.id C x))
        ≈⟨ id-l _ ⟩
      Θ₀ x • F₁ (Category.id C x)
        ≈⟨ •-cong ≈-refl (Functor.id F x) ⟩
      Θ₀ x • id (F₀ x)
        ≈⟨ id-r _ ⟩
      Θ₀ x ∎ where open ≈-Reasoning _ _

open composition-unit public


module vertical-composition-associative {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level}
  {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}}
  {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}}
  {F G H K : Functor C D}
  (Ψ : NatTrans H K)
  (Φ : NatTrans G H)
  (Θ : NatTrans F G) where

  open Category D

  private
    Ψ₀ = NatTrans.component Ψ
    Φ₀ = NatTrans.component Φ
    Θ₀ = NatTrans.component Θ

  •̂-assoc : (Ψ •̂ Φ) •̂ Θ ≈₂ Ψ •̂ (Φ •̂ Θ)
  •̂-assoc = make-≈₂ (λ x → assoc (Ψ₀ x) (Φ₀ x) (Θ₀ x))

open vertical-composition-associative public



module horizontal-composition-associative {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ ℓ₄ ℓ′₄ ℓ″₄ : Level} 
  {B : Category {ℓ₁} {ℓ′₁} {ℓ″₁}}
  {C : Category {ℓ₂} {ℓ′₂} {ℓ″₂}}
  {D : Category {ℓ₃} {ℓ′₃} {ℓ″₃}}
  {E : Category {ℓ₄} {ℓ′₄} {ℓ″₄}}
  {H H′ : Functor D E} (Θ : NatTrans H H′)
  {G G′ : Functor C D} (Ψ : NatTrans G G′)
  {F F′ : Functor B C} (Φ : NatTrans F F′) where

  open Category E
  open Category D hiding (assoc ; id-r ; id-l ; •-cong ; ≈-refl ; ≈-sym ; module ≈-Reasoning ; _≈_) renaming (_•_ to _•′_ ; id to id-D)

  private
    Θ₀ = NatTrans.component Θ
    Ψ₀ = NatTrans.component Ψ
    Φ₀ = NatTrans.component Φ

    Θ-naturality = λ {x} {y} f → NatTrans.naturality Θ {x} {y} f
    Ψ-naturality = λ {x} {y} f → NatTrans.naturality Ψ {x} {y} f
    Φ-naturality = λ {x} {y} f → NatTrans.naturality Φ {x} {y} f

    F₀ = Functor.obj F
    F′₀ = Functor.obj F′
    G₀ = Functor.obj G
    G′₀ = Functor.obj G′
    H₀ = Functor.obj H
    H′₀ = Functor.obj H′

    F₁ = λ {x} {y} f → Functor.homsets F {x} {y} f 
    F′₁ = λ {x} {y} f → Functor.homsets F′ {x} {y} f
    G₁ = λ {x} {y} f → Functor.homsets G {x} {y} f
    G′₁ = λ {x} {y} f → Functor.homsets G′ {x} {y} f
    H₁ = λ {x} {y} f → Functor.homsets H {x} {y} f
    H′₁ = λ {x} {y} f → Functor.homsets H′ {x} {y} f

  ⊙̂-assoc : (Θ ⊙̂ Ψ) ⊙̂ Φ ≈₂ ⊙-associator⁻¹ H′ G′ F′ •̂ (Θ ⊙̂ Ψ ⊙̂ Φ) •̂ ⊙-associator H G F
  ⊙̂-assoc = make-≈₂ K where
    K : (x : Category.obj B) → _ ≈ _
    K x = begin
      (Θ₀ (G′₀ (F′₀ x)) • H₁ (Ψ₀ (F′₀ x))) • H₁ (G₁ (Φ₀ x))
        ≈⟨ assoc _ _ _ ⟩
      Θ₀ (G′₀ (F′₀ x)) • (H₁ (Ψ₀ (F′₀ x)) • H₁ (G₁ (Φ₀ x)))
        ≈⟨ •-cong ≈-refl (≈-sym (Functor.compose H _ _)) ⟩
      Θ₀ (G′₀ (F′₀ x)) • H₁ (Ψ₀ (F′₀ x) •′ G₁ (Φ₀ x))
        ≈⟨ ≈-sym (id-r _) ⟩
      (Θ₀ (G′₀ (F′₀ x)) • H₁ (Ψ₀ (F′₀ x) •′ G₁ (Φ₀ x))) • id (H₀ (G₀ (F₀ x)))
        ≈⟨ ≈-sym (id-l _) ⟩
      id (H′₀ (G′₀ (F′₀ x))) • ((Θ₀ (G′₀ (F′₀ x)) • H₁ (Ψ₀ (F′₀ x) •′ G₁ (Φ₀ x))) • id (H₀ (G₀ (F₀ x)))) ∎ where open ≈-Reasoning _ _

open horizontal-composition-associative public


module horizontal-composition-compatible {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} 
  {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}}
  {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}}
  {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}}
  {F F′ : Functor C D}
  {G G′ : Functor D E}
  {Ψ Ψ′ : NatTrans G G′}
  {Φ Φ′ : NatTrans F F′} where

  private
    F′₀ = Functor.obj F′
    F′₁ = Functor.obj F′
    G₁ = λ {x} {y} f → Functor.homsets G {x} {y} f

  open Category E

  ⊙̂-cong : Ψ ≈₂ Ψ′ → Φ ≈₂ Φ′ → Ψ ⊙̂ Φ ≈₂ Ψ′ ⊙̂ Φ′
  ⊙̂-cong (make-≈₂ eΦ) (make-≈₂ eΨ) = make-≈₂ (λ x → •-cong (eΦ (Functor.obj F′ x)) (Functor.hom-cong G (eΨ x)))
 
open horizontal-composition-compatible public


module interchange-law {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} 
  {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}}
  {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}}
  {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}}
  {F F′ F″ : Functor C D}
  {G G′ G″ : Functor D E}
  (Ψ′ : NatTrans G′ G″) (Ψ : NatTrans G G′)
  (Φ′ : NatTrans F′ F″) (Φ : NatTrans F F′) where

  private
    Ψ′₀ = NatTrans.component Ψ′
    Ψ₀ = NatTrans.component Ψ
    Φ′₀ = NatTrans.component Φ′
    Φ₀ = NatTrans.component Φ

    Ψ′-naturality = λ {x} {y} f → NatTrans.naturality Ψ′ {x} {y} f
    Ψ-naturality = λ {x} {y} f → NatTrans.naturality Ψ {x} {y} f
    Φ′-naturality = λ {x} {y} f → NatTrans.naturality Φ′ {x} {y} f
    Φ-naturality = λ {x} {y} f → NatTrans.naturality Φ {x} {y} f

    F₀ = Functor.obj F
    F′₀ = Functor.obj F′
    F″₀ = Functor.obj F″
    G₀ = Functor.obj G
    G′₀ = Functor.obj G′
    G″₀ = Functor.obj G″

    F₁ = λ {x} {y} f → Functor.homsets F {x} {y} f 
    F′₁ = λ {x} {y} f → Functor.homsets F′ {x} {y} f
    F″₁ = λ {x} {y} f → Functor.homsets F″ {x} {y} f
    G′₁ = λ {x} {y} f → Functor.homsets G′ {x} {y} f
    G₁ = λ {x} {y} f → Functor.homsets G {x} {y} f
    G″₁ = λ {x} {y} f → Functor.homsets G″ {x} {y} f

  open Category E
  open Category D hiding (≈-sym ; module ≈-Reasoning ; •-cong ; ≈-refl ; _≈_) renaming (_•_ to _•′_ ; assoc to assoc′)

  interchange : ((Ψ′ ⊙̂ Φ′) •̂ (Ψ ⊙̂ Φ)) ≈₂ ((Ψ′ •̂ Ψ) ⊙̂ (Φ′ •̂ Φ))

  interchange = make-≈₂ H where
    H : (x : Category.obj C) → _ ≈ _
    H x = begin
      (Ψ′₀ (F″₀ x) • G′₁ (Φ′₀ x)) • (Ψ₀ (F′₀ x) • G₁ (Φ₀ x))
        ≈⟨ ≈-sym (assoc _ _ _) ⟩
      ((Ψ′₀ (F″₀ x) • G′₁ (Φ′₀ x)) • Ψ₀ (F′₀ x)) • G₁ (Φ₀ x)
        ≈⟨ •-cong (assoc _ _ _) ≈-refl ⟩
      (Ψ′₀ (F″₀ x) • (G′₁ (Φ′₀ x) • Ψ₀ (F′₀ x))) • G₁ (Φ₀ x)
        ≈⟨ •-cong (•-cong ≈-refl (≈-sym (Ψ-naturality (Φ′₀ x)))) ≈-refl ⟩
      (Ψ′₀ (F″₀ x) • (Ψ₀ (F″₀ x) • G₁ (Φ′₀ x))) • G₁ (Φ₀ x)
        ≈⟨ •-cong (≈-sym (assoc _ _ _)) ≈-refl ⟩
      ((Ψ′₀ (F″₀ x) • Ψ₀ (F″₀ x)) • G₁ (Φ′₀ x)) • G₁ (Φ₀ x)
        ≈⟨ assoc _ _ _ ⟩
      (Ψ′₀ (F″₀ x) • Ψ₀ (F″₀ x)) • (G₁ (Φ′₀ x) • G₁ (Φ₀ x))
        ≈⟨ •-cong ≈-refl (≈-sym (Functor.compose G (Φ′₀ x) (Φ₀ x))) ⟩
      (Ψ′₀ (F″₀ x) • Ψ₀ (F″₀ x)) • (G₁ (Φ′₀ x •′ Φ₀ x)) ∎ where open ≈-Reasoning _ _

open interchange-law public
