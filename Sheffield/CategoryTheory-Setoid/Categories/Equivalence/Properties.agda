module Sheffield.CategoryTheory-Setoid.Categories.Equivalence.Properties where

open import Function.Equality hiding (id)
open import Function.Injection hiding (id)
open import Function.Surjection hiding (id)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Equivalence
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism.Properties
open import Sheffield.CategoryTheory-Setoid.Functors.Properties
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality



module equivalence-properties-1 {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F : Functor C D) (eF : Equivalence₀ F) where

  open Equivalence₀ eF
  private
    G = reverse

  equivalence-faithful : faithful F
  equivalence-faithful x y e = ≅₁-morphisms unit (Functor.hom-cong G e)

open equivalence-properties-1 public


module equivalence-properties-2 {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F : Functor C D) (eF : Equivalence₀ F) where

  open Equivalence₀ eF
  open Category C
  open Category D using () renaming (obj to obj′ ; homset to homset′ ; _≈_ to _≈′_ ; _•_ to _•′_)

  private
    G = reverse
    eG = Equivalence₀-sym eF
    F₀ = Functor.obj F
    G₀ = Functor.obj G
    F₁ = λ {i} {j} → Functor.homsets F {i} {j}
    G₁ = λ {i} {j} → Functor.homsets G {i} {j}
    Φ = _≅₁_.obverse unit
    Ψ = _≅₁_.reverse unit
    Φ₀ = NatTrans.component Φ
    Ψ₀ = NatTrans.component Ψ

    Φ-lemma : (x : Category.obj C) → Φ₀ (G₀ (F₀ x)) ≈ G₁ (F₁ (Φ₀ x))
    Φ-lemma x = begin
      Φ₀ (G₀ (F₀ x))
        ≈⟨ ≈-sym (id-l _) ⟩
      id _ • Φ₀ (G₀ (F₀ x))
        ≈⟨ •-cong (≈-sym (_≈₂_.component-≈ ( _≅₁_.unit unit) _)) ≈-refl ⟩
      (Ψ₀ x • Φ₀ x) • Φ₀ (G₀ (F₀ x))
        ≈⟨ assoc _ _ _ ⟩
      Ψ₀ x • (Φ₀ x • Φ₀ (G₀ (F₀ x)))
        ≈⟨ •-cong ≈-refl (≈-sym (NatTrans.naturality Φ (Φ₀ x))) ⟩
      Ψ₀ x • (Φ₀ x • G₁ (F₁ (Φ₀ x)))
        ≈⟨ ≈-sym (assoc _ _ _) ⟩
      (Ψ₀ x • Φ₀ x) • G₁ (F₁ (Φ₀ x))
        ≈⟨ •-cong (_≈₂_.component-≈ ( _≅₁_.unit unit) _) ≈-refl ⟩
      id _ • G₁ (F₁ (Φ₀ x))
        ≈⟨ id-l _ ⟩
      G₁ (F₁ (Φ₀ x)) ∎ where open ≈-Reasoning _ _

    Ψ-lemma : (x : Category.obj C) → Ψ₀ (G₀ (F₀ x)) ≈ G₁ (F₁ (Ψ₀ x))
    Ψ-lemma x = begin
      Ψ₀ (G₀ (F₀ x))
        ≈⟨ ≈-sym (id-r _) ⟩
      Ψ₀ (G₀ (F₀ x)) • id _
        ≈⟨ •-cong ≈-refl (≈-sym (_≈₂_.component-≈ ( _≅₁_.unit unit) _)) ⟩
      Ψ₀ (G₀ (F₀ x)) • (Ψ₀ x • Φ₀ x)
        ≈⟨ ≈-sym (assoc _ _ _) ⟩
      (Ψ₀ (G₀ (F₀ x)) • Ψ₀ x) • Φ₀ x
        ≈⟨ •-cong (NatTrans.naturality Ψ (Ψ₀ x)) ≈-refl ⟩
      (G₁ (F₁ (Ψ₀ x)) • Ψ₀ x) • Φ₀ x
        ≈⟨ assoc _ _ _ ⟩
      G₁ (F₁ (Ψ₀ x)) • (Ψ₀ x • Φ₀ x)
        ≈⟨ •-cong ≈-refl (_≈₂_.component-≈ (_≅₁_.unit unit) _) ⟩
      G₁ (F₁ (Ψ₀ x)) • id _
        ≈⟨ id-r _ ⟩
      G₁ (F₁ (Ψ₀ x)) ∎ where open ≈-Reasoning _ _

    rio′ : {x y : obj} (f : homset′ (F₀ x) (F₀ y)) → G₁ (F₁ (Φ₀ y • G₁ f • Ψ₀ x)) ≈ G₁ f
    rio′ {x} {y} f = begin
      G₁ (F₁ (Φ₀ y • G₁ f • Ψ₀ x))
        ≈⟨ Functor.hom-cong G (Functor.compose F _ _) ⟩
      G₁ (F₁ (Φ₀ y) •′ F₁ (G₁ f • Ψ₀ x))
        ≈⟨ Functor.compose G _ _ ⟩
      G₁ (F₁ (Φ₀ y)) • G₁ (F₁ (G₁ f • Ψ₀ x))
        ≈⟨ •-cong ≈-refl (Functor.hom-cong G (Functor.compose F _ _)) ⟩
      G₁ (F₁ (Φ₀ y)) • G₁ (F₁ (G₁ f) •′ F₁ (Ψ₀ x))
        ≈⟨ •-cong ≈-refl (Functor.compose G _ _) ⟩
      G₁ (F₁ (Φ₀ y)) • G₁ (F₁ (G₁ f)) • G₁ (F₁ (Ψ₀ x))
        ≈⟨ •-cong ≈-refl (•-cong ≈-refl (≈-sym (Ψ-lemma x))) ⟩
      G₁ (F₁ (Φ₀ y)) • G₁ (F₁ (G₁ f)) • Ψ₀ (G₀ (F₀ x))
        ≈⟨ •-cong (≈-sym (Φ-lemma y)) (≈-sym (NatTrans.naturality Ψ (G₁ f))) ⟩
      Φ₀ (G₀ (F₀ y)) • (Ψ₀ (G₀ (F₀ y)) • G₁ f)
        ≈⟨ ≈-sym (assoc _ _ _) ⟩
      (Φ₀ (G₀ (F₀ y)) • Ψ₀ (G₀ (F₀ y))) • G₁ f
        ≈⟨ •-cong (_≈₂_.component-≈ (_≅₁_.counit unit) (G₀ (F₀ y))) ≈-refl ⟩
      id _ • G₁ f
        ≈⟨ id-l _ ⟩
      G₁ f ∎ where open ≈-Reasoning _ _

    rio : {x y : obj} (f : homset′ (F₀ x) (F₀ y)) → F₁ (Φ₀ y • G₁ f • Ψ₀ x) ≈′ f
    rio {x} {y} f = equivalence-faithful G eG (F₀ x) (F₀ y) (rio′ f)

  equivalence-full : full F
  equivalence-full x y = record {
    from = record {
      _⟨$⟩_ = λ f → Φ₀ y • Functor.homsets G f • Ψ₀ x;
      cong = λ {f} {g} e → •-cong ≈-refl (•-cong (Functor.hom-cong G e) ≈-refl) };
    right-inverse-of = rio }

  equivalence-essentially-surjective : essentially-surjective F
  equivalence-essentially-surjective = record {
    from = record {
      _⟨$⟩_ = Functor.obj G;
      cong = Functor.on-≅ G };
    right-inverse-of = ≅₁-≅ counit }

open equivalence-properties-2 public


module equivalence-properties-3 {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level}
  {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}}
  (F : Functor C D)
  (faF : faithful F)
  (fuF : full F)
  (eF : essentially-surjective F) where

  open Category C renaming (obj to obj′ ; hom to hom′ ; homset to homset′ ; _≈_ to _≈′_ ; _•_ to _•′_ ; •-cong to •′-cong ; ≈-refl to ≈′-refl ; ≈-sym to ≈′-sym ; ≈-trans to ≈′-trans ; id-l to id′-l ; id-r to id′-r ; module ≈-Reasoning to ≈′-Reasoning ; id to id′ ; assoc to assoc′)
  open Category D
  open Iso D

  assemble-equivalence : Equivalence₀ F

  assemble-equivalence = make-Equiv₀ F⁻¹ unit counit where
    deconcat : {u v w x y z : obj} (δ : homset y z) (g : homset x y) (γ : homset w x) (β : homset x w) (f : homset v x) (α : homset u v) → γ • β ≈ id x → (δ • g • γ) • (β • f • α) ≈ δ • (g • f) • α
    deconcat {u} {v} {w} {x} {y} {z} δ g γ β f α e = begin
      (δ • g • γ) • (β • f • α)
        ≈⟨ •-cong (≈-sym (assoc _ _ _)) ≈-refl ⟩
      ((δ • g) • γ) • (β • (f • α))
        ≈⟨ assoc _ _ _ ⟩
      (δ • g) • (γ • (β • (f • α)))
        ≈⟨ •-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
      (δ • g) • (γ • β) • (f • α)
        ≈⟨ •-cong ≈-refl (•-cong e ≈-refl) ⟩
      (δ • g) • id x • (f • α)
        ≈⟨ •-cong ≈-refl (id-l _) ⟩
      (δ • g) • (f • α)
        ≈⟨ assoc _ _ _ ⟩
      δ • (g • (f • α))
        ≈⟨ •-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
      δ • (g • f) • α ∎ where open ≈-Reasoning u z

    F⁻¹ : Functor D C
    F⁻¹ = makeFunctor o h i c where
      o = _⟨$⟩_ (Surjective.from eF)

      h : {x y : obj} → hom x y ⟶ hom′ (o x) (o y)
      h {x} {y} = record {
        _⟨$⟩_ = λ f → Surjective.from (fuF (o x) (o y)) ⟨$⟩ _≅_.reverse (Surjective.right-inverse-of eF y) • f • _≅_.obverse (Surjective.right-inverse-of eF x) ;
        cong = λ {f₁} {g₁} e → cong (Surjective.from (fuF (o x) (o y))) (•-cong ≈-refl (•-cong e ≈-refl)) }

      i : (x : obj) → _
      i x = faF (Surjective.from eF ⟨$⟩ x) (Surjective.from eF ⟨$⟩ x) (≈-trans (Surjective.right-inverse-of (fuF (o x) (o x)) _) (≈-trans (•-cong ≈-refl (id-l _)) (≈-trans (_≅_.unit (Surjective.right-inverse-of eF x)) (≈-sym (Functor.id F _)))))

      c : {x y z : obj} (g : homset y z) (f : homset x y) → _
      c {x} {y} {z} g f = faF (Surjective.from eF ⟨$⟩ x) (Surjective.from eF ⟨$⟩ z) (≈-trans (Surjective.right-inverse-of (fuF _ _) _) (≈-trans (≈-trans (≈-sym (deconcat _ _ _ _ _ _ (_≅_.counit (Surjective.right-inverse-of eF y)))) (≈-sym (•-cong (Surjective.right-inverse-of (fuF _ _) _) (Surjective.right-inverse-of (fuF _ _) _)))) (≈-sym (Functor.compose F _ _))))

    unit : F⁻¹ ⊙ F ≅₁ idFunctor C
    unit = isomorphic₁ Φ Ψ u c where
      Φ : NatTrans (F⁻¹ ⊙ F) (idFunctor C)
      Φ = makeNatTrans (λ x → Surjective.from (fuF _ _) ⟨$⟩ _≅_.obverse (Surjective.right-inverse-of eF (Functor.obj F x))) (λ {x} {y} f → faF _ _ (≈-trans (Functor.compose F _ _) (≈-trans (•-cong (Surjective.right-inverse-of (fuF _ _) _) (Surjective.right-inverse-of (fuF _ _) _)) (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (•-cong (_≅_.counit (Surjective.right-inverse-of eF (Functor.obj F y))) (•-cong ≈-refl (≈-sym (Surjective.right-inverse-of (fuF _ _) _)))) (≈-trans (id-l _) (≈-sym (Functor.compose F _ _))))))))
      Ψ : NatTrans (idFunctor C) (F⁻¹ ⊙ F)
      Ψ = makeNatTrans (λ x → Surjective.from (fuF _ _) ⟨$⟩ _≅_.reverse (Surjective.right-inverse-of eF (Functor.obj F x))) (λ {x} {y} f → faF _ _ (≈-trans (Functor.compose F _ _) (≈-trans (•-cong (Surjective.right-inverse-of (fuF _ _) _) ≈-refl) (≈-trans (≈-trans (≈-trans (•-cong ≈-refl (≈-trans (≈-trans (≈-sym (id-r _)) (•-cong ≈-refl (≈-sym (_≅_.counit (Surjective.right-inverse-of eF (Functor.obj F x)))))) (≈-sym (assoc _ _ _)))) (≈-sym (assoc _ _ _))) (≈-sym (•-cong (Surjective.right-inverse-of (fuF _ _) _) (Surjective.right-inverse-of (fuF _ _) _)))) (≈-sym (Functor.compose F _ _))))))
      u : Ψ •̂ Φ ≈₂ idNatTrans (F⁻¹ ⊙ F)
      u = make-≈₂ (λ x → faF _ _ (≈-trans (Functor.compose F _ _) (≈-trans (•-cong (Surjective.right-inverse-of (fuF _ _) _) (Surjective.right-inverse-of (fuF _ _) _)) (≈-trans (_≅_.unit (Surjective.right-inverse-of eF (Functor.obj F x))) (≈-sym (Functor.id F _))))))
      c : Φ •̂ Ψ ≈₂ idNatTrans (idFunctor C)
      c = make-≈₂ (λ x → faF _ _ (≈-trans (Functor.compose F _ _) (≈-trans (•-cong (Surjective.right-inverse-of (fuF _ _) _) (Surjective.right-inverse-of (fuF _ _) _)) (≈-trans (_≅_.counit (Surjective.right-inverse-of eF (Functor.obj F x))) (≈-sym (Functor.id F _))))))

    counit : F ⊙ F⁻¹ ≅₁ idFunctor D
    counit = isomorphic₁ Φ Ψ u c where
      Φ : NatTrans (F ⊙ F⁻¹) (idFunctor D)
      Φ = makeNatTrans (λ x → _≅_.obverse (Surjective.right-inverse-of eF x)) (λ {x} {y} f → ≈-trans (•-cong ≈-refl (Surjective.right-inverse-of (fuF _ _) _)) (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (•-cong (_≅_.counit (Surjective.right-inverse-of eF y)) ≈-refl) (id-l _))))
      Ψ : NatTrans (idFunctor D) (F ⊙ F⁻¹)
      Ψ = makeNatTrans (λ x → _≅_.reverse (Surjective.right-inverse-of eF x)) (λ {x} {y} f → ≈-sym (≈-trans (•-cong (Surjective.right-inverse-of (fuF _ _) _) ≈-refl) (≈-trans (assoc _ _ _) (•-cong ≈-refl (≈-trans (assoc _ _ _) (≈-trans (•-cong ≈-refl (_≅_.counit (Surjective.right-inverse-of eF x))) (id-r _)))))))
      u : Ψ •̂ Φ ≈₂ idNatTrans (F ⊙ F⁻¹)
      u = make-≈₂ (λ x → _≅_.unit (Surjective.right-inverse-of eF x))
      c : Φ •̂ Ψ ≈₂ idNatTrans (idFunctor D)
      c = make-≈₂ (λ x → _≅_.counit (Surjective.right-inverse-of eF x))

open equivalence-properties-3 public