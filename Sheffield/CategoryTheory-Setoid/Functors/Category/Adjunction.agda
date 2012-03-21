module Sheffield.CategoryTheory-Setoid.Functors.Category.Adjunction where

open import Data.Product hiding (_×_ ; curry ; uncurry)
open import Function.Equality hiding (id)
open import Level

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Equivalence
open import Sheffield.CategoryTheory-Setoid.Categories.Equivalence.Properties
open import Sheffield.CategoryTheory-Setoid.Categories.Product hiding (proj₁ ; proj₂)
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Category
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality



homs-products : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level}
  (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁})
  (D : Category {ℓ₂} {ℓ′₂} {ℓ″₂})
  (E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}) → Functors (C × D) E ≅₀ Functors C (Functors D E)

homs-products C D E = make-≅₀ curry (assemble-equivalence curry curry-faithful curry-full curry-ess-surj) where

  curry : Functor (Functors (C × D) E) (Functors C (Functors D E))
  curry = makeFunctor obj hom id compose where
    obj : Functor (C × D) E → Functor C (Functors D E)
    obj F = makeFunctor O H I P where
      O : Category.obj C → Functor D E
      O x = makeFunctor o h (λ y → Functor.id F (x ,′ y)) (λ g f → Category.≈-trans E (Functor.hom-cong F (Category.≈-sym C (Category.id-l C _) ,′ Category.≈-refl D)) (Functor.compose F (Category.id C x ,′ g) (Category.id C x ,′ f))) where
        o : Category.obj D → Category.obj E
        o y = Functor.obj F (x ,′ y)
        h : {y₁ y₂ : Category.obj D} → Category.hom D y₁ y₂ ⟶ Category.hom E (o y₁) (o y₂)
        h {y₁} {y₂} = record {
          _⟨$⟩_ = λ f → Functor.homsets F (Category.id C x ,′ f) ;
          cong = λ {f} {f′} e → Functor.hom-cong F (Category.≈-refl C ,′ e) }
      H : {x₁ x₂ : Category.obj C} → Category.hom C x₁ x₂ ⟶ Category.hom (Functors D E) (O x₁) (O x₂)
      H {x₁} {x₂} = record {
        _⟨$⟩_ = λ f → makeNatTrans (λ y → Functor.homsets F (f ,′ Category.id D y)) (λ {y₁} {y₂} g → Category.≈-trans E (Category.≈-trans E (Category.≈-sym E (Functor.compose F _ _)) (Functor.hom-cong F (Category.≈-trans C (Category.id-r C _) (Category.≈-sym C (Category.id-l C _)) ,′ Category.≈-trans D (Category.id-l D _) (Category.≈-sym D (Category.id-r D _))))) (Functor.compose F _ _)) ;
        cong = λ {f} {f′} e → make-≈₂ (λ y → Functor.hom-cong F (e ,′ Category.≈-refl D)) }
      I : (x : Category.obj C) → _
      I x = make-≈₂ (λ y → Functor.id F _)

      P : {x₁ x₂ x₃ : Category.obj C} (g : Category.homset C x₂ x₃) (f : Category.homset C x₁ x₂) → _
      P {x₁} {x₂} {x₃} g f = make-≈₂ (λ y → Category.≈-trans E (Functor.hom-cong F (Category.≈-refl C ,′ Category.≈-sym D (Category.id-l D _))) (Functor.compose F _ _))

    hom : {x y : Category.obj (Functors (C × D) E)} → Category.hom (Functors (C × D) E) x y ⟶ Category.hom (Functors C (Functors D E)) (obj x) (obj y)
    hom {F} {G} = record {
      _⟨$⟩_ = λ Θ → makeNatTrans (λ x → makeNatTrans (λ y → NatTrans.component Θ (x , y)) (λ {y₁} {y₂} g → NatTrans.naturality Θ (Category.id C x , g))) (λ {x₁} {x₂} f → make-≈₂ (λ y → NatTrans.naturality Θ (f , Category.id D y)));
      cong = λ {Θ} {Φ} ε → make-≈₂ (λ x → make-≈₂ (λ y → _≈₂_.component-≈ ε (x ,′ y))) }

    id : (F : Functor (C × D) E) → _
    id F = make-≈₂ (λ x → make-≈₂ (λ y → Category.≈-refl E))

    compose : {F₁ F₂ F₃ : Functor (C × D) E} (Ψ : Category.homset (Functors (C × D) E) F₂ F₃) (Φ : Category.homset (Functors (C × D) E) F₁ F₂) → _
    compose {F₁} {F₂} {F₃} Ψ Φ = make-≈₂ (λ x → make-≈₂ (λ y → Category.≈-refl E))



  uncurry-objs : Functor C (Functors D E) → Functor (C × D) E
  uncurry-objs F = makeFunctor O H I P where
    open Category E

    O : Category.obj (C × D) → obj
    O (x , y) = Functor.obj (Functor.obj F x) y
    H : {p q : Category.obj (C × D)} → Category.hom (C × D) p q ⟶ hom (O p) (O q)
    H {x₁ , y₁} {x₂ , y₂} = record {
      _⟨$⟩_ = λ f → NatTrans.component (Functor.homsets F (proj₁ f)) y₂ • Functor.homsets (Functor.obj F x₁) (proj₂ f) ;
      cong = λ {f} {f′} e → •-cong (_≈₂_.component-≈ (Functor.hom-cong F (proj₁ e)) y₂) (Functor.hom-cong (Functor.obj F x₁) (proj₂ e)) }
    I : (x : Category.obj (C × D)) → _
    I (x , y) = ≈-trans (•-cong (_≈₂_.component-≈ (Functor.id F x) y) (Functor.id (Functor.obj F x) y)) (id-r _)
    P : {p₁ p₂ p₃ : Category.obj (C × D)} (F′ : Category.homset (C × D) p₂ p₃) (F : Category.homset (C × D) p₁ p₂) → _
    P {x₁ , y₁} {x₂ , y₂} {x₃ , y₃} (f′ , g′) (f , g) = ≈-trans (•-cong (_≈₂_.component-≈ (Functor.compose F f′ f) y₃) (Functor.compose (Functor.obj F x₁) g′ g)) (≈-trans (assoc _ _ _) (≈-trans (•-cong ≈-refl (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (•-cong (NatTrans.naturality (Functor.homsets F f) g′) ≈-refl) (assoc _ _ _)))) (≈-sym (assoc _ _ _))))


  uncurry-cong : {F G : Functor C (Functors D E)} (ε : Iso._≅_ (Functors C (Functors D E)) F G) → _
  uncurry-cong {F} {G} ε = Iso.make-iso (Functors (C × D) E) obv rev {!!} {!!} where
    open Category E

    obv : NatTrans (uncurry-objs F) (uncurry-objs G)
    obv = makeNatTrans cpt nat where
      cpt : (p : Category.obj (C × D)) → _
      cpt (x , y) = NatTrans.component (NatTrans.component (Iso._≅_.obverse _ ε) x) y
      nat : {p₁ p₂ : Category.obj (C × D)} (f : Category.homset (C × D) p₁ p₂) → _
      nat {x₁ , y₁} {x₂ , y₂} (f , g) = {!!}

    rev : NatTrans (uncurry-objs G) (uncurry-objs F)
    rev = makeNatTrans cpt nat where
      cpt : (p : Category.obj (C × D)) → _
      cpt p = NatTrans.component (NatTrans.component (Iso._≅_.reverse _ ε) (proj₁ p)) (proj₂ p)
      nat : {p₁ p₂ : Category.obj (C × D)} (f : Category.homset (C × D) p₁ p₂) → _
      nat {x₁ , y₁} {x₂ , y₂} (f , g) = {!!}



  curry-faithful : faithful curry
  curry-faithful = λ F G {Φ} {Ψ} ε → make-≈₂ (λ p → _≈₂_.component-≈ (_≈₂_.component-≈ ε (proj₁ p)) (proj₂ p))

  curry-full : full curry
  curry-full = λ F G → record {
    from = record {
      _⟨$⟩_ = λ Θ → makeNatTrans (λ p → NatTrans.component (NatTrans.component Θ (proj₁ p)) (proj₂ p)) (λ {p₁} {p₂} h → {!_≈₂_.component-≈ (NatTrans.naturality Θ (proj₁ h)) !});
      cong = λ {Φ} {Ψ} ε → {!!} };
    right-inverse-of = λ Θ → {!!} }

  curry-ess-surj : essentially-surjective curry
  curry-ess-surj = record {
    from = record {
      _⟨$⟩_ = uncurry-objs ;
      cong = uncurry-cong };
    right-inverse-of = λ F → {!!} }

