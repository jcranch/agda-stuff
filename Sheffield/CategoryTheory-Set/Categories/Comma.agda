module Sheffield.CategoryTheory-Set.Categories.Comma where

open import Level
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.NaturalTransformations


module comma-category {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level} {A : Category {ℓ₁} {ℓ′₁}} {B : Category {ℓ₂} {ℓ′₂}} {C : Category {ℓ₃} {ℓ′₃}} (F : Functor A C) (G : Functor B C) where

  open Category A renaming (obj to objA ; hom to homA ; id to idA ; id-l to id-lA ; id-r to id-rA ; assoc to assocA ; compose to composeA ; _•_ to _•ˡ_)
  open Category B renaming (obj to objB ; hom to homB ; id to idB ; id-l to id-lB ; id-r to id-rB ; assoc to assocB ; compose to composeB ; _•_ to _•ʳ_)
  open Category C renaming (obj to objC ; hom to homC ; id to idC ; id-l to id-lC ; id-r to id-rC ; assoc to assocC ; compose to composeC)

  open Functor F renaming (obj to F₀ ; hom to F₁ ; id to idF ; compose to composeF)
  open Functor G renaming (obj to G₀ ; hom to G₁ ; id to idG ; compose to composeG)

  record obj : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₃) where
    constructor [_,_,_]

    field
      s : objA
      t : objB
      f : homC (F₀ s) (G₀ t)

  record hom (X₁ : obj) (X₂ : obj) : Set (ℓ′₁ ⊔ ℓ′₂ ⊔ ℓ′₃) where
    constructor make-hom

    s₁ = obj.s X₁
    t₁ = obj.t X₁
    f₁ = obj.f X₁
    s₂ = obj.s X₂
    t₂ = obj.t X₂
    f₂ = obj.f X₂

    field
      mor₁  : homA s₁ s₂
      mor₂  : homB t₁ t₂
      eq  : G₁ mor₂ • f₁ ≡ f₂ • F₁ mor₁

  hom-≡ : {X₁ X₂ : obj} (F₁ F₂ : hom X₁ X₂) → hom.mor₁ F₁ ≡ hom.mor₁ F₂ → hom.mor₂ F₁ ≡ hom.mor₂ F₂ → F₁ ≡ F₂
  hom-≡ (make-hom mor₁ mor₂ eq) (make-hom .mor₁ .mor₂ eq′) refl refl = cong (make-hom mor₁ mor₂) (proof-irrelevance eq eq′)

  id : (x : obj) → hom x x
  id [ s , t , f ] = make-hom (idA s) (idB t) e where
    open ≡-Reasoning
    e = begin
      G₁ (idB t) • f
        ≡⟨ cong (λ x → x • f) (idG t) ⟩
      idC (G₀ t) • f
        ≡⟨ id-lC f ⟩
      f
        ≡⟨ sym (id-rC f) ⟩
      f • idC (F₀ s)
        ≡⟨ cong (_•_ f) (sym (idF s)) ⟩
      f • F₁ (idA s) ∎

  compose : {x y z : obj} → hom y z → hom x y → hom x z
  compose {[ s₁ , t₁ , f₁ ]} {[ s₂ , t₂ , f₂ ]} {[ s₃ , t₃ , f₃ ]} (make-hom g′ h′ e′) (make-hom g h e) = make-hom (g′ •ˡ g) (h′ •ʳ h) e″ where
    open ≡-Reasoning
    e″ = begin
      G₁ (h′ •ʳ h) • f₁
        ≡⟨ cong (λ x → x • f₁) (Functor.compose G h′ h) ⟩
      (G₁ h′ • G₁ h) • f₁
        ≡⟨ sym (assocC (G₁ h′) (G₁ h) f₁) ⟩
      G₁ h′ • (G₁ h • f₁)
        ≡⟨ cong (λ x → G₁ h′ • x) e ⟩
      G₁ h′ • (f₂ • F₁ g)
        ≡⟨ assocC (G₁ h′) f₂ (F₁ g) ⟩
      (G₁ h′ • f₂) • F₁ g
        ≡⟨ cong (λ x → x • F₁ g) e′ ⟩
      (f₃ • F₁ g′) • F₁ g
        ≡⟨ sym (assocC f₃ (F₁ g′) (F₁ g)) ⟩
      f₃ • (F₁ g′ • F₁ g)
        ≡⟨ cong (_•_ f₃) (sym (Functor.compose F g′ g)) ⟩
      f₃ • F₁ (g′ •ˡ g) ∎

  id-l : {x y : obj} (f : hom x y) → compose (id y) f ≡ f
  id-l {[ s₁ , t₁ , f₁ ]} {[ s₂ , t₂ , f₂ ]} (make-hom g h e) = hom-≡ (compose (id [ s₂ , t₂ , f₂ ]) (make-hom g h e)) (make-hom g h e) (id-lA g) (id-lB h)

  id-r : {x y : obj} (f : hom x y) → compose f (id x) ≡ f
  id-r {[ s₁ , t₁ , f₁ ]} {[ s₂ , t₂ , f₂ ]} (make-hom g h e) = hom-≡ (compose (make-hom g h e) (id [ s₁ , t₁ , f₁ ])) (make-hom g h e) (id-rA g) (id-rB h)

  assoc : {w x y z : obj} (h : hom y z) (g : hom x y) (f : hom w x) → compose h (compose g f) ≡ compose (compose h g) f
  assoc {[ s₁ , t₁ , f₁ ]} {[ s₂ , t₂ , f₂ ]} {[ s₃ , t₃ , f₃ ]} {[ s₄ , t₄ , f₄ ]} (make-hom g″ f″ e″) (make-hom g′ f′ e′) (make-hom g f e) = hom-≡ (compose (make-hom g″ f″ e″) (compose (make-hom g′ f′ e′) (make-hom g f e))) (compose (compose (make-hom g″ f″ e″) (make-hom g′ f′ e′)) (make-hom g f e)) (assocA g″ g′ g) (assocB f″ f′ f)

  Comma : Category {ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₃} {ℓ′₁ ⊔ ℓ′₂ ⊔ ℓ′₃}
  Comma = makeCat obj hom id compose id-l id-r assoc

  Proj₁ : Functor Comma A
  Proj₁ = makeFunctor (λ x → obj.s x) (λ f → hom.mor₁ f) (λ _ → refl) (λ _ _ → refl)

  Proj₂ : Functor Comma B
  Proj₂ = makeFunctor (λ x → obj.t x) (λ f → hom.mor₂ f) (λ _ → refl) (λ _ _ → refl)

  -- the fundamental natural transformation
  Proj₁₂ : NatTrans (F ⊙ Proj₁) (G ⊙ Proj₂)
  Proj₁₂ = makeNatTrans component naturality where
    component : (x : obj) → homC (Functor.obj (F ⊙ Proj₁) x) (Functor.obj (G ⊙ Proj₂) x)
    component [ s , t , f ] = f
    naturality : {x y : obj} (f : hom x y) → component y • Functor.hom (F ⊙ Proj₁) f ≡ Functor.hom (G ⊙ Proj₂) f • component x
    naturality (make-hom mor₁ mor₂ eq) = sym eq

open comma-category public using (Comma ; Proj₁ ; Proj₂ ; Proj₁₂)

_↓_ : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level} {A : Category {ℓ₁} {ℓ′₁}} {B : Category {ℓ₂} {ℓ′₂}} {C : Category {ℓ₃} {ℓ′₃}} (F : Functor A C) (G : Functor B C) → Category {ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₃} {ℓ′₁ ⊔ ℓ′₂ ⊔ ℓ′₃}
_↓_ = Comma

{-
module comma-category-naturality
  {ℓ₁₁ ℓ′₁₁ ℓ₂₁ ℓ′₂₁ ℓ₃₁ ℓ′₃₁ ℓ₁₂ ℓ′₁₂ ℓ₂₂ ℓ′₂₂ ℓ₃₂ ℓ′₃₂ : Level}
  {A₁ : Category {ℓ₁₁} {ℓ′₁₁}} {B₁ : Category {ℓ₂₁} {ℓ′₂₁}} {C₁ : Category {ℓ₃₁} {ℓ′₃₁}}
  {A₂ : Category {ℓ₁₂} {ℓ′₁₂}} {B₂ : Category {ℓ₂₂} {ℓ′₂₂}} {C₂ : Category {ℓ₃₂} {ℓ′₃₂}}
  (F₁ : Functor A₁ C₁) (G₁ : Functor B₁ C₁)
  (F₂ : Functor A₂ C₂) (G₂ : Functor B₂ C₂)
  (HA : Functor A₁ A₂) (HB : Functor B₁ B₂) (HC : Functor C₁ C₂)
  (Φ : NatTrans (F₂ ⊙ HA) (HC ⊙ F₁))
  (Ψ : NatTrans (HC ⊙ G₁) (G₂ ⊙ HB)) where

  open comma-category F₁ G₁ renaming ([_,_,_] to [_,_,_]₁)
  open comma-category F₂ G₂ renaming ([_,_,_] to [_,_,_]₂)

  open Category C₂

  HA₀ = Functor.obj HA
  HB₀ = Functor.obj HB
  HC₁ = Functor.hom HC
  Φ₀ = NatTrans.component Φ
  Ψ₀ = NatTrans.component Ψ

  ↓-natural : Functor (F₁ ↓ G₁) (F₂ ↓ G₂)
  ↓-natural = makeFunctor {!!} {!!} {!!} {!!} where
    obj′ : Category.obj (F₁ ↓ G₁) → Category.obj (F₂ ↓ G₂)
    obj′ [ x , y , f ]₁ = [ HA₀ x , HB₀ y , (Φ₀ x) • (HC₁ f) • (Ψ₀ y) ]₂

open comma-category-naturality public using (↓-natural)
-}

-- one could also show that, given composable diagrams as above, the induced functors agree up to natural equality...