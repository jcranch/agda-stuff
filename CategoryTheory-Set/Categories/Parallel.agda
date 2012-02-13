-- Categories consisting of two objects, and a set of morphisms between them.

module Categories.Parallel where

open import Level
open import Relation.Binary.PropositionalEquality as PropEq

open import Categories
open import Functors
open import NaturalTransformations


parallels : {ℓ : Level} → Set ℓ → Category

data parallel-obj : Set where
  source : parallel-obj
  target : parallel-obj

data parallel-hom {ℓ : Level} (A : Set ℓ) : parallel-obj → parallel-obj → Set ℓ where
  id-s : parallel-hom A source source
  id-t : parallel-hom A target target
  parallel-map : A → parallel-hom A source target

parallels A  = makeCat parallel-obj (parallel-hom A) id compose id-l id-r assoc where
  id : (x : parallel-obj) → parallel-hom A x x
  id source = id-s
  id target = id-t
  compose : {x y z : parallel-obj} (g : parallel-hom A y z) (f : parallel-hom A x y) → parallel-hom A x z
  compose g id-s = g
  compose id-t f = f
  id-l : {x y : parallel-obj} (f : parallel-hom A x y) → compose (id y) f ≡ f
  id-l id-s = refl
  id-l id-t = refl
  id-l (parallel-map y) = refl
  id-r : {x y : parallel-obj} (f : parallel-hom A x y) → compose f (id x) ≡ f
  id-r {source} f = refl
  id-r {target} id-t = refl
  assoc : {w x y z : parallel-obj} (h : parallel-hom A y z) (g : parallel-hom A x y) (f : parallel-hom A w x) → compose h (compose g f) ≡ compose (compose h g) f
  assoc id-s () id-t
  assoc (parallel-map _) () id-t
  assoc (parallel-map _) () (parallel-map _)
  assoc id-s () (parallel-map _)
  assoc h g id-s = refl
  assoc id-t id-t id-t = refl
  assoc id-t id-t (parallel-map y) = refl



parallels-functor : {ℓ ℓ₁ ℓ′₁ : Level} {A : Set ℓ} {C : Category {ℓ₁} {ℓ′₁}} {s t : Category.obj C} (h : A → Category.hom C s t) → Functor (parallels A) C
parallels-functor {A = A} {C = C} {s} {t} h = makeFunctor obj hom id compose where
  obj : parallel-obj → Category.obj C
  obj source = s
  obj target = t

  hom : {x y : Category.obj (parallels A)} → Category.hom (parallels A) x y → Category.hom C (obj x) (obj y)
  hom id-s = Category.id C s
  hom id-t = Category.id C t
  hom (parallel-map y) = h y

  id : (x : Category.obj (parallels A)) → hom (Category.id (parallels A) x) ≡ Category.id C (obj x)
  id source = refl
  id target = refl

  compose : {x y z : Category.obj (parallels A)} (g : Category.hom (parallels A) y z) (f : Category.hom (parallels A) x y) → hom (Category.compose (parallels A) g f) ≡ Category.compose C (hom g) (hom f)
  compose id-s id-s = PropEq.sym (Category.id-l C _)
  compose id-t id-t = PropEq.sym (Category.id-l C _)
  compose id-t (parallel-map y) = PropEq.sym (Category.id-l C _)
  compose (parallel-map y) id-s = PropEq.sym (Category.id-r C _)



parallels-nat-trans : {ℓ ℓ₁ ℓ′₁ : Level} {A : Set ℓ} {C : Category {ℓ₁} {ℓ′₁}}
  (F G : Functor (parallels A) C)
  (source₁ : Category.hom C (Functor.obj F source) (Functor.obj G source))
  (target₁ : Category.hom C (Functor.obj F target) (Functor.obj G target))
  (n : (a : A) → Category.compose C target₁ (Functor.hom F (parallel-map a)) ≡ Category.compose C (Functor.hom G (parallel-map a)) source₁) → NatTrans F G
parallels-nat-trans {A = A} {C = C} F G s₁ t₁ n = makeNatTrans component naturality where
  open ≡-Reasoning
  component : (x : Category.obj (parallels A)) → Category.hom C (Functor.obj F x) (Functor.obj G x)
  component source = s₁
  component target = t₁
  naturality : {x y : Category.obj (parallels A)} (f : Category.hom (parallels A) x y) → Category.compose C (component y) (Functor.hom F f) ≡ Category.compose C (Functor.hom G f) (component x)
  naturality id-s = naturality-for-identities F G source s₁
  naturality id-t = naturality-for-identities F G target t₁
  naturality (parallel-map y) = n y
