module JuiceMaker where

open import Human.Nat
open import Human.List


data Ingredient : Set where
  orange    : Ingredient
  pineapple : Ingredient
  carrot    : Ingredient
  apple     : Ingredient
  beet      : Ingredient
  cabbage   : Ingredient

  -- TODO: implement or import
  -- Pair : ∀ (A B : Set) → Set
  -- Pair A B = A → B →

data Pair (A B : Set) : Set where
  pair : A -> B -> Pair A B

-- data IngredientPair : Set where
--   100-orange : Pair 100 orange



-- A proof that 2 elements belongs to the same Set
-- A set, a proof of x and y occuring in A
_===_ : ∀ {A : Set} (x : A) (y : A) → Set
_===_ x y = .A

sum : List Nat → Nat
sum = {!   !}

map : ∀ {A : Set} {B : Set} → (f : A → B) → List A → List B
map f xs = {!   !}



Item : Set
Item = (Pair Nat Ingredient)

get-ml : Item → Nat
get-ml = {!   !}

get-ingredient : Item → Ingredient
get-ingredient = {!   !}

data Event : Set where
  pick : Item -> Event
  undo : Event
  copy : Event
  done : Event

-- Requisito: no final, a lista terá 300ml e 5 itens
make : List Event -> List Item
make = {!   !}

made-juice-has-300-ml : ∀ (events : List Event) → sum (map get-ml (make events)) === 300
made-juice-has-300-ml = {!   !}

made-juice-has-5-items : ∀ (events : List Event) → length (map get-ingredient (make events)) === 5
made-juice-has-5-items = {!   !}
