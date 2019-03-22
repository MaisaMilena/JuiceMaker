module JuiceMaker where

open import Human.Nat hiding (_==_)
open import Human.List
open import Human.Equality


data Ingredient : Set where
  orange    : Ingredient
  pineapple : Ingredient
  carrot    : Ingredient
  apple     : Ingredient
  beet      : Ingredient
  cabbage   : Ingredient

data Quantity : Set where
  100ml : Nat → Quantity
  50ml  : Nat → Quantity

  -- TODO: implement or import
  -- Pair : ∀ (A B : Set) → Set
  -- Pair A B = A → B →

data Pair (A B : Set) : Set where
  pair : A -> B -> Pair A B

-- data IngredientPair : Set where
--   100-orange : Pair 100 orange

-- Victor pediu pra implementar isso
-- _===_ : ∀ {A : Set} (x : A) (y : A) → Set
-- _===_ x y = .A

-- How to reduce on Nat
-- t: total accumulated, c: current value
-- reducer-nat : (c : Nat) {t : Nat} → Nat
-- reducer-nat c {t} = t + c

-- Receives a List of Nat, a reducer (total and current value) and returns the reduced total
-- reduce : List Nat → (Nat → Nat → Nat) → Nat
-- reduce end r        = zero
-- reduce (x , l)  r = reduce l r {!   !}


-- Sum all numbers in a list. Used to sum the ml in a juice
sum-el-list : List Nat → Nat
sum-el-list end     = zero
sum-el-list (x , l) = x + (sum-el-list l)


map : ∀ {A : Set} {B : Set} → (f : A → B) → List A → List B
map f xs = ?


------ Item -------
Item : Set
Item = (Pair Nat Ingredient)

100ml-orange : Item
100ml-orange = (pair 100 orange)

50ml-pineapple : Item
50ml-pineapple = (pair 50 pineapple)

-----
-- Get the ml quantity in an Item
get-ml-item : Item → Nat
get-ml-item (pair ml ing) = ml

-- Get the ingredient in an Item
get-ingredient-item : Item → Ingredient
get-ingredient-item (pair ml ing) = ing

------------------

data Event : Set where
  pick : Item -> Event
  undo : Event
  copy : Event
  done : Event

-- Requisito: no final, a lista terá 300ml e 5 itens
make : List Event -> List Item
make = {!   !}

made-juice-has-300-ml : ∀ (events : List Event) → sum-el-list (map get-ml-item (make events)) == 300
made-juice-has-300-ml = {!   !}

made-juice-has-5-items : ∀ (events : List Event) → length (map get-ingredient-item (make events)) == 5
made-juice-has-5-items = {!   !}


---------------
---- Test -----
test-list : Nat
test-list = (sum-el-list (1 , 2 , 3 , 4 , 5 , end))
