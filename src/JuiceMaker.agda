module JuiceMaker where

open import Human.Nat hiding (_==_)
open import Human.List hiding (remove-last)
open import Human.Equality
open import Human.Maybe
open import Human.Bool


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

-- Victor pediu pra implementar isso
-- A proof that both arguments belong to the same Set?
-- _===_ : ∀ {A : Set} (x : A) (y : A) → Set
-- _===_ x y = x === y

_===_ : ∀ {A : Set} (x : A) (y : A) → Set
_===_ x y = x == y


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
----- Events -----
data Event : Set where
  pick : Item -> Event
  undo : Event
  copy : Event -- add again the last element
  done : Event

remove-last : List Item → List Item
remove-last end     = end
remove-last (x , l) = l

copy-last : List Item → List Item
copy-last end     = end
copy-last (x , l) = x , x , l

-- Requisito: no final, a lista terá 300ml e 5 itens
make : List Event -> List Item
make end          = end
make (pick x , e) = x , (make e) -- add element in the list and continues to look into List of Event
make (undo , e)   = remove-last (make e)
make (copy , e)   = copy-last (make e)
make (done , e)   = make e


---------------
---- Test -----

test-list : Nat
test-list = (sum-num-list (1 , 2 , 3 , 4 , 5 , end))

event-list : List Event
event-list = (pick (pair 100 orange) , (pick (pair 100 carrot) , (pick (pair 100 orange) , end)))


qtd-juice : Nat
qtd-juice = sum-num-list (map get-ml-item (make event-list))

made-juice-has-300-ml-ex : (sum-num-list (map get-ml-item (make event-list))) === 300
made-juice-has-300-ml-ex = refl

-- I have a list but I don't have access to its members
-- I need someway to check if the sum of it's elements (that is not know), is equal to 5
-- [!] As I don't know the list, the result can be true or false
-- [!] How to proof it is true?
-- sum-list-test : (l : List Nat) → sum-num-list l == 5
-- sum-list-test l = {!   !}

sum-list-test : (sum-list : Nat) → (expected : Nat) → Bool
sum-list-test l e = {!   !}

-- For all sum of ml in the items, the result must be 300
-- a Nat (value) is differente than a proof that this number will always be something
-- [?] transforms into Maybe 300?
made-juice-has-300-ml : ∀ (events : List Event) → (sum-num-list (map get-ml-item (make events))) === 300
made-juice-has-300-ml events = {!   !}


-- made-juice-has-300-ml : (events : List Event) → (sum-num-list (map get-ml-item (make events))) === 300
-- made-juice-has-300-ml events = ?

made-juice-has-5-items : ∀ (events : List Event) → length (map get-ingredient-item (make events)) == 5
made-juice-has-5-items = {!   !}
