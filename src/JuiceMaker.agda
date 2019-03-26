module JuiceMaker where

open import Human.Nat hiding (_==_)
open import Human.List hiding (remove-last)
open import Human.Equality
open import Human.Maybe
open import Human.Empty

-- Define constructors of what are the types of ingredients available
data Ingredient : Set where
  orange    : Ingredient
  pineapple : Ingredient
  carrot    : Ingredient
  apple     : Ingredient
  beet      : Ingredient
  cabbage   : Ingredient

{- Pair is a polimorfic type (as is List). Depends on two types to create a type (Pair of something).
   Ex: Pair Nat Nat, Pair Nat Ingredient, Pair Bool Bool -}
data Pair (A B : Set) : Set where
  pair : A -> B -> Pair A B

-- TODO: perguntar o que é esse "record". Vi que assim não da pra usar da mesma maneira
-- record Pair (A B : Set) : Set where
--  field
--    first  : A
--    second : B
--    pair : A -> B -> Pair A B
--
-- getFirst : ∀ {A B} → Pair A B → A
-- getFirst = Pair.first


-- Create a subset. Also called sigma ...
data Subset (A : Set) (IsOk : A → Set) : Set where
  subset : (a : A) (b : IsOk a) → Subset A IsOk


----------------------------------------------------------------
------ Items -------
{- Restricts of which can be the pair of ingredients.
   Acts like a filter to create a subset of valid Pair Nat Ingredient -}
data IsItem : Pair Nat Ingredient → Set where
  100-orange    : IsItem (pair 100 orange)
  100-pineapple : IsItem (pair 100 pineapple)
  100-apple     : IsItem (pair 100 apple)
  50-beet       : IsItem (pair 50 beet)
  50-cabbage    : IsItem (pair 50 cabbage)
  50-carrot     : IsItem (pair 50 carrot)
  50-orange     : IsItem (pair 50 orange)

-- An Item is a subset of Pair Nat Ingredient that restricts its elements using IsItem filter
Item : Set
Item = Subset (Pair Nat Ingredient) IsItem

100ml-orange : Item
100ml-orange = subset (pair 100 orange) 100-orange

-- 100ml-pineapple : Item
-- 100ml-pineapple = ?

50ml-beet : Item
50ml-beet = subset (pair 50 beet) 50-beet

--- Auxiliars ---
-- Get the ml quantity in an Item
get-ml-item : Item → Nat
get-ml-item (subset (pair ml ing) _) = ml

-- Get the ingredient in an Item
get-ingredient-item : (i : Item) → Ingredient
get-ingredient-item (subset (pair ml ing) _) = ing

----------------------------------------------------------------
------ Juice -------
{- IsJuice is a filter indexed in List Item (receives a list of Item),
  restricts what can become a juice (a proof that it have 300ml),
  and returns an element of IsJuice, that is, a proof that it was approved to become a juice -}
data IsJuice : List Item → Set where
  juice : ∀ (l : List Item) → (sum (map get-ml-item l) == 300) -> IsJuice l

-- A Juice is a subset of List Item that restricts its elements using IsJuice filter
Juice : Set
Juice = Subset (List Item) IsJuice

----------------------------------------------------------------
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


-- Evaluates a list of events checking if it can become a juice
-- event-to-item : List Event -> List Item
-- event-to-item end          = end
-- event-to-item (pick x , e) = x , (event-to-item e) -- add element in the list and continues to look into List of Event
-- event-to-item (undo , e)   = remove-last (event-to-item e)
-- event-to-item (copy , e)   = copy-last (event-to-item e)
-- event-to-item (done , e)   = make e

default-items : List Item
default-items = 100ml-orange , 100ml-orange , 100ml-orange , end

default-juice : Juice
default-juice = subset default-items (juice default-items refl)

-- como eu acho que deveria ser
make : List Item -> Maybe Juice
make = {!   !}

-- pra satisfazer o chefe
-- make-always : List Item -> Juice
-- make-always items with make items
-- ... | yes items-is-juice = subset items (juice items-is-juice)
-- ... | no items           = default-juice



---------------
---- Test -----

test-list : Nat
test-list = (sum (1 , 2 , 3 , 4 , 5 , end))

event-list : List Event
event-list = pick 100ml-orange , pick 50ml-beet , pick 50ml-beet , pick 100ml-orange , end


-- qtd-juice : Nat
-- qtd-juice = sum (map get-ml-item (make event-list))

-- made-juice-has-300-ml-ex : (sum (map get-ml-item (make event-list))) == 300
-- made-juice-has-300-ml-ex = refl


-- For all sum of ml in the items, the result must be 300
-- a Nat (value) is different than a proof that this number will always be something
-- made-juice-has-300-ml : ∀ (events : List Event) → (sum (map get-ml-item (make events))) == 300
-- made-juice-has-300-ml events = {!   !}
--
--
-- made-juice-has-5-items : ∀ (events : List Event) → length (map get-ingredient-item (make events)) == 5
-- made-juice-has-5-items = {!   !}
