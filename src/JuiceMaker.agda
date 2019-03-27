module JuiceMaker where

open import Human.Nat hiding (_==_)
open import Human.List hiding (remove-last)
open import Human.Equality
open import Human.Maybe
open import Human.Empty

Not : (P : Set) -> Set
Not P = P -> Empty

-- Different from Bool, shows an evidence of why the value is "yes" or "nop"
data Dec (P : Set) : Set where
  yes : P     -> Dec P
  nop : Not P -> Dec P

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

--Create a subset (or sigma).Receives a Set and a proof/filter to restricts what items can be part of a subset
data Subset (A : Set) (IsOk : A → Set) : Set where
  subset : (a : A) (b : IsOk a) → Subset A IsOk

----------------------------------------------------------------
------ Items -------
{- Restricts of which can be the pair of ingredients.
   Acts like a filter to create a subset of valid Pair Nat Ingredient -}
data IsItem : Pair Nat Ingredient → Set where
  100-orange    : IsItem (pair 100 orange)
  50-beet       : IsItem (pair 50 beet)

-- An Item is a subset of Pair Nat Ingredient that restricts its elements using IsItem filter
Item : Set
Item = Subset (Pair Nat Ingredient) IsItem

{- n: quantity of ml in an item
   i: a type of ingredient
   p: a proof that a Pair formed by n and i passed the "filter" of IsItem
   item-has-ml: returns a proof that an item has n ml -}
data ItemHasMl : (n : Nat) → (i : Item) → Set where
  item-has-ml : (n : Nat) (i : Ingredient) (p : IsItem (pair n i)) → ItemHasMl n (subset (pair n i) p)

--- Items ---
100ml-orange : Item
100ml-orange = subset (pair 100 orange) 100-orange

50ml-beet : Item
50ml-beet = subset (pair 50 beet) 50-beet

default-items : List Item
default-items = 100ml-orange , 100ml-orange , 100ml-orange , end


--- Auxiliar ---
-- Quantity of ml in an item and a proof that an item has n ml
get-ml-item : (i : Item) -> Subset Nat (λ n -> ItemHasMl n i)
get-ml-item (subset .(pair 100 orange) 100-orange) = subset 100 (item-has-ml 100 orange 100-orange)
get-ml-item (subset .(pair 50 beet) 50-beet)       = subset 50 (item-has-ml 50 beet 50-beet)

get-ml-item-aux : (i : Item) -> Subset Nat (λ n -> ItemHasMl n i) → Nat
get-ml-item-aux i (subset a b) = a

-- Get the ingredient in an Item
get-ingredient-item : (i : Item) → Ingredient
get-ingredient-item (subset (pair ml ing) _) = ing


----------------------------------------------------------------
------ Juice -------
{- This function helps to proof something about the ml in a list.
   n: quantity of ml in a list
   list: list of items
   empty-list-has-0ml: a proof that 0ml represents an empty list
   append-item-adds-ml: a proof that adding an item to a list, adds its ml to the result of list's ml
-}
data ListHasMl : (n : Nat) (list : List Item) → Set where
  empty-list-has-0ml  : ListHasMl 0 end
  -- receives ml in item, an item, ml is a list, a list. Also, a proof of ItemHasMl and ListHasMl
  append-item-adds-ml : ∀ it-ml it li-ml li → ItemHasMl it-ml it → ListHasMl li-ml li → ListHasMl (it-ml + li-ml) (it , li)

{- Get the quantity of ml in a list by returning the proof that n is the quantity of ml in a list.
   Obs: the second argument in Subset is something applied to n.
   λ is used to represents that something (ListhasMl) is applied to n. -}
get-ml-list : (list : List Item) -> Subset Nat (λ n → ListHasMl n list)
get-ml-list end = subset zero empty-list-has-0ml
get-ml-list (it , rest) with get-ml-item it | get-ml-list rest -- "with" acts similar to case, but opening values inside this case
get-ml-list (it , rest)
  | subset it-ml it-ml-pf
  | subset rest-ml rest-ml-pf
  = let sum-ml                 = it-ml + rest-ml
        append-list-has-sum-ml = append-item-adds-ml it-ml it rest-ml rest it-ml-pf rest-ml-pf
    in subset sum-ml append-list-has-sum-ml


  {- IsJuice is a filter indexed in List Item (receives a list of Item),
  restricts what can become a juice (a proof that it have 300ml),
  and returns an element of IsJuice, that is, a proof that it was approved to become a juice -}
data IsJuice : List Item → Set where
  juice : ∀ (l : List Item) → (ListHasMl 300 l) -> IsJuice l

-- A Juice is a subset of List Item that restricts its elements using IsJuice filter
Juice : Set
Juice = Subset (List Item) IsJuice

-- default-juice : Juice
-- default-juice = subset default-items (juice default-items refl)



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

-- Look into a list of events and return a list of items
event-to-item : List Event -> List Item
event-to-item end          = end
event-to-item (pick x , e) = x , (event-to-item e) -- add element in the list and continues to look into List of Event
event-to-item (undo , e)   = remove-last (event-to-item e)
event-to-item (copy , e)   = copy-last (event-to-item e)
event-to-item (done , e)   = event-to-item e

-- Given a list and a proof that the list has a quantity of ml, returns the ml
get-ml-list-aux : (l : List Item) → Subset Nat (λ n → ListHasMl n l) → Nat
get-ml-list-aux l (subset a b) = a


-- goal: Maybe (Subset (List (Subset (Pair Nat Ingredient) IsItem)) IsJuice)
make : List Item -> Maybe Juice
make end     = nothing
make (x , l) with make l
... | just m  =
      let it-ml = (get-ml-item-aux x (get-ml-item x)) -- quantity of ml in x
          li-ml = (get-ml-list-aux l (get-ml-list l)) --
          -- is-juice = subset l (juice l (append-item-aadds-ml it-ml x li-ml l (item-has-ml it-ml x) ? ))
          -- usar o get-ml-list pra provar que o suco tem 300 ml
          -- is-juice = subset l (juice l (get-ml-list l))
      in {!   !} -- just (subset l) (juice l is-juice))
... | nothing = nothing


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
