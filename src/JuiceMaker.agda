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
  50-beet       : IsItem (pair 50 beet)

-- An Item is a subset of Pair Nat Ingredient that restricts its elements using IsItem filter
Item : Set
Item = Subset (Pair Nat Ingredient) IsItem

100ml-orange : Item
100ml-orange = subset (pair 100 orange) 100-orange

data ItemHasMl : (n : Nat) → (i : Item) → Set where
  item-has-ml : (n : Nat) (i : Ingredient) (p : IsItem (pair n i)) → ItemHasMl n (subset (pair n i) p)
-- 100ml-pineapple : Item
-- 100ml-pineapple = ?

50ml-beet : Item
50ml-beet = subset (pair 50 beet) 50-beet

default-items : List Item
default-items = 100ml-orange , 100ml-orange , 100ml-orange , end

get-ml-item : (i : Item) -> Subset Nat (λ n -> ItemHasMl n i)
get-ml-item (subset .(pair 100 orange) 100-orange) = subset 100 (item-has-ml 100 orange 100-orange)
get-ml-item (subset .(pair 50 beet) 50-beet)       = subset 50 (item-has-ml 50 beet 50-beet)

-- Get the ingredient in an Item
get-ingredient-item : (i : Item) → Ingredient
get-ingredient-item (subset (pair ml ing) _) = ing


----------------------------------------------------------------

data ListHasMl : (n : Nat) (list : List Item) → Set where
  empty-list-has-0ml  : ListHasMl 0 end
  append-item-adds-ml : ∀ it-ml it li-ml li → ItemHasMl it-ml it → ListHasMl li-ml li → ListHasMl (it-ml + li-ml) (it , li)

-- subset: é um par que tem um numero natural (a quantidade de ml que tem na lista)
-- essa parte do λ diz que: n é um número e a parte da direita é uma prova de que esse número é a quantidade de ml da lista
get-ml-list : (list : List Item) -> Subset Nat (λ n → ListHasMl n list)
get-ml-list end = subset zero empty-list-has-0ml
get-ml-list (it , rest) with get-ml-item it | get-ml-list rest
get-ml-list (it , rest)
  | subset it-ml it-ml-pf
  | subset rest-ml rest-ml-pf
  = let sum-ml                 = it-ml + rest-ml
        append-list-has-sum-ml = append-item-adds-ml it-ml it rest-ml rest it-ml-pf rest-ml-pf
    in subset sum-ml append-list-has-sum-ml



------ Juice -------
{- IsJuice is a filter indexed in List Item (receives a list of Item),
  restricts what can become a juice (a proof that it have 300ml),
  and returns an element of IsJuice, that is, a proof that it was approved to become a juice -}
-- data IsJuice : List Item → Set where
--   juice : ∀ (l : List Item) → (ListHasMl 300 l) -> IsJuice l
--
-- -- A Juice is a subset of List Item that restricts its elements using IsJuice filter
-- Juice : Set
-- Juice = Subset (List Item) IsJuice
--
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



-- get-ml-proof : (n : Nat) (list : List Item) -> Dec (sum (map get-ml-item list) == n)
-- get-ml-proof zero end = yes refl
-- get-ml-proof (suc n) end = nop (λ ())
-- get-ml-proof n (subset .(pair 100 orange) 100-orange , list) = {!   !}
-- get-ml-proof n (subset .(pair 100 pineapple) 100-pineapple , list) = {!   !}
-- get-ml-proof n (subset .(pair 100 apple) 100-apple , list) = {!   !}
-- get-ml-proof n (subset .(pair 50 beet) 50-beet , list) = {!   !}
-- get-ml-proof n (subset .(pair 50 cabbage) 50-cabbage , list) = {!   !}
-- get-ml-proof n (subset .(pair 50 carrot) 50-carrot , list) = {!   !}
-- get-ml-proof n (subset .(pair 50 orange)  50-orange , list) = {!   !}

-- como eu acho que deveria ser
-- make : List Item -> Maybe Juice
-- make end     = nothing
-- make (x , l) with make l
-- ... | just juice  = {!   !}
-- ... | nothing = nothing

-- when checking that the pattern just has type
-- Maybe (Subset (List (Subset (Pair Nat Ingredient) IsItem)) IsJuice)




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
