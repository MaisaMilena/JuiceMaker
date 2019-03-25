module JuiceMaker where

open import Human.Nat hiding (_==_)
open import Human.List hiding (remove-last)
open import Human.Equality
open import Human.Maybe
open import Human.Bool
open import Human.Empty


data Ingredient : Set where
  orange    : Ingredient
  pineapple : Ingredient
  carrot    : Ingredient
  apple     : Ingredient
  beet      : Ingredient
  cabbage   : Ingredient

-- Tipo polimófico. Depende de 2 outros tipos
data Pair (A B : Set) : Set where
  pair : A -> B -> Pair A B -- construtor

data IsItem : Pair Nat Ingredient → Set where
   100-orange : IsItem (pair 100 orange)
   50-beet    : IsItem (pair 50 beet)

data Subset (A : Set) (IsOk : A -> Set) : Set where
    subset : (a : A) (b : IsOk a) -> Subset A IsOk

-- Criar um subset para verificar se uma lista de eventos é suficiente para fazer um suco, ou seja,
-- a lista é válida para criar um suco (canBecomeJuice)
-- 1. Criar a restrição: um tipo que depende de outro tipo (similiar ao IsItem)
-- 2. Criar o subset que só aceita lista de eventos que a soma das ml dos itens é igual a 300ml.
--    O nome dele pode ser OrderList, uma lista de ordens válidas para se fazer um suco


------ Item -------
Item : Set
Item = Subset (Pair Nat Ingredient) IsItem

100ml-orange : Item
100ml-orange = subset (pair 100 orange) 100-orange

50ml-beet : Item
50ml-beet = subset (pair 50 beet) 50-beet

-----
-- Get the ml quantity in an Item
get-ml-item : Item → Nat
get-ml-item (subset (pair ml ing) _) = ml

-- Get the ingredient in an Item
get-ingredient-item : (i : Item) → Ingredient
get-ingredient-item (subset (pair ml ing) _) = ing

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
event-list = pick 100ml-orange , pick 50ml-beet , pick 50ml-beet , pick 100ml-orange , end


qtd-juice : Nat
qtd-juice = sum-num-list (map get-ml-item (make event-list))

made-juice-has-300-ml-ex : (sum-num-list (map get-ml-item (make event-list))) == 300
made-juice-has-300-ml-ex = refl

-- I have a list but I don't have access to its members
-- I need someway to check if the sum of it's elements (that is not know), is equal to 5
-- [!] As I don't know the list, the result can be true or false
-- [!] How to proof it is true?
-- sum-list-test : (l : List Nat) → eq-nat (sum-num-list l) 5 == true
-- sum-list-test l =

sum-list-test : (l : List Nat) → (Nat → Nat → Bool) → Maybe Bool
sum-list-test l p = {!   !}

-- For all sum of ml in the items, the result must be 300
-- a Nat (value) is differente than a proof that this number will always be something
made-juice-has-300-ml : ∀ (events : List Event) → (sum-num-list (map get-ml-item (make events))) == 300
made-juice-has-300-ml events = {!   !}


made-juice-has-5-items : ∀ (events : List Event) → length (map get-ingredient-item (make events)) == 5
made-juice-has-5-items = {!   !}
