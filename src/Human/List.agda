module Human.List where

open import Human.Nat

infixr 5 _,_
data List {a} (A : Set a) : Set a where
  end : List A
  _,_ : (x : A) (xs : List A) → List A

{-# BUILTIN LIST List #-}

{-# COMPILE JS  List = function(x,v) { if (x.length < 1) { return v["[]"](); } else { return v["_∷_"](x[0], x.slice(1)); } } #-}
{-# COMPILE JS end = Array() #-}
{-# COMPILE JS _,_ = function (x) { return function(y) { return Array(x).concat(y); }; } #-}

foldr : ∀ {A : Set} {B : Set} → (A → B → B) → B → List A → B
foldr c n end       = n
foldr c n (x , xs) = c x (foldr c n xs)

length : ∀ {A : Set} → List A → Nat
length = foldr (λ a n → suc n) zero

-- TODO --
-- filter
-- reduce

-- Receives a function that transforms each element of A, a function A and a new list, B.
map : ∀ {A : Set} {B : Set} → (f : A → B) → List A → List B
map f end      = end
map f (x , xs) = (f x) , (map f xs) -- f transforms element x, return map to do a new transformation

-- Sum all numbers in a list
sum : List Nat → Nat
sum end     = zero
sum (x , l) = x + (sum l)

remove-last : ∀ {A : Set} → List A → List A
remove-last end     = end
remove-last (x , l) = l
