module Human.Equality where

open import Human.Bool
open import Human.Nat hiding (_==_)

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}

sym : {A : Set} (x : A) (y : A) -> x == y -> y == x
sym x .x refl = refl

cong : {A : Set} {B : Set} (x : A) (y : A) (f : A -> B) -> x == y -> f x == f y
cong x y f refl = refl

-- Check if two Nat are equal
eq-nat : (a b : Nat) → Bool
eq-nat zero    zero    = true
eq-nat zero    (suc b) = false
eq-nat (suc a) zero    = false
eq-nat (suc a) (suc b) = eq-nat a b
