module Human.Maybe where

data Maybe (A : Set) : Set where
  just    : Maybe A
  nothing : A -> Maybe A
