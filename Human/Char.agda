module Human.Char where

open import Human.Nat
open import Human.Bool

postulate Char : Set
{-# BUILTIN CHAR Char #-}

primitive
  primIsLower             : Char → Bool
  primIsDigit             : Char → Bool
  primIsAlpha             : Char → Bool
  primIsSpace             : Char → Bool
  primIsAscii             : Char → Bool
  primIsLatin1            : Char → Bool
  primIsPrint             : Char → Bool
  primIsHexDigit          : Char → Bool
  primToUpper primToLower : Char → Char
  primCharToNat           : Char → Nat
  primNatToChar           : Nat → Char
  primCharEquality        : Char → Char → Bool

-- {-# COMPILE JS primCharToNat = function(c) { return c.charCodeAt(0); } #-}
-- {-# COMPILE JS primNatToChar = function(c) { return JSON.stringify(c); } #-}
-- {-# COMPILE JS primCharEquality = function(c) { return function(d) { return c === d; }; } #-}
