{-# OPTIONS --without-K --safe #-}

module Data.Setoid where

open import Relation.Binary using (Setoid)
open import Function.Construct.Setoid using () renaming (setoid to infixr 0 _⇒ₛ_) public

open Setoid renaming (Carrier to ∣_∣) public
