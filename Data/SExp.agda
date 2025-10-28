{-# OPTIONS --without-K --safe #-}

module Data.SExp where

open import Data.List using (List)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Show using () renaming (show to showNat)
open import Data.String.Base as String using (String; parens; intersperse; _<+>_)

open List

module ListBased where

  data SExp : Set where
    Atom : String → SExp
    Nat : ℕ → SExp
    SExps : List SExp → SExp

  mutual
    showSExp : SExp → String
    showSExp (Atom s)   = s
    showSExp (Nat n)    = showNat n
    showSExp (SExps xs) = parens (intersperse " " (showList xs))

    -- expanded out map for termination checker
    showList : List SExp → List String
    showList []       = []
    showList (x ∷ xs) = showSExp x ∷ showList xs

module PairBased where

  data SExp : Set where
    Atom : String → SExp
    Nat : ℕ → SExp
    Nil : SExp
    Pair : SExp → SExp → SExp

  mutual
    showSExp : SExp → String
    showSExp (Atom s)   = s
    showSExp (Nat n)    = showNat n
    showSExp Nil        = "()"
    showSExp (Pair l r) = parens (showPair l r)

    showPair : SExp → SExp → String
    showPair x (Atom s)   = showSExp x <+> "." <+> s
    showPair x (Nat n)    = showSExp x <+> "." <+> showNat n
    showPair x Nil        = showSExp x
    showPair x (Pair l r) = showSExp x <+> showPair l r

open ListBased public
open PairBased

mutual
  sexpL→sexpP : ListBased.SExp → PairBased.SExp
  sexpL→sexpP (Atom s)  = Atom s
  sexpL→sexpP (Nat n)   = Nat n
  sexpL→sexpP (SExps xs) = [sexpL]→sexpP xs

  [sexpL]→sexpP : List (ListBased.SExp) → PairBased.SExp
  [sexpL]→sexpP []       = Nil
  [sexpL]→sexpP (x ∷ xs) = Pair (sexpL→sexpP x) ([sexpL]→sexpP xs)

mutual
  sexpP→sexpL : PairBased.SExp → ListBased.SExp
  sexpP→sexpL (Atom s)   = Atom s
  sexpP→sexpL (Nat n)    = Nat n
  sexpP→sexpL Nil        = SExps []
  sexpP→sexpL (Pair x y) = SExps (sexpP→sexpL x ∷ sexpP→[sexpL] y)

  sexpP→[sexpL] : PairBased.SExp → List (ListBased.SExp)
  sexpP→[sexpL] (Atom _)   = []
  sexpP→[sexpL] (Nat _)    = []
  sexpP→[sexpL] Nil        = []
  sexpP→[sexpL] (Pair x y) = sexpP→sexpL x ∷ sexpP→[sexpL] y
