{-# OPTIONS --without-K --safe #-}

module Category.Instance.Nat.FinitelyCocomplete where

open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Categories.Category.Instance.Nat using (Nat; Nat-Cocartesian)
open import Level using (0ℓ)
open import Nat.Properties using (Coeq)

Nat-FinitelyCocomplete : FinitelyCocompleteCategory 0ℓ 0ℓ 0ℓ
Nat-FinitelyCocomplete = record
    { U = Nat
    ; finCo = record
        { cocartesian = Nat-Cocartesian
        ; coequalizer = Coeq
        }
    }

