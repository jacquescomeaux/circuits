{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Category.Instance.One.Properties {o ℓ e : Level} where

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.One using () renaming (One to One′)

One : Category o ℓ e
One = One′

open import Categories.Category.Cocartesian One using (Cocartesian)
open import Categories.Category.Cocomplete.Finitely One using (FinitelyCocomplete)
open import Categories.Object.Initial One using (Initial)
open import Categories.Category.Cocartesian One using (BinaryCoproducts)


One-Initial : Initial
One-Initial = _

One-BinaryCoproducts : BinaryCoproducts
One-BinaryCoproducts = _

One-Cocartesian : Cocartesian
One-Cocartesian = record
    { initial = One-Initial
    ; coproducts = One-BinaryCoproducts
    }

One-FinitelyCocomplete : FinitelyCocomplete
One-FinitelyCocomplete = record
    { cocartesian = One-Cocartesian
    ; coequalizer = _
    }
