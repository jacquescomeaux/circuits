{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Category.Instance.One.Properties {o ℓ e : Level} where

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.One using () renaming (One to One′)

One : Category o ℓ e
One = One′ {o} {ℓ} {e}

open import Categories.Category.Cocartesian One using (Cocartesian)
open import Categories.Category.Cocomplete.Finitely One using (FinitelyCocomplete)
open import Categories.Object.Initial One using (Initial)
open import Categories.Category.Cocartesian One using (BinaryCoproducts)


initial : Initial
initial = _

coproducts : BinaryCoproducts
coproducts = _

cocartesian : Cocartesian
cocartesian = record
    { initial = initial
    ; coproducts = coproducts
    }

finitelyCocomplete : FinitelyCocomplete
finitelyCocomplete = record
    { cocartesian = cocartesian
    ; coequalizer = _
    }
