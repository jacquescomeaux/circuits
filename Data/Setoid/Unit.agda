{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Data.Setoid.Unit {c ℓ : Level} where

open import Categories.Category.Instance.SingletonSet using (SingletonSetoid)
open import Relation.Binary using (Setoid)

⊤ₛ : Setoid c ℓ
⊤ₛ = SingletonSetoid {c} {ℓ}
