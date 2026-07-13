{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Data.System {c ℓ : Level} where

open import Data.System.Core {c} {ℓ} public
open import Data.System.Category {c} {ℓ} public
open import Data.System.Looped {c} {ℓ} public
open import Data.System.Monoidal {c} {ℓ} public using (Systems-MC; Systems-SMC)
