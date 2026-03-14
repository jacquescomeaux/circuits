{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Data.System {ℓ : Level} where

open import Data.System.Core {ℓ} public
open import Data.System.Category {ℓ} public
open import Data.System.Looped {ℓ} public
open import Data.System.Monoidal {ℓ} public using (Systems-MC; Systems-SMC)
