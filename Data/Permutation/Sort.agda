{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (DecTotalOrder)

module Data.Permutation.Sort {ℓ₁ ℓ₂ ℓ₃} (dto : DecTotalOrder ℓ₁ ℓ₂ ℓ₃) where

open DecTotalOrder dto using (module Eq; totalOrder) renaming (Carrier to A)

open import Data.List.Base using (List)
open import Data.List.Relation.Binary.Equality.Setoid Eq.setoid using (_≋_)
open import Data.List.Relation.Binary.Permutation.Setoid Eq.setoid using (_↭_; module PermutationReasoning)
open import Data.List.Relation.Unary.Sorted.TotalOrder.Properties using (↗↭↗⇒≋)
open import Data.List.Sort dto using (sortingAlgorithm)
open import Data.List.Sort.Base totalOrder using (SortingAlgorithm)
open SortingAlgorithm sortingAlgorithm using (sort; sort-↭ₛ; sort-↗)

sorted-≋
    : {xs ys : List A}
    → xs ↭ ys
    → sort xs ≋ sort ys
sorted-≋ {xs} {ys} xs↭ys = ↗↭↗⇒≋ totalOrder (sort-↗ xs) (sort-↗ ys) sort-xs↭sort-ys
  where
    open PermutationReasoning
    sort-xs↭sort-ys : sort xs ↭ sort ys
    sort-xs↭sort-ys = begin
      sort xs ↭⟨ sort-↭ₛ xs ⟩
      xs      ↭⟨ xs↭ys ⟩
      ys      ↭⟨ sort-↭ₛ ys ⟨
      sort ys ∎
