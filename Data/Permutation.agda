{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Data.Permutation {ℓ : Level} (A : Set ℓ) where

import Data.Fin as Fin
import Data.Fin.Properties as FinProp
import Data.Fin.Permutation as ↔-Fin
import Data.List as List
import Data.List.Properties as ListProp
import Data.List.Relation.Binary.Permutation.Propositional as ↭-List
import Data.Nat as Nat
import Data.Vec.Functional as Vector
import Data.Vec.Functional.Properties as VectorProp
import Data.Vec.Functional.Relation.Binary.Permutation as ↭-Vec
import Data.Vec.Functional.Relation.Binary.Permutation.Properties as ↭-VecProp

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Vec.Functional.Relation.Unary.Any using (Any)
open import Function.Base using (_∘_)

open ↭-Vec using () renaming (_↭_ to _↭′_)
open ↭-List using (_↭_; ↭-sym; module PermutationReasoning)
open ↔-Fin using (Permutation; _⟨$⟩ˡ_; _⟨$⟩ʳ_)
open List using (List) hiding (module List)
open Fin using (Fin; cast) hiding (module Fin)
open Vector using (Vector; toList; fromList)
open Fin.Fin
open Nat using (ℕ; zero; suc)
open _↭_

module _ where

  open Fin using (#_)
  open ↔-Fin using (lift₀; insert)
  open ↭-VecProp using (↭-refl; ↭-trans)

  -- convert a List permutation to a Vector permutation
  fromList-↭
      : {A : Set}
        {xs ys : List A}
      → xs ↭ ys
      → fromList xs ↭′ fromList ys
  fromList-↭ refl = ↭-refl
  fromList-↭ (prep _ xs↭ys)
    with n↔m , xs↭ys′ ← fromList-↭ xs↭ys = lift₀ n↔m , λ where
      zero → ≡.refl
      (suc i) → xs↭ys′ i
  fromList-↭ (swap x y xs↭ys)
    with n↔m , xs↭ys′ ← fromList-↭ xs↭ys = insert (# 0) (# 1) (lift₀ n↔m) , λ where
      zero → ≡.refl
      (suc zero) → ≡.refl
      (suc (suc i)) → xs↭ys′ i
  fromList-↭ (trans {xs} xs↭ys ys↭zs) =
      ↭-trans {_} {_} {_} {i = fromList xs} (fromList-↭ xs↭ys) (fromList-↭ ys↭zs)

-- witness for an element in a Vector
_∈_ : A → {n : ℕ} → Vector A n → Set ℓ
x ∈ xs = Any (x ≡_) xs

-- apply a permutation to a witness
apply
    : {n m : ℕ}
      {xs : Vector A n}
      {ys : Vector A m}
      {x : A}
    → (xs↭ys : xs ↭′ ys)
    → x ∈ xs
    → x ∈ ys
apply {suc n} {zero} (↔n , _) (i , _) with () ← ↔n ⟨$⟩ˡ i
apply {suc n} {suc m} {xs} {ys} {x} (↔n , ↔≗) (i , x≡xs-i) = i′ , x≡ys-i′
  where
    i′ : Fin (suc m)
    i′ = ↔n ⟨$⟩ˡ i
    open ≡.≡-Reasoning
    x≡ys-i′ : x ≡ ys i′
    x≡ys-i′ = begin
      x                         ≡⟨ x≡xs-i ⟩
      xs i                      ≡⟨ ≡.cong xs (↔-Fin.inverseʳ ↔n) ⟨
      xs (↔n ⟨$⟩ʳ (↔n ⟨$⟩ˡ i))  ≡⟨⟩
      xs (↔n ⟨$⟩ʳ i′)           ≡⟨ ↔≗ i′ ⟩
      ys i′                     ∎

-- remove an element from a Vector
remove : {n : ℕ} {x : A} (xs : Vector A (suc n)) → x ∈ xs → Vector A n
remove xs (i , _) = Vector.removeAt xs i

-- remove an element and its image from a permutation
↭-remove
    : {n m : ℕ}
      {xs : Vector A (suc n)}
      {ys : Vector A (suc m)}
      {x : A}
    → (xs↭ys : xs ↭′ ys)
    → (x∈xs : x ∈ xs)
    → let x∈ys = apply xs↭ys x∈xs in
      remove xs x∈xs ↭′ remove ys x∈ys
↭-remove {n} {m} {xs} {ys} {x} xs↭ys@(ρ , ↔≗) x∈xs@(k , _) = ρ⁻ , ↔≗⁻
  where
    k′ : Fin (suc m)
    k′ = ρ ⟨$⟩ˡ k
    x∈ys : x ∈ ys
    x∈ys = apply xs↭ys x∈xs
    ρ⁻ : Permutation m n
    ρ⁻ = ↔-Fin.remove k′ ρ
    xs⁻ : Vector A n
    xs⁻ = remove xs x∈xs
    ys⁻ : Vector A m
    ys⁻ = remove ys x∈ys
    open ≡.≡-Reasoning
    open Fin using (punchIn)
    ↔≗⁻ : (i : Fin m) → xs⁻ (ρ⁻ ⟨$⟩ʳ i) ≡ ys⁻ i
    ↔≗⁻ i = begin
        xs⁻ (ρ⁻ ⟨$⟩ʳ i)             ≡⟨⟩
        remove xs x∈xs (ρ⁻ ⟨$⟩ʳ i)  ≡⟨⟩
        xs (punchIn k (ρ⁻ ⟨$⟩ʳ i))  ≡⟨ ≡.cong xs (↔-Fin.punchIn-permute′ ρ k i) ⟨
        xs (ρ ⟨$⟩ʳ (punchIn k′ i))  ≡⟨ ↔≗ (punchIn k′ i) ⟩
        ys (punchIn k′ i)           ≡⟨⟩
        remove ys x∈ys i            ≡⟨⟩
        ys⁻ i                       ∎

open List.List
open List using (length; insertAt)

-- build a permutation which moves the first element of a list to an arbitrary position
↭-insert-half
    : {x₀ : A}
      {xs : List A}
    → (i : Fin (suc (length xs)))
    → x₀ ∷ xs ↭ insertAt xs i x₀
↭-insert-half zero = refl
↭-insert-half {x₀} {x₁ ∷ xs} (suc i) = trans (swap x₀ x₁ refl) (prep x₁ (↭-insert-half i))

-- add a mapping to a permutation, given a value and its start and end positions
↭-insert
    : {xs ys : List A}
    → xs ↭ ys
    → (i : Fin (suc (length xs)))
      (j : Fin (suc (length ys)))
      (x : A)
    → insertAt xs i x ↭ insertAt ys j x
↭-insert {xs} {ys} xs↭ys i j x = xs↭ys⁺
  where
    open PermutationReasoning
    xs↭ys⁺ : insertAt xs i x ↭ insertAt ys j x
    xs↭ys⁺ = begin
      insertAt xs i x ↭⟨ ↭-insert-half i ⟨
      x ∷ xs          <⟨ xs↭ys ⟩
      x ∷ ys          ↭⟨ ↭-insert-half j ⟩
      insertAt ys j x ∎

open ListProp using (length-tabulate; tabulate-cong)
insertAt-toList
    : {n : ℕ}
      {v : Vector A n}
      (i : Fin (suc (length (toList v))))
      (i′ : Fin (suc n))
    → i ≡ cast (≡.cong suc (≡.sym (length-tabulate v))) i′
    → (x : A)
    → insertAt (toList v) i x
    ≡ toList (Vector.insertAt v i′ x)
insertAt-toList zero zero _ x = ≡.refl
insertAt-toList {suc n} {v} (suc i) (suc i′) ≡.refl x =
    ≡.cong (v zero ∷_) (insertAt-toList i i′ ≡.refl x)

-- convert a Vector permutation to a List permutation
toList-↭
    : {n m : ℕ}
      {xs : Vector A n}
      {ys : Vector A m}
    → xs ↭′ ys
    → toList xs ↭ toList ys
toList-↭ {zero} {zero} _ = refl
toList-↭ {zero} {suc m} (ρ , _) with () ← ρ ⟨$⟩ʳ zero
toList-↭ {suc n} {zero} (ρ , _) with () ← ρ ⟨$⟩ˡ zero
toList-↭ {suc n} {suc m} {xs} {ys} xs↭ys′ = xs↭ys
  where
    -- first element and its image
    x₀ : A
    x₀ = xs zero
    x₀∈xs : x₀ ∈ xs
    x₀∈xs = zero , ≡.refl
    x₀∈ys : x₀ ∈ ys
    x₀∈ys = apply xs↭ys′ x₀∈xs
    -- reduce the problem by removing those elements
    xs⁻ : Vector A n
    xs⁻ = remove xs x₀∈xs
    ys⁻ : Vector A m
    ys⁻ = remove ys x₀∈ys
    xs↭ys⁻ : xs⁻ ↭′ ys⁻
    xs↭ys⁻ = ↭-remove xs↭ys′ x₀∈xs
    -- recursion on the reduced problem
    xs↭ys⁻′ : toList xs⁻ ↭ toList ys⁻
    xs↭ys⁻′ = toList-↭ xs↭ys⁻
    -- indices for working with vectors
    i : Fin (suc n)
    i = proj₁ x₀∈xs
    j : Fin (suc m)
    j = proj₁ x₀∈ys
    i′ : Fin (suc (length (toList xs⁻)))
    i′ = cast (≡.sym (≡.cong suc (length-tabulate xs⁻))) i
    j′ : Fin (suc (length (toList ys⁻)))
    j′ = cast (≡.sym (≡.cong suc (length-tabulate ys⁻))) j
    -- main construction
    open VectorProp using (insertAt-removeAt)
    open PermutationReasoning
    open Vector using () renaming (insertAt to insertAt′)
    xs↭ys : toList xs ↭ toList ys
    xs↭ys = begin
        toList xs                       ≡⟨ tabulate-cong (insertAt-removeAt xs i) ⟨
        toList (insertAt′ xs⁻ i x₀)     ≡⟨ insertAt-toList i′ i ≡.refl x₀ ⟨
        insertAt (toList xs⁻) i′ x₀     ↭⟨ ↭-insert xs↭ys⁻′ i′ j′ x₀ ⟩
        insertAt (toList ys⁻) j′ x₀     ≡⟨ insertAt-toList j′ j ≡.refl x₀ ⟩
        toList (insertAt′ ys⁻ j x₀)     ≡⟨ ≡.cong (toList ∘ insertAt′ ys⁻ j) (proj₂ x₀∈ys) ⟩
        toList (insertAt′ ys⁻ j (ys j)) ≡⟨ tabulate-cong (insertAt-removeAt ys j) ⟩
        toList ys ∎
