{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (DecTotalOrder)

module Data.Permutation.Sort {ℓ₁ ℓ₂ ℓ₃} (dto : DecTotalOrder ℓ₁ ℓ₂ ℓ₃) where

open DecTotalOrder dto
  using
    ( _≈_ ; module Eq
    ; totalOrder
    ; _≤_ ; _≤?_
    ; ≤-respˡ-≈ ; ≤-respʳ-≈
    ; antisym
    )
  renaming (Carrier to A; trans to ≤-trans; reflexive to ≤-reflexive)

open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; _++_; [_])
open import Data.List.Membership.Setoid Eq.setoid using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (module Pointwise)
open import Data.List.Relation.Binary.Equality.Setoid Eq.setoid using (_≋_; ≋-refl; ≋-sym; ≋-trans)
open import Data.List.Relation.Unary.Linked using (Linked)
open import Data.List.Relation.Unary.Sorted.TotalOrder totalOrder using (Sorted)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-trans; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (↭-length)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Sort dto using (sort; sort-↭; sort-↗)
open import Relation.Nullary.Decidable.Core using (yes; no)
open Fin
open _↭_
open Any
open List
open Linked
open Pointwise

insert : List A → A → List A
insert [] x = [ x ]
insert (x₀ ∷ xs) x with x ≤? x₀
... | yes _ = x ∷ x₀ ∷ xs
... | no _ = x₀ ∷ insert xs x

insert-resp-≋ : {xs ys : List A} (v : A) → xs ≋ ys → insert xs v ≋ insert ys v
insert-resp-≋ _ [] = ≋-refl
insert-resp-≋ {x ∷ xs} {y ∷ ys} v (x≈y ∷ xs≋ys)
  with v ≤? x | v ≤? y
... | yes v≤x | yes v≤y = Eq.refl ∷ x≈y ∷ xs≋ys
... | yes v≤x | no v≰y with () ← v≰y (≤-respʳ-≈ x≈y v≤x)
... | no v≰x | yes v≤y with () ← v≰x (≤-respʳ-≈ (Eq.sym x≈y) v≤y)
... | no v≰x | no v≰y = x≈y ∷ insert-resp-≋ v xs≋ys

remove : {x : A} (xs : List A) → x ∈ xs → List A
remove (_ ∷ xs) (here _) = xs
remove (x ∷ xs) (there elem) = x ∷ remove xs elem

remove-sorted : {x : A} {xs : List A} → Sorted xs → (x∈xs : x ∈ xs) → Sorted (remove xs x∈xs)
remove-sorted [-] (here x≡x₀) = []
remove-sorted (x₀≤x₁ ∷ s-xs) (here px) = s-xs
remove-sorted (x₀≤x₁ ∷ [-]) (there (here px)) = [-]
remove-sorted (x₀≤x₁ ∷ x₁≤x₂ ∷ s-xs) (there (here px)) = ≤-trans x₀≤x₁ x₁≤x₂ ∷ s-xs
remove-sorted (x₀≤x₁ ∷ x₁≤x₂ ∷ s-xs) (there (there x∈xs)) = x₀≤x₁ ∷ remove-sorted (x₁≤x₂ ∷ s-xs) (there x∈xs)

head : {xs : List A} {x : A} → .(x ∈ xs) → A
head {x ∷ _} _ = x

tail : {xs : List A} {x : A} → .(x ∈ xs) → List A
tail {_ ∷ xs} _ = xs

head-≤ : {xs : List A}
      {x : A}
    → Sorted xs
    → (x∈xs : x ∈ xs)
    → head x∈xs ≤ x
head-≤ {x ∷ []} [-] (here px) = ≤-reflexive (Eq.sym px)
head-≤ {x₀ ∷ x₁ ∷ xs} (x₀≤x₁ ∷ s-xs) (here px) = ≤-reflexive (Eq.sym px)
head-≤ {x₀ ∷ x₁ ∷ xs} (x₀≤x₁ ∷ s-xs) (there x∈xs) = ≤-trans x₀≤x₁ (head-≤ s-xs x∈xs)

remove-head
    : {xs : List A}
      {x : A}
    → Sorted xs
    → (x∈xs : x ∈ xs)
    → x ≈ head x∈xs
    → remove xs x∈xs ≋ tail x∈xs
remove-head _ (here _) _ = ≋-refl
remove-head {x₀ ∷ x₁ ∷ xs} {x} (x₀≤x₁ ∷ s-xs) (there x∈xs) x≈x₀ =
    x₀≈x₁ ∷ remove-head s-xs x∈xs x≈x₁
  where
    x₀≈x₁ : x₀ ≈ x₁
    x₀≈x₁ = antisym x₀≤x₁ (≤-respʳ-≈ x≈x₀ (head-≤ s-xs x∈xs))
    x≈x₁ : x ≈ x₁
    x≈x₁ = Eq.trans x≈x₀ x₀≈x₁

insert-remove
    : {xs : List A}
      {x : A}
    → (s-xs : Sorted xs)
    → (x∈xs : x ∈ xs)
    → insert (remove xs x∈xs) x ≋ xs
insert-remove [-] (here px) = px ∷ []
insert-remove {x₀ ∷ x₁ ∷ xs} {x} (x₀≤x₁ ∷ s-xs) (here px) with x ≤? x₁
... | yes x≤x₁ = px ∷ ≋-refl
... | no x≰x₁ with () ← x≰x₁ (≤-respˡ-≈ (Eq.sym px) x₀≤x₁)
insert-remove {x₀ ∷ x₁ ∷ xs} {x} (x₀≤x₁ ∷ s-xs) (there x∈xs) with x ≤? x₀
... | yes x≤x₀ =
          antisym x≤x₀ (≤-trans x₀≤x₁ x₁≤x) ∷
          antisym x₀≤x₁ (≤-trans x₁≤x x≤x₀) ∷
          remove-head s-xs x∈xs (antisym (≤-trans x≤x₀ x₀≤x₁) (head-≤ s-xs x∈xs))
        where
          x₁≤x : x₁ ≤ x
          x₁≤x = head-≤ s-xs x∈xs
... | no x≰x₀ = Eq.refl ∷ insert-remove s-xs x∈xs

apply : {xs ys : List A} {x : A} → xs ↭ ys → x ∈ xs → x ∈ ys
apply refl x-in-xs = x-in-xs
apply (prep x xs↭ys) (here px) = here px
apply (prep x xs↭ys) (there x-in-xs) = there (apply xs↭ys x-in-xs)
apply (swap x y xs↭ys) (here px) = there (here px)
apply (swap x y xs↭ys) (there (here px)) = here px
apply (swap x y xs↭ys) (there (there x-in-xs)) = there (there (apply xs↭ys x-in-xs))
apply (trans xs↭ys ys↭zs) x-in-xs = apply ys↭zs (apply xs↭ys x-in-xs)

↭-remove
    : {xs ys : List A}
      {x : A}
    → (xs↭ys : xs ↭ ys)
    → (x∈xs : x ∈ xs)
    → let x∈ys = apply xs↭ys x∈xs in
      remove xs x∈xs ↭ remove ys x∈ys
↭-remove refl x∈xs = refl
↭-remove (prep x xs↭ys) (here px) = xs↭ys
↭-remove (prep x xs↭ys) (there x∈xs) = prep x (↭-remove xs↭ys x∈xs)
↭-remove (swap x y xs↭ys) (here px) = prep y xs↭ys
↭-remove (swap x y xs↭ys) (there (here px)) = prep x xs↭ys
↭-remove (swap x y xs↭ys) (there (there x∈xs)) = swap x y (↭-remove xs↭ys x∈xs)
↭-remove (trans xs↭ys ys↭zs) x∈xs = trans (↭-remove xs↭ys x∈xs) (↭-remove ys↭zs (apply xs↭ys x∈xs))

sorted-unique
    : {xs ys : List A}
    → xs ↭ ys
    → Sorted xs
    → Sorted ys
    → xs ≋ ys
sorted-unique {[]} {ys} xs↭ys s-xs s-ys with .(↭-length xs↭ys)
sorted-unique {[]} {[]} xs↭ys s-xs s-ys | _ = []
sorted-unique xs@{x ∷ xs′} {ys} xs↭ys s-xs s-ys = ≋-trans ≋xs (≋-trans xs≋ys″ ≋ys)
  where
    x∈xs : x ∈ xs
    x∈xs = here Eq.refl
    x∈ys : x ∈ ys
    x∈ys = apply xs↭ys x∈xs
    s-xs′ : Sorted (remove xs x∈xs)
    s-xs′ = remove-sorted s-xs x∈xs
    s-ys′ : Sorted (remove ys x∈ys)
    s-ys′ = remove-sorted s-ys x∈ys
    xs↭ys′ : remove xs x∈xs ↭ remove ys x∈ys
    xs↭ys′ = ↭-remove xs↭ys x∈xs
    xs≋ys′ : remove xs x∈xs ≋ remove ys x∈ys
    xs≋ys′ = sorted-unique {xs′} xs↭ys′ s-xs′ s-ys′
    xs≋ys″ : insert (remove xs x∈xs) x ≋ insert (remove ys x∈ys) x
    xs≋ys″ = insert-resp-≋ x xs≋ys′
    ≋xs : xs ≋ insert (remove xs x∈xs) x
    ≋xs = ≋-sym (insert-remove s-xs x∈xs)
    ≋ys : insert (remove ys x∈ys) x ≋ ys
    ≋ys = insert-remove s-ys x∈ys

sorted-≋
    : {xs ys : List A}
    → xs ↭ ys
    → sort xs ≋ sort ys
sorted-≋ {xs} {ys} xs↭ys =
    sorted-unique
      (↭-trans
        (sort-↭ xs)
        (↭-trans xs↭ys (↭-sym (sort-↭ ys))))
      (sort-↗ xs)
      (sort-↗ ys)
