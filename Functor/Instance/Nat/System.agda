{-# OPTIONS --without-K --safe #-}

module Functor.Instance.Nat.System where

open import Level using (suc; 0ℓ)
open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor.Core using (Functor)
open import Data.Circuit.Value using (Value)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; _×_)
open import Data.System {suc 0ℓ} using (System; ≤-System; Systemₛ)
open import Data.System.Values Value using (module ≋)
open import Function.Bundles using (Func; _⟶ₛ_)
open import Function.Base using (id; _∘_)
open import Function.Construct.Setoid using (_∙_)
open import Functor.Instance.Nat.Pull using (Pull₁; Pull-resp-≈)
open import Functor.Instance.Nat.Push using (Push₁; Push-identity; Push-homomorphism; Push-resp-≈)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)

-- import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Function.Construct.Identity as Id

open Func
open ≤-System
open Functor

private
  variable A B C : ℕ

map : (Fin A → Fin B) → System A → System B
map f X = record
    { S = S
    ; fₛ = fₛ ∙ Pull₁ f
    ; fₒ = Push₁ f ∙ fₒ
    }
  where
    open System X

≤-cong : (f : Fin A → Fin B) {X Y : System A} → ≤-System Y X → ≤-System (map f Y) (map f X)
⇒S (≤-cong f x≤y) = ⇒S x≤y
≗-fₛ (≤-cong f x≤y) = ≗-fₛ x≤y ∘ to (Pull₁ f)
≗-fₒ (≤-cong f x≤y) = cong (Push₁ f) ∘ ≗-fₒ x≤y

System₁ : (Fin A → Fin B) → Systemₛ A ⟶ₛ Systemₛ B
to (System₁ f) = map f
cong (System₁ f) (x≤y , y≤x) = ≤-cong f x≤y , ≤-cong f y≤x

id-x≤x : {X : System A} → ≤-System (map id X) X
⇒S (id-x≤x) = Id.function _
≗-fₛ (id-x≤x {_} {x}) i s = System.refl x
≗-fₒ (id-x≤x {A} {x}) s = Push-identity

x≤id-x : {x : System A} → ≤-System x (map id x)
⇒S x≤id-x = Id.function _
≗-fₛ (x≤id-x {A} {x}) i s = System.refl x
≗-fₒ (x≤id-x {A} {x}) s = ≋.sym Push-identity


System-homomorphism
    : {f : Fin A → Fin B}
      {g : Fin B → Fin C} 
      {X : System A}
    → ≤-System (map (g ∘ f) X) (map g (map f X)) × ≤-System (map g (map f X)) (map (g ∘ f) X)
System-homomorphism {f = f} {g} {X} = left , right
  where
    open System X
    left : ≤-System (map (g ∘ f) X) (map g (map f X))
    left .⇒S = Id.function S
    left .≗-fₛ i s = refl
    left .≗-fₒ s = Push-homomorphism
    right : ≤-System (map g (map f X)) (map (g ∘ f) X)
    right .⇒S = Id.function S
    right .≗-fₛ i s = refl
    right .≗-fₒ s = ≋.sym Push-homomorphism

System-resp-≈
    : {f g : Fin A → Fin B}
    → f ≗ g
    → {X : System A}
    → (≤-System (map f X) (map g X)) × (≤-System (map g X) (map f X))
System-resp-≈ {A} {B} {f = f} {g} f≗g {X} = both f≗g , both (≡.sym ∘ f≗g)
  where
    open System X
    both : {f g : Fin A → Fin B} → f ≗ g → ≤-System (map f X) (map g X)
    both f≗g .⇒S = Id.function S
    both f≗g .≗-fₛ i s = cong fₛ (Pull-resp-≈ f≗g {i})
    both {f} {g} f≗g .≗-fₒ s = Push-resp-≈ f≗g

Sys : Functor Nat (Setoids (suc 0ℓ) (suc 0ℓ))
Sys .F₀ = Systemₛ
Sys .F₁ = System₁
Sys .identity = id-x≤x , x≤id-x
Sys .homomorphism {x = X} = System-homomorphism {X = X}
Sys .F-resp-≈ = System-resp-≈
