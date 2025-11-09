{-# OPTIONS --without-K --safe #-}

module Functor.Instance.Nat.System where


open import Level using (suc; 0ℓ)

open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor.Core using (Functor)
open import Data.Circuit.Value using (Monoid)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; _×_)
open import Data.System {suc 0ℓ} using (System; _≤_; Systemₛ)
open import Data.System.Values Monoid using (module ≋)
open import Data.Unit using (⊤; tt)
open import Function.Base using (id; _∘_)
open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (_∙_)
open import Functor.Instance.Nat.Pull using (Pull)
open import Functor.Instance.Nat.Push using (Push)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)

open Func
open Functor
open _≤_

private

  variable A B C : ℕ

  opaque

    map : (Fin A → Fin B) → System A → System B
    map f X = let open System X in record
        { S = S
        ; fₛ = fₛ ∙ Pull.₁ f
        ; fₒ = Push.₁ f ∙ fₒ
        }

    ≤-cong : (f : Fin A → Fin B) {X Y : System A} → Y ≤ X → map f Y ≤ map f X
    ⇒S (≤-cong f x≤y) = ⇒S x≤y
    ≗-fₛ (≤-cong f x≤y) = ≗-fₛ x≤y ∘ to (Pull.₁ f)
    ≗-fₒ (≤-cong f x≤y) = cong (Push.₁ f) ∘ ≗-fₒ x≤y

    System₁ : (Fin A → Fin B) → Systemₛ A ⟶ₛ Systemₛ B
    to (System₁ f) = map f
    cong (System₁ f) (x≤y , y≤x) = ≤-cong f x≤y , ≤-cong f y≤x

  opaque

    unfolding System₁

    id-x≤x : {X : System A} → System₁ id ⟨$⟩ X ≤ X
    ⇒S (id-x≤x) = Id _
    ≗-fₛ (id-x≤x {_} {x}) i s = cong (System.fₛ x) Pull.identity
    ≗-fₒ (id-x≤x {A} {x}) s = Push.identity

    x≤id-x : {x : System A} → x ≤ System₁ id ⟨$⟩ x
    ⇒S x≤id-x = Id _
    ≗-fₛ (x≤id-x {A} {x}) i s = cong (System.fₛ x) (≋.sym Pull.identity)
    ≗-fₒ (x≤id-x {A} {x}) s = ≋.sym Push.identity

    System-homomorphism
        : {f : Fin A → Fin B}
          {g : Fin B → Fin C} 
          {X : System A}
        → System₁ (g ∘ f) ⟨$⟩ X ≤ System₁ g ⟨$⟩ (System₁ f ⟨$⟩ X)
        × System₁ g ⟨$⟩ (System₁ f ⟨$⟩ X) ≤ System₁ (g ∘ f) ⟨$⟩ X
    System-homomorphism {f = f} {g} {X} = left , right
      where
        open System X
        left : map (g ∘ f) X ≤ map g (map f X)
        left .⇒S = Id S
        left .≗-fₛ i s = cong fₛ Pull.homomorphism
        left .≗-fₒ s = Push.homomorphism
        right : map g (map f X) ≤ map (g ∘ f) X
        right .⇒S = Id S
        right .≗-fₛ i s = cong fₛ (≋.sym Pull.homomorphism)
        right .≗-fₒ s = ≋.sym Push.homomorphism

    System-resp-≈
        : {f g : Fin A → Fin B}
        → f ≗ g
        → {X : System A}
        → System₁ f ⟨$⟩ X ≤ System₁ g ⟨$⟩ X
        × System₁ g ⟨$⟩ X ≤ System₁ f ⟨$⟩ X
    System-resp-≈ {A} {B} {f = f} {g} f≗g {X} = both f≗g , both (≡.sym ∘ f≗g)
      where
        open System X
        both : {f g : Fin A → Fin B} → f ≗ g → map f X ≤ map g X
        both f≗g .⇒S = Id S
        both f≗g .≗-fₛ i s = cong fₛ (Pull.F-resp-≈ f≗g {i})
        both {f} {g} f≗g .≗-fₒ s = Push.F-resp-≈ f≗g

opaque
  unfolding System₁
  Sys-defs : ⊤
  Sys-defs = tt

Sys : Functor Nat (Setoids (suc 0ℓ) (suc 0ℓ))
Sys .F₀ = Systemₛ
Sys .F₁ = System₁
Sys .identity = id-x≤x , x≤id-x
Sys .homomorphism {x = X} = System-homomorphism {X = X}
Sys .F-resp-≈ = System-resp-≈

module Sys = Functor Sys
