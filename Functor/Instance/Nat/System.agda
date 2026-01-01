{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

module Functor.Instance.Nat.System where

open import Level using (suc; 0ℓ)

open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Category using (Category)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Data.Circuit.Value using (Monoid)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product.Base using (_,_; _×_)
open import Data.Setoid using (∣_∣)
open import Data.System {suc 0ℓ} using (System; _≤_; Systemₛ; Systems; ≤-refl; ≤-trans; _≈_)
open import Data.System.Values Monoid using (module ≋; module Object; Values; ≋-isEquiv)
open import Relation.Binary using (Setoid)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_; _∘_; id)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (_∙_)
open import Functor.Instance.Nat.Pull using (Pull)
open import Functor.Instance.Nat.Push using (Push)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)

open import Category.Instance.Setoids.SymmetricMonoidal {0ℓ} {0ℓ} using (Setoids-×)
open import Category.Construction.CMonoids Setoids-×.symmetric using (CMonoids)
open import Object.Monoid.Commutative Setoids-×.symmetric using (CommutativeMonoid; CommutativeMonoid⇒)

open CommutativeMonoid⇒ using (arr)
open Object using (Valuesₘ)
open Func
open Functor
open _≤_

private
  variable A B C : ℕ

opaque
  unfolding Valuesₘ ≋-isEquiv
  map : (Fin A → Fin B) → System A → System B
  map {A} {B} f X = let open System X in record
      { S = S
      ; fₛ = fₛ ∙ arr (Pull.₁ f)
      ; fₒ = arr (Push.₁ f) ∙ fₒ
      }

opaque
  unfolding map
  open System
  map-≤ : (f : Fin A → Fin B) {X Y : System A} → X ≤ Y → map f X ≤ map f Y
  ⇒S (map-≤ f x≤y) = ⇒S x≤y
  ≗-fₛ (map-≤ f x≤y) = ≗-fₛ x≤y ∘ to (arr (Pull.₁ f))
  ≗-fₒ (map-≤ f x≤y) = cong (arr (Push.₁ f)) ∘ ≗-fₒ x≤y

opaque
  unfolding map-≤
  map-≤-refl
      : (f : Fin A → Fin B)
      → {X : System A}
      → map-≤ f (≤-refl {A} {X}) ≈ ≤-refl
  map-≤-refl f {X} = Setoid.refl (S (map f X))

opaque
  unfolding map-≤
  map-≤-trans
      : (f : Fin A → Fin B)
      → {X Y Z : System A}
      → {h : X ≤ Y}
      → {g : Y ≤ Z}
      → map-≤ f (≤-trans h g) ≈ ≤-trans (map-≤ f h) (map-≤ f g)
  map-≤-trans f {Z = Z} = Setoid.refl (S (map f Z))

opaque
  unfolding map-≤
  map-≈
      : (f : Fin A → Fin B)
      → {X Y : System A}
      → {g h : X ≤ Y}
      → h ≈ g
      → map-≤ f h ≈ map-≤ f g
  map-≈ f h≈g = h≈g

Sys₁ : (Fin A → Fin B) → Functor (Systems A) (Systems B)
Sys₁ {A} {B} f = record
    { F₀ = map f
    ; F₁ = λ C≤D → map-≤ f C≤D
    ; identity = map-≤-refl f
    ; homomorphism = map-≤-trans f
    ; F-resp-≈ = map-≈ f
    }

opaque
  unfolding map
  map-id-≤ : (X : System A) → map id X ≤ X
  map-id-≤ X .⇒S = Id (S X)
  map-id-≤ X .≗-fₛ i s = cong (fₛ X) Pull.identity
  map-id-≤ X .≗-fₒ s = Push.identity

opaque
  unfolding map
  map-id-≥ : (X : System A) → X ≤ map id X
  map-id-≥ X .⇒S = Id (S X)
  map-id-≥ X .≗-fₛ i s = cong (fₛ X) (≋.sym Pull.identity)
  map-id-≥ X .≗-fₒ s = ≋.sym Push.identity

opaque
  unfolding map-≤ map-id-≤
  map-id-comm
      : {X Y : System A}
        (f : X ≤ Y)
      → ≤-trans (map-≤ id f) (map-id-≤ Y) ≈ ≤-trans (map-id-≤ X) f
  map-id-comm {Y} f = Setoid.refl (S Y)

opaque

  unfolding map-id-≤ map-id-≥

  map-id-isoˡ
      : (X : System A)
      → ≤-trans (map-id-≤ X) (map-id-≥ X) ≈ ≤-refl
  map-id-isoˡ X = Setoid.refl (S X)

  map-id-isoʳ
      : (X : System A)
      → ≤-trans (map-id-≥ X) (map-id-≤ X) ≈ ≤-refl
  map-id-isoʳ X = Setoid.refl (S X)

Sys-identity : Sys₁ {A} id ≃ idF
Sys-identity = niHelper record
    { η = map-id-≤
    ; η⁻¹ = map-id-≥
    ; commute = map-id-comm
    ; iso = λ X → record
        { isoˡ = map-id-isoˡ X
        ; isoʳ = map-id-isoʳ X
        }
    }

opaque
  unfolding map
  map-∘-≤
      : (f : Fin A → Fin B)
        (g : Fin B → Fin C)
        (X : System A)
      → map (g ∘ f) X ≤ map g (map f X)
  map-∘-≤ f g X .⇒S = Id (S X)
  map-∘-≤ f g X .≗-fₛ i s = cong (fₛ X) Pull.homomorphism
  map-∘-≤ f g X .≗-fₒ s = Push.homomorphism

opaque
  unfolding map
  map-∘-≥
      : (f : Fin A → Fin B)
        (g : Fin B → Fin C)
        (X : System A)
      → map g (map f X) ≤ map (g ∘ f) X
  map-∘-≥ f g X .⇒S = Id (S X)
  map-∘-≥ f g X .≗-fₛ i s = cong (fₛ X) (≋.sym Pull.homomorphism)
  map-∘-≥ f g X .≗-fₒ s = ≋.sym Push.homomorphism

Sys-homo
    : (f : Fin A → Fin B)
      (g : Fin B → Fin C)
    → Sys₁ (g ∘ f) ≃ Sys₁ g ∘F Sys₁ f
Sys-homo {A} f g = niHelper record
    { η = map-∘-≤ f g
    ; η⁻¹ = map-∘-≥ f g
    ; commute = map-∘-comm f g
    ; iso = λ X → record
        { isoˡ = isoˡ X
        ; isoʳ = isoʳ X
        }
    }
  where
    opaque
      unfolding map-∘-≤ map-≤
      map-∘-comm
          : (f : Fin A → Fin B)
            (g : Fin B → Fin C)
          → {X Y : System A}
            (X≤Y : X ≤ Y)
          → ≤-trans (map-≤ (g ∘ f) X≤Y) (map-∘-≤ f g Y)
          ≈ ≤-trans (map-∘-≤ f g X) (map-≤ g (map-≤ f X≤Y))
      map-∘-comm f g {Y} X≤Y = Setoid.refl (S Y)
    module _ (X : System A) where
      opaque
        unfolding map-∘-≤ map-∘-≥
        isoˡ : ≤-trans (map-∘-≤ f g X) (map-∘-≥ f g X) ≈ ≤-refl
        isoˡ = Setoid.refl (S X)
        isoʳ : ≤-trans (map-∘-≥ f g X) (map-∘-≤ f g X) ≈ ≤-refl
        isoʳ = Setoid.refl (S X)


module _ {f g : Fin A → Fin B} (f≗g : f ≗ g) (X : System A) where

  opaque

    unfolding map

    map-cong-≤ : map f X ≤ map g X
    map-cong-≤ .⇒S = Id (S X)
    map-cong-≤ .≗-fₛ i s = cong (fₛ X) (Pull.F-resp-≈ f≗g)
    map-cong-≤ .≗-fₒ s = Push.F-resp-≈ f≗g

    map-cong-≥ : map g X ≤ map f X
    map-cong-≥ .⇒S = Id (S X)
    map-cong-≥ .≗-fₛ i s = cong (fₛ X) (Pull.F-resp-≈ (≡.sym ∘ f≗g))
    map-cong-≥ .≗-fₒ s = Push.F-resp-≈ (≡.sym ∘ f≗g)

opaque
  unfolding map-≤ map-cong-≤
  map-cong-comm
      : {f g : Fin A → Fin B}
        (f≗g : f ≗ g)
        {X Y : System A}
        (h : X ≤ Y)
      → ≤-trans (map-≤ f h) (map-cong-≤ f≗g Y)
      ≈ ≤-trans (map-cong-≤ f≗g X) (map-≤ g h)
  map-cong-comm f≗g {Y} h = Setoid.refl (S Y)

opaque

  unfolding map-cong-≤

  map-cong-isoˡ
      : {f g : Fin A → Fin B}
        (f≗g : f ≗ g)
        (X : System A)
      → ≤-trans (map-cong-≤ f≗g X) (map-cong-≥ f≗g X) ≈ ≤-refl
  map-cong-isoˡ f≗g X = Setoid.refl (S X)

  map-cong-isoʳ
      : {f g : Fin A → Fin B}
        (f≗g : f ≗ g)
        (X : System A)
      → ≤-trans (map-cong-≥ f≗g X) (map-cong-≤ f≗g X) ≈ ≤-refl
  map-cong-isoʳ f≗g X = Setoid.refl (S X)

Sys-resp-≈ : {f g : Fin A → Fin B} → f ≗ g → Sys₁ f ≃ Sys₁ g
Sys-resp-≈ f≗g = niHelper record
    { η = map-cong-≤ f≗g
    ; η⁻¹ = map-cong-≥ f≗g
    ; commute = map-cong-comm f≗g
    ; iso = λ X → record
        { isoˡ = map-cong-isoˡ f≗g X
        ; isoʳ = map-cong-isoʳ f≗g X
        }
    }

Sys : Functor Nat (Cats (suc 0ℓ) (suc 0ℓ) 0ℓ)
Sys .F₀ = Systems
Sys .F₁ = Sys₁
Sys .identity = Sys-identity
Sys .homomorphism = Sys-homo _ _
Sys .F-resp-≈ = Sys-resp-≈

module Sys = Functor Sys
