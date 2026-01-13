{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --lossy-unification #-}

module Functor.Instance.Nat.System where

open import Level using (suc; 0ℓ)

import Data.System.Monoidal {suc 0ℓ} as System-⊗
import Categories.Morphism as Morphism
import Functor.Free.Instance.SymmetricMonoidalPreorder.Strong as SymmetricMonoidalPreorder

open import Category.Instance.Setoids.SymmetricMonoidal using (Setoids-×)

open import Categories.Category using (Category)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.Monoidals using (StrongMonoidals)
open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)
open import Categories.Functor.Monoidal.Properties using (idF-StrongMonoidal; ∘-StrongMonoidal)
open import Categories.Functor.Monoidal.Symmetric using () renaming (module Strong to Strong₃)
open import Categories.Functor.Monoidal.Symmetric.Properties using (idF-StrongSymmetricMonoidal; ∘-StrongSymmetricMonoidal)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper; NaturalIsomorphism)
open import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal using () renaming (module Strong to Strong₂)
open import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Symmetric using () renaming (module Strong to Strong₄)
open import Category.Construction.CMonoids (Setoids-×.symmetric {suc 0ℓ} {suc 0ℓ}) using (CMonoids)
open import Category.Instance.SymMonCat using () renaming (module Strong to Strong₁)
open import Data.Circuit.Value using (Monoid)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; _×_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Setoid using (∣_∣)
open import Data.Setoid.Unit using (⊤ₛ)
open import Data.System {suc 0ℓ} using (System; _≤_; Systemₛ; Systems; ≤-refl; ≤-trans; _≈_; discrete)
open import Data.System.Monoidal {suc 0ℓ} using (Systems-MC; Systems-SMC)
open import Data.Values Monoid using (module ≋; module Object; Values; ≋-isEquiv)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_; _∘_; id)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (_∙_)
open import Functor.Free.Instance.InducedCMonoid using (InducedCMonoid)
open import Functor.Instance.Nat.Pull using (Pull)
open import Functor.Instance.Nat.Push using (Push)
open import Object.Monoid.Commutative (Setoids-×.symmetric {0ℓ} {0ℓ}) using (CommutativeMonoid; CommutativeMonoid⇒)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)

open CommutativeMonoid⇒ using (arr)
open Func
open Functor
open Object using (Valuesₘ)
open Strong₁ using (SymMonCat)
open Strong₂ using (MonoidalNaturalIsomorphism)
open Strong₃ using (SymmetricMonoidalFunctor)
open Strong₄ using (SymmetricMonoidalNaturalIsomorphism)
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

module NatCat where

  Sys : Functor Nat (Cats (suc 0ℓ) (suc 0ℓ) 0ℓ)
  Sys .F₀ = Systems
  Sys .F₁ = Sys₁
  Sys .identity = Sys-identity
  Sys .homomorphism = Sys-homo _ _
  Sys .F-resp-≈ = Sys-resp-≈

  module Sys = Functor Sys

module NatMC where

  module _ (f : Fin A → Fin B) where

    module A = System-⊗ A
    module B = System-⊗ B

    open CommutativeMonoid⇒ (Push.₁ f)
    open Morphism (Systems B) using (_≅_)

    opaque
      unfolding map
      ε-≅ : discrete B ≅ map f (discrete A)
      ε-≅ = record
          -- other fields can be inferred
          { from = record
              { ⇒S = Id ⊤ₛ
              ; ≗-fₒ = λ s → ≋.sym preserves-η
              }
          ; to = record
              { ⇒S = Id ⊤ₛ
              ; ≗-fₒ = λ s → preserves-η
              }
          }

    opaque
      unfolding map-≤
      ⊗-homo-≃ : B.⊗ ∘F (Sys₁ f ⁂ Sys₁ f) ≃ Sys₁ f ∘F A.⊗
      ⊗-homo-≃ = niHelper record
          { η = λ (X , Y) → record
              { ⇒S = Id (S X ×ₛ S Y)
              ; ≗-fₛ = λ i s → Setoid.refl (S X ×ₛ S Y)
              ; ≗-fₒ = λ (s₁ , s₂) → ≋.sym preserves-μ
              }
          ; η⁻¹ = λ (X , Y) → record
              { ⇒S = Id (S X ×ₛ S Y)
              ; ≗-fₛ = λ i s → Setoid.refl (S X ×ₛ S Y)
              ; ≗-fₒ = λ s → preserves-μ
              }
          ; commute = λ { {_} {Z′ , Y′} _ → Setoid.refl (S Z′ ×ₛ S Y′) }
          ; iso = λ (X , Y) → record
              { isoˡ = Setoid.refl (S X ×ₛ S Y)
              ; isoʳ = Setoid.refl (S X ×ₛ S Y)
              }
          }

    private

      module ε-≅ = _≅_ ε-≅
      module ⊗-homo-≃ = NaturalIsomorphism ⊗-homo-≃
      module A-MC = MonoidalCategory A.Systems-MC
      module B-MC = MonoidalCategory B.Systems-MC

      F : Functor (Systems A) (Systems B)
      F = Sys₁ f

      module F = Functor F

    open B-MC using () renaming (_∘_ to _∘′_)

    opaque

      unfolding ⊗-homo-≃

      associativity
          : {X Y Z : System A}
          → F.₁ A.Associator.assoc-≤
          ∘′ ⊗-homo-≃.⇒.η (X A.⊗₀ Y , Z)
          ∘′ ⊗-homo-≃.⇒.η (X , Y) B.⊗₁ B-MC.id
          B-MC.≈ ⊗-homo-≃.⇒.η (X , Y A.⊗₀ Z)
          ∘′ B-MC.id B.⊗₁ ⊗-homo-≃.⇒.η (Y , Z) 
          ∘′ B.Associator.assoc-≤
      associativity {X} {Y} {Z} = Setoid.refl (S X ×ₛ (S Y ×ₛ S Z))

      unitaryˡ
          : {X : System A}
          →  F.₁ A.Unitors.⊗-discreteˡ-≤
          ∘′ ⊗-homo-≃.⇒.η (A-MC.unit , X)
          ∘′ ε-≅.from B.⊗₁ B-MC.id 
          B-MC.≈ B-MC.unitorˡ.from
      unitaryˡ {X} = Setoid.refl (S X)

      unitaryʳ
          : {X : System A}
          →  F.₁ A.Unitors.⊗-discreteʳ-≤
          ∘′ ⊗-homo-≃.⇒.η (X , discrete A)
          ∘′ B-MC.id B.⊗₁ ε-≅.from
          B-MC.≈ B-MC.unitorʳ.from
      unitaryʳ {X} = Setoid.refl (S X)

    Sys-MC₁ : StrongMonoidalFunctor (Systems-MC A) (Systems-MC B)
    Sys-MC₁ = record
        { F = Sys₁ f
        ; isStrongMonoidal = record
            { ε = ε-≅
            ; ⊗-homo = ⊗-homo-≃
            ; associativity = associativity
            ; unitaryˡ = unitaryˡ
            ; unitaryʳ = unitaryʳ
            }
        }

  opaque
    unfolding map-id-≤ ⊗-homo-≃
    Sys-MC-identity : MonoidalNaturalIsomorphism (Sys-MC₁ id) (idF-StrongMonoidal (Systems-MC A))
    Sys-MC-identity = record
        { U = NatCat.Sys.identity
        ; F⇒G-isMonoidal = record
            { ε-compat = _
            ; ⊗-homo-compat = λ {X Y} → Setoid.refl (S X ×ₛ S Y)
            }
        }

  opaque
    unfolding map-∘-≤ ⊗-homo-≃
    Sys-MC-homomorphism
        : {g : Fin B → Fin C}
          {f : Fin A → Fin B}
        → MonoidalNaturalIsomorphism (Sys-MC₁ (g ∘ f)) (∘-StrongMonoidal (Sys-MC₁ g) (Sys-MC₁ f))
    Sys-MC-homomorphism = record
        { U = NatCat.Sys.homomorphism
        ; F⇒G-isMonoidal = record
            { ε-compat = _
            ; ⊗-homo-compat = λ {X Y} → Setoid.refl (S X ×ₛ S Y)
            }
        }

  opaque
    unfolding map-cong-≤ ⊗-homo-≃
    Sys-MC-resp-≈
        : {f g : Fin A → Fin B}
        → f ≗ g
        → MonoidalNaturalIsomorphism (Sys-MC₁ f) (Sys-MC₁ g)
    Sys-MC-resp-≈ f≗g = record
        { U = NatCat.Sys.F-resp-≈ f≗g
        ; F⇒G-isMonoidal = record
            { ε-compat = _
            ; ⊗-homo-compat = λ {X Y} → Setoid.refl (S X ×ₛ S Y)
            }
        }

  Sys : Functor Nat (StrongMonoidals (suc 0ℓ) (suc 0ℓ) 0ℓ)
  Sys .F₀ = Systems-MC
  Sys .F₁ = Sys-MC₁
  Sys .identity = Sys-MC-identity
  Sys .homomorphism = Sys-MC-homomorphism
  Sys .F-resp-≈ = Sys-MC-resp-≈

  module Sys = Functor Sys

module NatSMC where

  module _ (f : Fin A → Fin B) where

    private

      module A = System-⊗ A
      module B = System-⊗ B
      module A-SMC = SymmetricMonoidalCategory A.Systems-SMC
      module B-SMC = SymmetricMonoidalCategory B.Systems-SMC

      F : Functor (Systems A) (Systems B)
      F = Sys₁ f

      module F = Functor F

      F-MF : StrongMonoidalFunctor (Systems-MC A) (Systems-MC B)
      F-MF = NatMC.Sys.₁ f
      module F-MF = StrongMonoidalFunctor F-MF

    opaque
      unfolding NatMC.⊗-homo-≃
      σ-compat
          : {X Y : System A}
          → F.₁ (A-SMC.braiding.⇒.η (X , Y)) B-SMC.∘ F-MF.⊗-homo.⇒.η (X , Y)
          B-SMC.≈ F-MF.⊗-homo.⇒.η (Y , X) B-SMC.∘ B-SMC.braiding.⇒.η (F.₀ X , F.₀ Y)
      σ-compat {X} {Y} = Setoid.refl (S Y ×ₛ S X)

    Sys-SMC₁ : SymmetricMonoidalFunctor (Systems-SMC A) (Systems-SMC B)
    Sys-SMC₁ = record
        { F-MF
        ; isBraidedMonoidal = record
            { F-MF
            ; braiding-compat = σ-compat
            }
        }

  Sys-SMC-identity : SymmetricMonoidalNaturalIsomorphism (Sys-SMC₁ id) (idF-StrongSymmetricMonoidal (Systems-SMC A))
  Sys-SMC-identity = record { MonoidalNaturalIsomorphism NatMC.Sys.identity }

  Sys-SMC-homomorphism
      : {g : Fin B → Fin C}
        {f : Fin A → Fin B}
      → SymmetricMonoidalNaturalIsomorphism (Sys-SMC₁ (g ∘ f)) (∘-StrongSymmetricMonoidal (Sys-SMC₁ g) (Sys-SMC₁ f))
  Sys-SMC-homomorphism = record { MonoidalNaturalIsomorphism NatMC.Sys.homomorphism }

  Sys-SMC-resp-≈
      : {f g : Fin A → Fin B}
      → f ≗ g
      → SymmetricMonoidalNaturalIsomorphism (Sys-SMC₁ f) (Sys-SMC₁ g)
  Sys-SMC-resp-≈ f≗g = record { MonoidalNaturalIsomorphism (NatMC.Sys.F-resp-≈ f≗g) }

  Sys : Functor Nat (SymMonCat {suc 0ℓ} {suc 0ℓ} {0ℓ})
  Sys .F₀ = Systems-SMC
  Sys .F₁ = Sys-SMC₁
  Sys .identity = Sys-SMC-identity
  Sys .homomorphism = Sys-SMC-homomorphism
  Sys .F-resp-≈ = Sys-SMC-resp-≈

  module Sys = Functor Sys

module NatCMon where

  Sys : Functor Nat CMonoids
  Sys = InducedCMonoid ∘F SymmetricMonoidalPreorder.Free ∘F NatSMC.Sys

  module Sys = Functor Sys
