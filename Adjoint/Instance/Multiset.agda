{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_; suc; 0ℓ)

module Adjoint.Instance.Multiset {ℓ : Level} where

open import Category.Instance.Setoids.SymmetricMonoidal {ℓ} {ℓ} using (Setoids-×)

private
  module S = Setoids-×

import Categories.Object.Monoid S.monoidal as MonoidObject
import Data.List as L
import Data.List.Relation.Binary.Permutation.Setoid as ↭
import Functor.Forgetful.Instance.CMonoid S.symmetric as CMonoid
import Functor.Forgetful.Instance.Monoid S.monoidal as Monoid
import Object.Monoid.Commutative S.symmetric as CMonoidObject

open import Categories.Adjoint using (_⊣_)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor; id; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Category.Construction.CMonoids using (CMonoids)
open import Data.CMonoid using (toCMonoid; toCMonoid⇒)
open import Data.Monoid using (toMonoid; toMonoid⇒)
open import Data.Opaque.Multiset using ([-]ₛ; Multisetₛ; foldₛ; ++ₛ-homo; []ₛ-homo; fold-mapₛ; fold)
open import Data.Product using (_,_; uncurry)
open import Data.Setoid using (∣_∣)
open import Function using (_⟶ₛ_; _⟨$⟩_)
open import Functor.Free.Instance.CMonoid {ℓ} {ℓ} using (Multisetₘ; mapₘ; MultisetCMonoid) renaming (Free to Free′)
open import Relation.Binary using (Setoid)

open CMonoidObject using (CommutativeMonoid; CommutativeMonoid⇒)
open CommutativeMonoid using (Carrier; monoid; identityʳ)
open CommutativeMonoid⇒ using (arr; monoid⇒)
open MonoidObject using (Monoid; Monoid⇒)
open Monoid⇒ using (preserves-μ; preserves-η)

CMon[S] : Category (suc ℓ) ℓ ℓ
CMon[S] = CMonoids S.symmetric

Free : Functor S.U CMon[S]
Free = Free′

Forget : Functor CMon[S] S.U
Forget = Monoid.Forget ∘F CMonoid.Forget

opaque
  unfolding [-]ₛ
  map-[-]ₛ
      : {X Y : Setoid ℓ ℓ}
        (f : X ⟶ₛ Y)
        {x : ∣ X ∣}
      → (open Setoid (Multisetₛ Y))
      → [-]ₛ ⟨$⟩ (f ⟨$⟩ x)
      ≈ arr (mapₘ f) ⟨$⟩ ([-]ₛ ⟨$⟩ x)
  map-[-]ₛ {X} {Y} f {x} = Setoid.refl (Multisetₛ Y)

unit : NaturalTransformation id (Forget ∘F Free)
unit = ntHelper record
    { η = λ X → [-]ₛ {ℓ} {ℓ} {X}
    ; commute = map-[-]ₛ
    }

opaque
  unfolding toMonoid MultisetCMonoid
  foldₘ : (X : CommutativeMonoid) → CommutativeMonoid⇒ (Multisetₘ (Carrier X)) X
  foldₘ X .monoid⇒ .Monoid⇒.arr = foldₛ (toCMonoid X)
  foldₘ X .monoid⇒ .preserves-μ {xs , ys} = ++ₛ-homo (toCMonoid X) xs ys
  foldₘ X .monoid⇒ .preserves-η {_} = []ₛ-homo (toCMonoid X)

opaque
  unfolding foldₘ toMonoid⇒
  fold-mapₘ
      : {X Y : CommutativeMonoid}
        (f : CommutativeMonoid⇒ X Y)
        {x : ∣ Multisetₛ (Carrier X) ∣}
      → (open Setoid (Carrier Y))
      → arr (foldₘ Y) ⟨$⟩ (arr (mapₘ (arr f)) ⟨$⟩ x)
      ≈ arr f ⟨$⟩ (arr (foldₘ X) ⟨$⟩ x)
  fold-mapₘ {X} {Y} f = uncurry (fold-mapₛ (toCMonoid X) (toCMonoid Y)) (toCMonoid⇒ X Y f)

counit : NaturalTransformation (Free ∘F Forget) id
counit = ntHelper record
    { η = foldₘ
    ; commute = fold-mapₘ
    }

opaque
  unfolding foldₘ fold Multisetₛ
  zig : (Aₛ  : Setoid ℓ ℓ)
        {xs : ∣ Multisetₛ Aₛ ∣}
      → (open Setoid (Multisetₛ Aₛ))
      → arr (foldₘ (Multisetₘ Aₛ)) ⟨$⟩ (arr (mapₘ [-]ₛ) ⟨$⟩ xs) ≈ xs
  zig Aₛ {L.[]} = ↭.↭-refl Aₛ
  zig Aₛ {x L.∷ xs} = ↭.prep (Setoid.refl Aₛ) (zig Aₛ)

opaque
  unfolding foldₘ fold
  zag : (M : CommutativeMonoid)
        {x : ∣ Carrier M ∣}
      → (open Setoid (Carrier M))
      → arr (foldₘ M) ⟨$⟩ ([-]ₛ ⟨$⟩ x) ≈ x
  zag M {x} = Setoid.sym (Carrier M) (identityʳ M {x , _})

Multiset⊣ : Free ⊣ Forget
Multiset⊣ = record
    { unit = unit
    ; counit = counit
    ; zig = λ {X} → zig X
    ; zag = λ {M} → zag M
    }
