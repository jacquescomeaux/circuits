{-# OPTIONS --without-K --safe #-}

module NaturalTransformation.Instance.GateSemantics where

open import Level using (suc; 0ℓ)
open import Category.Instance.Setoids.SymmetricMonoidal {suc 0ℓ} {suc 0ℓ} using (Setoids-×)

import Data.Fin.Properties as FinProp
import Data.Circuit.Value as Value
import Functor.Forgetful.Instance.CMonoid Setoids-×.symmetric as CMonoid
import Functor.Forgetful.Instance.Monoid Setoids-×.monoidal as Monoid

open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor) renaming (_∘F_ to _∙_)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Category.Construction.CMonoids Setoids-×.symmetric using (CMonoids)
open import Data.Circuit {suc 0ℓ} using () renaming (module Edge to EGate)
open import Data.Circuit.Gate using (Gate; Gates)
open import Data.Fin using (Fin; #_)
open import Data.Fin.Patterns using (0F; 1F; 2F)
open import Data.Nat using (ℕ)
open import Data.Setoid using (∣_∣; _⇒ₛ_)
open import Data.Setoid.Unit using (⊤ₛ)
open import Data.System {suc 0ℓ} using (System)
open import Data.System.Values Value.Monoid using (Values)
open import Function using (Func; _⟶ₛ_; id; _⟨$⟩_)
open import Function.Construct.Constant using () renaming (function to Const)
open import Function.Construct.Identity using () renaming (function to Id)
open import Functor.Instance.Nat.Edge {suc 0ℓ} Gates using (Edge)
open import Functor.Instance.Nat.System using (module NatCMon)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open Value using (Value)
open NatCMon using (Sys)
open System
open Func

Valueₛ : Setoid 0ℓ 0ℓ
Valueₛ = ≡.setoid Value

opaque

  unfolding Values

  1-cell : Value → System 1
  1-cell x .S = ⊤ₛ
  1-cell x .fₛ = Const (Values 1) (⊤ₛ ⇒ₛ ⊤ₛ) (Id ⊤ₛ)
  1-cell x .fₒ = Const ⊤ₛ (Values 1) λ { 0F → x }

  2-cell : (Value → Value) → System 2
  2-cell f .S = Valueₛ
  2-cell f .fₛ .to x = Const Valueₛ Valueₛ (f (x (# 0)))
  2-cell f .fₛ .cong x = ≡.cong f (x (# 0))
  2-cell f .fₒ .to x 0F = Value.U
  2-cell f .fₒ .to x 1F = x
  2-cell f .fₒ .cong _ 0F = ≡.refl
  2-cell f .fₒ .cong x 1F = x

  3-cell : (Value → Value → Value) → System 3
  3-cell f .S = Valueₛ
  3-cell f .fₛ .to i = Const Valueₛ Valueₛ (f (i (# 0)) (i (# 1)))
  3-cell f .fₛ .cong ≡i = ≡.cong₂ f (≡i (# 0)) (≡i (# 1))
  3-cell f .fₒ .to _ 0F = Value.U
  3-cell f .fₒ .to _ 1F = Value.U
  3-cell f .fₒ .to x 2F = x
  3-cell f .fₒ .cong _ 0F = ≡.refl
  3-cell f .fₒ .cong _ 1F = ≡.refl
  3-cell f .fₒ .cong x 2F = x

-- Belnap's four-valued logic
module Belnap where

  open Value.Value

  true false : Value
  true = T
  false = F

  not : Value → Value
  not U = U
  not T = F
  not F = T
  not X = X

  and : Value → Value → Value
  and U U = U
  and U T = U
  and U F = F
  and U X = F
  and T y = y
  and F _ = F
  and X U = F
  and X T = X
  and X F = F
  and X X = X

  or : Value → Value → Value
  or U U = U
  or U T = T
  or U F = U
  or U X = T
  or T _ = T
  or F y = y
  or X U = T
  or X T = T
  or X F = X
  or X X = X

  xor : Value → Value → Value
  xor x y = or (and x (not y)) (and (not x) y)

  nand : Value → Value → Value
  nand x y = not (and x y)

  nor : Value → Value → Value
  nor x y = not (or x y)

  xnor : Value → Value → Value
  xnor x y = not (xor x y)

module _ where

  open Belnap
  open Gate

  system-of-gate : {n : ℕ} → Gate n → System n
  system-of-gate ZERO = 1-cell true
  system-of-gate ONE  = 1-cell false
  system-of-gate ID   = 2-cell id
  system-of-gate NOT  = 2-cell not
  system-of-gate AND  = 3-cell and
  system-of-gate OR   = 3-cell or
  system-of-gate XOR  = 3-cell xor
  system-of-gate NAND = 3-cell nand
  system-of-gate NOR  = 3-cell nor
  system-of-gate XNOR = 3-cell xnor

private

  U : Functor CMonoids (Setoids (suc 0ℓ) (suc 0ℓ))
  U = Monoid.Forget ∙ CMonoid.Forget

  module U = Functor U
  module Edge = Functor Edge

open EGate hiding (Edge)

system-of-edge : {n : ℕ} → ∣ Edge.₀ n ∣ → System n
system-of-edge (mkEdge gate ports) = U.₁ (Sys.₁ ports) ⟨$⟩ system-of-gate gate

system-of-edgeₛ : (n : ℕ) → Edge.₀ n ⟶ₛ U.₀ (Sys.₀ n)
system-of-edgeₛ n .to = system-of-edge {n}
system-of-edgeₛ n .cong {mkEdge label₁ ports₁} {mkEdge label₂ ports₂} (mk≈ ≡.refl ≡.refl ≡ports)
    rewrite EGate.HL.cast-is-id ≡.refl label₁ = Sys.F-resp-≈ ≗ports {system-of-gate label₁}
  where
    ≗ports : (x : Fin _) → ports₁ x ≡ ports₂ x
    ≗ports x = ≡.trans (≡ports x) (≡.cong ports₂ (FinProp.cast-is-id ≡.refl x))

semantics : NaturalTransformation Edge (U ∙ Sys)
semantics = ntHelper record
    { η = system-of-edgeₛ
    ; commute = λ _ → Sys.homomorphism
    }
