{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_; suc)

module SplitIdempotents.CMonoids {c ℓ : Level} where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import SplitIdempotents.Monoids as SIM

open import Category.Instance.Setoids.SymmetricMonoidal {c} {ℓ} using (Setoids-×; ×-symmetric′)

open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Object.Monoid Setoids-×.monoidal using (Monoid)
open import Category.Construction.CMonoids Setoids-×.symmetric using (CMonoids)
open import Category.KaroubiComplete CMonoids using (KaroubiComplete)
open import Data.Product using (_,_)
open import Data.Setoid using (∣_∣)
open import Function using (_⟶ₛ_; _⟨$⟩_)
open import Function.Construct.Setoid using (_∙_)
open import Object.Monoid.Commutative Setoids-×.symmetric using (CommutativeMonoid; CommutativeMonoid⇒)
open import Relation.Binary using (Setoid)

open Category CMonoids using (_∘_; _≈_)
open Symmetric Setoids-×.symmetric using (_⊗₀_; unit; _⊗₁_)

module _ {M : CommutativeMonoid} (F : CommutativeMonoid⇒ M M) where

  private
    module M = CommutativeMonoid M
    module F = CommutativeMonoid⇒ F

  module MQ = Monoid (SIM.Q F.monoid⇒)

  X : Setoid c ℓ
  X = MQ.Carrier

  private
    module X = Setoid X
    module S = Setoid M.Carrier

  open ≈-Reasoning M.Carrier

  opaque
    unfolding ×-symmetric′ SIM.μ
    comm
        : {x : ∣ MQ.Carrier ⊗₀ MQ.Carrier ∣}
        → (MQ.μ ⟨$⟩ x)
        X.≈ (MQ.μ ∙ Setoids-×.braiding.⇒.η (X , X) ⟨$⟩ x)
    comm {x , y} = begin
        F.arr ⟨$⟩ (MQ.μ ⟨$⟩ (x , y))          ≈⟨ F.preserves-μ ⟩
        MQ.μ ⟨$⟩ (F.arr ⟨$⟩ x , F.arr ⟨$⟩ y)  ≈⟨ M.commutative ⟩
        MQ.μ ⟨$⟩ (F.arr ⟨$⟩ y , F.arr ⟨$⟩ x)  ≈⟨ F.preserves-μ ⟨
        F.arr ⟨$⟩ (MQ.μ ⟨$⟩ (y , x))          ∎

  Q : CommutativeMonoid
  Q = record
      { Carrier = X
      ; isCommutativeMonoid = record
          { isMonoid = MQ.isMonoid
          ; commutative = comm
          }
      }

  M⇒Q : CommutativeMonoid⇒ M Q
  M⇒Q = record
      { monoid⇒ = SIM.M⇒Q F.monoid⇒
      }

  Q⇒M : CommutativeMonoid⇒ Q M
  Q⇒M = record
      { monoid⇒ = SIM.Q⇒M F.monoid⇒
      }

Monoids-KaroubiComplete : KaroubiComplete
Monoids-KaroubiComplete = record
    { split = λ {A} {f} f∘f≈f → record
        { obj = Q f
        ; retract = M⇒Q f
        ; section = Q⇒M f
        ; retracts = f∘f≈f
        ; splits = Setoid.refl (CommutativeMonoid.Carrier A)
        }
    }
