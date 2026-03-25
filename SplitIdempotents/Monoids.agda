{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_; suc)

module SplitIdempotents.Monoids {c ℓ : Level} where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Category.Instance.Setoids.SymmetricMonoidal {c} {ℓ} using (Setoids-×; ×-monoidal′)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Monoids Setoids-×.monoidal using (Monoids)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Object.Monoid Setoids-×.monoidal using (Monoid; Monoid⇒)
open import Category.KaroubiComplete Monoids using (KaroubiComplete)
open import Data.Product using (_,_)
open import Data.Setoid using (∣_∣)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_; id)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (_∙_)
open import Relation.Binary using (Setoid)
open import SplitIdempotents.Setoids using () renaming (Q to Q′)

open Category Monoids using (_∘_; _≈_) renaming (id to Id⇒)
open Func
open Monoidal Setoids-×.monoidal using (_⊗₀_; unit; _⊗₁_)

module _ {M : Monoid} (F : Monoid⇒ M M) where

  private
    module M = Monoid M
    module F = Monoid⇒ F

  X′ : Setoid c ℓ
  X′ = Q′ F.arr

  private
    module S = Setoid M.Carrier
    module X′ = Setoid X′

  open ≈-Reasoning M.Carrier

  opaque
    unfolding ×-monoidal′
    μ : X′ ⊗₀ X′ ⟶ₛ X′
    μ = record
        { to = λ (x , y) → M.μ ⟨$⟩ (x , y)
        ; cong = λ { {A , B} {C , D} (FA≈FB , FC≈FD) → begin
            F.arr ⟨$⟩ (M.μ ⟨$⟩ (A , B))         ≈⟨ F.preserves-μ ⟩
            M.μ ⟨$⟩ (F.arr ⟨$⟩ A , F.arr ⟨$⟩ B) ≈⟨ cong M.μ (FA≈FB , FC≈FD) ⟩
            M.μ ⟨$⟩ (F.arr ⟨$⟩ C , F.arr ⟨$⟩ D) ≈⟨ F.preserves-μ ⟨
            F.arr ⟨$⟩ (M.μ ⟨$⟩ (C , D))         ∎
          }
        }

  η : unit ⟶ₛ X′
  η = record
      { to = to M.η
      ; cong = λ { {A} {B} eq → begin
          F.arr ⟨$⟩ (M.η ⟨$⟩ A) ≈⟨ F.preserves-η ⟩
          M.η ⟨$⟩ A             ≈⟨ cong M.η eq ⟩
          M.η ⟨$⟩ B             ≈⟨ F.preserves-η ⟨
          F.arr ⟨$⟩ (M.η ⟨$⟩ B) ∎
        }
      }

  opaque
    unfolding μ
    assoc
        : {x : ∣ (X′ ⊗₀ X′) ⊗₀ X′ ∣}
        → μ ∙ μ ⊗₁ Setoids-×.id ⟨$⟩ x
        X′.≈ (μ ∙ Id X′ ⊗₁ μ ∙ Setoids-×.associator.from ⟨$⟩ x)
    assoc {(x , y) , z} = begin
        F.arr ⟨$⟩ (μ ⟨$⟩ (μ ⟨$⟩ (x , y) , z))                   ≈⟨ F.preserves-μ ⟩
        μ ⟨$⟩ (F.arr ⟨$⟩ (μ ⟨$⟩ (x , y)) , F.arr ⟨$⟩ z)         ≈⟨ cong M.μ (F.preserves-μ , X′.refl) ⟩
        μ ⟨$⟩ (μ ⟨$⟩ (F.arr ⟨$⟩ x , F.arr ⟨$⟩ y) , F.arr ⟨$⟩ z) ≈⟨ M.assoc ⟩
        μ ⟨$⟩ (F.arr ⟨$⟩ x , μ ⟨$⟩ (F.arr ⟨$⟩ y , F.arr ⟨$⟩ z)) ≈⟨ cong M.μ (X′.refl , F.preserves-μ) ⟨
        μ ⟨$⟩ (F.arr ⟨$⟩ x , F.arr ⟨$⟩ (μ ⟨$⟩ (y , z)))         ≈⟨ F.preserves-μ ⟨
        F.arr ⟨$⟩ (μ ⟨$⟩ (x , μ ⟨$⟩ (y , z)))                   ∎

  opaque
    unfolding μ
    identityˡ
        : {x : ∣ unit ⊗₀ X′ ∣}
        → (Setoids-×.unitorˡ.from ⟨$⟩ x)
        X′.≈ (μ ∙ η ⊗₁ Id X′ ⟨$⟩ x)
    identityˡ {_ , x} = begin
        F.arr ⟨$⟩ x                               ≈⟨ M.identityˡ ⟩
        μ ⟨$⟩ (η ⟨$⟩ _ , F.arr ⟨$⟩ x)             ≈⟨ cong M.μ (F.preserves-η , X′.refl) ⟨
        μ ⟨$⟩ (F.arr ⟨$⟩ (η ⟨$⟩ _) , F.arr ⟨$⟩ x) ≈⟨ F.preserves-μ ⟨
        F.arr ⟨$⟩ (μ ⟨$⟩ (η ⟨$⟩ _ , x))           ∎

  opaque
    unfolding μ
    identityʳ
        : {x : ∣ X′ ⊗₀ unit ∣}
        → (Setoids-×.unitorʳ.from ⟨$⟩ x)
        X′.≈ (μ ∙ Id _ ⊗₁ η ⟨$⟩ x)
    identityʳ {x , _} = begin
        F.arr ⟨$⟩ x                               ≈⟨ M.identityʳ ⟩
        μ ⟨$⟩ (F.arr ⟨$⟩ x , η ⟨$⟩ _)             ≈⟨ cong M.μ (X′.refl , F.preserves-η) ⟨
        μ ⟨$⟩ (F.arr ⟨$⟩ x , F.arr ⟨$⟩ (η ⟨$⟩ _)) ≈⟨ F.preserves-μ ⟨
        F.arr ⟨$⟩ (μ ⟨$⟩ (x , to M.η _))          ∎

  Q : Monoid
  Q = record
      { Carrier = X′
      ; isMonoid = record
          { μ = μ
          ; η = η
          ; assoc = assoc
          ; identityˡ = identityˡ
          ; identityʳ = identityʳ
          }
      }

  M⇒Q : Monoid⇒ M Q
  M⇒Q = record
      { arr = arr
      ; preserves-μ = preserves-μ
      ; preserves-η = S.refl
      }
    where
      arr : M.Carrier ⟶ₛ X′
      arr = record
          { to = id
          ; cong = cong F.arr
          }
      opaque
        unfolding μ
        preserves-μ : {x : ∣ M.Carrier ⊗₀ M.Carrier ∣} → (arr ∙ M.μ ⟨$⟩ x) X′.≈ (μ ∙ arr ⊗₁ arr ⟨$⟩ x)
        preserves-μ = S.refl

  Q⇒M : Monoid⇒ Q M
  Q⇒M = record
      { arr = arr
      ; preserves-μ = preserves-μ
      ; preserves-η = F.preserves-η
      }
    where
      arr : X′ ⟶ₛ M.Carrier
      arr = record
          { to = to F.arr
          ; cong = id
          }
      opaque
        unfolding μ
        preserves-μ : {x : ∣ X′ ⊗₀ X′ ∣} → arr ∙ μ ⟨$⟩ x S.≈ M.μ ∙ arr ⊗₁ arr ⟨$⟩ x
        preserves-μ = F.preserves-μ

Monoids-KaroubiComplete : KaroubiComplete
Monoids-KaroubiComplete = record
    { split = λ {A} {f} f∘f≈f → record
        { obj = Q f
        ; retract = M⇒Q f
        ; section = Q⇒M f
        ; retracts = f∘f≈f
        ; splits = Setoid.refl (Monoid.Carrier A)
        }
    }
