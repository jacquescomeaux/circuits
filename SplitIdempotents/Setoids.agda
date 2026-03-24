{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module SplitIdempotents.Setoids {c ℓ : Level} where

open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_; id)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (_∙_)
open import Relation.Binary using (Setoid)
open import Morphism.SplitIdempotent (Setoids c ℓ) using (IsSplitIdempotent)

open Category (Setoids c ℓ) using (_≈_)
open Func using (cong)

module _ {S : Setoid c ℓ} (f : S ⟶ₛ S)  where

  private
    module S = Setoid S

  Q : Setoid c ℓ
  Q = record
      { Carrier = S.Carrier
      ; _≈_ = λ a b → f ⟨$⟩ a S.≈ f ⟨$⟩ b
      ; isEquivalence = record
          { refl = S.refl
          ; sym = S.sym
          ; trans = S.trans
          }
      }

  to : S ⟶ₛ Q
  to = record
      { to = id
      ; cong = cong f
      }

  from : Q ⟶ₛ S
  from = record
      { to = f ⟨$⟩_
      ; cong = id
      }

  from∘to : from ∙ to ≈ f
  from∘to = S.refl

  module _ (idem : (f ∙ f) ≈ f) where

    to∘from : to ∙ from ≈ Id Q
    to∘from = idem

    split : IsSplitIdempotent f
    split = record
        { B = Q
        ; r = to
        ; s = from
        ; s∘r = from∘to
        ; r∘s = to∘from
        }
