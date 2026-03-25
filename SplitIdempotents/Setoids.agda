{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module SplitIdempotents.Setoids {c ℓ : Level} where

open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Category.KaroubiComplete (Setoids c ℓ) using (KaroubiComplete)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_; id)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (_∙_)
open import Relation.Binary using (Setoid)

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

Setoids-KaroubiComplete : KaroubiComplete
Setoids-KaroubiComplete = record
    { split = λ {A} {f} idem → record
        { obj = Q f
        ; retract = to f
        ; section = from f
        ; retracts = idem
        ; splits = Setoid.refl A
        }
    }
