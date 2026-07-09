{-# OPTIONS --without-K --safe #-}

open import Level using (Level; suc; _⊔_)

module Data.System.Looped {c ℓ : Level} where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra using (CommutativeMonoid)
open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Functor using (Functor)
open import Data.System.Category using (Systems[_,_])
open import Data.System.Core using (System; _≤_)
open import Function using (Func; _⟨$⟩_) renaming (id to idf)
open import Relation.Binary using (Setoid)

open Func
open System

private

  module _ {V : CommutativeMonoid c ℓ} where

    open CommutativeMonoid V

    loop : System setoid V → System setoid V
    loop X = record
        { S = X.S
        ; fₛ = record
            { to = λ i → record
                { to = λ s → X.fₛ′ (i ∙ X.fₒ′ s) s
                ; cong = λ {s} {s′} ≈s →
                    X.S.trans
                      (cong X.fₛ (∙-cong refl (cong X.fₒ ≈s)))
                      (cong (X.fₛ ⟨$⟩ (i ∙ X.fₒ′ s′)) ≈s)
                }
            ; cong = λ ≈v → cong X.fₛ (∙-congʳ ≈v)
            }
        ; fₒ = X.fₒ
        }
      where
        module X = System X

    loop-≤ : {A B : System setoid V} → A ≤ B → loop A ≤ loop B
    loop-≤ {A} {B} A≤B = record
        { ⇒S = A≤B.⇒S
        ; ≗-fₛ = λ i s → begin
            A≤B.⇒S ⟨$⟩ (fₛ′ (loop A) i s)                   ≈⟨ A≤B.≗-fₛ (i ∙ A.fₒ′ s) s ⟩
            B.fₛ′ (i ∙ A.fₒ′ s) (A≤B.⇒S ⟨$⟩ s)              ≈⟨ cong B.fₛ (∙-cong refl (A≤B.≗-fₒ s)) ⟩
            B.fₛ′ (i ∙ B.fₒ′ (A≤B.⇒S ⟨$⟩ s)) (A≤B.⇒S ⟨$⟩ s) ∎
        ; ≗-fₒ = A≤B.≗-fₒ
        }
      where
        module A = System A
        module B = System B
        open ≈-Reasoning B.S
        module A≤B = _≤_ A≤B

module _ (V : CommutativeMonoid c ℓ) where

  open CommutativeMonoid V using (setoid)

  Loop : Functor Systems[ setoid , V ] Systems[ setoid , V ]
  Loop = record
      { F₀ = loop
      ; F₁ = loop-≤
      ; identity = λ {A} → Setoid.refl (S A)
      ; homomorphism = λ {Z = Z} → Setoid.refl (S Z)
      ; F-resp-≈ = idf
      }

  open Category Systems[ setoid , V ]
  open Functor Loop

  Systems[_] : Category (c ⊔ suc ℓ) (c ⊔ ℓ) ℓ
  Systems[_] = categoryHelper record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = λ f g → F₁ f ≈ F₁ g
      ; id = id
      ; _∘_ = _∘_
      ; assoc = λ {f = f} {g h} → assoc {f = f} {g} {h}
      ; identityˡ = λ {A B f} → identityˡ {A} {B} {f}
      ; identityʳ = λ {A B f} → identityʳ {A} {B} {f}
      ; equiv = equiv
      ; ∘-resp-≈ = λ {f = f} {g h i} f≈g h≈i → ∘-resp-≈ {f = f} {g} {h} {i} f≈g h≈i
      }
