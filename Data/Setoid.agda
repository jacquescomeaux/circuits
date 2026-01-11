{-# OPTIONS --without-K --safe #-}

module Data.Setoid where

open import Data.Product using (_,_)
open import Data.Product.Function.NonDependent.Setoid using (_×-function_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Function using (Func; _⟶ₛ_)
open import Function.Construct.Setoid using () renaming (setoid to infixr 0 _⇒ₛ_) public
open import Level using (Level)
open import Relation.Binary using (Setoid)

open Setoid renaming (Carrier to ∣_∣) public

open Func

_×-⇒_
    : {c₁ c₂ c₃ c₄ c₅ c₆ : Level}
      {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}
      {A : Setoid c₁ ℓ₁}
      {B : Setoid c₂ ℓ₂}
      {C : Setoid c₃ ℓ₃}
      {D : Setoid c₄ ℓ₄}
      {E : Setoid c₅ ℓ₅}
      {F : Setoid c₆ ℓ₆}
    → A ⟶ₛ B ⇒ₛ C
    → D ⟶ₛ E ⇒ₛ F
    → A ×ₛ D ⟶ₛ B ×ₛ E ⇒ₛ C ×ₛ F
_×-⇒_ f g .to (x , y) = to f x ×-function to g y
_×-⇒_ f g .cong (x , y) = cong f x , cong g y

assocₛ⇒
    : {c₁ c₂ c₃ : Level}
      {ℓ₁ ℓ₂ ℓ₃ : Level}
      {A : Setoid c₁ ℓ₁}
      {B : Setoid c₂ ℓ₂}
      {C : Setoid c₃ ℓ₃}
    → (A ×ₛ B) ×ₛ C ⟶ₛ A ×ₛ (B ×ₛ C)
assocₛ⇒ .to ((x , y) , z) = x , (y , z)
assocₛ⇒ .cong ((≈x , ≈y) , ≈z) = ≈x , (≈y , ≈z)

assocₛ⇐
    : {c₁ c₂ c₃ : Level}
      {ℓ₁ ℓ₂ ℓ₃ : Level}
      {A : Setoid c₁ ℓ₁}
      {B : Setoid c₂ ℓ₂}
      {C : Setoid c₃ ℓ₃}
    → A ×ₛ (B ×ₛ C) ⟶ₛ (A ×ₛ B) ×ₛ C
assocₛ⇐ .to (x , (y , z)) = (x , y) , z
assocₛ⇐ .cong (≈x , (≈y , ≈z)) = (≈x , ≈y) , ≈z
