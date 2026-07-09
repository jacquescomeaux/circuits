{-# OPTIONS --without-K --safe #-}

open import Level using (Level; 0ℓ; _⊔_)

-- Functor from category of rigs to the category of categories
module Data.Matrix.Matrices {c ℓ : Level} where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra using (Semiring)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Morphism.Properties using (id-iso)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper)
open import Category.Instance.Rigs using (Rigs; RigHomomorphism; _≗_; compose) renaming (id to idRigHomo)
open import Data.Matrix.BaseChange using (ChangeBase)
open import Data.Matrix.BaseChange using (change)
open import Data.Matrix.Category as Cat using (Mat)
open import Data.Matrix.Core as Core using ()
open import Data.Matrix.Endofunctor using (mapₛ; identity; homomorphism; F-resp-≈)
open import Data.Matrix.Transform as Transform using ()
open import Data.Nat using (ℕ)

≃-identity : {A : Semiring c ℓ} → ChangeBase A A (Category.Instance.Rigs.id A) ≃ idF
≃-identity {A} = niHelper record
    { η = λ n → I {n}
    ; η⁻¹ = λ n → I {n}
    ; commute = commute
    ; iso = λ n → id-iso (Mat A)
    }
  where
    module A = Semiring A
    open Core A.setoid
    open Transform A
    open Cat A hiding (Mat)
    commute : {n m : ℕ} (M : Matrix n m) → I · change A A (idRigHomo A) M ≋ M · I
    commute {n} {m} M = begin
        I · change A A (idRigHomo A) M  ≈⟨ ·-Iˡ ⟩
        change A A (idRigHomo A) M      ≈⟨ identity n m ⟩
        M                               ≈⟨ ·-Iʳ ⟨
        M · I                           ∎
      where
        open ≈-Reasoning (Matrixₛ n m)

≃-homo
    : {X Y Z : Semiring c ℓ}
      {g : RigHomomorphism Y Z}
      {f : RigHomomorphism X Y}
    → ChangeBase X Z (compose X Y Z g f) ≃ ChangeBase Y Z g ∘F ChangeBase X Y f
≃-homo {X} {Y} {Z} {g} {f} = niHelper record
    { η = λ n → I {n}
    ; η⁻¹ = λ n → I {n}
    ; commute = commute
    ; iso = λ n → id-iso (Mat Z)
    }
  where
    module Z = Semiring Z
    module X = Semiring X
    open Core Z.setoid using (_≋_; Matrixₛ)
    open Core X.setoid using (Matrix)
    open Transform Z
    open Cat Z hiding (Mat)
    commute : {n m : ℕ} (M : Matrix n m) → I · change X Z (compose X Y Z g f) M ≋ change Y Z g (change X Y f M) · I
    commute {n} {m} M = begin
        I · change X Z (compose X Y Z g f) M  ≈⟨ ·-Iˡ ⟩
        change X Z (compose X Y Z g f) M      ≈⟨ homomorphism n m ⟩
        change Y Z g (change X Y f M)         ≈⟨ ·-Iʳ ⟨
        change Y Z g (change X Y f M) · I     ∎
      where
        open ≈-Reasoning (Matrixₛ n m)

resp-≈ : {A B : Semiring c ℓ}
    → {f g : RigHomomorphism A B}
    → f ≗ g
    → ChangeBase A B f ≃ ChangeBase A B g
resp-≈ {A} {B} {f} {g} f≗g = niHelper record
    { η = λ n → I {n}
    ; η⁻¹ = λ n → I {n}
    ; commute = commute
    ; iso = λ n → id-iso (Mat B)
    }
  where
    module A = Semiring A
    module B = Semiring B
    open Core A.setoid using (Matrix)
    open Core B.setoid using (_≋_; Matrixₛ)
    open Transform B
    open Cat B hiding (Mat)
    commute : {n m : ℕ} (M : Matrix n m) → I · change A B f M ≋ change A B g M · I
    commute {n} {m} M = begin
        I · change A B f M  ≈⟨ ·-Iˡ ⟩
        change A B f M      ≈⟨ F-resp-≈ n m (λ {x} → f≗g x) ⟩
        change A B g M      ≈⟨ ·-Iʳ ⟨
        change A B g M · I  ∎
      where
        open ≈-Reasoning (Matrixₛ n m)

Matrices : Functor (Rigs {c} {ℓ}) (Cats 0ℓ c (c ⊔ ℓ))
Matrices = record
    { F₀ = Mat
    ; F₁ = λ {R S} → ChangeBase R S
    ; identity = ≃-identity
    ; homomorphism = ≃-homo
    ; F-resp-≈ = resp-≈
    }
