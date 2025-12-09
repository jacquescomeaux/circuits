{-# OPTIONS --without-K --safe #-}

module Functor.Monoidal.Instance.Nat.Pull where

import Categories.Morphism as Morphism

open import Level using (0ℓ; Level)

open import Category.Instance.Setoids.SymmetricMonoidal {0ℓ} {0ℓ} using (Setoids-×)
open import Category.Monoidal.Instance.Nat using (Natop,+,0; Natop-Cartesian)

open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cocartesian using (Cocartesian; BinaryCoproducts)
open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Category.Instance.Nat using (Nat-Cocartesian)
open import Data.Setoid.Unit using (⊤ₛ)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (_∘F_)
open import Categories.Functor.Monoidal.Symmetric Natop,+,0 Setoids-× using (module Strong)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; niHelper)
open import Data.Circuit.Value using (Monoid)
open import Data.Vector using (++-assoc)
open import Data.Fin.Base using (Fin; splitAt; join)
open import Data.Fin.Permutation using (Permutation; _⟨$⟩ʳ_; _⟨$⟩ˡ_)
open import Data.Fin.Preimage using (preimage)
open import Data.Fin.Properties using (splitAt-join; splitAt-↑ˡ; splitAt-↑ʳ; join-splitAt)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product.Base using (_,_; _×_; Σ; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Setoid using (∣_∣)
open import Data.Subset.Functional using (Subset)
open import Data.Sum.Base using ([_,_]′; map; map₁; map₂; inj₁; inj₂)
open import Data.Sum.Properties using ([,]-map; [,]-cong; [-,]-cong; [,-]-cong; [,]-∘)
open import Data.System.Values Monoid using (Values; <ε>; []-unique; _++_; ++ₛ; splitₛ; _≋_; [])
open import Data.Unit.Polymorphic using (tt)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_; _∘_)
open import Function.Construct.Constant using () renaming (function to Const)
open import Functor.Instance.Nat.Pull using (Pull; Pull-defs)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_; module ≡-Reasoning)

open Cartesian (Setoids-Cartesian {0ℓ} {0ℓ}) using (products)

open BinaryProducts products using (-×-)
open Cocartesian Nat-Cocartesian using (module Dual; _+₁_; +-assocʳ; +-comm; +-swap; +₁∘+-swap; i₁; i₂)
open Dual.op-binaryProducts using () renaming (-×- to -+-; assocˡ∘⟨⟩ to []∘assocʳ; swap∘⟨⟩ to []∘swap)
open Func
open Morphism (Setoids-×.U) using (_≅_; module Iso)
open Strong using (SymmetricMonoidalFunctor)
open ≡-Reasoning

private

  open _≅_
  open Iso

  Pull-ε : ⊤ₛ ≅ Values 0
  from Pull-ε = Const ⊤ₛ (Values 0) []
  to Pull-ε = Const (Values 0) ⊤ₛ tt
  isoˡ (iso Pull-ε) = tt
  isoʳ (iso Pull-ε) {x} = []-unique [] x

  opaque
    unfolding _++_
    unfolding Pull-defs
    Pull-++
        : {n n′ m m′ : ℕ}
          (f : Fin n → Fin n′)
          (g : Fin m → Fin m′)
          {xs : ∣ Values n′ ∣}
          {ys : ∣ Values m′ ∣}
        → (Pull.₁ f ⟨$⟩ xs) ++ (Pull.₁ g ⟨$⟩ ys) ≋ Pull.₁ (f +₁ g) ⟨$⟩ (xs ++ ys)
    Pull-++ {n} {n′} {m} {m′} f g {xs} {ys} e = begin
        (xs ∘ f ++ ys ∘ g) e                            ≡⟨ [,]-map (splitAt n e) ⟨
        [ xs , ys ]′ (map f g (splitAt n e))            ≡⟨ ≡.cong [ xs , ys ]′ (splitAt-join n′ m′ (map f g (splitAt n e))) ⟨
        (xs ++ ys) (join n′ m′ (map f g (splitAt n e))) ≡⟨ ≡.cong (xs ++ ys) ([,]-map (splitAt n e)) ⟩
        (xs ++ ys) ((f +₁ g) e)                         ∎

  module _ {n m : ℕ} where

    opaque
      unfolding splitₛ

      open import Function.Construct.Setoid using (setoid)
      open module ⇒ₛ {A} {B} = Setoid (setoid {0ℓ} {0ℓ} {0ℓ} {0ℓ} A B) using (_≈_)
      open import Function.Construct.Setoid using (_∙_)
      open import Function.Construct.Identity using () renaming (function to Id)

      split∘++ : splitₛ ∙ ++ₛ ≈ Id (Values n ×ₛ Values m)
      split∘++ {xs , ys} .proj₁ i = ≡.cong [ xs , ys ]′ (splitAt-↑ˡ n i m)
      split∘++ {xs , ys} .proj₂ i = ≡.cong [ xs , ys ]′ (splitAt-↑ʳ n m i)

      ++∘split : ++ₛ {n} ∙ splitₛ ≈ Id (Values (n + m))
      ++∘split {x} i = ≡.trans (≡.sym ([,]-∘ x (splitAt n i))) (≡.cong x (join-splitAt n m i))

  ⊗-homomorphism : NaturalIsomorphism (-×- ∘F (Pull ⁂ Pull)) (Pull ∘F -+-)
  ⊗-homomorphism = niHelper record
      { η = λ (n , m) → ++ₛ {n} {m}
      ; η⁻¹ = λ (n , m) → splitₛ {n} {m}
      ; commute = λ { {n , m} {n′ , m′} (f , g) {xs , ys} → Pull-++ f  g }
      ; iso = λ (n , m) → record
          { isoˡ = split∘++
          ; isoʳ = ++∘split
          }
      }

  module _ {n m : ℕ} where

    opaque
      unfolding Pull-++

      Pull-i₁
          : (X : ∣ Values n ∣)
            (Y : ∣ Values m ∣)
          → Pull.₁ i₁ ⟨$⟩ (X ++ Y) ≋ X
      Pull-i₁ X Y i = ≡.cong [ X , Y ]′ (splitAt-↑ˡ n i m)

      Pull-i₂
          : (X : ∣ Values n ∣)
            (Y : ∣ Values m ∣)
          → Pull.₁ i₂ ⟨$⟩ (X ++ Y) ≋ Y
      Pull-i₂ X Y i = ≡.cong [ X , Y ]′ (splitAt-↑ʳ n m i)

  opaque
    unfolding Pull-++

    Push-assoc
        : {m n o : ℕ}
          (X : ∣ Values m ∣)
          (Y : ∣ Values n ∣)
          (Z : ∣ Values o ∣)
        → Pull.₁ (+-assocʳ {m} {n} {o}) ⟨$⟩ ((X ++ Y) ++ Z) ≋ X ++ (Y ++ Z)
    Push-assoc {m} {n} {o} X Y Z i = ++-assoc X Y Z i

    Pull-swap
        : {n m : ℕ}
          (X : ∣ Values n ∣)
          (Y : ∣ Values m ∣)
        → Pull.₁ (+-swap {n}) ⟨$⟩ (X ++ Y) ≋ Y ++ X
    Pull-swap {n} {m} X Y i = begin
        ((X ++ Y) ∘ +-swap {n}) i                         ≡⟨ [,]-∘ (X ++ Y) (splitAt m i) ⟩
        [ (X ++ Y) ∘ i₂ , (X ++ Y) ∘ i₁ ]′ (splitAt m i)  ≡⟨ [-,]-cong (Pull-i₂ X Y) (splitAt m i) ⟩
        [ Y , (X ++ Y) ∘ i₁ ]′ (splitAt m i)              ≡⟨ [,-]-cong (Pull-i₁ X Y) (splitAt m i) ⟩
        [ Y , X ]′ (splitAt m i)                          ≡⟨⟩
        (Y ++ X) i                                        ∎

open SymmetricMonoidalFunctor

Pull,++,[] : SymmetricMonoidalFunctor
Pull,++,[] .F = Pull
Pull,++,[] .isBraidedMonoidal = record
    { isStrongMonoidal = record
        { ε = Pull-ε
        ; ⊗-homo = ⊗-homomorphism
        ; associativity = λ { {_} {_} {_} {(X , Y) , Z} → Push-assoc X Y Z }
        ; unitaryˡ = λ { {n} {_ , X} → Pull-i₂ {0} {n} [] X }
        ; unitaryʳ = λ { {n} {X , _} → Pull-i₁ {n} {0} X [] }
        }
    ; braiding-compat = λ { {n} {m} {X , Y} → Pull-swap X Y }
    }

module Pull,++,[] = SymmetricMonoidalFunctor Pull,++,[]
