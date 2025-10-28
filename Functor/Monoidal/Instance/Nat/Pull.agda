{-# OPTIONS --without-K --safe #-}

module Functor.Monoidal.Instance.Nat.Pull where

open import Category.Monoidal.Instance.Nat using (Natop,+,0; Natop-Cartesian)
open import Categories.Category.Instance.Nat using (Nat-Cocartesian)
open import Categories.Category.Instance.SingletonSet using (SingletonSetoid)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; niHelper)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cocartesian using (Cocartesian; BinaryCoproducts)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (_∘F_)
open import Data.Subset.Functional using (Subset)
open import Data.Nat.Base using (ℕ; _+_)
open import Relation.Binary using (Setoid)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Product.Base using (_,_; _×_; Σ)
open import Data.Vec.Functional using ([]; _++_)
open import Data.Vec.Functional.Properties using (++-cong)
open import Data.Vec.Functional using (Vector; [])
open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)
open import Functor.Instance.Nat.Pull using (Pull; Pull₁)
open import Level using (0ℓ; Level)

open import Data.Fin.Permutation using (Permutation; _⟨$⟩ʳ_; _⟨$⟩ˡ_)
open Cartesian (Setoids-Cartesian {0ℓ} {0ℓ}) using (products)
open BinaryProducts products using (-×-)
open Cocartesian Nat-Cocartesian using (module Dual; _+₁_; +-assocʳ; +-comm; +-swap; +₁∘+-swap; i₁; i₂)
open Dual.op-binaryProducts using () renaming (-×- to -+-; assocˡ∘⟨⟩ to []∘assocʳ; swap∘⟨⟩ to []∘swap)

open import Data.Fin.Base using (Fin; splitAt; join; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (splitAt-join; splitAt-↑ˡ; splitAt-↑ʳ; join-splitAt)
open import Data.Sum.Base using ([_,_]′; map; map₁; map₂; inj₁; inj₂)
open import Data.Sum.Properties using ([,]-map; [,]-cong; [-,]-cong; [,-]-cong; [,]-∘)
open import Data.Fin.Preimage using (preimage)
open import Function.Base using (_∘_; id)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_; module ≡-Reasoning)
open import Data.Bool.Base using (Bool)
open import Data.Setoid using (∣_∣)
open import Data.Circuit.Value using (Value)
open import Data.System.Values Value using (Values)

open import Category.Instance.Setoids.SymmetricMonoidal {0ℓ} {0ℓ} using (Setoids-×)
open import Categories.Functor.Monoidal.Symmetric Natop,+,0 Setoids-× using (module Strong)
open Strong using (SymmetricMonoidalFunctor)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

module Setoids-× = SymmetricMonoidalCategory Setoids-×
import Function.Construct.Constant as Const

open Func

module _ where

  open import Categories.Morphism (Setoids-×.U) using (_≅_; module Iso)
  open import Data.Unit.Polymorphic using (tt)
  open _≅_
  open Iso

  Pull-ε : SingletonSetoid ≅ Values 0
  from Pull-ε = Const.function SingletonSetoid (Values 0) []
  to Pull-ε = Const.function (Values 0) SingletonSetoid tt
  isoˡ (iso Pull-ε) = tt
  isoʳ (iso Pull-ε) ()

++ₛ : {n m : ℕ} → Values n ×ₛ Values m ⟶ₛ Values (n + m)
to ++ₛ (xs , ys) = xs ++ ys
cong ++ₛ (≗xs , ≗ys) = ++-cong _ _ ≗xs ≗ys

splitₛ : {n m : ℕ} → Values (n + m) ⟶ₛ Values n ×ₛ Values m
to (splitₛ {n} {m}) v = v ∘ (_↑ˡ m) , v ∘ (n ↑ʳ_)
cong (splitₛ {n} {m}) v₁≋v₂ = v₁≋v₂ ∘ (_↑ˡ m) , v₁≋v₂ ∘ (n ↑ʳ_)

Pull-++
    : {n n′ m m′ : ℕ}
      (f : Fin n → Fin n′)
      (g : Fin m → Fin m′)
      {xs : ∣ Values n′ ∣}
      {ys : ∣ Values m′ ∣}
    → (Pull₁ f ⟨$⟩ xs) ++ (Pull₁ g ⟨$⟩ ys) ≗ Pull₁ (f +₁ g) ⟨$⟩ (xs ++ ys)
Pull-++ {n} {n′} {m} {m′} f g {xs} {ys} e = begin
    (xs ∘ f ++ ys ∘ g) e                                            ≡⟨ [,]-map (splitAt n e) ⟨
    [ xs , ys ]′ (map f g (splitAt n e))                            ≡⟨ ≡.cong [ xs , ys ]′ (splitAt-join n′ m′ (map f g (splitAt n e))) ⟨
    [ xs , ys ]′ (splitAt n′ (join n′ m′ (map f g (splitAt n e))))  ≡⟨ ≡.cong ([ xs , ys ]′ ∘ splitAt n′) ([,]-map (splitAt n e)) ⟩
    [ xs , ys ]′ (splitAt n′ ((f +₁ g) e))                          ∎
  where
    open ≡-Reasoning

⊗-homomorphism : NaturalIsomorphism (-×- ∘F (Pull ⁂ Pull)) (Pull ∘F -+-)
⊗-homomorphism = niHelper record
    { η = λ (n , m) → ++ₛ {n} {m}
    ; η⁻¹ = λ (n , m) → splitₛ {n} {m}
    ; commute = λ (f , g) → Pull-++ f g
    ; iso = λ (n , m) → record
        { isoˡ = λ { {x , y} → (λ i → ≡.cong [ x , y ] (splitAt-↑ˡ n i m)) , (λ i → ≡.cong [ x , y ] (splitAt-↑ʳ n m i)) }
        ; isoʳ = λ { {x} i → ≡.trans (≡.sym ([,]-∘ x (splitAt n i))) (≡.cong x (join-splitAt n m i)) }
        }
    }
  where
    open import Data.Sum.Base using ([_,_])
    open import Data.Product.Base using (proj₁; proj₂)

++-↑ˡ
    : {n m : ℕ}
      (X : ∣ Values n ∣)
      (Y : ∣ Values m ∣)
    → (X ++ Y) ∘ i₁ ≗ X
++-↑ˡ {n} {m} X Y i = ≡.cong [ X , Y ]′ (splitAt-↑ˡ n i m)

++-↑ʳ
    : {n m : ℕ}
      (X : ∣ Values n ∣)
      (Y : ∣ Values m ∣)
    → (X ++ Y) ∘ i₂ ≗ Y
++-↑ʳ {n} {m} X Y i = ≡.cong [ X , Y ]′ (splitAt-↑ʳ n m i)

-- TODO move to Data.Vector
++-assoc
    : {m n o : ℕ}
      (X : ∣ Values m ∣)
      (Y : ∣ Values n ∣)
      (Z : ∣ Values o ∣)
    → ((X ++ Y) ++ Z) ∘ +-assocʳ {m} ≗ X ++ (Y ++ Z)
++-assoc {m} {n} {o} X Y Z i = begin
    ((X ++ Y) ++ Z) (+-assocʳ {m} i)                                    ≡⟨⟩
    ((X ++ Y) ++ Z) ([ i₁ ∘ i₁ , _ ]′ (splitAt m i))                    ≡⟨ [,]-∘ ((X ++ Y) ++ Z) (splitAt m i) ⟩
    [ ((X ++ Y) ++ Z) ∘ i₁ ∘ i₁ , _ ]′ (splitAt m i)                    ≡⟨ [-,]-cong (++-↑ˡ (X ++ Y) Z ∘ i₁) (splitAt m i) ⟩
    [ (X ++ Y) ∘ i₁ , _ ]′ (splitAt m i)                                ≡⟨ [-,]-cong (++-↑ˡ X Y) (splitAt m i) ⟩
    [ X , ((X ++ Y) ++ Z) ∘ [ _ , _ ]′ ∘ splitAt n ]′ (splitAt m i)     ≡⟨ [,-]-cong ([,]-∘ ((X ++ Y) ++ Z) ∘ splitAt n) (splitAt m i) ⟩
    [ X , [ (_ ++ Z) ∘ i₁ ∘ i₂ {m} , _ ]′ ∘ splitAt n ]′ (splitAt m i)  ≡⟨ [,-]-cong ([-,]-cong (++-↑ˡ (X ++ Y) Z ∘ i₂) ∘ splitAt n) (splitAt m i) ⟩
    [ X , [ (X ++ Y) ∘ i₂ , _ ]′ ∘ splitAt n ]′ (splitAt m i)           ≡⟨ [,-]-cong ([-,]-cong (++-↑ʳ X Y) ∘ splitAt n) (splitAt m i) ⟩
    [ X , [ Y , ((X ++ Y) ++ Z) ∘ i₂ ]′ ∘ splitAt n ]′ (splitAt m i)    ≡⟨ [,-]-cong ([,-]-cong (++-↑ʳ (X ++ Y) Z) ∘ splitAt n) (splitAt m i) ⟩
    [ X , [ Y , Z ]′ ∘ splitAt n ]′ (splitAt m i)                       ≡⟨⟩
    (X ++ (Y ++ Z)) i                                                   ∎
  where
    open Bool
    open Fin
    open ≡-Reasoning

-- TODO also Data.Vector
Pull-unitaryˡ
    : {n : ℕ}
      (X : ∣ Values n ∣)
    → (X ++ []) ∘ i₁ ≗ X
Pull-unitaryˡ {n} X i = begin
    [ X , [] ]′ (splitAt _ (i ↑ˡ 0))  ≡⟨ ≡.cong ([ X , [] ]′) (splitAt-↑ˡ n i 0) ⟩
    [ X , [] ]′ (inj₁ i)              ≡⟨⟩
    X i                               ∎
  where
    open ≡-Reasoning

open import Function.Bundles using (Inverse)
open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Morphism Nat using (_≅_)
Pull-swap
    : {n m : ℕ}
      (X : ∣ Values n ∣)
      (Y : ∣ Values m ∣)
    → (X ++ Y) ∘ (+-swap {n}) ≗ Y ++ X
Pull-swap {n} {m} X Y i = begin
    ((X ++ Y) ∘ +-swap {n}) i                         ≡⟨ [,]-∘ (X ++ Y) (splitAt m i) ⟩
    [ (X ++ Y) ∘ i₂ , (X ++ Y) ∘ i₁ ]′ (splitAt m i)  ≡⟨ [-,]-cong (++-↑ʳ X Y) (splitAt m i) ⟩
    [ Y , (X ++ Y) ∘ i₁ ]′ (splitAt m i)              ≡⟨ [,-]-cong (++-↑ˡ X Y) (splitAt m i) ⟩
    [ Y , X ]′ (splitAt m i)                          ≡⟨⟩
    (Y ++ X) i                                        ∎
  where
    open ≡-Reasoning
    open Inverse
    module +-swap = _≅_ (+-comm {m} {n})
    n+m↔m+n : Permutation (n + m) (m + n)
    n+m↔m+n .to = +-swap.to
    n+m↔m+n .from = +-swap.from
    n+m↔m+n .to-cong ≡.refl = ≡.refl
    n+m↔m+n .from-cong ≡.refl = ≡.refl
    n+m↔m+n .inverse = (λ { ≡.refl → +-swap.isoˡ _ }) , (λ { ≡.refl → +-swap.isoʳ _ })

open SymmetricMonoidalFunctor
Pull,++,[] : SymmetricMonoidalFunctor
Pull,++,[] .F = Pull
Pull,++,[] .isBraidedMonoidal = record
    { isStrongMonoidal = record
        { ε = Pull-ε
        ; ⊗-homo = ⊗-homomorphism
        ; associativity = λ { {m} {n} {o} {(X , Y) , Z} i → ++-assoc X Y Z i  }
        ; unitaryˡ = λ _ → ≡.refl
        ; unitaryʳ = λ { {n} {X , _} i → Pull-unitaryˡ X i }
        }
    ; braiding-compat = λ { {n} {m} {X , Y} i → Pull-swap X Y i }
    }
