{-# OPTIONS --without-K --safe #-}

module Functor.Monoidal.Instance.Nat.Preimage where

open import Category.Monoidal.Instance.Nat using (Natop,+,0; Natop-Cartesian)
open import Categories.Category.Instance.Nat using (Nat-Cocartesian)
open import Categories.Category.Instance.SingletonSet using (SingletonSetoid)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cocartesian using (Cocartesian; BinaryCoproducts)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (_∘F_)
open import Data.Subset.Functional using (Subset)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Product.Base using (_,_; _×_; Σ)
open import Data.Vec.Functional using ([]; _++_)
open import Data.Vec.Functional.Properties using (++-cong)
open import Data.Vec.Functional using (Vector; [])
open import Function.Bundles using (Func; _⟶ₛ_)
open import Functor.Instance.Nat.Preimage using (Preimage; Subsetₛ)
open import Level using (0ℓ)

open Cartesian (Setoids-Cartesian {0ℓ} {0ℓ}) using (products)
open BinaryProducts products using (-×-)
open Cocartesian Nat-Cocartesian using (module Dual; _+₁_; +-assocʳ; +-swap; +₁∘+-swap)
open Dual.op-binaryProducts using () renaming (-×- to -+-; assocˡ∘⟨⟩ to []∘assocʳ; swap∘⟨⟩ to []∘swap)

open import Data.Fin.Base using (Fin; splitAt; join; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (splitAt-join; splitAt-↑ˡ)
open import Data.Sum.Base using ([_,_]′; map; map₁; map₂; inj₁; inj₂)
open import Data.Sum.Properties using ([,]-map; [,]-cong; [-,]-cong; [,-]-cong; [,]-∘)
open import Data.Fin.Preimage using (preimage)
open import Function.Base using (_∘_; id)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_; module ≡-Reasoning)
open import Data.Bool.Base using (Bool)

open Func
Preimage-ε : SingletonSetoid {0ℓ} {0ℓ} ⟶ₛ Subsetₛ 0
to Preimage-ε x = []
cong Preimage-ε x ()

++ₛ : {n m : ℕ} → Subsetₛ n ×ₛ Subsetₛ m ⟶ₛ Subsetₛ (n + m)
to ++ₛ (xs , ys) = xs ++ ys
cong ++ₛ (≗xs , ≗ys) = ++-cong _ _ ≗xs ≗ys

preimage-++
    : {n n′ m m′ : ℕ}
      (f : Fin n → Fin n′)
      (g : Fin m → Fin m′)
      {xs : Subset n′}
      {ys : Subset m′}
    → preimage f xs ++ preimage g ys ≗ preimage (f +₁ g) (xs ++ ys)
preimage-++ {n} {n′} {m} {m′} f g {xs} {ys} e = begin
    (xs ∘ f ++ ys ∘ g) e                                            ≡⟨ [,]-map (splitAt n e) ⟨
    [ xs , ys ]′ (map f g (splitAt n e))                            ≡⟨ ≡.cong [ xs , ys ]′ (splitAt-join n′ m′ (map f g (splitAt n e))) ⟨
    [ xs , ys ]′ (splitAt n′ (join n′ m′ (map f g (splitAt n e))))  ≡⟨ ≡.cong ([ xs , ys ]′ ∘ splitAt n′) ([,]-map (splitAt n e)) ⟩
    [ xs , ys ]′ (splitAt n′ ((f +₁ g) e))                          ∎
  where
    open ≡-Reasoning

⊗-homomorphism : NaturalTransformation (-×- ∘F (Preimage ⁂ Preimage)) (Preimage ∘F -+-)
⊗-homomorphism = ntHelper record
    { η = λ (n , m) → ++ₛ {n} {m}
    ; commute = λ { {n′ , m′} {n , m} (f , g) {xs , ys} e → preimage-++ f g e }
    }

open import Category.Instance.Setoids.SymmetricMonoidal {0ℓ} using (Setoids-×)
open import Categories.Functor.Monoidal.Symmetric Natop,+,0 Setoids-× using (module Lax)
open Lax using (SymmetricMonoidalFunctor)

++-assoc
    : {m n o : ℕ}
      (X : Subset m)
      (Y : Subset n)
      (Z : Subset o)
    → ((X ++ Y) ++ Z) ∘ +-assocʳ {m} ≗ X ++ (Y ++ Z)
++-assoc {m} {n} {o} X Y Z i = begin
    ((X ++ Y) ++ Z) (+-assocʳ {m} i) ≡⟨⟩
    [ [ X , Y ]′ ∘ splitAt m , Z ]′ (splitAt (m + n) (+-assocʳ {m} i))          ≡⟨ [,]-cong ([,]-cong (inv ∘ X) (inv ∘ Y) ∘ splitAt m) (inv ∘ Z) (splitAt (m + n) (+-assocʳ {m} i)) ⟨
    [ [ b ∘ X′ , b ∘ Y′ ]′ ∘ splitAt m , b ∘ Z′ ]′ (splitAt _ (+-assocʳ {m} i)) ≡⟨ [-,]-cong ([,]-∘ b ∘ splitAt m) (splitAt (m + n) (+-assocʳ {m} i)) ⟨
    [ b ∘ [ X′ , Y′ ]′ ∘ splitAt m , b ∘ Z′ ]′ (splitAt _ (+-assocʳ {m} i))     ≡⟨ [,]-∘ b (splitAt (m + n) (+-assocʳ {m} i)) ⟨
    b ([ [ X′ , Y′ ]′ ∘ splitAt m , Z′ ]′ (splitAt _ (+-assocʳ {m} i)))         ≡⟨ ≡.cong b ([]∘assocʳ {2} {m} i) ⟩
    b ([ X′ , [ Y′ , Z′ ]′ ∘ splitAt n ]′ (splitAt m i))                        ≡⟨ [,]-∘ b (splitAt m i) ⟩
    [ b ∘ X′ , b ∘ [ Y′ , Z′ ]′ ∘ splitAt n ]′ (splitAt m i)                    ≡⟨ [,-]-cong ([,]-∘ b ∘ splitAt n) (splitAt m i) ⟩
    [ b ∘ X′ , [ b ∘ Y′ , b ∘ Z′ ]′ ∘ splitAt n ]′ (splitAt m i)                ≡⟨ [,]-cong (inv ∘ X) ([,]-cong (inv ∘ Y) (inv ∘ Z) ∘ splitAt n) (splitAt m i) ⟩
    [ X , [ Y , Z ]′ ∘ splitAt n ]′ (splitAt m i)                               ≡⟨⟩
    (X ++ (Y ++ Z)) i                                                           ∎
  where
    open Bool
    open Fin
    f : Bool → Fin 2
    f false = zero
    f true = suc zero
    b : Fin 2 → Bool
    b zero = false
    b (suc zero) = true
    inv : b ∘ f ≗ id
    inv false = ≡.refl
    inv true = ≡.refl
    X′ : Fin m → Fin 2
    X′ = f ∘ X
    Y′ : Fin n → Fin 2
    Y′ = f ∘ Y
    Z′ : Fin o → Fin 2
    Z′ = f ∘ Z
    open ≡-Reasoning

Preimage-unitaryˡ
    : {n : ℕ}
      (X : Subset n)
    → (X ++ []) ∘ (_↑ˡ 0) ≗ X
Preimage-unitaryˡ {n} X i = begin
    [ X , [] ]′ (splitAt _ (i ↑ˡ 0))  ≡⟨ ≡.cong ([ X , [] ]′) (splitAt-↑ˡ n i 0) ⟩
    [ X , [] ]′ (inj₁ i)              ≡⟨⟩
    X i                               ∎
  where
    open ≡-Reasoning

++-swap
    : {n m : ℕ}
      (X : Subset n)
      (Y : Subset m)
    → (X ++ Y) ∘ +-swap {n} ≗ Y ++ X
++-swap {n} {m} X Y i = begin
    [ X , Y ]′ (splitAt n (+-swap {n} i))           ≡⟨ [,]-cong (inv ∘ X) (inv ∘ Y) (splitAt n (+-swap {n} i)) ⟨
    [ b ∘ X′ , b ∘ Y′ ]′ (splitAt n (+-swap {n} i)) ≡⟨ [,]-∘ b (splitAt n (+-swap {n} i)) ⟨
    b ([ X′ , Y′ ]′ (splitAt n (+-swap {n} i)))     ≡⟨ ≡.cong b ([]∘swap {2} {n} i) ⟩
    b ([ Y′ , X′ ]′ (splitAt m i))                  ≡⟨ [,]-∘ b (splitAt m i) ⟩
    [ b ∘ Y′ , b ∘ X′ ]′ (splitAt m i)              ≡⟨ [,]-cong (inv ∘ Y) (inv ∘ X) (splitAt m i) ⟩
    [ Y  , X ]′ (splitAt m i)                       ∎
  where
    open Bool
    open Fin
    f : Bool → Fin 2
    f false = zero
    f true = suc zero
    b : Fin 2 → Bool
    b zero = false
    b (suc zero) = true
    inv : b ∘ f ≗ id
    inv false = ≡.refl
    inv true = ≡.refl
    X′ : Fin n → Fin 2
    X′ = f ∘ X
    Y′ : Fin m → Fin 2
    Y′ = f ∘ Y
    open ≡-Reasoning

open SymmetricMonoidalFunctor
Preimage,++,[] : SymmetricMonoidalFunctor
Preimage,++,[] .F = Preimage
Preimage,++,[] .isBraidedMonoidal = record
    { isMonoidal = record
        { ε = Preimage-ε
        ; ⊗-homo = ⊗-homomorphism
        ; associativity = λ { {m} {n} {o} {(X , Y) , Z} i → ++-assoc X Y Z i }
        ; unitaryˡ = λ _ → ≡.refl
        ; unitaryʳ = λ { {n} {X , _} i → Preimage-unitaryˡ X i }
        }
    ; braiding-compat = λ { {n} {m} {X , Y} i → ++-swap X Y i }
    }
