{-# OPTIONS --without-K --safe #-}

module Functor.Monoidal.Instance.Nat.Push where

open import Categories.Category.Instance.Nat using (Nat)
open import Data.Bool.Base using (Bool; false)
open import Data.Subset.Functional using (Subset; ⁅_⁆; ⊥)
open import Function.Base using (_∘_; case_of_; _$_; id)
open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)
open import Level using (0ℓ; Level)
open import Relation.Binary using (Rel; Setoid)
open import Functor.Instance.Nat.Push using (Push; Push-defs)
open import Data.Setoid.Unit using (⊤ₛ)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Data.Vec.Functional as Vec using (Vector)
open import Data.Vector using (++-assoc; ++-↑ˡ; ++-↑ʳ)
-- open import Data.Vec.Functional.Properties using (++-cong)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Function.Construct.Constant using () renaming (function to Const)
open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open Cartesian (Setoids-Cartesian {0ℓ} {0ℓ}) using (products)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Categories.Category.Instance.Nat using (Nat-Cocartesian)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using () renaming (_∘F_ to _∘′_)
open Cocartesian Nat-Cocartesian using (module Dual; i₁; i₂; -+-; _+₁_; +-assoc; +-assocʳ; +-assocˡ; +-comm; +-swap; +₁∘+-swap)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)
open import Data.Product.Base using (_,_; _×_; Σ)
open import Data.Fin.Preimage using (preimage; preimage-⊥; preimage-cong₂)
open import Functor.Monoidal.Instance.Nat.Preimage using (preimage-++)
open import Data.Sum.Base using ([_,_]; [_,_]′; inj₁; inj₂)
open import Data.Sum.Properties using ([,]-cong; [,-]-cong; [-,]-cong; [,]-∘; [,]-map)
open import Data.Circuit.Merge using (merge-with; merge; merge-⊥; merge-[]; ⁅⁆-++; merge-++; merge-cong₁; merge-cong₂; merge-suc; _when_; join-merge; merge-preimage-ρ; merge-⁅⁆)
open import Data.Circuit.Value using (Value; join; join-comm; join-assoc; Monoid)
open import Data.Fin.Base using (splitAt; _↑ˡ_; _↑ʳ_) renaming (join to joinAt)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ; ↑ˡ-injective; ↑ʳ-injective; _≟_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; _≗_; module ≡-Reasoning)
open BinaryProducts products using (-×-)
open Value using (U)
open Bool using (false)

open import Function.Bundles using (Equivalence)
open import Category.Monoidal.Instance.Nat using (Nat,+,0)
open import Category.Instance.Setoids.SymmetricMonoidal {0ℓ} {0ℓ} using (Setoids-×)
open import Categories.Functor.Monoidal.Symmetric Nat,+,0 Setoids-× using (module Lax)
open Lax using (SymmetricMonoidalFunctor)
open import Categories.Morphism Nat using (_≅_)
open import Function.Bundles using (Inverse)
open import Data.Fin.Permutation using (Permutation; _⟨$⟩ʳ_; _⟨$⟩ˡ_)
open Dual.op-binaryProducts using () renaming (assocˡ∘⟨⟩ to []∘assocʳ; swap∘⟨⟩ to []∘swap)
open import Relation.Nullary.Decidable using (does; does-⇔; dec-false)
open import Data.Setoid using (∣_∣)

open ℕ

open import Data.System.Values Monoid using (Values; <ε>; ++ₛ; _++_; head; tail; _≋_)

open Func
open ≡-Reasoning

private

  Push-ε : ⊤ₛ {0ℓ} {0ℓ} ⟶ₛ Values 0
  Push-ε = Const ⊤ₛ (Values 0) <ε>

  opaque

    unfolding _++_

    unfolding Push-defs
    Push-++
        : {n n′ m m′ : ℕ }
        → (f : Fin n → Fin n′)
        → (g : Fin m → Fin m′)
        → (xs : ∣ Values n ∣)
        → (ys : ∣ Values m ∣)
        → (Push.₁ f ⟨$⟩ xs) ++ (Push.₁ g ⟨$⟩ ys)
        ≋ Push.₁ (f +₁ g) ⟨$⟩ (xs ++ ys)
    Push-++ {n} {n′} {m} {m′} f g xs ys i = begin
        ((merge xs ∘ preimage f ∘ ⁅_⁆) ++ (merge ys ∘ preimage g ∘ ⁅_⁆)) i
            ≡⟨ [,]-cong left right (splitAt n′ i) ⟩
        [ (λ x → merge (xs ++ ys) _) , (λ x → merge (xs ++ ys) _) ]′ (splitAt n′ i)
            ≡⟨ [,]-∘ (merge (xs ++ ys) ∘ (preimage (f +₁ g))) (splitAt n′ i) ⟨
        merge (xs ++ ys) (preimage (f +₁ g) ((⁅⁆++⊥ Vec.++ ⊥++⁅⁆) i))     ≡⟨ merge-cong₂ (xs ++ ys) (preimage-cong₂ (f +₁ g) (⁅⁆-++ {n′} i)) ⟩
        merge (xs ++ ys) (preimage (f +₁ g) ⁅ i ⁆) ∎
      where
        ⁅⁆++⊥ : Vector (Subset (n′ + m′)) n′
        ⁅⁆++⊥ x = ⁅ x ⁆ Vec.++ ⊥
        ⊥++⁅⁆ : Vector (Subset (n′ + m′)) m′
        ⊥++⁅⁆ x = ⊥ Vec.++ ⁅ x ⁆
        left : (x : Fin n′) → merge xs (preimage f ⁅ x ⁆) ≡ merge (xs ++ ys) (preimage (f +₁ g) (⁅ x ⁆ Vec.++ ⊥))
        left x = begin
            merge xs (preimage f ⁅ x ⁆)                                   ≡⟨ join-comm U (merge xs (preimage f ⁅ x ⁆)) ⟩
            join (merge xs (preimage f ⁅ x ⁆)) U                          ≡⟨ ≡.cong (join (merge _ _)) (merge-⊥ ys) ⟨
            join (merge xs (preimage f ⁅ x ⁆)) (merge ys ⊥)               ≡⟨ ≡.cong (join (merge _ _)) (merge-cong₂ ys (preimage-⊥ g)) ⟨
            join (merge xs (preimage f ⁅ x ⁆)) (merge ys (preimage g ⊥))  ≡⟨ merge-++ xs ys (preimage f ⁅ x ⁆) (preimage g ⊥) ⟨
            merge (xs ++ ys) ((preimage f ⁅ x ⁆) Vec.++ (preimage g ⊥))   ≡⟨ merge-cong₂ (xs ++ ys) (preimage-++ f g) ⟩
            merge (xs ++ ys) (preimage (f +₁ g) (⁅ x ⁆ Vec.++ ⊥))         ∎
        right : (x : Fin m′) → merge ys (preimage g ⁅ x ⁆) ≡ merge (xs ++ ys) (preimage (f +₁ g) (⊥ Vec.++ ⁅ x ⁆))
        right x = begin
            merge ys (preimage g ⁅ x ⁆)                                   ≡⟨⟩
            join U (merge ys (preimage g ⁅ x ⁆))                          ≡⟨ ≡.cong (λ h → join h (merge _ _)) (merge-⊥ xs) ⟨
            join (merge xs ⊥) (merge ys (preimage g ⁅ x ⁆))               ≡⟨ ≡.cong (λ h → join h (merge _ _)) (merge-cong₂ xs (preimage-⊥ f)) ⟨
            join (merge xs (preimage f ⊥)) (merge ys (preimage g ⁅ x ⁆))  ≡⟨ merge-++ xs ys (preimage f ⊥) (preimage g ⁅ x ⁆) ⟨
            merge (xs ++ ys) ((preimage f ⊥) Vec.++ (preimage g ⁅ x ⁆))   ≡⟨ merge-cong₂ (xs ++ ys) (preimage-++ f g) ⟩
            merge (xs ++ ys) (preimage (f +₁ g) (⊥ Vec.++ ⁅ x ⁆))         ∎

  ⊗-homomorphism : NaturalTransformation (-×- ∘′ (Push ⁂ Push)) (Push ∘′ -+-)
  ⊗-homomorphism = ntHelper record
      { η = λ (n , m) → ++ₛ {n} {m}
      ; commute = λ { (f , g) {xs , ys} → Push-++ f g xs ys }
      }

  opaque

    unfolding Push-defs
    unfolding _++_

    Push-assoc
        : {m n o : ℕ}
          (X : ∣ Values m ∣)
          (Y : ∣ Values n ∣)
          (Z : ∣ Values o ∣)
        → (Push.₁ (+-assocˡ {m} {n} {o}) ⟨$⟩ ((X ++ Y) ++ Z)) ≋ X ++ Y ++ Z
    Push-assoc {m} {n} {o} X Y Z i = begin
        merge ((X ++ Y) ++ Z) (preimage (+-assocˡ {m}) ⁅ i ⁆)         ≡⟨ merge-preimage-ρ ↔-mno ((X ++ Y) ++ Z) ⁅ i ⁆ ⟩
        merge (((X ++ Y) ++ Z) ∘ (+-assocʳ {m})) (⁅ i ⁆)              ≡⟨⟩
        merge (((X ++ Y) ++ Z) ∘ (+-assocʳ {m})) (preimage id ⁅ i ⁆)  ≡⟨ merge-cong₁ (++-assoc X Y Z) (preimage id ⁅ i ⁆) ⟩
        merge (X ++ (Y ++ Z)) (preimage id ⁅ i ⁆)                     ≡⟨ Push.identity i ⟩
        (X ++ (Y ++ Z)) i                                             ∎
      where
        open Inverse
        module +-assoc = _≅_ (+-assoc {m} {n} {o})
        ↔-mno : Permutation ((m + n) + o) (m + (n + o))
        ↔-mno .to = +-assocˡ {m}
        ↔-mno .from = +-assocʳ {m}
        ↔-mno .to-cong ≡.refl = ≡.refl
        ↔-mno .from-cong ≡.refl = ≡.refl
        ↔-mno .inverse = (λ { ≡.refl → +-assoc.isoˡ _ }) , λ { ≡.refl → +-assoc.isoʳ _ }

    Push-unitaryˡ
        : {n : ℕ}
          (X : ∣ Values n ∣)
        → Push.₁ id ⟨$⟩ (<ε> ++ X) ≋ X
    Push-unitaryˡ = merge-⁅⁆

    preimage-++′
        : {n m o : ℕ}
          (f : Vector (Fin o) n)
          (g : Vector (Fin o) m)
          (S : Subset o)
        → preimage (f Vec.++ g) S ≗ preimage f S Vec.++ preimage g S
    preimage-++′ {n} f g S = [,]-∘ S ∘ splitAt n

    Push-unitaryʳ
        : {n : ℕ}
          (X : ∣ Values n ∣)
        → Push.₁ (id Vec.++ (λ())) ⟨$⟩ (X ++ (<ε> {0})) ≋ X
    Push-unitaryʳ {n} X i = begin
        merge (X ++ <ε>) (preimage (id Vec.++ (λ ())) ⁅ i ⁆)     ≡⟨ merge-cong₂ (X Vec.++ <ε>) (preimage-++′ id (λ ()) ⁅ i ⁆) ⟩
        merge (X ++ <ε>) (⁅ i ⁆ Vec.++ preimage (λ ()) ⁅ i ⁆)    ≡⟨ merge-++ X <ε> ⁅ i ⁆ (preimage (λ ()) ⁅ i ⁆) ⟩
        join (merge X ⁅ i ⁆) (merge <ε> (preimage (λ ()) ⁅ i ⁆)) ≡⟨ ≡.cong (join (merge X ⁅ i ⁆)) (merge-[] <ε> (preimage (λ ()) ⁅ i ⁆)) ⟩
        join (merge X ⁅ i ⁆) U                                  ≡⟨ join-comm (merge X ⁅ i ⁆) U ⟩
        merge X ⁅ i ⁆                                           ≡⟨ merge-⁅⁆ X i ⟩
        X i ∎

    Push-swap
        : {n m : ℕ}
          (X : ∣ Values n ∣)
          (Y : ∣ Values m ∣)
        → Push.₁ (+-swap {m}) ⟨$⟩ (X ++ Y) ≋ (Y ++ X)
    Push-swap {n} {m} X Y i = begin
        merge (X ++ Y) (preimage (+-swap {m}) ⁅ i ⁆)      ≡⟨ merge-preimage-ρ n+m↔m+n (X ++ Y) ⁅ i ⁆ ⟩
        merge ((X ++ Y) ∘ +-swap {n}) ⁅ i ⁆               ≡⟨ merge-⁅⁆ ((X ++ Y) ∘ (+-swap {n})) i ⟩
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
Push,++,[] : SymmetricMonoidalFunctor
Push,++,[] .F = Push
Push,++,[] .isBraidedMonoidal = record
    { isMonoidal = record
        { ε = Push-ε
        ; ⊗-homo = ⊗-homomorphism
        ; associativity = λ { {n} {m} {o} {(X , Y) , Z} → Push-assoc X Y Z }
        ; unitaryˡ = λ { {n} {_ , X} → Push-unitaryˡ X }
        ; unitaryʳ = λ { {n} {X , _} → Push-unitaryʳ X }
        }
    ; braiding-compat = λ { {n} {m} {X , Y} → Push-swap X Y }
    }

module Push,++,[] = SymmetricMonoidalFunctor Push,++,[]
