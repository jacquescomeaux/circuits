{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (CommutativeMonoid)
open import Level using (0ℓ)

module Data.System.Values (A : CommutativeMonoid 0ℓ 0ℓ) where

open import Category.Instance.Setoids.SymmetricMonoidal {0ℓ} {0ℓ} using (Setoids-×)

import Algebra.Properties.CommutativeMonoid.Sum A as Sum
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as Pointwise
import Object.Monoid.Commutative Setoids-×.symmetric as Obj
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Data.Bool using (Bool; if_then_else_)
open import Data.Bool.Properties using (if-cong)
open import Data.Monoid using (module FromMonoid)
open import Data.CMonoid using (fromCMonoid)
open import Data.Fin using (Fin; splitAt; _↑ˡ_; _↑ʳ_; punchIn; punchOut)
open import Data.Fin using (_≟_)
open import Data.Fin.Permutation using (Permutation; Permutation′; _⟨$⟩ʳ_; _⟨$⟩ˡ_; id; flip; inverseˡ; inverseʳ; punchIn-permute; insert; remove)
open import Data.Fin.Preimage using (preimage; preimage-cong₁; preimage-cong₂)
open import Data.Fin.Properties using (punchIn-punchOut)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Setoid using (∣_∣)
open import Data.Subset.Functional using (Subset; ⁅_⁆; ⁅⁆∘ρ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec.Functional as Vec using (Vector; zipWith; replicate)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_; _∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_; module ≡-Reasoning)
open import Relation.Nullary.Decidable using (yes; no)

open Bool
open CommutativeMonoid A renaming (Carrier to Value; setoid to Valueₛ)
open Fin
open Func
open Pointwise Valueₛ using (≋-setoid; ≋-isEquivalence)
open ℕ

opaque
  Values : ℕ → Setoid 0ℓ 0ℓ
  Values = ≋-setoid

_when_ : Value → Bool → Value
x when b = if b then x else ε

-- when preserves setoid equivalence
when-cong
    : {x y : Value}
    → x ≈ y
    → (b : Bool)
    → x when b ≈ y when b
when-cong _ false = refl
when-cong x≈y true = x≈y

module _ {n : ℕ} where

  opaque

    unfolding Values

    _⊕_ : ∣ Values n ∣ → ∣ Values n ∣ → ∣ Values n ∣
    xs ⊕ ys = zipWith _∙_ xs ys

    <ε> : ∣ Values n ∣
    <ε> = replicate n ε

    mask : Subset n → ∣ Values n ∣ → ∣ Values n ∣
    mask S v i = v i when S i

    sum : ∣ Values n ∣ → Value
    sum = Sum.sum

    merge : ∣ Values n ∣ → Subset n → Value
    merge v S = sum (mask S v)

    -- mask preserves setoid equivalence
    maskₛ : Subset n → Values n ⟶ₛ Values n
    maskₛ S .to = mask S
    maskₛ S .cong v≋w i = when-cong (v≋w i) (S i)

    -- sum preserves setoid equivalence
    sumₛ : Values n ⟶ₛ Valueₛ
    sumₛ .to = Sum.sum
    sumₛ .cong = Sum.sum-cong-≋

    head : ∣ Values (suc n) ∣ → Value
    head xs = xs zero

    tail : ∣ Values (suc n) ∣ → ∣ Values n ∣
    tail xs = xs ∘ suc

    lookup : ∣ Values n ∣ → Fin n → Value
    lookup v i = v i

  module ≋ = Setoid (Values n)

  _≋_ : Rel ∣ Values n ∣ 0ℓ
  _≋_ = ≋._≈_

  infix 4 _≋_

  opaque

    unfolding merge

    -- merge preserves setoid equivalence
    merge-cong
        : (S : Subset n)
        → {xs ys : ∣ Values n ∣}
        → xs ≋ ys
        → merge xs S ≈ merge ys S
    merge-cong S {xs} {ys} xs≋ys = cong sumₛ (cong (maskₛ S) xs≋ys)

    mask-cong₁
        : {S₁ S₂ : Subset n}
        → S₁ ≗ S₂
        → (xs : ∣ Values n ∣)
        → mask S₁ xs ≋ mask S₂ xs
    mask-cong₁ S₁≋S₂ _ i = reflexive (if-cong (S₁≋S₂ i))

    merge-cong₂
        : (xs : ∣ Values n ∣)
        → {S₁ S₂ : Subset n}
        → S₁ ≗ S₂
        → merge xs S₁ ≈ merge xs S₂
    merge-cong₂ xs S₁≋S₂ = cong sumₛ (mask-cong₁ S₁≋S₂ xs)

module _ where

  open Setoid

  opaque
    unfolding Values
    ≋-isEquiv : ∀ n → IsEquivalence (_≈_ (Values n))
    ≋-isEquiv = ≋-isEquivalence

module _ {n : ℕ} where

  opaque

    unfolding _⊕_

    ⊕-cong : {x y u v : ≋.Carrier {n}} → x ≋ y → u ≋ v → x ⊕ u ≋ y ⊕ v
    ⊕-cong x≋y u≋v i = ∙-cong (x≋y i) (u≋v i)

    ⊕-assoc : (x y z : ≋.Carrier {n}) → (x ⊕ y) ⊕ z ≋ x ⊕ (y ⊕ z)
    ⊕-assoc x y z i = assoc (x i) (y i) (z i)

    ⊕-identityˡ : (x : ≋.Carrier {n}) → <ε> ⊕ x ≋ x
    ⊕-identityˡ x i = identityˡ (x i)

    ⊕-identityʳ : (x : ≋.Carrier {n}) → x ⊕ <ε> ≋ x
    ⊕-identityʳ x i = identityʳ (x i)

    ⊕-comm : (x y : ≋.Carrier {n}) → x ⊕ y ≋ y ⊕ x
    ⊕-comm x y i = comm (x i) (y i)

module Algebra where

  open CommutativeMonoid

  Valuesₘ : ℕ → CommutativeMonoid 0ℓ 0ℓ
  Valuesₘ n .Carrier = ∣ Values n ∣
  Valuesₘ n ._≈_ = _≋_
  Valuesₘ n ._∙_ = _⊕_
  Valuesₘ n .ε = <ε>
  Valuesₘ n .isCommutativeMonoid = record
      { isMonoid = record
          { isSemigroup = record
              { isMagma = record
                  { isEquivalence = ≋-isEquiv n
                  ; ∙-cong = ⊕-cong
                  }
              ; assoc = ⊕-assoc
              }
          ; identity = ⊕-identityˡ , ⊕-identityʳ
          }
      ; comm = ⊕-comm
      }

module Object where

  opaque
    unfolding FromMonoid.μ
    Valuesₘ : ℕ → Obj.CommutativeMonoid
    Valuesₘ n = fromCMonoid (Algebra.Valuesₘ n)

opaque

  unfolding Values

  [] : ∣ Values 0 ∣
  [] = Vec.[]

  []-unique : (xs ys : ∣ Values 0 ∣) → xs ≋ ys
  []-unique xs ys ()

module _ {n m : ℕ} where

  opaque

    unfolding Values

    _++_ : ∣ Values n ∣ → ∣ Values m ∣ → ∣ Values (n + m) ∣
    _++_ = Vec._++_

    infixr 5 _++_

    ++-cong
        : (xs xs′ : ∣ Values n ∣)
          {ys ys′ : ∣ Values m ∣}
        → xs ≋ xs′
        → ys ≋ ys′
        → xs ++ ys ≋ xs′ ++ ys′
    ++-cong xs xs′ xs≋xs′ ys≋ys′ i with splitAt n i
    ... | inj₁ i = xs≋xs′ i
    ... | inj₂ i = ys≋ys′ i

    splitₛ : Values (n + m) ⟶ₛ Values n ×ₛ Values m
    to splitₛ v = v ∘ (_↑ˡ m) , v ∘ (n ↑ʳ_)
    cong splitₛ v₁≋v₂ = v₁≋v₂ ∘ (_↑ˡ m) , v₁≋v₂ ∘ (n ↑ʳ_)

  ++ₛ : Values n ×ₛ Values m ⟶ₛ Values (n + m)
  to ++ₛ (xs , ys) = xs ++ ys
  cong ++ₛ (≗xs , ≗ys) = ++-cong _ _ ≗xs ≗ys

opaque

  unfolding merge

  mask-⊕
      : {n : ℕ}
        (xs ys : ∣ Values n ∣)
        (S : Subset n)
      → mask S (xs ⊕ ys) ≋ mask S xs ⊕ mask S ys
  mask-⊕ xs ys S i with S i
  ... | false = sym (identityˡ ε)
  ... | true = refl

  sum-⊕
      : {n : ℕ}
      → (xs ys : ∣ Values n ∣)
      → sum (xs ⊕ ys) ≈ sum xs ∙ sum ys
  sum-⊕ {zero} xs ys = sym (identityˡ ε)
  sum-⊕ {suc n} xs ys = begin
      (head xs ∙ head ys) ∙ sum (tail xs ⊕ tail ys)         ≈⟨ ∙-congˡ (sum-⊕ (tail xs) (tail ys)) ⟩
      (head xs ∙ head ys) ∙ (sum (tail xs) ∙ sum (tail ys)) ≈⟨ assoc (head xs) (head ys) _ ⟩
      head xs ∙ (head ys ∙ (sum (tail xs) ∙ sum (tail ys))) ≈⟨ ∙-congˡ (assoc (head ys) (sum (tail xs)) _) ⟨
      head xs ∙ ((head ys ∙ sum (tail xs)) ∙ sum (tail ys)) ≈⟨ ∙-congˡ (∙-congʳ (comm (head ys) (sum (tail xs)))) ⟩
      head xs ∙ ((sum (tail xs) ∙ head ys) ∙ sum (tail ys)) ≈⟨ ∙-congˡ (assoc (sum (tail xs)) (head ys) _) ⟩
      head xs ∙ (sum (tail xs) ∙ (head ys ∙ sum (tail ys))) ≈⟨ assoc (head xs) (sum (tail xs)) _ ⟨
      (head xs ∙ sum (tail xs)) ∙ (head ys ∙ sum (tail ys)) ∎
    where
      open ≈-Reasoning Valueₛ

  merge-⊕
      : {n : ℕ}
        (xs ys : ∣ Values n ∣)
        (S : Subset n)
      → merge (xs ⊕ ys) S ≈ merge xs S ∙ merge ys S
  merge-⊕ {n} xs ys S = begin
      sum (mask S (xs ⊕ ys))            ≈⟨ cong sumₛ (mask-⊕ xs ys S) ⟩
      sum (mask S xs ⊕ mask S ys)       ≈⟨ sum-⊕ (mask S xs) (mask S ys) ⟩
      sum (mask S xs) ∙ sum (mask S ys) ∎
    where
      open ≈-Reasoning Valueₛ

  mask-<ε> : {n : ℕ} (S : Subset n) → mask {n} S <ε> ≋ <ε>
  mask-<ε> S i with S i
  ... | false = refl
  ... | true = refl

  sum-<ε> : (n : ℕ) → sum {n} <ε> ≈ ε
  sum-<ε> zero = refl
  sum-<ε> (suc n) = trans (identityˡ (sum {n} <ε>)) (sum-<ε> n)

  merge-<ε> : {n : ℕ} (S : Subset n) → merge {n} <ε> S ≈ ε
  merge-<ε> {n} S = begin
      sum (mask S <ε>)  ≈⟨ cong sumₛ (mask-<ε> S) ⟩
      sum {n} <ε>       ≈⟨ sum-<ε> n ⟩
      ε                 ∎
    where
      open ≈-Reasoning Valueₛ

  merge-⁅⁆
      : {n : ℕ}
        (xs : ∣ Values n ∣)
        (i : Fin n)
      → merge xs ⁅ i ⁆ ≈ lookup xs i
  merge-⁅⁆ {suc n} xs zero = trans (∙-congˡ (sum-<ε> n)) (identityʳ (head xs))
  merge-⁅⁆ {suc n} xs (suc i) = begin
      ε ∙ merge (tail xs) ⁅ i ⁆ ≈⟨ identityˡ (sum (mask ⁅ i ⁆ (tail xs))) ⟩
      merge (tail xs) ⁅ i ⁆     ≈⟨ merge-⁅⁆ (tail xs) i ⟩
      tail xs i                 ∎
    where
      open ≈-Reasoning Valueₛ

opaque

  unfolding Values

  push : {A B : ℕ} → ∣ Values A ∣ → (Fin A → Fin B) → ∣ Values B ∣
  push v f = merge v ∘ preimage f ∘ ⁅_⁆

  pull : {A B : ℕ} → ∣ Values B ∣ → (Fin A → Fin B) → ∣ Values A ∣
  pull v f = v ∘ f

insert-f0-0
    : {A B : ℕ}
      (f : Fin (suc A) → Fin (suc B))
    → Σ[ ρ ∈ Permutation′ (suc B) ] (ρ ⟨$⟩ʳ (f zero) ≡ zero)
insert-f0-0 {A} {B} f = ρ , ρf0≡0
  where
    ρ : Permutation′ (suc B)
    ρ = insert (f zero) zero id
    ρf0≡0 : ρ ⟨$⟩ʳ f zero ≡ zero
    ρf0≡0 with f zero ≟ f zero
    ... | yes _ = ≡.refl
    ... | no f0≢f0 with () ← f0≢f0 ≡.refl

opaque
  unfolding push
  push-cong
      : {A B : ℕ}
      → (v : ∣ Values A ∣)
        {f g : Fin A → Fin B}
      → f ≗ g
      → push v f ≋ push v g
  push-cong v f≋g i = merge-cong₂ v (≡.cong ⁅ i ⁆ ∘ f≋g)

opaque
  unfolding Values
  removeAt : {n : ℕ} → ∣ Values (suc n) ∣ → Fin (suc n) → ∣ Values n ∣
  removeAt v i = Vec.removeAt v i

opaque
  unfolding merge removeAt
  merge-removeAt
      : {A : ℕ}
        (k : Fin (suc A))
        (v : ∣ Values (suc A) ∣)
        (S : Subset (suc A))
      → merge v S ≈ lookup v k when S k ∙ merge (removeAt v k) (Vec.removeAt S k)
  merge-removeAt {A} zero v S = refl
  merge-removeAt {suc A} (suc k) v S = begin
      v0? ∙ merge (tail v) (Vec.tail S)           ≈⟨ ∙-congˡ (merge-removeAt k (tail v) (Vec.tail S)) ⟩
      v0? ∙ (vk? ∙ merge (tail v-) (Vec.tail S-)) ≈⟨ assoc v0? vk? _ ⟨
      (v0? ∙ vk?) ∙ merge (tail v-) (Vec.tail S-) ≈⟨ ∙-congʳ (comm v0? vk?) ⟩
      (vk? ∙ v0?) ∙ merge (tail v-) (Vec.tail S-) ≈⟨ assoc vk? v0? _ ⟩
      vk? ∙ (v0? ∙ merge (tail v-) (Vec.tail S-)) ≡⟨⟩
      vk? ∙ merge v- S- ∎
    where
      open ≈-Reasoning Valueₛ
      v0? vk? : Value
      v0? = head v when Vec.head S
      vk? = tail v k when Vec.tail S k
      v- : Vector Value (suc A)
      v- = removeAt v (suc k)
      S- : Subset (suc A)
      S- = Vec.removeAt S (suc k)

opaque
  unfolding merge pull removeAt
  merge-preimage-ρ
      : {A B : ℕ}
      → (ρ : Permutation A B)
      → (v : ∣ Values A ∣)
        (S : Subset B)
      → merge v (preimage (ρ ⟨$⟩ʳ_) S) ≈ merge (pull v (ρ ⟨$⟩ˡ_)) S
  merge-preimage-ρ {zero} {zero} ρ v S = refl
  merge-preimage-ρ {zero} {suc B} ρ v S with () ← ρ ⟨$⟩ˡ zero
  merge-preimage-ρ {suc A} {zero} ρ v S with () ← ρ ⟨$⟩ʳ zero
  merge-preimage-ρ {suc A} {suc B} ρ v S = begin
      merge v (preimage ρʳ S)                                       ≈⟨ merge-removeAt (ρˡ zero) v (preimage ρʳ S) ⟩
      mask (preimage ρʳ S) v (ρˡ zero) ∙ merge v- [preimage-ρʳ-S]-  ≈⟨ ∙-congʳ ≈vρˡ0? ⟩
      mask S (pull v ρˡ) zero ∙ merge v- [preimage-ρʳ-S]-           ≈⟨ ∙-congˡ (merge-cong₂ v- preimage-) ⟩
      mask S (pull v ρˡ) zero ∙ merge v- (preimage ρʳ- S-)          ≈⟨ ∙-congˡ (merge-preimage-ρ ρ- v- S-) ⟩
      mask S (pull v ρˡ) zero ∙ merge (pull v- ρˡ-) S-              ≈⟨ ∙-congˡ (merge-cong S- (reflexive ∘ pull-v-ρˡ-)) ⟩
      mask S (pull v ρˡ) zero ∙ merge (tail (pull v ρˡ)) S-         ≡⟨⟩
      merge (pull v ρˡ) S                                           ∎
    where
      ρˡ : Fin (suc B) → Fin (suc A)
      ρˡ = ρ ⟨$⟩ˡ_
      ρʳ : Fin (suc A) → Fin (suc B)
      ρʳ = ρ ⟨$⟩ʳ_
      ρ- : Permutation A B
      ρ- = remove (ρˡ zero) ρ
      ρˡ- : Fin B → Fin A
      ρˡ- = ρ- ⟨$⟩ˡ_
      ρʳ- : Fin A → Fin B
      ρʳ- = ρ- ⟨$⟩ʳ_
      v- : ∣ Values A ∣
      v- = removeAt v (ρˡ zero)
      S- : Subset B
      S- = S ∘ suc
      [preimage-ρʳ-S]- : Subset A
      [preimage-ρʳ-S]- = Vec.removeAt (preimage ρʳ S) (ρˡ zero)
      vρˡ0? : Value
      vρˡ0? = head (pull v ρˡ) when S zero
      ≈vρˡ0?  : mask (S ∘ ρʳ ∘ ρˡ) (pull v ρˡ) zero ≈ mask S (pull v ρˡ) zero
      ≈vρˡ0? = mask-cong₁ (λ i → ≡.cong S (inverseʳ ρ {i})) (pull v ρˡ) zero
      module _ where
        open ≡-Reasoning
        preimage- : [preimage-ρʳ-S]- ≗ preimage ρʳ- S-
        preimage- x = begin
            [preimage-ρʳ-S]- x                        ≡⟨⟩
            Vec.removeAt (preimage ρʳ S) (ρˡ zero) x  ≡⟨⟩
            S (ρʳ (punchIn (ρˡ zero) x))              ≡⟨ ≡.cong S (punchIn-permute ρ (ρˡ zero) x) ⟩ 
            S (punchIn (ρʳ (ρˡ zero)) (ρʳ- x))        ≡⟨ ≡.cong (λ h → S (punchIn h (ρʳ- x))) (inverseʳ ρ) ⟩ 
            S (punchIn zero (ρʳ- x))                  ≡⟨⟩ 
            S (suc (ρʳ- x))                           ≡⟨⟩
            preimage ρʳ- S- x                         ∎
        pull-v-ρˡ- : pull v- ρˡ- ≗ tail (pull v ρˡ)
        pull-v-ρˡ- i = begin
            v- (ρˡ- i)                                        ≡⟨⟩
            v (punchIn (ρˡ zero) (punchOut {A} {ρˡ zero} _))  ≡⟨ ≡.cong v (punchIn-punchOut _) ⟩
            v (ρˡ (punchIn (ρʳ (ρˡ zero)) i))                 ≡⟨ ≡.cong (λ h → v (ρˡ (punchIn h i))) (inverseʳ ρ) ⟩
            v (ρˡ (punchIn zero i))                           ≡⟨⟩
            v (ρˡ (suc i))                                    ≡⟨⟩
            tail (v ∘ ρˡ) i                                   ∎
      open ≈-Reasoning Valueₛ

opaque

  unfolding push merge mask

  mutual

    merge-preimage
        : {A B : ℕ}
          (f : Fin A → Fin B)
        → (v : ∣ Values A ∣)
          (S : Subset B)
        → merge v (preimage f S) ≈ merge (push v f) S
    merge-preimage {zero} {zero} f v S = refl
    merge-preimage {zero} {suc B} f v S = sym (trans (cong sumₛ (mask-<ε> S)) (sum-<ε> (suc B)))
    merge-preimage {suc A} {zero} f v S with () ← f zero
    merge-preimage {suc A} {suc B} f v S with insert-f0-0 f
    ... | ρ , ρf0≡0 = begin
            merge v (preimage f S)                      ≈⟨ merge-cong₂ v (preimage-cong₁ (λ x → inverseˡ ρ {f x}) S) ⟨
            merge v (preimage (ρˡ ∘ ρʳ ∘ f) S)          ≡⟨⟩
            merge v (preimage (ρʳ ∘ f) (preimage ρˡ S)) ≈⟨ merge-preimage-f0≡0 (ρʳ ∘ f) ρf0≡0 v (preimage ρˡ S) ⟩
            merge (push v (ρʳ ∘ f)) (preimage ρˡ S)     ≈⟨ merge-preimage-ρ (flip ρ) (push v (ρʳ ∘ f)) S ⟩
            merge (pull (push v (ρʳ ∘ f)) ρʳ) S         ≈⟨ merge-cong S (merge-cong₂ v ∘ preimage-cong₂ (ρʳ ∘ f) ∘ ⁅⁆∘ρ ρ) ⟩
            merge (push v (ρˡ ∘ ρʳ ∘ f)) S              ≈⟨ merge-cong S (push-cong v (λ x → inverseˡ ρ {f x})) ⟩
            merge (push v f) S      ∎
          where
            open ≈-Reasoning Valueₛ
            ρʳ ρˡ : Fin (ℕ.suc B) → Fin (ℕ.suc B)
            ρʳ = ρ ⟨$⟩ʳ_
            ρˡ = ρ ⟨$⟩ˡ_

    merge-preimage-f0≡0
        : {A B : ℕ}
          (f : Fin (suc A) → Fin (suc B))
        → f zero ≡ zero
        → (v : ∣ Values (suc A) ∣)
          (S : Subset (suc B))
        → merge v (preimage f S) ≈ merge (push v f) S
    merge-preimage-f0≡0 {A} {B} f f0≡0 v S
      using S0 , S- ← S zero , S ∘ suc
      using v0 , v- ← head v , tail v
      using f0 , f- ← f zero , f ∘ suc = begin
          merge v f⁻¹[S]                    ≡⟨⟩
          v0? ∙ merge v- f⁻¹[S]-            ≈⟨ ∙-congˡ (merge-preimage f- v- S) ⟩
          v0? ∙ merge f[v-] S               ≡⟨⟩
          v0? ∙ (f[v-]0? ∙ merge f[v-]- S-) ≈⟨ assoc v0? f[v-]0? (merge f[v-]- S-) ⟨
          v0? ∙ f[v-]0? ∙ merge f[v-]- S-   ≈⟨ ∙-congʳ v0?∙f[v-]0?≈f[v]0? ⟩
          f[v]0? ∙ merge f[v-]- S-          ≈⟨ ∙-congˡ (merge-cong S- ≋f[v]-) ⟩
          f[v]0? ∙ merge f[v]- S-           ≡⟨⟩
          merge f[v] S                      ∎
        where
          open ≈-Reasoning Valueₛ
          f⁻¹[S] : Subset (suc A)
          f⁻¹[S] = preimage f S
          f⁻¹[S]- : Subset A
          f⁻¹[S]- = f⁻¹[S] ∘ suc
          f⁻¹[S]0 : Bool
          f⁻¹[S]0 = f⁻¹[S] zero
          f[v] : ∣ Values (suc B) ∣
          f[v] = push v f
          f[v]- : Vector Value B
          f[v]- = tail f[v]
          f[v]0 : Value
          f[v]0 = head f[v]
          f[v-] : ∣ Values (suc B) ∣
          f[v-] = push v- f-
          f[v-]- : Vector Value B
          f[v-]- = tail f[v-]
          f[v-]0 : Value
          f[v-]0 = head f[v-]
          v0? f[v-]0? v0?+[f[v-]0?] f[v]0? : Value
          v0? = v0 when f⁻¹[S]0
          f[v-]0? = f[v-]0 when S0
          v0?+[f[v-]0?] = if S0 then v0? ∙ f[v-]0 else v0?
          f[v]0? = f[v]0 when S0
          v0?∙f[v-]0?≈f[v]0? : v0? ∙ f[v-]0? ≈ f[v]0?
          v0?∙f[v-]0?≈f[v]0? rewrite f0≡0 with S0
          ... | true = refl
          ... | false = identityˡ ε
          ≋f[v]- : f[v-]- ≋ f[v]-
          ≋f[v]- x rewrite f0≡0 = sym (identityˡ (push v- f- (suc x)))

opaque
  unfolding push
  merge-push
      : {A B C : ℕ}
        (f : Fin A → Fin B)
        (g : Fin B → Fin C)
      → (v : ∣ Values A ∣)
      → push v (g ∘ f) ≋ push (push v f) g
  merge-push f g v i = merge-preimage f v (preimage g ⁅ i ⁆)
