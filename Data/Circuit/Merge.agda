{-# OPTIONS --without-K --safe #-}

module Data.Circuit.Merge where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin; pinch; punchIn; punchOut; splitAt)
open import Data.Fin.Properties using (punchInᵢ≢i; punchIn-punchOut)
open import Data.Bool.Properties using (if-eta)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Circuit.Value using (Value; join; join-comm; join-assoc)
open import Data.Sum.Properties using ([,]-cong; [,-]-cong; [-,]-cong; [,]-∘; [,]-map)
open import Data.Subset.Functional
  using
      ( Subset
      ; ⁅_⁆ ; ⊥ ; ⁅⁆∘ρ
      ; foldl ; foldl-cong₁ ; foldl-cong₂
      ; foldl-[] ; foldl-suc
      ; foldl-⊥ ; foldl-⁅⁆
      ; foldl-fusion
      )
open import Data.Vector as V using (Vector; head; tail; removeAt)
open import Data.Vec.Functional using (_++_)
open import Data.Fin.Permutation
  using
    ( Permutation
    ; Permutation′
    ; _⟨$⟩ˡ_ ; _⟨$⟩ʳ_
    ; inverseˡ ; inverseʳ
    ; id
    ; flip
    ; insert ; remove
    ; punchIn-permute
    )
open import Data.Product using (Σ-syntax; _,_)
open import Data.Fin.Preimage using (preimage; preimage-cong₁; preimage-cong₂)
open import Function.Base using (∣_⟩-_; _∘_; case_of_; _$_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; _≗_; module ≡-Reasoning)

open Value using (U)
open ℕ
open Fin
open Bool

open ≡-Reasoning

_when_ : Value → Bool → Value
x when b = if b then x else U

opaque
  merge-with : {A : ℕ} → Value → Vector Value A → Subset A → Value
  merge-with e v = foldl (∣ join ⟩- v) e

  merge-with-cong : {A : ℕ} {v₁ v₂ : Vector Value A} (e : Value) → v₁ ≗ v₂ → merge-with e v₁ ≗ merge-with e v₂
  merge-with-cong e v₁≗v₂ = foldl-cong₁ (λ x → ≡.cong (join x) ∘ v₁≗v₂) e

  merge-with-cong₂ : {A : ℕ} (e : Value) (v : Vector Value A) {S₁ S₂ : Subset A} → S₁ ≗ S₂ → merge-with e v S₁ ≡ merge-with e v S₂
  merge-with-cong₂ e v = foldl-cong₂ (∣ join ⟩- v) e

  merge-with-⊥ : {A : ℕ} (e : Value) (v : Vector Value A) → merge-with e v ⊥ ≡ e
  merge-with-⊥ e v = foldl-⊥ (∣ join ⟩- v) e

  merge-with-[] : (e : Value) (v : Vector Value 0) (S : Subset 0) → merge-with e v S ≡ e
  merge-with-[] e v = foldl-[] (∣ join ⟩- v) e

  merge-with-suc
      : {A : ℕ} (e : Value) (v : Vector Value (suc A)) (S : Subset (suc A))
      → merge-with e v S
      ≡ merge-with (if head S then join e (head v) else e) (tail v) (tail S)
  merge-with-suc e v = foldl-suc (∣ join ⟩- v) e

  merge-with-join
      : {A : ℕ}
        (x y : Value)
        (v : Vector Value A)
      → merge-with (join x y) v ≗ join x ∘ merge-with y v
  merge-with-join {A} x y v S = ≡.sym (foldl-fusion (join x) fuse y S)
    where
      fuse : (acc : Value) (k : Fin A) → join x (join acc (v k)) ≡ join (join x acc) (v k)
      fuse acc k = ≡.sym (join-assoc x acc (v k))

  merge-with-⁅⁆ : {A : ℕ} (e : Value) (v : Vector Value A) (x : Fin A) → merge-with e v ⁅ x ⁆ ≡ join e (v x)
  merge-with-⁅⁆ e v = foldl-⁅⁆ (∣ join ⟩- v) e

merge-with-U : {A : ℕ} (e : Value) (S : Subset A) → merge-with e (λ _ → U) S ≡ e
merge-with-U {zero} e S = merge-with-[] e (λ _ → U) S
merge-with-U {suc A} e S = begin
    merge-with e (λ _ → U) S                ≡⟨ merge-with-suc e (λ _ → U) S ⟩
    merge-with
        (if head S then join e U else e)
        (tail (λ _ → U)) (tail S)           ≡⟨ ≡.cong (λ h → merge-with (if head S then h else e) _ _) (join-comm e U) ⟩
    merge-with
        (if head S then e else e)
        (tail (λ _ → U)) (tail S)           ≡⟨ ≡.cong (λ h → merge-with h (λ _ → U) (tail S)) (if-eta (head S)) ⟩
    merge-with e (tail (λ _ → U)) (tail S)  ≡⟨⟩
    merge-with e (λ _ → U) (tail S)         ≡⟨ merge-with-U e (tail S) ⟩
    e                                       ∎

merge : {A : ℕ} → Vector Value A → Subset A → Value
merge v = merge-with U v

merge-cong₁ : {A : ℕ} {v₁ v₂ : Vector Value A} → v₁ ≗ v₂ → merge v₁ ≗ merge v₂
merge-cong₁ = merge-with-cong U

merge-cong₂ : {A : ℕ} (v : Vector Value A) {S₁ S₂ : Subset A} → S₁ ≗ S₂ → merge v S₁ ≡ merge v S₂
merge-cong₂ = merge-with-cong₂ U

merge-⊥ : {A : ℕ} (v : Vector Value A) → merge v ⊥ ≡ U
merge-⊥ = merge-with-⊥ U

merge-[] : (v : Vector Value 0) (S : Subset 0) → merge v S ≡ U
merge-[] = merge-with-[] U

merge-[]₂ : {v₁ v₂ : Vector Value 0} {S₁ S₂ : Subset 0} → merge v₁ S₁ ≡ merge v₂ S₂
merge-[]₂ {v₁} {v₂} {S₁} {S₂} = ≡.trans (merge-[] v₁ S₁) (≡.sym (merge-[] v₂ S₂))

merge-⁅⁆ : {A : ℕ} (v : Vector Value A) (x : Fin A) → merge v ⁅ x ⁆ ≡ v x
merge-⁅⁆ = merge-with-⁅⁆ U

join-merge : {A : ℕ} (e : Value) (v : Vector Value A) (S : Subset A) → join e (merge v S) ≡ merge-with e v S
join-merge e v S = ≡.sym (≡.trans (≡.cong (λ h → merge-with h v S) (join-comm U e)) (merge-with-join e U v S))

merge-suc
    : {A : ℕ} (v : Vector Value (suc A)) (S : Subset (suc A))
    → merge v S
    ≡ merge-with (head v when head S) (tail v) (tail S)
merge-suc = merge-with-suc U

insert-f0-0
    : {A B : ℕ}
      (f : Fin (suc A) → Fin (suc B))
    → Σ[ ρ ∈ Permutation′ (suc B) ] (ρ ⟨$⟩ʳ (f zero) ≡ zero)
insert-f0-0 f = insert (f zero) zero id , help
  where
    open import Data.Fin using (_≟_)
    open import Relation.Nullary.Decidable using (yes; no)
    help : insert (f zero) zero id ⟨$⟩ʳ f zero ≡ zero
    help with f zero ≟ f zero
    ... | yes _ = ≡.refl
    ... | no f0≢f0 with () ← f0≢f0 ≡.refl

merge-removeAt
    : {A : ℕ}
      (k : Fin (suc A))
      (v : Vector Value (suc A))
      (S : Subset (suc A))
    → merge v S ≡ join (v k when S k) (merge (removeAt v k) (removeAt S k))
merge-removeAt {A} zero v S = begin
    merge-with U v S                                            ≡⟨ merge-suc v S ⟩
    merge-with (head v when head S) (tail v) (tail S)           ≡⟨ join-merge (head v when head S) (tail v) (tail S) ⟨
    join (head v when head S) (merge-with U (tail v) (tail S))  ∎
merge-removeAt {suc A} (suc k) v S = begin
    merge-with U v S                                  ≡⟨ merge-suc v S ⟩
    merge-with v0? (tail v) (tail S)                  ≡⟨ join-merge _ (tail v) (tail S) ⟨
    join v0? (merge (tail v) (tail S))                ≡⟨ ≡.cong (join v0?) (merge-removeAt k (tail v) (tail S)) ⟩
    join v0? (join vk? (merge (tail v-) (tail S-)))   ≡⟨ join-assoc (head v when head S) _ _ ⟨
    join (join v0? vk?) (merge (tail v-) (tail S-))   ≡⟨ ≡.cong (λ h → join h (merge (tail v-) (tail S-))) (join-comm (head v- when head S-) _) ⟩
    join (join vk? v0?) (merge (tail v-) (tail S-))   ≡⟨ join-assoc (tail v k when tail S k) _ _ ⟩
    join vk? (join v0? (merge (tail v-) (tail S-)))   ≡⟨ ≡.cong (join vk?) (join-merge _ (tail v-) (tail S-)) ⟩
    join vk? (merge-with v0? (tail v-) (tail S-))     ≡⟨ ≡.cong (join vk?) (merge-suc v- S-) ⟨
    join vk? (merge v- S-)                            ∎
  where
    v0? vk? : Value
    v0? = head v when head S
    vk? = tail v k when tail S k
    v- : Vector Value (suc A)
    v- = removeAt v (suc k)
    S- : Subset (suc A)
    S- = removeAt S (suc k)

import Function.Structures as FunctionStructures
open module FStruct {A B : Set} = FunctionStructures {_} {_} {_} {_} {A} _≡_ {B} _≡_ using (IsInverse)
open IsInverse using () renaming (inverseˡ to invˡ; inverseʳ to invʳ)

merge-preimage-ρ
    : {A B : ℕ}
    → (ρ : Permutation A B)
    → (v : Vector Value A)
      (S : Subset B)
    → merge v (preimage (ρ ⟨$⟩ʳ_) S) ≡ merge (v ∘ (ρ ⟨$⟩ˡ_)) S
merge-preimage-ρ {zero} {zero} ρ v S = merge-[]₂
merge-preimage-ρ {zero} {suc B} ρ v S with () ← ρ ⟨$⟩ˡ zero
merge-preimage-ρ {suc A} {zero} ρ v S with () ← ρ ⟨$⟩ʳ zero
merge-preimage-ρ {suc A} {suc B} ρ v S = begin
    merge v (preimage ρʳ S)                   ≡⟨ merge-removeAt (head ρˡ) v (preimage ρʳ S) ⟩
    join
        (head (v ∘ ρˡ) when S (ρʳ (ρˡ zero)))
        (merge v- [preimageρʳS]-)             ≡⟨ ≡.cong (λ h → join h (merge v- [preimageρʳS]-)) ≡vρˡ0? ⟩
    join vρˡ0? (merge v- [preimageρʳS]-)      ≡⟨ ≡.cong (join vρˡ0?) (merge-cong₂ v- preimage-) ⟩
    join vρˡ0? (merge v- (preimage ρʳ- S-))   ≡⟨ ≡.cong (join vρˡ0?) (merge-preimage-ρ ρ- v- S-) ⟩
    join vρˡ0? (merge (v- ∘ ρˡ-) S-)          ≡⟨ ≡.cong (join vρˡ0?) (merge-cong₁ v∘ρˡ- S-) ⟩
    join vρˡ0? (merge (tail (v ∘ ρˡ)) S-)     ≡⟨ join-merge vρˡ0? (tail (v ∘ ρˡ)) S- ⟩
    merge-with vρˡ0? (tail (v ∘ ρˡ)) S-       ≡⟨ merge-suc (v ∘ ρˡ) S ⟨
    merge (v ∘ ρˡ) S                          ∎
  where
    ρˡ : Fin (suc B) → Fin (suc A)
    ρˡ = ρ ⟨$⟩ˡ_
    ρʳ : Fin (suc A) → Fin (suc B)
    ρʳ = ρ ⟨$⟩ʳ_
    ρ- : Permutation A B
    ρ- = remove (head ρˡ) ρ
    ρˡ- : Fin B → Fin A
    ρˡ- = ρ- ⟨$⟩ˡ_
    ρʳ- : Fin A → Fin B
    ρʳ- = ρ- ⟨$⟩ʳ_
    v- : Vector Value A
    v- = removeAt v (head ρˡ)
    [preimageρʳS]- : Subset A
    [preimageρʳS]- = removeAt (preimage ρʳ S) (head ρˡ)
    S- : Subset B
    S- = tail S
    vρˡ0? : Value
    vρˡ0? = head (v ∘ ρˡ) when head S
    ≡vρˡ0?  : head (v ∘ ρˡ) when S (ρʳ (head ρˡ)) ≡ head (v ∘ ρˡ) when head S
    ≡vρˡ0? = ≡.cong ((head (v ∘ ρˡ) when_) ∘ S) (inverseʳ ρ)
    v∘ρˡ- : v- ∘ ρˡ- ≗ tail (v ∘ ρˡ)
    v∘ρˡ- x = begin
        v- (ρˡ- x)                                        ≡⟨⟩
        v (punchIn (head ρˡ) (punchOut {A} {head ρˡ} _))  ≡⟨ ≡.cong v (punchIn-punchOut _) ⟩
        v (ρˡ (punchIn (ρʳ (ρˡ zero)) x))                 ≡⟨ ≡.cong (λ h → v (ρˡ (punchIn h x))) (inverseʳ ρ) ⟩
        v (ρˡ (punchIn zero x))                           ≡⟨⟩
        v (ρˡ (suc x))                                    ≡⟨⟩
        tail (v ∘ ρˡ) x                                   ∎
    preimage- : [preimageρʳS]- ≗ preimage ρʳ- S-
    preimage- x = begin
        [preimageρʳS]- x                      ≡⟨⟩
        removeAt (preimage ρʳ S) (head ρˡ) x  ≡⟨⟩
        S (ρʳ (punchIn (head ρˡ) x))          ≡⟨ ≡.cong S (punchIn-permute ρ (head ρˡ) x) ⟩ 
        S (punchIn (ρʳ (head ρˡ)) (ρʳ- x))    ≡⟨⟩
        S (punchIn (ρʳ (ρˡ zero)) (ρʳ- x))    ≡⟨ ≡.cong (λ h → S (punchIn h (ρʳ- x))) (inverseʳ ρ) ⟩ 
        S (punchIn zero (ρʳ- x))              ≡⟨⟩ 
        S (suc (ρʳ- x))                       ≡⟨⟩
        preimage ρʳ- S- x                     ∎

push-with : {A B : ℕ} → (e : Value) → Vector Value A → (Fin A → Fin B) → Vector Value B
push-with e v f = merge-with e v ∘ preimage f ∘ ⁅_⁆

push : {A B : ℕ} → Vector Value A → (Fin A → Fin B) → Vector Value B
push = push-with U

mutual
  merge-preimage
      : {A B : ℕ}
        (f : Fin A → Fin B)
      → (v : Vector Value A)
        (S : Subset B)
      → merge v (preimage f S) ≡ merge (push v f) S
  merge-preimage {zero} {zero} f v S = merge-[]₂
  merge-preimage {zero} {suc B} f v S = begin
      merge v (preimage f S)  ≡⟨ merge-[] v (preimage f S) ⟩
      U                       ≡⟨ merge-with-U U S ⟨
      merge (λ _ → U) S       ≡⟨ merge-cong₁ (λ x → ≡.sym (merge-[] v (⁅ x ⁆ ∘ f))) S ⟩
      merge (push v f) S      ∎
  merge-preimage {suc A} {zero} f v S with () ← f zero
  merge-preimage {suc A} {suc B} f v S with insert-f0-0 f
  ... | ρ , ρf0≡0 = begin
          merge v (preimage f S)                                    ≡⟨ merge-cong₂ v (preimage-cong₁ (λ x → inverseˡ ρ {f x}) S) ⟨
          merge v (preimage (ρˡ ∘ ρʳ ∘ f) S)                        ≡⟨⟩
          merge v (preimage (ρʳ ∘ f) (preimage ρˡ S))               ≡⟨ merge-preimage-f0≡0 (ρʳ ∘ f) ρf0≡0 v (preimage ρˡ S) ⟩
          merge (merge v ∘ preimage (ρʳ ∘ f) ∘ ⁅_⁆) (preimage ρˡ S) ≡⟨ merge-preimage-ρ (flip ρ) (merge v ∘ preimage (ρʳ ∘ f) ∘ ⁅_⁆) S ⟩
          merge (merge v ∘ preimage (ρʳ ∘ f) ∘ ⁅_⁆ ∘ ρʳ) S          ≡⟨ merge-cong₁ (merge-cong₂ v ∘ preimage-cong₂ (ρʳ ∘ f) ∘ ⁅⁆∘ρ ρ) S ⟩
          merge (merge v ∘ preimage (ρʳ ∘ f) ∘ preimage ρˡ ∘ ⁅_⁆) S ≡⟨⟩
          merge (merge v ∘ preimage (ρˡ ∘ ρʳ ∘ f) ∘ ⁅_⁆) S          ≡⟨ merge-cong₁ (merge-cong₂ v ∘ preimage-cong₁ (λ y → inverseˡ ρ {f y}) ∘ ⁅_⁆) S ⟩
          merge (merge v ∘ preimage f ∘ ⁅_⁆) S                      ∎
        where
          ρʳ ρˡ : Fin (ℕ.suc B) → Fin (ℕ.suc B)
          ρʳ = ρ ⟨$⟩ʳ_
          ρˡ = ρ ⟨$⟩ˡ_

  merge-preimage-f0≡0
      : {A B : ℕ}
        (f : Fin (ℕ.suc A) → Fin (ℕ.suc B))
      → f Fin.zero ≡ Fin.zero
      → (v : Vector Value (ℕ.suc A))
        (S : Subset (ℕ.suc B))
      → merge v (preimage f S) ≡ merge (merge v ∘ preimage f ∘ ⁅_⁆) S
  merge-preimage-f0≡0 {A} {B} f f0≡0 v S
    using S0 , S- ← head S , tail S
    using v0 , v- ← head v , tail v
    using _  , f- ← head f , tail f
      = begin
            merge v f⁻¹[S]                      ≡⟨ merge-suc v f⁻¹[S] ⟩
            merge-with v0? v- f⁻¹[S]-           ≡⟨ join-merge v0? v- f⁻¹[S]- ⟨
            join v0? (merge v- f⁻¹[S]-)         ≡⟨ ≡.cong (join v0?) (merge-preimage f- v- S) ⟩
            join v0? (merge f[v-] S)            ≡⟨ join-merge v0? f[v-] S ⟩
            merge-with v0? f[v-] S              ≡⟨ merge-with-suc v0? f[v-] S ⟩
            merge-with v0?+[f[v-]0?] f[v-]- S-  ≡⟨ ≡.cong (λ h → merge-with h f[v-]- S-) ≡f[v]0 ⟩
            merge-with f[v]0? f[v-]- S-         ≡⟨ merge-with-cong f[v]0? ≡f[v]- S- ⟩
            merge-with f[v]0? f[v]- S-          ≡⟨ merge-suc f[v] S ⟨
            merge f[v] S                        ∎
          where
            f⁻¹[S] : Subset (suc A)
            f⁻¹[S] = preimage f S
            f⁻¹[S]- : Subset A
            f⁻¹[S]- = tail f⁻¹[S]
            f⁻¹[S]0 : Bool
            f⁻¹[S]0 = head f⁻¹[S]
            f[v] : Vector Value (suc B)
            f[v] = push v f
            f[v]- : Vector Value B
            f[v]- = tail f[v]
            f[v]0 : Value
            f[v]0 = head f[v]
            f[v-] : Vector Value (suc B)
            f[v-] = push v- f-
            f[v-]- : Vector Value B
            f[v-]- = tail f[v-]
            f[v-]0 : Value
            f[v-]0 = head f[v-]
            f⁻¹⁅0⁆ : Subset (suc A)
            f⁻¹⁅0⁆ = preimage f ⁅ zero ⁆
            f⁻¹⁅0⁆- : Subset A
            f⁻¹⁅0⁆- = tail f⁻¹⁅0⁆
            v0? v0?+[f[v-]0?] f[v]0? : Value
            v0? = v0 when f⁻¹[S]0
            v0?+[f[v-]0?] = (if S0 then join v0? f[v-]0 else v0?)
            f[v]0? = f[v]0 when S0
            ≡f[v]0 : v0?+[f[v-]0?] ≡ f[v]0?
            ≡f[v]0 rewrite f0≡0 with S0
            ... | true = begin
                      join v0 (merge v- f⁻¹⁅0⁆-)  ≡⟨ join-merge v0 v- (tail (preimage f ⁅ zero ⁆)) ⟩
                      merge-with v0 v- f⁻¹⁅0⁆-    ≡⟨ ≡.cong (λ h → merge-with (v0 when ⁅ zero ⁆ h) v- f⁻¹⁅0⁆-) f0≡0 ⟨
                      merge-with v0?′ v- f⁻¹⁅0⁆-  ≡⟨ merge-suc v (preimage f ⁅ zero ⁆) ⟨
                      merge v f⁻¹⁅0⁆              ∎
                    where
                      v0?′ : Value
                      v0?′ = v0 when head f⁻¹⁅0⁆
            ... | false = ≡.refl
            ≡f[v]- : f[v-]- ≗ f[v]-
            ≡f[v]- x = begin
                push v- f- (suc x)            ≡⟨ ≡.cong (λ h → merge-with (v0 when ⁅ suc x ⁆ h) v- (preimage f- ⁅ suc x ⁆)) f0≡0 ⟨
                push-with v0?′ v- f- (suc x)  ≡⟨ merge-suc v (preimage f ⁅ suc x ⁆) ⟨
                push v f (suc x)              ∎
              where
                v0?′ : Value
                v0?′ = v0 when head (preimage f ⁅ suc x ⁆)

merge-++
    : {n m : ℕ}
      (xs : Vector Value n)
      (ys : Vector Value m)
      (S₁ : Subset n)
      (S₂ : Subset m)
    → merge (xs ++ ys) (S₁ ++ S₂)
    ≡ join (merge xs S₁) (merge ys S₂)
merge-++ {zero} {m} xs ys S₁ S₂ = begin
    merge (xs ++ ys) (S₁ ++ S₂)       ≡⟨ merge-cong₂ (xs ++ ys) (λ _ → ≡.refl) ⟩
    merge (xs ++ ys) S₂               ≡⟨ merge-cong₁ (λ _ → ≡.refl) S₂ ⟩
    merge ys S₂                       ≡⟨ ≡.cong (λ h → join h (merge ys S₂)) (merge-[] xs S₁) ⟨
    join (merge xs S₁) (merge ys S₂)  ∎
merge-++ {suc n} {m} xs ys S₁ S₂ = begin
    merge (xs ++ ys) (S₁ ++ S₂)                                                   ≡⟨ merge-suc (xs ++ ys) (S₁ ++ S₂) ⟩
    merge-with (head xs when head S₁) (tail (xs ++ ys)) (tail (S₁ ++ S₂))         ≡⟨ join-merge (head xs when head S₁) (tail (xs ++ ys)) (tail (S₁ ++ S₂)) ⟨
    join (head xs when head S₁) (merge (tail (xs ++ ys)) (tail (S₁ ++ S₂)))
        ≡⟨ ≡.cong (join (head xs when head S₁)) (merge-cong₁ ([,]-map ∘ splitAt n) (tail (S₁ ++ S₂))) ⟩
    join (head xs when head S₁) (merge (tail xs ++ ys) (tail (S₁ ++ S₂)))
        ≡⟨ ≡.cong (join (head xs when head S₁)) (merge-cong₂ (tail xs ++ ys) ([,]-map ∘ splitAt n)) ⟩
    join (head xs when head S₁) (merge (tail xs ++ ys) (tail S₁ ++ S₂))           ≡⟨ ≡.cong (join (head xs when head S₁)) (merge-++ (tail xs) ys (tail S₁) S₂) ⟩
    join (head xs when head S₁) (join (merge (tail xs) (tail S₁)) (merge ys S₂))  ≡⟨ join-assoc (head xs when head S₁) (merge (tail xs) (tail S₁)) _ ⟨
    join (join (head xs when head S₁) (merge (tail xs) (tail S₁))) (merge ys S₂)
        ≡⟨ ≡.cong (λ h → join h (merge ys S₂)) (join-merge (head xs when head S₁) (tail xs) (tail S₁)) ⟩
    join (merge-with (head xs when head S₁) (tail xs) (tail S₁)) (merge ys S₂)    ≡⟨ ≡.cong (λ h → join h (merge ys S₂)) (merge-suc xs S₁) ⟨
    join (merge xs S₁) (merge ys S₂)                                              ∎

open import Function using (Equivalence)
open Equivalence
open import Data.Nat using (_+_)
open import Data.Fin using (_↑ˡ_; _↑ʳ_; _≟_)
open import Data.Fin.Properties using (↑ˡ-injective; ↑ʳ-injective; splitAt⁻¹-↑ˡ; splitAt-↑ˡ; splitAt⁻¹-↑ʳ; splitAt-↑ʳ)
open import Relation.Nullary.Decidable using (does; does-⇔; dec-false)

open Fin
⁅⁆-≟ : {n : ℕ} (x y : Fin n) → ⁅ x ⁆ y ≡ does (x ≟ y)
⁅⁆-≟ zero zero = ≡.refl
⁅⁆-≟ zero (suc y) = ≡.refl
⁅⁆-≟ (suc x) zero = ≡.refl
⁅⁆-≟ (suc x) (suc y) = ⁅⁆-≟ x y

open import Data.Sum using ([_,_]′; inj₁; inj₂)
⁅⁆-++
    : {n′ m′ : ℕ}
      (i : Fin (n′ + m′))
    → [ (λ x → ⁅ x ⁆ ++ ⊥) , (λ x → ⊥ ++ ⁅ x ⁆) ]′ (splitAt n′ i) ≗ ⁅ i ⁆
⁅⁆-++ {n′} {m′} i x with splitAt n′ i in eq₁
... | inj₁ i′ with splitAt n′ x in eq₂
...   | inj₁ x′ = begin
            ⁅ i′ ⁆ x′                   ≡⟨ ⁅⁆-≟ i′ x′ ⟩
            does (i′ ≟ x′)              ≡⟨ does-⇔ ⇔ (i′ ≟ x′) (i′ ↑ˡ m′ ≟ x′ ↑ˡ m′) ⟩
            does (i′ ↑ˡ m′ ≟ x′ ↑ˡ m′)  ≡⟨ ⁅⁆-≟ (i′ ↑ˡ m′) (x′ ↑ˡ m′) ⟨
            ⁅ i′ ↑ˡ m′ ⁆ (x′ ↑ˡ m′)     ≡⟨ ≡.cong₂ ⁅_⁆ (splitAt⁻¹-↑ˡ eq₁) (splitAt⁻¹-↑ˡ eq₂) ⟩
            ⁅ i ⁆ x                 ∎
          where
            ⇔ : Equivalence (≡.setoid (i′ ≡ x′)) (≡.setoid (i′ ↑ˡ m′ ≡ x′ ↑ˡ m′))
            ⇔ .to = ≡.cong (_↑ˡ m′)
            ⇔ .from = ↑ˡ-injective m′ i′ x′
            ⇔ .to-cong ≡.refl = ≡.refl
            ⇔ .from-cong ≡.refl = ≡.refl
...   | inj₂ x′ = begin
            false                       ≡⟨ dec-false (i′ ↑ˡ m′ ≟ n′ ↑ʳ x′) ↑ˡ≢↑ʳ ⟨
            does (i′ ↑ˡ m′ ≟ n′ ↑ʳ x′)  ≡⟨ ⁅⁆-≟ (i′ ↑ˡ m′) (n′ ↑ʳ x′) ⟨
            ⁅ i′ ↑ˡ m′ ⁆ (n′ ↑ʳ x′)     ≡⟨ ≡.cong₂ ⁅_⁆ (splitAt⁻¹-↑ˡ eq₁) (splitAt⁻¹-↑ʳ eq₂) ⟩
            ⁅ i ⁆ x                     ∎
          where
            ↑ˡ≢↑ʳ : i′ ↑ˡ m′ ≢ n′ ↑ʳ x′
            ↑ˡ≢↑ʳ ≡ = case ≡.trans (≡.sym (splitAt-↑ˡ n′ i′ m′)) (≡.trans (≡.cong (splitAt n′) ≡) (splitAt-↑ʳ n′ m′ x′)) of λ { () }
⁅⁆-++ {n′} i x | inj₂ i′ with splitAt n′ x in eq₂
⁅⁆-++ {n′} {m′} i x | inj₂ i′ | inj₁ x′ = begin
    [ ⊥ , ⁅ i′ ⁆ ]′ (splitAt n′ x)  ≡⟨ ≡.cong ([ ⊥ , ⁅ i′ ⁆ ]′) eq₂ ⟩
    false                           ≡⟨ dec-false (n′ ↑ʳ i′ ≟ x′ ↑ˡ m′) ↑ʳ≢↑ˡ ⟨
    does (n′ ↑ʳ i′ ≟ x′ ↑ˡ m′)      ≡⟨ ⁅⁆-≟ (n′ ↑ʳ i′) (x′ ↑ˡ m′) ⟨
    ⁅ n′ ↑ʳ i′ ⁆ (x′ ↑ˡ m′)         ≡⟨ ≡.cong₂ ⁅_⁆ (splitAt⁻¹-↑ʳ eq₁) (splitAt⁻¹-↑ˡ eq₂) ⟩
    ⁅ i ⁆ x                         ∎
  where
    ↑ʳ≢↑ˡ : n′ ↑ʳ i′ ≢ x′ ↑ˡ m′
    ↑ʳ≢↑ˡ ≡ = case ≡.trans (≡.sym (splitAt-↑ʳ n′ m′ i′)) (≡.trans (≡.cong (splitAt n′) ≡) (splitAt-↑ˡ n′ x′ m′)) of λ { () }
⁅⁆-++ {n′} i x | inj₂ i′ | inj₂ x′ = begin
    [ ⊥ , ⁅ i′ ⁆ ]′ (splitAt n′ x)  ≡⟨ ≡.cong [ ⊥ , ⁅ i′ ⁆ ]′ eq₂ ⟩
    ⁅ i′ ⁆ x′                       ≡⟨ ⁅⁆-≟ i′ x′ ⟩
    does (i′ ≟ x′)                  ≡⟨ does-⇔ ⇔ (i′ ≟ x′) (n′ ↑ʳ i′ ≟ n′ ↑ʳ x′) ⟩
    does (n′ ↑ʳ i′ ≟ n′ ↑ʳ x′)      ≡⟨ ⁅⁆-≟ (n′ ↑ʳ i′) (n′ ↑ʳ x′) ⟨
    ⁅ n′ ↑ʳ i′ ⁆ (n′ ↑ʳ x′)         ≡⟨ ≡.cong₂ ⁅_⁆ (splitAt⁻¹-↑ʳ eq₁) (splitAt⁻¹-↑ʳ eq₂) ⟩
    ⁅ i ⁆ x                         ∎
  where
    ⇔ : Equivalence (≡.setoid (i′ ≡ x′)) (≡.setoid (n′ ↑ʳ i′ ≡ n′ ↑ʳ x′))
    ⇔ .to = ≡.cong (n′ ↑ʳ_)
    ⇔ .from = ↑ʳ-injective n′ i′ x′
    ⇔ .to-cong ≡.refl = ≡.refl
    ⇔ .from-cong ≡.refl = ≡.refl
