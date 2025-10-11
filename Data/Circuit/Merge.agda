{-# OPTIONS --without-K --safe #-}

module Data.Circuit.Merge where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin; pinch; punchIn; punchOut)
open import Data.Fin.Properties using (punchInᵢ≢i; punchIn-punchOut)
open import Data.Bool.Properties using (if-float)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Circuit.Value using (Value; join; join-comm; join-assoc)
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
open import Data.Fin.Permutation
  using
    ( Permutation′
    ; _⟨$⟩ˡ_ ; _⟨$⟩ʳ_
    ; inverseˡ ; inverseʳ
    ; id
    ; flip
    ; insert ; remove
    ; punchIn-permute
    )
open import Data.Product using (Σ-syntax; _,_)
open import Data.Fin.Preimage using (preimage; preimage-cong₁; preimage-cong₂)
open import Function.Base using (∣_⟩-_; _∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)

open Value using (U)
open ℕ
open Fin
open Bool

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
        (tail (λ _ → U)) (tail S)           ≡⟨ ≡.cong (λ h → merge-with h (λ _ → U) (tail S)) (either-way (head S)) ⟨
    merge-with e (tail (λ _ → U)) (tail S)  ≡⟨⟩
    merge-with e (λ _ → U) (tail S)         ≡⟨ merge-with-U e (tail S) ⟩
    e                                       ∎
  where
    open ≡.≡-Reasoning
    either-way : (b : Bool) → e ≡ (if b then e else e)
    either-way b = if-float (λ _ → e) b {e} {e}

merge : {A : ℕ} → Vector Value A → Subset A → Value
merge v = merge-with U v

merge-cong₁ : {A : ℕ} {v₁ v₂ : Vector Value A} → v₁ ≗ v₂ → merge v₁ ≗ merge v₂
merge-cong₁ = merge-with-cong U

merge-cong₂ : {A : ℕ} (v : Vector Value A) {S₁ S₂ : Subset A} → S₁ ≗ S₂ → merge v S₁ ≡ merge v S₂
merge-cong₂ = merge-with-cong₂ U

merge-⊥ : {A : ℕ} (v : Vector Value A) → merge-with U v ⊥ ≡ U
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
  where
    open ≡.≡-Reasoning
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
    open ≡.≡-Reasoning

import Function.Structures as FunctionStructures
open module FStruct {A B : Set} = FunctionStructures {_} {_} {_} {_} {A} _≡_ {B} _≡_ using (IsInverse)
open IsInverse using () renaming (inverseˡ to invˡ; inverseʳ to invʳ)

merge-preimage-ρ
    : {A : ℕ}
    → (ρ : Permutation′ A)
    → (v : Vector Value A)
      (S : Subset A)
    → merge v (preimage (ρ ⟨$⟩ʳ_) S) ≡ merge (v ∘ (ρ ⟨$⟩ˡ_)) S
merge-preimage-ρ {zero} ρ v S = merge-[]₂
merge-preimage-ρ {suc A} ρ v S = begin
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
    ρˡ ρʳ : Fin (suc A) → Fin (suc A)
    ρˡ = ρ ⟨$⟩ˡ_
    ρʳ = ρ ⟨$⟩ʳ_
    ρ- : Permutation′ A
    ρ- = remove (head ρˡ) ρ
    ρˡ- ρʳ- : Fin A → Fin A
    ρˡ- = ρ- ⟨$⟩ˡ_
    ρʳ- = ρ- ⟨$⟩ʳ_
    v- : Vector Value A
    v- = removeAt v (head ρˡ)
    [preimageρʳS]- : Subset A
    [preimageρʳS]- = removeAt (preimage ρʳ S) (head ρˡ)
    S- : Subset A
    S- = tail S
    vρˡ0? : Value
    vρˡ0? = head (v ∘ ρˡ) when head S
    open ≡.≡-Reasoning
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
    where
      open ≡.≡-Reasoning
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
          open ≡.≡-Reasoning
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
            open ≡.≡-Reasoning
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
