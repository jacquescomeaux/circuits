module FinMerge.Properties where

open import Data.Fin using (Fin; fromℕ<; toℕ; #_; lower₁)
open import Data.Fin.Properties using (¬Fin0)
open import Data.Nat using (ℕ; _+_; _≤_; _<_; z<s; pred; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; <⇒≢)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; _≢_)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Maybe.Base using (Maybe; nothing; just; fromMaybe)

open import Util using (_<_<_; _<_≤_; toℕ<)

open import FinMerge using (merge; pluck)


private
  variable
    m n : ℕ

not-n : {x : Fin (ℕ.suc n)} → toℕ x < m ≤ n → n ≢ toℕ x
not-n (x<m , m≤n) n≡x = <⇒≢ (≤-trans x<m m≤n) (sym n≡x)

pluck-<
    : {x : Fin (ℕ.suc n)}
    → (m≤n : m ≤ n)
    → (x<m : toℕ x < m)
    → pluck m≤n x ≡ just (lower₁ x (not-n (x<m , m≤n)))
pluck-< {_} {_} {Fin.zero} (_≤_.s≤s m≤n) (_≤_.s≤s x<m) = refl
pluck-< {_} {_} {Fin.suc x} (_≤_.s≤s m≤n) (_≤_.s≤s x<m) = ≡
  where
    open ≡-Reasoning
    ≡ : pluck (_≤_.s≤s m≤n) (Fin.suc x)
        ≡ just (lower₁ (Fin.suc x) (not-n (s≤s x<m , s≤s m≤n)))
    ≡ = begin
        pluck (_≤_.s≤s m≤n) (Fin.suc x) ≡⟨⟩
        Data.Maybe.Base.map Fin.suc (pluck m≤n x)
            ≡⟨ cong (Data.Maybe.Base.map Fin.suc) (pluck-< m≤n x<m) ⟩
        Data.Maybe.Base.map Fin.suc (just (lower₁ x (not-n (x<m , m≤n)))) ≡⟨⟩
        just (Fin.suc (lower₁ x (not-n (x<m , m≤n)))) ≡⟨⟩
        just (lower₁ (Fin.suc x) (not-n (s≤s x<m , s≤s m≤n))) ∎

pluck-≡
    : {x : Fin (ℕ.suc n)}
    → (m≤n : m ≤ n)
    → (x≡m : toℕ x ≡ m)
    → pluck m≤n x ≡ nothing
pluck-≡ {_} {_} {Fin.zero} z≤n x≡m = refl
pluck-≡ {_} {_} {Fin.suc x} (s≤s m≤n) refl = ≡
  where
    open ≡-Reasoning
    ≡ : pluck (s≤s m≤n) (Fin.suc x) ≡ nothing
    ≡ = begin
        pluck (s≤s m≤n) (Fin.suc x) ≡⟨⟩
        Data.Maybe.Base.map Fin.suc (pluck m≤n x)
            ≡⟨ cong (Data.Maybe.Base.map Fin.suc) (pluck-≡ m≤n refl) ⟩
        Data.Maybe.Base.map Fin.suc nothing ≡⟨⟩
        nothing ∎

i-to-i
    : {i j : Fin (ℕ.suc n)} (i<j≤n@(i<j , j≤n) : toℕ i < toℕ j ≤ n)
    → merge i<j≤n i ≡ lower₁ i (not-n i<j≤n)
i-to-i {i = i} (lt , le) = ≡
  where
    open ≡-Reasoning
    ≡ : merge (lt , le) i ≡ lower₁ i (not-n (lt , le))
    ≡ = begin
        merge (lt , le) i ≡⟨⟩
        fromMaybe (fromℕ< (≤-trans lt le)) (pluck le i)
            ≡⟨ cong (fromMaybe (fromℕ< (≤-trans lt le))) (pluck-< le lt) ⟩
        fromMaybe (fromℕ< (≤-trans lt le)) (just (lower₁ i (not-n (lt , le)))) ≡⟨⟩
        lower₁ i (not-n (lt , le)) ∎

lemma₁
    : {i j : Fin (ℕ.suc n)} ((lt , le) : toℕ i < toℕ j ≤ n)
    → fromℕ< (≤-trans lt le) ≡ lower₁ i (not-n (lt , le))
lemma₁ {ℕ.suc _} {Fin.zero} {Fin.suc _} _ = refl
lemma₁ {ℕ.suc _} {Fin.suc _} {Fin.suc _} (s≤s lt , s≤s le) = cong Fin.suc (lemma₁ (lt , le))

j-to-i
    : {i j : Fin (ℕ.suc n)} (i<j≤n@(i<j , j≤n) : toℕ i < toℕ j ≤ n)
    → merge i<j≤n j ≡ lower₁ i (not-n i<j≤n)
j-to-i {i = i} {j = j} (lt , le) = ≡
  where
    open ≡-Reasoning
    ≡ : merge (lt , le) j ≡ lower₁ i (not-n (lt , le))
    ≡ = begin
        merge (lt , le) j ≡⟨⟩
        fromMaybe (fromℕ< (≤-trans lt le)) (pluck le j)
            ≡⟨ cong (fromMaybe (fromℕ< (≤-trans lt le))) (pluck-≡ le refl) ⟩
        fromMaybe (fromℕ< (≤-trans lt le)) nothing ≡⟨⟩
        fromℕ< (≤-trans lt le) ≡⟨ lemma₁ (lt , le) ⟩
        lower₁ i (not-n (lt , le)) ∎

merge-i-j
    : {i j : Fin (ℕ.suc n)}
    → (i<j≤n : toℕ i < toℕ j ≤ n)
    → merge i<j≤n i ≡ merge i<j≤n j
merge-i-j {_} {i} {j} i<j≤n = ≡
  where
    open ≡-Reasoning
    ≡ : merge i<j≤n i ≡ merge i<j≤n j
    ≡ = begin
      merge i<j≤n i ≡⟨ i-to-i i<j≤n ⟩
      lower₁ i (not-n i<j≤n) ≡⟨ sym (j-to-i i<j≤n) ⟩
      merge i<j≤n j ∎
