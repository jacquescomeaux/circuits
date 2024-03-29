{-# OPTIONS --without-K --safe #-}
module FinMerge.Properties where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; fromℕ<; toℕ; #_; lower₁)
open import Data.Fin.Properties using (¬Fin0)
open import Data.Nat using (ℕ; _+_; _≤_; _<_; z<s; pred; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; <⇒≢)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong-app; sym; _≢_)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Maybe.Base using (Maybe; nothing; just; fromMaybe)
open import Function using (id;  _∘_)

open import Util using (_<_<_; _<_≤_; toℕ<; Ordering; less; equal; greater; compare)

open import FinMerge using (merge; pluck; glue-once; glue-unglue-once; glue-iter)


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

glue-once-correct
    : {i j : Fin (ℕ.suc n)}
    → (i?j : Ordering i j)
    → proj₂ (glue-once i?j) i ≡ proj₂ (glue-once i?j) j
glue-once-correct (less (i<j , s≤s j≤n)) = merge-i-j (i<j , j≤n)
glue-once-correct (equal i≡j) = i≡j
glue-once-correct (greater (j<i , s≤s i≤n)) = sym (merge-i-j (j<i , i≤n))

glue-once-correct′
    : {i j : Fin (ℕ.suc n)}
    → (i?j : Ordering i j)
    → proj₁ (proj₂ (glue-unglue-once i?j)) i ≡ proj₁ (proj₂ (glue-unglue-once i?j)) j
glue-once-correct′ (less (i<j , s≤s j≤n)) = merge-i-j (i<j , j≤n)
glue-once-correct′ (equal i≡j) = i≡j
glue-once-correct′ (greater (j<i , s≤s i≤n)) = sym (merge-i-j (j<i , i≤n))

glue-iter-append
    : {y : ℕ}
    → (f g : Fin m → Fin y)
    → (h : Fin n → Fin y)
    → Σ[ h′ ∈ (Fin y → Fin (proj₁ (glue-iter f g h))) ] (proj₂ (glue-iter f g h) ≡ h′ ∘ h)
glue-iter-append {ℕ.zero} f g h = id , refl
glue-iter-append {ℕ.suc m} {_} {ℕ.zero} f g h = ⊥-elim (¬Fin0 (f (# 0)))
glue-iter-append {ℕ.suc m} {_} {ℕ.suc y} f g h =
  let
    p = proj₁ (proj₂ (glue-unglue-once (compare (f (# 0)) (g (# 0)))))
    h′ , glue-p∘h≡h′∘p∘h = glue-iter-append (p ∘ f ∘ Fin.suc) (p ∘ g ∘ Fin.suc) (p ∘ h)
  in
    h′ ∘ p , glue-p∘h≡h′∘p∘h

lemma₂
    : (f g : Fin (ℕ.suc m) → Fin n)
    → let p = proj₂ (glue-iter f g id) in p (f (# 0)) ≡ p (g (# 0))
lemma₂ {_} {ℕ.zero} f g = ⊥-elim (¬Fin0 (f (# 0)))
lemma₂ {_} {ℕ.suc n} f g =
  let
    p = proj₁ (proj₂ (glue-unglue-once (compare (f (# 0)) (g (# 0)))))
    h′ , glue≡h′∘h = glue-iter-append (p ∘ f ∘ Fin.suc) (p ∘ g ∘ Fin.suc) p
    f′ = f ∘ Fin.suc
    g′ = g ∘ Fin.suc
    ≡ : proj₂ (glue-iter (p ∘ f′) (p ∘ g′) p) (f Fin.zero)
      ≡ proj₂ (glue-iter (p ∘ f′) (p ∘ g′) p) (g Fin.zero)
    ≡ = begin
        proj₂ (glue-iter (p ∘ f′) (p ∘ g′) p) (f Fin.zero)
                              ≡⟨ cong-app glue≡h′∘h (f Fin.zero) ⟩
        h′ (p (f Fin.zero))   ≡⟨ cong h′ (glue-once-correct′ (compare (f (# 0)) (g (# 0)))) ⟩
        h′ (p (g Fin.zero))   ≡⟨ sym (cong-app glue≡h′∘h (g Fin.zero)) ⟩
        proj₂ (glue-iter (p ∘ f′) (p ∘ g′) p) (g Fin.zero) ∎
  in
    ≡
  where open ≡-Reasoning
