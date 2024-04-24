{-# OPTIONS --without-K --safe #-}
module FinMerge.Properties where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; fromℕ<; toℕ; #_; lower₁; _↑ˡ_; cast)
open import Data.Fin.Properties using (¬Fin0)
open import Data.Nat using (ℕ; _+_; _≤_; _<_; z<s; pred; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; <⇒≢; <-cmp)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong-app; sym; _≢_)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Maybe.Base using (Maybe; map; nothing; just; fromMaybe)
open import Function using (id;  _∘_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

open import Util using (_<_<_; _<_≤_; toℕ<; Ordering; less; equal; greater; compare)

open import FinMerge using (merge; unmerge; pluck; glue-once; glue-unglue-once; glue-iter; unpluck)


private
  variable
    m n : ℕ

s≡s⁻¹ : {j k : ℕ} → ℕ.suc j ≡ ℕ.suc k → j ≡ k
s≡s⁻¹ {ℕ.zero} {ℕ.zero} _ = refl
s≡s⁻¹ {ℕ.suc j} {ℕ.suc .j} refl = refl

not-n : {x : Fin (ℕ.suc n)} → toℕ x < m ≤ n → n ≢ toℕ x
not-n (x<m , m≤n) n≡x = <⇒≢ (≤-trans x<m m≤n) (sym n≡x)

pluck-<
    : {x : Fin (ℕ.suc n)}
    → (m≤n : m ≤ n)
    → (x<m : toℕ x < m)
    → pluck m≤n x ≡ just (lower₁ x (not-n (x<m , m≤n)))
pluck-< {_} {_} {Fin.zero} (s≤s m≤n) (s≤s x<m) = refl
pluck-< {_} {_} {Fin.suc x} (s≤s m≤n) (s≤s x<m) = ≡
  where
    open ≡-Reasoning
    ≡ : pluck (s≤s m≤n) (Fin.suc x)
        ≡ just (lower₁ (Fin.suc x) (not-n (s≤s x<m , s≤s m≤n)))
    ≡ = begin
        pluck (s≤s m≤n) (Fin.suc x) ≡⟨⟩
        Data.Maybe.Base.map Fin.suc (pluck m≤n x)
            ≡⟨ cong (map Fin.suc) (pluck-< m≤n x<m) ⟩
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
        map Fin.suc (pluck m≤n x)   ≡⟨ cong (map Fin.suc) (pluck-≡ m≤n refl) ⟩
        map Fin.suc nothing         ≡⟨⟩
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

merge-unmerge-<
    : {i j k : Fin (ℕ.suc n)}
    → (i<j≤n : toℕ i < toℕ j ≤ n)
    → (k<j : toℕ k < toℕ j)
    → unmerge i<j≤n (merge i<j≤n k) ≡ k
merge-unmerge-< {_} {_} {_} {k} i<j≤n@(i<j , j≤n) k<j = let open ≡-Reasoning in begin
    unmerge i<j≤n (merge i<j≤n k)                 ≡⟨ cong (unmerge i<j≤n ∘ (fromMaybe (fromℕ< (≤-trans i<j j≤n)))) (k-to-just (k<j , j≤n)) ⟩
    unmerge i<j≤n (fromℕ< (≤-trans k<j j≤n))      ≡⟨⟩
    unpluck j≤n (just (fromℕ< (≤-trans k<j j≤n))) ≡⟨ unpluck-k-< j≤n k<j ⟩
    k                                         ∎
  where
    k-to-just
        : {j k : Fin (ℕ.suc m)} ((k<j , j≤m) : toℕ k < toℕ j ≤ m)
        → pluck j≤m k ≡ just (fromℕ< (≤-trans k<j j≤m))
    k-to-just {ℕ.suc m} {Fin.suc j} {Fin.zero} (s≤s k<j , s≤s j≤m) = refl
    k-to-just {ℕ.suc m} {Fin.suc j} {Fin.suc k} (s≤s k<j , s≤s j≤m) = cong (map Fin.suc) (k-to-just (k<j , j≤m))
    unpluck-k-<
        : {j k : Fin (ℕ.suc m)} (j≤m : toℕ j ≤ m) (k<j : toℕ k < toℕ j)
        → unpluck j≤m (just (fromℕ< (≤-trans k<j j≤m))) ≡ k
    unpluck-k-< {ℕ.suc m} {Fin.suc j} {Fin.zero} (s≤s j≤m) (s≤s k<j)  = refl
    unpluck-k-< {ℕ.suc m} {Fin.suc j} {Fin.suc k} (s≤s j≤m) (s≤s k<j) = cong Fin.suc (unpluck-k-< j≤m k<j)

merge-unmerge-=
    : {i j k : Fin (ℕ.suc n)}
    → (i<j≤n : toℕ i < toℕ j ≤ n)
    → k ≡ j
    → unmerge i<j≤n (merge i<j≤n k) ≡ i
merge-unmerge-= {_} {i} {j} {k} i<j≤n@(i<j , j≤n) k≡j = let open ≡-Reasoning in begin
    unmerge i<j≤n (merge i<j≤n k)             ≡⟨ cong (unmerge i<j≤n ∘ merge i<j≤n) k≡j ⟩
    unmerge i<j≤n (merge i<j≤n j)             ≡⟨ cong (unmerge i<j≤n ∘ fromMaybe (fromℕ< (≤-trans i<j j≤n))) (j-to-nothing j≤n) ⟩
    unmerge i<j≤n (fromℕ< (≤-trans i<j j≤n))  ≡⟨ unmerge-i i<j≤n ⟩
    i                                         ∎
  where
    j-to-nothing : {j : Fin (ℕ.suc n)} → (j≤n : toℕ j ≤ n) → pluck j≤n j ≡ nothing
    j-to-nothing {ℕ.zero} {Fin.zero} z≤n = refl
    j-to-nothing {ℕ.suc n} {Fin.zero} z≤n = refl
    j-to-nothing {ℕ.suc n} {Fin.suc j} (s≤s j≤n) = cong (map Fin.suc) (j-to-nothing j≤n)
    unmerge-i
        : {i j : Fin (ℕ.suc n)} ((i<j , j≤n) : toℕ i < toℕ j ≤ n)
        → unmerge (i<j , j≤n) (fromℕ< (≤-trans i<j j≤n)) ≡ i
    unmerge-i {ℕ.suc n} {Fin.zero} {Fin.suc j} (s≤s i<j , s≤s j≤n) = refl
    unmerge-i {ℕ.suc n} {Fin.suc i} {Fin.suc j} (s≤s i<j , s≤s j≤n) = cong Fin.suc (unmerge-i (i<j , j≤n))

merge-unmerge->
    : {i j k : Fin (ℕ.suc n)}
    → (i<j≤n : toℕ i < toℕ j ≤ n)
    → (j<k : toℕ j < toℕ k)
    → unmerge i<j≤n (merge i<j≤n k) ≡ k
merge-unmerge-> {n} {i} {j} {Fin.suc k} i<j≤n@(i<j , j≤n) j<k = let open ≡-Reasoning in begin
    unmerge i<j≤n (merge i<j≤n (Fin.suc k)) ≡⟨⟩
    unmerge i<j≤n
        (fromMaybe
            (fromℕ< (≤-trans i<j j≤n))
            (pluck j≤n (Fin.suc k)))        ≡⟨ cong (unmerge i<j≤n ∘ fromMaybe (fromℕ< (≤-trans i<j j≤n))) (sk-to-just j≤n j<k) ⟩
    unmerge i<j≤n k                         ≡⟨⟩
    unpluck j≤n (just k)                    ≡⟨ unpluck-k-> j≤n j<k ⟩
    Fin.suc k                               ∎
  where
    sk-to-just
        : {n : ℕ} {j : Fin (ℕ.suc n)} {k : Fin n} (j≤n : toℕ j ≤ n) (j<sk : toℕ j < ℕ.suc (toℕ k))
        → pluck j≤n (Fin.suc k) ≡ just k
    sk-to-just {ℕ.suc _} {Fin.zero} {Fin.zero} z≤n (s≤s _) = refl
    sk-to-just {ℕ.suc _} {Fin.zero} {Fin.suc _} z≤n (s≤s _) = refl
    sk-to-just {ℕ.suc _} {Fin.suc _} {Fin.suc _} (s≤s j≤n) (s≤s j<sk) = cong (map Fin.suc) (sk-to-just j≤n j<sk)
    unpluck-k->
        : {j : Fin (ℕ.suc m)} {k : Fin m} (j≤m : toℕ j ≤ m) (j<sk : toℕ j < ℕ.suc (toℕ k))
        → unpluck j≤m (just k) ≡ Fin.suc k
    unpluck-k-> {ℕ.suc m} {Fin.zero} {_} z≤n (s≤s j<sk) = refl
    unpluck-k-> {ℕ.suc m} {Fin.suc j} {Fin.suc k} (s≤s j≤m) (s≤s j<sk) = cong Fin.suc (unpluck-k-> j≤m j<sk)

merge-unmerge
    : {i j k : Fin (ℕ.suc n)}
    → (i<j≤n : toℕ i < toℕ j ≤ n)
    → (f : Fin (ℕ.suc n) → Fin m)
    → f i ≡ f j
    → f (unmerge i<j≤n (merge i<j≤n k)) ≡ f k
merge-unmerge {n} {m} {i} {j} {k} i<j≤n f fi≡fj with compare k j
... | less (k<j , _) = cong f (merge-unmerge-< i<j≤n k<j)
... | equal k≡j = let open ≡-Reasoning in begin
        f (unmerge i<j≤n (merge i<j≤n k)) ≡⟨ cong f (merge-unmerge-= i<j≤n k≡j) ⟩
        f i                               ≡⟨ fi≡fj ⟩
        f j                               ≡⟨ cong f (sym k≡j) ⟩
        f k                               ∎
... | greater (j<k , _) = cong f (merge-unmerge-> i<j≤n j<k)

unmerge-merge-<
    : {i j : Fin (ℕ.suc n)}
    → {k : Fin n}
    → (i<j≤n@(i<j , j≤n) : toℕ i < toℕ j ≤ n)
    → (k<j : toℕ k < toℕ j)
    → merge i<j≤n (unmerge i<j≤n k) ≡ k
unmerge-merge-< {n} {i} {j} {k} i<j≤n@(i<j , j≤n) k<j = let open ≡-Reasoning in begin
    merge i<j≤n (unmerge i<j≤n k)                 ≡⟨⟩
    merge i<j≤n (unpluck j≤n (just k))            ≡⟨⟩
    fromMaybe
        (fromℕ< (≤-trans i<j j≤n))
        (pluck j≤n (unpluck j≤n (just k)))        ≡⟨ cong (fromMaybe (fromℕ< (≤-trans i<j j≤n))) (unpluck-pluck-< j≤n k<j) ⟩
    fromMaybe (fromℕ< (≤-trans i<j j≤n)) (just k) ≡⟨⟩
    k                                             ∎
  where
    unpluck-pluck-<
        : {j : Fin (ℕ.suc m)}
        → {k : Fin m}
        → (j≤m : toℕ j ≤ m)
        → (k<j : toℕ k < toℕ j)
        → pluck j≤m (unpluck j≤m (just k)) ≡ just k
    unpluck-pluck-< {ℕ.suc m} {Fin.suc j} {Fin.zero} (s≤s j≤m) (s≤s k<j) = refl
    unpluck-pluck-< {ℕ.suc m} {Fin.suc j} {Fin.suc k} (s≤s j≤m) (s≤s k<j) = cong (map Fin.suc) (unpluck-pluck-< j≤m k<j)

unmerge-merge-=
    : {i j : Fin (ℕ.suc n)}
    → {k : Fin n}
    → (i<j≤n@(i<j , j≤n) : toℕ i < toℕ j ≤ n)
    → toℕ k ≡ toℕ j
    → merge i<j≤n (unmerge i<j≤n k) ≡ k
unmerge-merge-= {_} {i} {j} {k} i<j≤n@(i<j , j≤n) k≡j = let open ≡-Reasoning in begin
    merge i<j≤n (unmerge i<j≤n k)                 ≡⟨⟩
    fromMaybe
        (fromℕ< (≤-trans i<j j≤n))
        (pluck j≤n (unpluck j≤n (just k)))        ≡⟨ cong (fromMaybe (fromℕ< (≤-trans i<j j≤n))) (unpluck-pluck-= j≤n k≡j) ⟩
    fromMaybe (fromℕ< (≤-trans i<j j≤n)) (just k) ≡⟨⟩
    k                                             ∎
  where
    unpluck-pluck-=
        : {j : Fin (ℕ.suc m)}
        → {k : Fin m}
        → (j≤m : toℕ j ≤ m)
        → toℕ k ≡ toℕ j
        → pluck j≤m (unpluck j≤m (just k)) ≡ just k
    unpluck-pluck-= {ℕ.suc m} {Fin.zero} {Fin.zero} z≤n k≡j = refl
    unpluck-pluck-= {ℕ.suc m} {Fin.suc j} {Fin.suc k} (s≤s j≤m) k≡j = cong (map Fin.suc) (unpluck-pluck-= j≤m (s≡s⁻¹ k≡j))

unmerge-merge->
    : {i j : Fin (ℕ.suc n)}
    → {k : Fin n}
    → (i<j≤n@(i<j , j≤n) : toℕ i < toℕ j ≤ n)
    → (j<k : toℕ j < toℕ k)
    → merge i<j≤n (unmerge i<j≤n k) ≡ k
unmerge-merge-> {n} {i} {j} {k} i<j≤n@(i<j , j≤n) j<k = let open ≡-Reasoning in begin
    merge i<j≤n (unmerge i<j≤n k)                 ≡⟨⟩
    merge i<j≤n (unpluck j≤n (just k))            ≡⟨⟩
    fromMaybe
        (fromℕ< (≤-trans i<j j≤n))
        (pluck j≤n (unpluck j≤n (just k)))        ≡⟨ cong (fromMaybe (fromℕ< (≤-trans i<j j≤n))) (unpluck-pluck-> j≤n j<k) ⟩
    fromMaybe (fromℕ< (≤-trans i<j j≤n)) (just k) ≡⟨⟩
    k                                             ∎
  where
    unpluck-pluck->
        : {j : Fin (ℕ.suc m)}
        → {k : Fin m}
        → (j≤m : toℕ j ≤ m)
        → (j<k : toℕ j < toℕ k)
        → pluck j≤m (unpluck j≤m (just k)) ≡ just k
    unpluck-pluck-> {ℕ.suc m} {Fin.zero} {Fin.suc k} z≤n (s≤s j<k) = refl
    unpluck-pluck-> {ℕ.suc m} {Fin.suc j} {Fin.suc k} (s≤s j≤m) (s≤s j<k) = cong (map Fin.suc) (unpluck-pluck-> j≤m j<k)

unmerge-merge
    : {i j : Fin (ℕ.suc n)}
    → {k : Fin n}
    → (i<j≤n : toℕ i < toℕ j ≤ n)
    → merge i<j≤n (unmerge i<j≤n k) ≡ k
unmerge-merge {n} {i} {j} {k} i<j≤n with <-cmp (toℕ k) (toℕ j)
... | tri< k<j _ _ = unmerge-merge-< i<j≤n k<j
... | tri≈ _ k≡j _ = unmerge-merge-= i<j≤n k≡j
... | tri> _ _ j<k = unmerge-merge-> i<j≤n j<k
