{-# OPTIONS --without-K --safe #-}

module Functor.Monoidal.Instance.Nat.Push where

open import Categories.Category.Instance.Nat using (Nat)
open import Data.Bool.Base using (Bool; false)
open import Data.Subset.Functional using (Subset; ⁅_⁆; ⊥)
open import Function.Base using (_∘_; case_of_; _$_; id)
open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)
open import Level using (0ℓ; Level)
open import Relation.Binary using (Rel; Setoid)
open import Functor.Instance.Nat.Push using (Values; Push; Push₁; Push-identity)
open import Categories.Category.Instance.SingletonSet using (SingletonSetoid)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Data.Vec.Functional using (Vector; []; _++_; head; tail)
open import Data.Vec.Functional.Properties using (++-cong)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open Cartesian (Setoids-Cartesian {0ℓ} {0ℓ}) using (products)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Categories.Category.Instance.Nat using (Nat-Cocartesian)
open import Categories.Category.Cocartesian using (Cocartesian; module BinaryCoproducts)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using () renaming (_∘F_ to _∘′_)
open Cocartesian Nat-Cocartesian using (module Dual; i₁; i₂; -+-; _+₁_; +-assoc; +-assocʳ; +-assocˡ; +-comm; +-swap; +₁∘+-swap)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_,_; _×_; Σ)
open import Data.Fin.Preimage using (preimage; preimage-⊥; preimage-cong₂)
open import Functor.Monoidal.Instance.Nat.Preimage using (preimage-++)
open import Data.Sum.Base using ([_,_]; [_,_]′; inj₁; inj₂)
open import Data.Sum.Properties using ([,]-cong; [,-]-cong; [-,]-cong; [,]-∘; [,]-map)
open import Data.Circuit.Merge using (merge-with; merge; merge-⊥; merge-[]; merge-cong₁; merge-cong₂; merge-suc; _when_; join-merge; merge-preimage-ρ; merge-⁅⁆)
open import Data.Circuit.Value using (Value; join; join-comm; join-assoc)
open import Data.Fin.Base using (splitAt; _↑ˡ_; _↑ʳ_) renaming (join to joinAt)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ; ↑ˡ-injective; ↑ʳ-injective; _≟_; 2↔Bool)
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



open Func
Push-ε : SingletonSetoid {0ℓ} {0ℓ} ⟶ₛ Values 0
to Push-ε x = []
cong Push-ε x ()

++ₛ : {n m : ℕ} → Values n ×ₛ Values m ⟶ₛ Values (n + m)
to ++ₛ (xs , ys) = xs ++ ys
cong ++ₛ (≗xs , ≗ys) = ++-cong _ _ ≗xs ≗ys

∣_∣ : {c ℓ : Level} → Setoid c ℓ → Set c
∣_∣ = Setoid.Carrier

open ℕ
merge-++
    : {n m : ℕ}
      (xs : ∣ Values n ∣)
      (ys : ∣ Values m ∣)
      (S₁ : Subset n)
      (S₂ : Subset m)
    → merge (xs ++ ys) (S₁ ++ S₂)
    ≡ join (merge xs S₁) (merge ys S₂)
merge-++ {zero} {m} xs ys S₁ S₂ = begin
    merge (xs ++ ys) (S₁ ++ S₂)       ≡⟨ merge-cong₂ (xs ++ ys) (λ _ → ≡.refl) ⟩
    merge (xs ++ ys) S₂               ≡⟨ merge-cong₁ (λ _ → ≡.refl) S₂ ⟩
    merge ys S₂                       ≡⟨ ≡.cong (λ h → join h (merge ys S₂)) (merge-[] xs S₁) ⟨
    join (merge xs S₁) (merge ys S₂)  ∎
  where
    open ≡-Reasoning
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
  where
    open ≡-Reasoning

open Fin
⁅⁆-≟ : {n : ℕ} (x y : Fin n) → ⁅ x ⁆ y ≡ does (x ≟ y)
⁅⁆-≟ zero zero = ≡.refl
⁅⁆-≟ zero (suc y) = ≡.refl
⁅⁆-≟ (suc x) zero = ≡.refl
⁅⁆-≟ (suc x) (suc y) = ⁅⁆-≟ x y

Push-++
    : {n n′ m m′ : ℕ}
      (f : Fin n → Fin n′)
      (g : Fin m → Fin m′)
      (xs : ∣ Values n ∣)
      (ys : ∣ Values m ∣)
    → merge xs ∘ preimage f ∘ ⁅_⁆ ++ merge ys ∘ preimage g ∘ ⁅_⁆
    ≗ merge (xs ++ ys) ∘ preimage (f +₁ g) ∘ ⁅_⁆
Push-++ {n} {n′} {m} {m′} f g xs ys i = begin
    ((merge xs ∘ preimage f ∘ ⁅_⁆) ++ (merge ys ∘ preimage g ∘ ⁅_⁆)) i ≡⟨⟩
    [ merge xs ∘ preimage f ∘ ⁅_⁆ , merge ys ∘ preimage g ∘ ⁅_⁆ ]′ (splitAt n′ i)
        ≡⟨ [,]-cong left right (splitAt n′ i) ⟩
    [ (λ x → merge (xs ++ ys) _) , (λ x → merge (xs ++ ys) _) ]′ (splitAt n′ i)
        ≡⟨ [,]-∘ (merge (xs ++ ys) ∘ (preimage (f +₁ g))) (splitAt n′ i) ⟨
    merge (xs ++ ys) (preimage (f +₁ g) ([ ⁅⁆++⊥ , ⊥++⁅⁆ ]′ (splitAt n′ i))) ≡⟨⟩
    merge (xs ++ ys) (preimage (f +₁ g) ((⁅⁆++⊥ ++ ⊥++⁅⁆) i)) ≡⟨ merge-cong₂ (xs ++ ys) (preimage-cong₂ (f +₁ g) (⁅⁆-++ i)) ⟩
    merge (xs ++ ys) (preimage (f +₁ g) ⁅ i ⁆) ∎
  where
    open ≡-Reasoning
    left : (x : Fin n′) → merge xs (preimage f ⁅ x ⁆) ≡ merge (xs ++ ys) (preimage (f +₁ g) (⁅ x ⁆ ++ ⊥))
    left x = begin
        merge xs (preimage f ⁅ x ⁆)                                   ≡⟨ join-comm U (merge xs (preimage f ⁅ x ⁆)) ⟩
        join (merge xs (preimage f ⁅ x ⁆)) U                          ≡⟨ ≡.cong (join (merge _ _)) (merge-⊥ ys) ⟨
        join (merge xs (preimage f ⁅ x ⁆)) (merge ys ⊥)               ≡⟨ ≡.cong (join (merge _ _)) (merge-cong₂ ys (preimage-⊥ g)) ⟨
        join (merge xs (preimage f ⁅ x ⁆)) (merge ys (preimage g ⊥))  ≡⟨ merge-++ xs ys (preimage f ⁅ x ⁆) (preimage g ⊥) ⟨
        merge (xs ++ ys) ((preimage f ⁅ x ⁆) ++ (preimage g ⊥))       ≡⟨ merge-cong₂ (xs ++ ys) (preimage-++ f g) ⟩
        merge (xs ++ ys) (preimage (f +₁ g) (⁅ x ⁆ ++ ⊥))             ∎
    right : (x : Fin m′) → merge ys (preimage g ⁅ x ⁆) ≡ merge (xs ++ ys) (preimage (f +₁ g) (⊥ ++ ⁅ x ⁆))
    right x = begin
        merge ys (preimage g ⁅ x ⁆)                                   ≡⟨⟩
        join U (merge ys (preimage g ⁅ x ⁆))                          ≡⟨ ≡.cong (λ h → join h (merge _ _)) (merge-⊥ xs) ⟨
        join (merge xs ⊥) (merge ys (preimage g ⁅ x ⁆))               ≡⟨ ≡.cong (λ h → join h (merge _ _)) (merge-cong₂ xs (preimage-⊥ f)) ⟨
        join (merge xs (preimage f ⊥)) (merge ys (preimage g ⁅ x ⁆))  ≡⟨ merge-++ xs ys (preimage f ⊥) (preimage g ⁅ x ⁆) ⟨
        merge (xs ++ ys) ((preimage f ⊥) ++ (preimage g ⁅ x ⁆))       ≡⟨ merge-cong₂ (xs ++ ys) (preimage-++ f g) ⟩
        merge (xs ++ ys) (preimage (f +₁ g) (⊥ ++ ⁅ x ⁆))             ∎
    ⁅⁆++⊥ : Vector (Subset (n′ + m′)) n′
    ⁅⁆++⊥ x = ⁅ x ⁆ ++ ⊥
    ⊥++⁅⁆ : Vector (Subset (n′ + m′)) m′
    ⊥++⁅⁆ x = ⊥ ++ ⁅ x ⁆

    open ℕ

    open Equivalence

    ⁅⁆-++
        : (i : Fin (n′ + m′))
        → [ (λ x → ⁅ x ⁆ ++ ⊥) , (λ x → ⊥ ++ ⁅ x ⁆) ]′ (splitAt n′ i) ≗ ⁅ i ⁆
    ⁅⁆-++ i x with splitAt n′ i in eq₁
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
    ⁅⁆-++ i x | inj₂ i′ with splitAt n′ x in eq₂
    ⁅⁆-++ i x | inj₂ i′ | inj₁ x′ = ≡.trans (≡.cong ([ ⊥ , ⁅ i′ ⁆ ]′) eq₂) $ begin
        false                       ≡⟨ dec-false (n′ ↑ʳ i′ ≟ x′ ↑ˡ m′) ↑ʳ≢↑ˡ ⟨
        does (n′ ↑ʳ i′ ≟ x′ ↑ˡ m′)  ≡⟨ ⁅⁆-≟ (n′ ↑ʳ i′) (x′ ↑ˡ m′) ⟨
        ⁅ n′ ↑ʳ i′ ⁆ (x′ ↑ˡ m′)     ≡⟨ ≡.cong₂ ⁅_⁆ (splitAt⁻¹-↑ʳ eq₁) (splitAt⁻¹-↑ˡ eq₂) ⟩
        ⁅ i ⁆ x                     ∎
      where
        ↑ʳ≢↑ˡ : n′ ↑ʳ i′ ≢ x′ ↑ˡ m′
        ↑ʳ≢↑ˡ ≡ = case ≡.trans (≡.sym (splitAt-↑ʳ n′ m′ i′)) (≡.trans (≡.cong (splitAt n′) ≡) (splitAt-↑ˡ n′ x′ m′)) of λ { () }
    ⁅⁆-++ i x | inj₂ i′ | inj₂ x′ = begin
        [ ⊥ , ⁅ i′ ⁆ ] (splitAt n′ x) ≡⟨ ≡.cong ([ ⊥ , ⁅ i′ ⁆ ]) eq₂ ⟩
        ⁅ i′ ⁆ x′                     ≡⟨ ⁅⁆-≟ i′ x′ ⟩
        does (i′ ≟ x′)                ≡⟨ does-⇔ ⇔ (i′ ≟ x′) (n′ ↑ʳ i′ ≟ n′ ↑ʳ x′) ⟩
        does (n′ ↑ʳ i′ ≟ n′ ↑ʳ x′)    ≡⟨ ⁅⁆-≟ (n′ ↑ʳ i′) (n′ ↑ʳ x′) ⟨
        ⁅ n′ ↑ʳ i′ ⁆ (n′ ↑ʳ x′)       ≡⟨ ≡.cong₂ ⁅_⁆ (splitAt⁻¹-↑ʳ eq₁) (splitAt⁻¹-↑ʳ eq₂) ⟩
        ⁅ i ⁆ x                       ∎
      where
        ⇔ : Equivalence (≡.setoid (i′ ≡ x′)) (≡.setoid (n′ ↑ʳ i′ ≡ n′ ↑ʳ x′))
        ⇔ .to = ≡.cong (n′ ↑ʳ_)
        ⇔ .from = ↑ʳ-injective n′ i′ x′
        ⇔ .to-cong ≡.refl = ≡.refl
        ⇔ .from-cong ≡.refl = ≡.refl

⊗-homomorphism : NaturalTransformation (-×- ∘′ (Push ⁂ Push)) (Push ∘′ -+-)
⊗-homomorphism = ntHelper record
    { η = λ (n , m) → ++ₛ {n} {m}
    ; commute = λ { {n , m} {n′ , m′} (f , g) {xs , ys} i → Push-++ f g xs ys i }
    }

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

Push-assoc
    : {m n o : ℕ}
      (X : ∣ Values m ∣)
      (Y : ∣ Values n ∣)
      (Z : ∣ Values o ∣)
    → merge ((X ++ Y) ++ Z) ∘ preimage (+-assocˡ {m}) ∘  ⁅_⁆
    ≗ X ++ (Y ++ Z)
Push-assoc {m} {n} {o} X Y Z i = begin
    merge ((X ++ Y) ++ Z) (preimage (+-assocˡ {m}) ⁅ i ⁆)         ≡⟨ merge-preimage-ρ ↔-mno ((X ++ Y) ++ Z) ⁅ i ⁆ ⟩
    merge (((X ++ Y) ++ Z) ∘ (+-assocʳ {m})) (⁅ i ⁆)              ≡⟨⟩
    merge (((X ++ Y) ++ Z) ∘ (+-assocʳ {m})) (preimage id ⁅ i ⁆)  ≡⟨ merge-cong₁ (++-assoc X Y Z) (preimage id ⁅ i ⁆) ⟩
    merge (X ++ (Y ++ Z)) (preimage id ⁅ i ⁆)                     ≡⟨ Push-identity i ⟩
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
    open ≡-Reasoning

preimage-++′
    : {n m o : ℕ}
      (f : Vector (Fin o) n)
      (g : Vector (Fin o) m)
      (S : Subset o)
    → preimage (f ++ g) S ≗ preimage f S ++ preimage g S
preimage-++′ {n} f g S = [,]-∘ S ∘ splitAt n

Push-unitaryʳ
    : {n : ℕ}
      (X : ∣ Values n ∣)
      (i : Fin n)
    → merge (X ++ []) (preimage (id ++ (λ ())) ⁅ i ⁆) ≡ X i
Push-unitaryʳ {n} X i = begin
    merge (X ++ []) (preimage (id ++ (λ ())) ⁅ i ⁆)               ≡⟨ merge-cong₂ (X ++ []) (preimage-++′ id (λ ()) ⁅ i ⁆) ⟩
    merge (X ++ []) (preimage id ⁅ i ⁆ ++ preimage (λ ()) ⁅ i ⁆)  ≡⟨⟩
    merge (X ++ []) (⁅ i ⁆ ++ preimage (λ ()) ⁅ i ⁆)              ≡⟨ merge-++ X [] ⁅ i ⁆ (preimage (λ ()) ⁅ i ⁆) ⟩
    join (merge X ⁅ i ⁆) (merge [] (preimage (λ ()) ⁅ i ⁆))       ≡⟨ ≡.cong (join (merge X ⁅ i ⁆)) (merge-[] [] (preimage (λ ()) ⁅ i ⁆)) ⟩
    join (merge X ⁅ i ⁆) U                                        ≡⟨ join-comm (merge X ⁅ i ⁆) U ⟩
    merge X ⁅ i ⁆                                                 ≡⟨ merge-⁅⁆ X i ⟩
    X i ∎
  where
    open ≡-Reasoning
    t : Fin (n + 0) → Fin n
    t = id ++ (λ ())

Push-swap
    : {n m : ℕ}
      (X : ∣ Values n ∣)
      (Y : ∣ Values m ∣)
    → merge (X ++ Y) ∘ preimage (+-swap {m}) ∘ ⁅_⁆ ≗ Y ++ X
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
        ; associativity = λ { {m} {n} {o} {(X , Y) , Z} i → Push-assoc X Y Z i }
        ; unitaryˡ = λ { {n} {_ , X} i → merge-⁅⁆ X i }
        ; unitaryʳ = λ { {n} {X , _} i → Push-unitaryʳ X i }
        }
    ; braiding-compat = λ { {n} {m} {X , Y} i → Push-swap X Y i }
    }
