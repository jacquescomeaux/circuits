{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Semiring)
open import Level using (Level; 0ℓ; _⊔_)

module Data.Mat.Category {c ℓ : Level} (Rig : Semiring c ℓ) where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Data.Vec.Relation.Binary.Equality.Setoid as PW

open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; zipWith; foldr; foldr′; map; replicate)
open import Data.Mat.Util
  using
    ( foldr-cong ; zipWith-cong ; transpose ; transpose-involutive ; map-replicate
    ; zipWith-map ; map-zipWith ; zipWith-map-map ; transpose-zipWith ; transpose-cong
    )
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)
open import Data.Vec.Properties using (map-id; map-∘; map-cong; zipWith-replicate₁)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_; _≡_; module ≡-Reasoning)
open import Function using (_∘_; id)

open Vec
open ℕ

open Semiring Rig renaming (Carrier to R)
module V = PW setoid

private
  variable
    n m o p : ℕ

opaque
  -- Vectors over the rig
  Vector : ℕ → Set c
  Vector = Vec R

opaque
  -- N by M matrices over the rig
  Matrix : Rel ℕ c
  Matrix n m = Vec (Vector n) m

opaque

  unfolding Vector

  -- Pointwise equality of vectors
  _≊_ : Rel (Vector n) (c ⊔ ℓ)
  _≊_ {n} A B = A V.≋ B

  ≊-setoid : ℕ → Setoid c (c ⊔ ℓ)
  ≊-setoid n = record
      { Carrier = Vector n
      ; _≈_ = _≊_ {n}
      ; isEquivalence = record
          { refl = V.≋-refl
          ; sym = V.≋-sym
          ; trans = V.≋-trans
          }
    }

module ≊ {n} = Setoid (≊-setoid n)

infix 4 _≊_

module M {n} = PW (≊-setoid n)

opaque

  unfolding Matrix ≊-setoid

  -- Pointwise equality of matrices
  _≋_ : Rel (Matrix n m) (c ⊔ ℓ)
  _≋_ {n} {m} A B = A M.≋ B

  ≋-setoid : ℕ → ℕ → Setoid c (c ⊔ ℓ)
  ≋-setoid n m = record
      { Carrier = Matrix n m
      ; _≈_ = _≋_ {n} {m}
      ; isEquivalence = record
          { refl = M.≋-refl
          ; sym = M.≋-sym
          ; trans = M.≋-trans
          }
    }

  ≋-isEquivalence : IsEquivalence (_≋_ {n} {m})
  ≋-isEquivalence {n} {m} = Setoid.isEquivalence (≋-setoid n m)

module ≋ {n} {m} = Setoid (≋-setoid n m)

infix 4 _≋_

opaque
  unfolding Vector
  -- Sum the elements of a vector
  sum : Vector n → R
  sum = foldr′ _+_ 0#

opaque
  unfolding sum _≊_
  sum-cong : {x y : Vector n} → x ≊ y → sum x ≈ sum y
  sum-cong = foldr-cong {A = setoid} (λ _ → setoid) +-cong refl

opaque
  unfolding sum
  -- Dot product of two vectors
  _∙_ : Vector n → Vector n → R
  _∙_ v w = sum (zipWith _*_ v w)

infix 8 _∙_

opaque
  unfolding Vector
  -- Pointwise sum of two vectors
  _⊕_ : Vector n → Vector n → Vector n
  _⊕_ = zipWith _+_

infixl 6 _⊕_

opaque
  unfolding Vector
  -- Scaling a vector
  _⟨_⟩ : R → Vector n → Vector n
  _⟨_⟩ r = map (r *_)

infix 9 _⟨_⟩

opaque
  unfolding _∙_ _≊_
  ∙-cong : {v₁ v₂ w₁ w₂ : Vector n} → v₁ ≊ v₂ → w₁ ≊ w₂ → v₁ ∙ w₁ ≈ v₂ ∙ w₂
  ∙-cong {n} ≋v ≋w = sum-cong (zipWith-cong *-cong ≋v ≋w)

opaque
  unfolding Vector
  -- The zero vector
  zeros : Vector n
  zeros {n} = replicate n 0#

opaque
  unfolding Matrix Vector
  -- The identity matrix
  I : Matrix n n
  I {zero} = []
  I {suc n} = (1# ∷ zeros) ∷ map (0# ∷_) I

opaque
  unfolding Matrix Vector
  _[_] : Matrix n m → Vector n → Vector m
  _[_] M V = map (_∙ V) M

opaque
  unfolding Matrix Vector
  [_]_ : Vector m → Matrix n m → Vector n
  [_]_ V M = map (V ∙_) (transpose M)

opaque
  unfolding Matrix
  mapRows : (Vector n → Vector m) → Matrix n p → Matrix m p
  mapRows = map

opaque
  unfolding Matrix Vector
  _ᵀ : Matrix n m → Matrix m n
  _ᵀ = transpose

infix 10 _ᵀ

opaque
  unfolding _ᵀ
  _ᵀᵀ : (M : Matrix n m) → M ᵀ ᵀ ≡ M
  _ᵀᵀ M = transpose-involutive M

infix 10 _ᵀᵀ

opaque
  unfolding mapRows _ᵀ _[_] [_]_
  -[-]ᵀ : (A : Matrix m o) (B : Matrix n m) → mapRows (A [_]) (B ᵀ) ≡ (mapRows ([_] B) A) ᵀ
  -[-]ᵀ [] B = map-replicate [] (transpose B)
  -[-]ᵀ (A₀ ∷ A) B = begin
      map (λ V → A₀ ∙ V ∷ map (_∙ V) A) (B ᵀ)             ≡⟨ zipWith-map (A₀ ∙_) (A [_]) _∷_ (B ᵀ) ⟨
      zipWith _∷_ ([ A₀ ] B) (map (A [_]) (B ᵀ))          ≡⟨ ≡.cong (zipWith _∷_ ([ A₀ ] B)) (-[-]ᵀ A B) ⟩
      zipWith _∷_ ([ A₀ ] B) (transpose (map ([_] B) A))  ∎
    where
      open ≡-Reasoning

-- matrix multiplication
_·_ : {n m o : ℕ} → Matrix m o → Matrix n m → Matrix n o
_·_ A B = mapRows ([_] B) A

-- alternative form
_·′_ : Matrix m o → Matrix n m → Matrix n o
_·′_ A B = (mapRows (A [_]) (B ᵀ)) ᵀ

infixr 9 _·_ _·′_

·-·′ : (A : Matrix m o) (B : Matrix n m) → A · B ≡ A ·′ B
·-·′ A B = begin
    mapRows ([_] B) A       ≡⟨ mapRows ([_] B) A ᵀᵀ ⟨
    mapRows ([_] B) A ᵀ ᵀ   ≡⟨ ≡.cong (_ᵀ) (-[-]ᵀ A B) ⟨
    mapRows (A [_]) (B ᵀ) ᵀ ∎
  where
    open ≡-Reasoning

opaque
  unfolding _∙_ zeros

  ∙-zerosˡ : (V : Vector n) → zeros ∙ V ≈ 0#
  ∙-zerosˡ [] = refl
  ∙-zerosˡ (x ∷ V) = begin
      0# * x + zeros ∙ V  ≈⟨ +-congʳ (zeroˡ x) ⟩
      0# + zeros ∙ V      ≈⟨ +-identityˡ (zeros ∙ V) ⟩
      zeros ∙ V           ≈⟨ ∙-zerosˡ V ⟩
      0#                  ∎
    where
      open ≈-Reasoning setoid

  ∙-zerosʳ : (V : Vector n) → V ∙ zeros ≈ 0#
  ∙-zerosʳ [] = refl
  ∙-zerosʳ (x ∷ V) = begin
      x * 0# + V ∙ zeros  ≈⟨ +-congʳ (zeroʳ x) ⟩
      0# + V ∙ zeros      ≈⟨ +-identityˡ (V ∙ zeros) ⟩
      V ∙ zeros           ≈⟨ ∙-zerosʳ V ⟩
      0#                  ∎
    where
      open ≈-Reasoning setoid

opaque
  unfolding _∙_ _⊕_
  ∙-distribʳ : (A B C : Vector n) → (A ⊕ B) ∙ C ≈ A ∙ C + B ∙ C
  ∙-distribʳ [] [] [] = sym (+-identityˡ 0#)
  ∙-distribʳ (a ∷ A) (b ∷ B) (c ∷ C) = begin
      (a + b) * c + (zipWith _+_ A B ∙ C) ≈⟨ +-congˡ (∙-distribʳ A B C) ⟩
      (a + b) * c + (A ∙ C + B ∙ C)       ≈⟨ +-congʳ (distribʳ c a b) ⟩
      a * c + b * c + (A ∙ C + B ∙ C)     ≈⟨ +-assoc _ _ _ ⟩
      a * c + (b * c + (A ∙ C + B ∙ C))   ≈⟨ +-congˡ (+-assoc _ _ _) ⟨
      a * c + (b * c + A ∙ C + B ∙ C)     ≈⟨ +-congˡ (+-congʳ (+-comm _ _)) ⟩
      a * c + (A ∙ C + b * c + B ∙ C)     ≈⟨ +-congˡ (+-assoc _ _ _) ⟩
      a * c + (A ∙ C + (b * c + B ∙ C))   ≈⟨ +-assoc _ _ _ ⟨
      a * c + A ∙ C + (b * c + B ∙ C)     ∎
    where
      open ≈-Reasoning setoid

opaque
  unfolding _⟨_⟩ _∙_
  *-∙ˡ : (r : R) (A B : Vector n) → r * A ∙ B ≈ r ⟨ A ⟩ ∙ B
  *-∙ˡ r [] [] = zeroʳ r
  *-∙ˡ r (a ∷ A) (b ∷ B) = begin
      r * (a * b + A ∙ B)           ≈⟨ distribˡ r (a * b) (A ∙ B) ⟩
      r * (a * b) + r * A ∙ B       ≈⟨ +-congʳ (*-assoc r a b) ⟨
      r * a * b + r * A ∙ B         ≈⟨ +-congˡ (*-∙ˡ r A B )⟩
      r * a * b + map (r *_) A ∙ B  ∎
    where
      open ≈-Reasoning setoid

module _  where

  open ≈-Reasoning setoid

  opaque
    unfolding [_]_ _[_] zeros _∙_ _≋_ _ᵀ _⊕_ _⟨_⟩

    []-∙ : (V : Vector m) (M : Matrix n m) (W : Vector n) → [ V ] M ∙ W ≈ V ∙ M [ W ]
    []-∙ {n = n} [] M@[] W = begin
        map (zeros ∙_) (M ᵀ) ∙ W  ≈⟨ ∙-cong (PW.map⁺ (λ {x} _ → ∙-zerosˡ x) {xs = M ᵀ} ≋.refl) ≊.refl ⟩
        map (λ _ → 0#) (M ᵀ) ∙ W  ≡⟨ ≡.cong (_∙ W) (map-replicate 0# (M ᵀ)) ⟩
        zeros ∙ W                 ≈⟨ ∙-zerosˡ W ⟩
        0#                        ∎
    []-∙ (V₀ ∷ V) (M₀ ∷ M) W = begin
        [ V₀ ∷ V ] (M₀ ∷ M) ∙ W                         ≡⟨ ≡.cong (_∙ W) (map-zipWith ((V₀ ∷ V) ∙_) _∷_ M₀ (M ᵀ)) ⟩
        (zipWith (λ x y → V₀ * x + V ∙ y) M₀ (M ᵀ)) ∙ W ≡⟨ ≡.cong (_∙ W) (zipWith-map-map (V₀ *_) (V ∙_) _+_ M₀ (M ᵀ)) ⟩
        (V₀ ⟨ M₀ ⟩ ⊕ [ V ] M) ∙ W                       ≈⟨ ∙-distribʳ (map (V₀ *_) M₀) ([ V ] M) W ⟩
        V₀ ⟨ M₀ ⟩ ∙ W + [ V ] M ∙ W                     ≈⟨ +-congʳ (*-∙ˡ V₀ M₀ W) ⟨
        V₀ * (M₀ ∙ W) + ([ V ] M) ∙ W                   ≈⟨ +-congˡ ([]-∙ V M W) ⟩
        (V₀ ∷ V) ∙ (M₀ ∷ M) [ W ] ∎

opaque
  unfolding _≊_ _[_]
  -[-]-cong : {x y : Vector n} (A : Matrix n m) → x ≊ y → A [ x ] ≊ A [ y ]
  -[-]-cong {x = x} {y} A ≋V = PW.map⁺ (λ ≋w → ∙-cong ≋w ≋V) {xs = A} M.≋-refl

opaque
  unfolding _≊_ [_]_ _ᵀ _≋_
  [-]--cong : {x y : Vector m} {A B : Matrix n m} → x ≊ y → A ≋ B → [ x ] A ≊ [ y ] B
  [-]--cong {x = x} {y} ≋V A≋B = PW.map⁺ (λ ≋w → ∙-cong ≋V ≋w) (transpose-cong setoid A≋B)

opaque
  unfolding mapRows _[_] _≊_
  ·-[] : {A B C : ℕ} (M : Matrix A B) (N : Matrix B C) (V : Vector A) → (N · M) [ V ] ≊ N [ M [ V ] ]
  ·-[] {A} {B} {zero} M [] V = PW.[]
  ·-[] {A} {B} {suc C} M (N₀ ∷ N) V = []-∙ N₀ M V PW.∷ ·-[] M N V

opaque
  unfolding [_]_ _ᵀ mapRows _≋_
  []-· : {A B C : ℕ} (V : Vector C) (M : Matrix A B) (N : Matrix B C) → [ V ] (N · M) ≊ [ [ V ] N ] M
  []-· {A} {B} {C} V M N = begin
      [ V ] (map ([_] M) N)           ≡⟨ ≡.cong (map (V ∙_)) (-[-]ᵀ N M) ⟨
      map (V ∙_) (map (N [_]) (M ᵀ))  ≡⟨ map-∘ (V ∙_) (N [_]) (M ᵀ) ⟨
      map ((V ∙_) ∘ (N [_])) (M ᵀ)    ≈⟨ PW.map⁺ (λ {W} ≋W → trans ([]-∙ V N W) (∙-cong ≊.refl (-[-]-cong N ≋W))) {xs = M ᵀ} ≋.refl ⟨
      map ([ V ] N ∙_) (M ᵀ)          ∎
    where
      open ≈-Reasoning (≊-setoid A)

opaque
  unfolding mapRows _≋_ _ᵀ
  ·-assoc : {A B C D : ℕ} {f : Matrix A B} {g : Matrix B C} {h : Matrix C D} → (h · g) · f ≋ h · g · f
  ·-assoc {A} {B} {C} {D} {f} {g} {h} = begin
      map ([_] f) (map ([_] g) h)   ≡⟨ map-∘ ([_] f) ([_] g) h ⟨
      map (λ v → [ [ v ] g ] f) h   ≈⟨ PW.map⁺ (λ {x} x≊y → ≊.trans ([]-· x f g) ([-]--cong ([-]--cong x≊y ≋.refl) ≋.refl)) {xs = h} M.≋-refl ⟨
      map (λ v → [ v ] (g · f)) h  ∎
    where
      open ≈-Reasoning (≋-setoid A D)

opaque
  unfolding _≋_ _ᵀ _≊_ ≊-setoid I zeros
  transpose-I : I ᵀ ≡ I {n}
  transpose-I {zero} = ≡.refl
  transpose-I {suc n} = begin
      zipWith _∷_ (1# ∷ zeros) ((map (0# ∷_) I) ᵀ)        ≡⟨ ≡.cong (zipWith _∷_ (1# ∷ zeros) ∘ (_ᵀ)) (zipWith-replicate₁ _∷_ 0# I) ⟨
      zipWith _∷_ (1# ∷ zeros) ((zipWith _∷_ zeros I) ᵀ)  ≡⟨ ≡.cong (zipWith _∷_ (1# ∷ zeros)) (transpose-zipWith zeros I) ⟩
      (1# ∷ zeros) ∷ zipWith _∷_ zeros (I ᵀ)              ≡⟨ ≡.cong ((1# ∷ zeros) ∷_) (zipWith-replicate₁ _∷_ 0# (I ᵀ)) ⟩
      (1# ∷ zeros) ∷ map (0# ∷_) (I ᵀ)                    ≡⟨ ≡.cong (((1# ∷ zeros) ∷_) ∘ map (0# ∷_)) (transpose-I) ⟩
      (1# ∷ zeros) ∷ map (0# ∷_) I ∎
    where
      open ≡-Reasoning

opaque
  unfolding Vector [_]_ I ≊-setoid _∙_ zeros ≋-setoid mapRows _ᵀ
  [-]I : {n : ℕ} (V : Vector n) → [ V ] I ≊ V
  [-]I {zero} [] = ≊.refl
  [-]I {suc n} (x ∷ V) = begin
      map ((x ∷ V) ∙_) (zipWith _∷_ (1# ∷ zeros) (map (0# ∷_ ) I ᵀ))      ≡⟨ ≡.cong (map ((x ∷ V) ∙_) ∘ zipWith _∷_ (1# ∷ zeros) ∘ _ᵀ) (zipWith-replicate₁ _∷_ 0# I) ⟨
      map ((x ∷ V) ∙_) (zipWith _∷_ (1# ∷ zeros) (zipWith _∷_ zeros I ᵀ)) ≡⟨ ≡.cong (map ((x ∷ V) ∙_) ∘ zipWith _∷_ (1# ∷ zeros)) (transpose-zipWith zeros I) ⟩
      map ((x ∷ V) ∙_) (zipWith _∷_ (1# ∷ zeros) (zeros ∷ I ᵀ))           ≡⟨ ≡.cong (map ((x ∷ V) ∙_) ∘ zipWith _∷_ (1# ∷ zeros) ∘ (zeros ∷_)) transpose-I ⟩
      map ((x ∷ V) ∙_) (zipWith _∷_ (1# ∷ zeros) (zeros ∷ I))             ≡⟨⟩
      map ((x ∷ V) ∙_) ((1# ∷ zeros) ∷ zipWith _∷_ zeros I)               ≡⟨ ≡.cong (map ((x ∷ V) ∙_) ∘ ((1# ∷ zeros) ∷_)) (zipWith-replicate₁ _∷_ 0# I) ⟩
      map ((x ∷ V) ∙_) ((1# ∷ zeros) ∷ map (0# ∷_) I)                     ≡⟨⟩
      (x ∷ V) ∙ (1# ∷ zeros) ∷ map ((x ∷ V) ∙_) ((map (0# ∷_) I))         ≡⟨⟩
      x * 1# + V ∙ zeros ∷ map ((x ∷ V) ∙_) (map (0# ∷_) I)               ≈⟨ +-congʳ (*-identityʳ x) PW.∷ ≊.refl ⟩
      x + V ∙ zeros ∷ map ((x ∷ V) ∙_) (map (0# ∷_) I)                    ≈⟨ +-congˡ (∙-zerosʳ V) PW.∷ ≊.refl ⟩
      x + 0# ∷ map ((x ∷ V) ∙_) (map (0# ∷_) I)                           ≈⟨ +-identityʳ x PW.∷ ≊.refl ⟩
      x ∷ map ((x ∷ V) ∙_) (map (0# ∷_) I)                                ≡⟨ ≡.cong (x ∷_) (map-∘ ((x ∷ V) ∙_) (0# ∷_) I) ⟨
      x ∷ map (λ u → (x ∷ V) ∙ (0# ∷ u)) I                                ≡⟨⟩
      x ∷ map (λ u → x * 0# + V ∙ u) I                                    ≈⟨ refl PW.∷ PW.map⁺ (λ ≋V → trans (+-congʳ (zeroʳ x)) (+-congˡ (∙-cong {v₁ = V} ≊.refl ≋V))) {xs = I} ≋.refl ⟩
      x ∷ map (λ u → 0# + V ∙ u) I                                        ≈⟨ refl PW.∷ PW.map⁺ (λ {z} ≋V → trans (+-identityˡ (V ∙ z)) (∙-cong {v₁ = V} ≊.refl ≋V)) {xs = I} ≋.refl ⟩
      x ∷ map (V ∙_) I                                                    ≡⟨ ≡.cong (λ y → x ∷ map (V ∙_) y) transpose-I ⟨
      x ∷ map (V ∙_) (I ᵀ)                                                ≈⟨ refl PW.∷ ([-]I V) ⟩
      x ∷ V                                                               ∎
    where
      open ≈-Reasoning (≊-setoid (suc n))

opaque
  unfolding Vector _≊_ I _[_] _∙_ _≋_
  transform-with-I : {n : ℕ} (V : Vector n) → I [ V ] ≊ V
  transform-with-I {zero} [] = PW.[]
  transform-with-I {suc n} (x ∷ V) = hd PW.∷ tl
    where
      hd : (1# ∷ zeros) ∙ (x ∷ V) ≈ x
      hd = begin
          1# * x + zeros ∙ V  ≈⟨ +-congʳ (*-identityˡ x) ⟩
          x + zeros ∙ V       ≈⟨ +-congˡ (∙-zerosˡ V) ⟩
          x + 0#              ≈⟨ +-identityʳ x ⟩
          x                   ∎
        where
          open ≈-Reasoning setoid
      tl : map (_∙ (x ∷ V)) (map (0# ∷_ ) I) ≊ V
      tl = begin
          map (_∙ (x ∷ V)) (map (0# ∷_) I)  ≡⟨ map-∘ (_∙ (x ∷ V)) (0# ∷_) I ⟨
          map (λ t → 0# * x + t ∙ V) I      ≈⟨ PW.map⁺ (λ ≋X → trans (+-congʳ (zeroˡ x)) (+-congˡ (∙-cong ≋X ≊.refl))) {xs = I} ≋.refl ⟩
          map (λ t → 0# + t ∙ V) I          ≈⟨ PW.map⁺ (λ {t} ≋X → trans (+-identityˡ (t ∙ V)) (∙-cong ≋X ≊.refl)) {xs = I} ≋.refl ⟩
          map (_∙ V) I                      ≈⟨ transform-with-I V ⟩
          V ∎
        where
          open ≈-Reasoning (≊-setoid n)

opaque
  unfolding mapRows _[_] _ᵀ _≋_ _≊_ [_]_
  map--[-]-I : (M : Matrix n m) → mapRows (M [_]) I ≋ M ᵀ
  map--[-]-I {n} {m} [] = ≋.reflexive (map-replicate [] I)
  map--[-]-I {n} {suc m} (M₀ ∷ M) = begin
      map ((M₀ ∷ M) [_]) I                        ≡⟨⟩
      map (λ V → M₀ ∙ V ∷ M [ V ]) I              ≡⟨ zipWith-map (M₀ ∙_) (M [_]) _∷_ I ⟨
      zipWith _∷_ (map (M₀ ∙_) I) (map (M [_]) I) ≈⟨ zipWith-cong PW._∷_ (≊.reflexive (≡.sym (≡.cong (map (M₀ ∙_)) (transpose-I)))) (map--[-]-I M) ⟩
      zipWith _∷_ ([ M₀ ] I) (M ᵀ)                ≈⟨ zipWith-cong PW._∷_ ([-]I M₀) ≋.refl ⟩
      zipWith _∷_ M₀ (M ᵀ)                        ∎
    where
      open ≈-Reasoning (≋-setoid (suc m) n)

opaque
  unfolding mapRows ≋-setoid _ᵀ
  ·-identityˡ : {f : Matrix n m} → I · f ≋ f
  ·-identityˡ {A} {B} {f} = begin
      I · f               ≡⟨ ·-·′ I f ⟩
      map (I [_]) (f ᵀ) ᵀ ≈⟨ transpose-cong setoid (PW.map⁺ (λ {x} ≊V → ≊.trans (transform-with-I x) ≊V) {xs = f ᵀ} ≋.refl) ⟩
      map id (f ᵀ) ᵀ      ≡⟨ ≡.cong (_ᵀ) (map-id (f ᵀ)) ⟩
      f ᵀ ᵀ               ≡⟨ f ᵀᵀ ⟩
      f                   ∎
    where
      open ≈-Reasoning (≋-setoid A B)

opaque
  unfolding _≋_ mapRows ≊-setoid ≋-setoid _≊_ _ᵀ
  ·-identityʳ : {f : Matrix n m} → f · I ≋ f
  ·-identityʳ {A} {B} {f} = begin
      f · I               ≡⟨ ·-·′ f I ⟩
      map (f [_]) (I ᵀ) ᵀ ≈⟨ transpose-cong setoid (≋.reflexive (≡.cong (map (f [_])) transpose-I)) ⟩
      map (f [_]) I ᵀ     ≈⟨ transpose-cong setoid (map--[-]-I f) ⟩
      f ᵀ ᵀ               ≡⟨ f ᵀᵀ ⟩
      f ∎
    where
      open ≈-Reasoning (≋-setoid A B)

opaque
  unfolding _ᵀ _≋_ mapRows
  ·-resp-≋ : {X X′ : Matrix n p} {Y Y′ : Matrix m n} → X ≋ X′ → Y ≋ Y′ → X · Y ≋ X′ · Y′
  ·-resp-≋ ≋X ≋Y = PW.map⁺ (λ {_} {y} ≋V → [-]--cong ≋V ≋Y) ≋X

-- The category of matrices over a rig
Mat : Category 0ℓ c (c ⊔ ℓ)
Mat = categoryHelper record
    { Obj = ℕ
    ; _⇒_ = Matrix
    ; _≈_ = _≋_
    ; id = I
    ; _∘_ = _·_
    ; assoc = λ {A B C D f g h} → ·-assoc {f = f} {g} {h}
    ; identityˡ = ·-identityˡ
    ; identityʳ = ·-identityʳ
    ; equiv = ≋-isEquivalence
    ; ∘-resp-≈ = ·-resp-≋
    }
