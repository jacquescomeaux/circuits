{-# OPTIONS --without-K --safe #-}

module Data.Circuit.Gate where

open import Level using (0ℓ)
open import Data.Castable using (Castable)
open import Data.Hypergraph.Base using (HypergraphLabel; module Edge; module HypergraphList)
open import Data.String using (String)
open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; isEquivalence; cong)
import Relation.Binary.PropositionalEquality as ≡

import Data.Nat as Nat
import Data.Fin as Fin

data Gate : ℕ → Set where
    ZERO  : Gate 1
    ONE   : Gate 1
    ID    : Gate 2
    NOT   : Gate 2
    AND   : Gate 3
    OR    : Gate 3
    XOR   : Gate 3
    NAND  : Gate 3
    NOR   : Gate 3
    XNOR  : Gate 3

cast-gate : {e e′ : ℕ} → .(e ≡ e′) → Gate e → Gate e′
cast-gate {1} {1} eq g = g
cast-gate {2} {2} eq g = g
cast-gate {3} {3} eq g = g

cast-gate-trans
    : {m n o : ℕ}
    → .(eq₁ : m ≡ n)
      .(eq₂ : n ≡ o)
      (g : Gate m)
    → cast-gate eq₂ (cast-gate eq₁ g) ≡ cast-gate (trans eq₁ eq₂) g
cast-gate-trans {1} {1} {1} eq₁ eq₂ g = refl
cast-gate-trans {2} {2} {2} eq₁ eq₂ g = refl
cast-gate-trans {3} {3} {3} eq₁ eq₂ g = refl

cast-gate-is-id : {m : ℕ} .(eq : m ≡ m) (g : Gate m) → cast-gate eq g ≡ g
cast-gate-is-id {1} eq g = refl
cast-gate-is-id {2} eq g = refl
cast-gate-is-id {3} eq g = refl

subst-is-cast-gate : {m n : ℕ} (eq : m ≡ n) (g : Gate m) → subst Gate eq g ≡ cast-gate eq g
subst-is-cast-gate refl g = sym (cast-gate-is-id refl g)

GateCastable : Castable
GateCastable = record
    { B = Gate
    ; isCastable = record
        { cast = cast-gate
        ; cast-trans = cast-gate-trans
        ; cast-is-id = cast-gate-is-id
        ; subst-is-cast = subst-is-cast-gate
        }
    }

showGate : (n : ℕ) → Gate n → String
showGate _ ZERO = "ZERO"
showGate _ ONE  = "ONE"
showGate _ ID   = "ID"
showGate _ NOT  = "NOT"
showGate _ AND  = "AND"
showGate _ OR   = "OR"
showGate _ XOR  = "XOR"
showGate _ NAND = "NAND"
showGate _ NOR  = "NOR"
showGate _ XNOR = "XNOR"

toℕ : (n : ℕ) → Gate n → ℕ
toℕ 1 ZERO = 0
toℕ 1 ONE = 1
toℕ 2 ID = 0
toℕ 2 NOT = 1
toℕ 3 AND = 0
toℕ 3 OR = 1
toℕ 3 XOR = 2
toℕ 3 NAND = 3
toℕ 3 NOR = 4
toℕ 3 XNOR = 5

toℕ-injective : {n : ℕ} {x y : Gate n} → toℕ n x ≡ toℕ n y → x ≡ y
toℕ-injective {1} {ZERO} {ZERO} refl = refl
toℕ-injective {1} {ONE} {ONE} refl = refl
toℕ-injective {2} {ID} {ID} refl = refl
toℕ-injective {2} {NOT} {NOT} refl = refl
toℕ-injective {3} {AND} {AND} refl = refl
toℕ-injective {3} {OR} {OR} refl = refl
toℕ-injective {3} {XOR} {XOR} refl = refl
toℕ-injective {3} {NAND} {NAND} refl = refl
toℕ-injective {3} {NOR} {NOR} refl = refl
toℕ-injective {3} {XNOR} {XNOR} refl = refl

open import Relation.Binary using (Rel; Decidable; DecidableEquality)
import Relation.Nullary.Decidable as Dec

_[_≤_] : (n : ℕ) → Rel (Gate n) 0ℓ
_[_≤_] n x y = toℕ n x ≤ toℕ n y

_≟_ : {n : ℕ} → DecidableEquality (Gate n)
_≟_ {n} x y = Dec.map′ toℕ-injective (cong (toℕ n)) (toℕ n x Nat.≟ toℕ n y)

_≤?_ : {n : ℕ} → Decidable (n [_≤_])
_≤?_ {n} x y = toℕ n x Nat.≤? toℕ n y

GateLabel : HypergraphLabel
GateLabel = record
    { Label = Gate
    ; showLabel = showGate
    ; isCastable = record
        { cast = cast-gate
        ; cast-trans = cast-gate-trans
        ; cast-is-id = cast-gate-is-id
        ; subst-is-cast = subst-is-cast-gate
        }
    ; _[_≤_] = λ n x y → toℕ n x ≤ toℕ n y
    ; isDecTotalOrder = λ n → record
        { isTotalOrder = record
          { isPartialOrder = record
              { isPreorder = record
                  { isEquivalence = isEquivalence
                  ; reflexive = λ { refl → ≤-refl }
                  ; trans = ≤-trans
                  }
              ; antisym = λ i≤j j≤i → toℕ-injective (≤-antisym i≤j j≤i)
              }
          ; total = λ { x y → ≤-total (toℕ n x) (toℕ n y) }
          }
        ; _≟_ = _≟_
        ; _≤?_ = _≤?_
        }
    }
