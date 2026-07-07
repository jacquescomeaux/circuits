{-# OPTIONS --without-K --safe #-}

module Data.Circuit.Value where

import Relation.Binary.Lattice.Properties.BoundedJoinSemilattice as LatticeProp

open import Algebra.Bundles using (CommutativeMonoid; Semiring)
open import Algebra.Lattice.Bundles using (Semilattice)
open import Algebra.Structures using (IsCommutativeMonoid; IsMonoid; IsSemigroup; IsMagma)
open import Data.Product.Base using (_×_; _,_)
open import Data.String.Base using (String)
open import Lattice.Bundle.BoundedDistributive using (BoundedDistributiveLattice)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

data Value : Set where
  U T F X : Value

data ≤-Value : Value → Value → Set where
    v≤v : {v : Value} → ≤-Value v v
    U≤T : ≤-Value U T
    U≤F : ≤-Value U F
    U≤X : ≤-Value U X
    T≤X : ≤-Value T X
    F≤X : ≤-Value F X

≤-reflexive : {x y : Value} → x ≡ y → ≤-Value x y
≤-reflexive ≡.refl = v≤v

≤-transitive : {i j k : Value} → ≤-Value i j → ≤-Value j k → ≤-Value i k
≤-transitive v≤v y = y
≤-transitive x v≤v = x
≤-transitive U≤T T≤X = U≤X
≤-transitive U≤F F≤X = U≤X

≤-antisymmetric : {i j : Value} → ≤-Value i j → ≤-Value j i → i ≡ j
≤-antisymmetric v≤v _ = ≡.refl

showValue : Value → String
showValue U = "U"
showValue T = "T"
showValue F = "F"
showValue X = "X"

join : Value → Value → Value
join U y = y
join T U = T
join T T = T
join T F = X
join T X = X
join F U = F
join F T = X
join F F = F
join F X = X
join X _ = X

meet : Value → Value → Value
meet U _ = U
meet T U = U
meet T T = T
meet T F = U
meet T X = T
meet F U = U
meet F T = U
meet F F = F
meet F X = F
meet X y = y

implies : Value → Value → Value
implies U _ = X
implies T U = U
implies T T = X
implies T F = F
implies T X = X
implies F U = U
implies F T = T
implies F F = X
implies F X = X
implies X U = U
implies X T = T
implies X F = F
implies X X = X

≤-infimum
    : (x y : Value)
    → ≤-Value (meet x y) x
    × ≤-Value (meet x y) y
    × ((z : Value) → ≤-Value z x → ≤-Value z y → ≤-Value z (meet x y))
≤-infimum U U = v≤v , v≤v , λ _ z≤x _ → z≤x
≤-infimum U T = v≤v , U≤T , λ _ z≤x _ → z≤x
≤-infimum U F = v≤v , U≤F , λ _ z≤x _ → z≤x
≤-infimum U X = v≤v , U≤X , λ _ z≤x _ → z≤x
≤-infimum T U = U≤T , v≤v , λ _ _ z≤y → z≤y
≤-infimum T T = v≤v , v≤v , λ _ z≤x _ → z≤x
≤-infimum T F = U≤T , U≤F , λ { U _ _ → v≤v }
≤-infimum T X = v≤v , T≤X , λ _ z≤x _ → z≤x
≤-infimum F U = U≤F , v≤v , λ _ _ z≤y → z≤y
≤-infimum F T = U≤F , U≤T , λ { U _ _ → v≤v }
≤-infimum F F = v≤v , v≤v , λ _ z≤x _ → z≤x
≤-infimum F X = v≤v , F≤X , λ _ z≤x _ → z≤x
≤-infimum X U = U≤X , v≤v , λ _ _ z≤y → z≤y
≤-infimum X T = T≤X , v≤v , λ _ _ z≤y → z≤y
≤-infimum X F = F≤X , v≤v , λ _ _ z≤y → z≤y
≤-infimum X X = v≤v , v≤v , λ _ z≤x _ → z≤x

≤-supremum
    : (x y : Value)
    → ≤-Value x (join x y)
    × ≤-Value y (join x y)
    × ((z : Value) → ≤-Value x z → ≤-Value y z → ≤-Value (join x y) z)
≤-supremum U U = v≤v , v≤v , λ _ x≤z _ → x≤z
≤-supremum U T = U≤T , v≤v , λ _ _ y≤z → y≤z
≤-supremum U F = U≤F , v≤v , λ _ _ y≤z → y≤z
≤-supremum U X = U≤X , v≤v , λ _ _ y≤z → y≤z
≤-supremum T U = v≤v , U≤T , λ _ x≤z _ → x≤z
≤-supremum T T = v≤v , v≤v , λ _ x≤z _ → x≤z
≤-supremum T F = T≤X , F≤X , λ { X _ _ → v≤v }
≤-supremum T X = T≤X , v≤v , λ _ _ y≤z → y≤z
≤-supremum F U = v≤v , U≤F , λ _ x≤z _ → x≤z
≤-supremum F T = F≤X , T≤X , λ { X _ _ → v≤v }
≤-supremum F F = v≤v , v≤v , λ _ x≤z _ → x≤z
≤-supremum F X = F≤X , v≤v , λ _ _ y≤z → y≤z
≤-supremum X U = v≤v , U≤X , λ _ x≤z _ → x≤z
≤-supremum X T = v≤v , T≤X , λ _ x≤z _ → x≤z
≤-supremum X F = v≤v , F≤X , λ _ x≤z _ → x≤z
≤-supremum X X = v≤v , v≤v , λ _ x≤z _ → x≤z

join-comm : (x y : Value) → join x y ≡ join y x
join-comm U U = ≡.refl
join-comm U T = ≡.refl
join-comm U F = ≡.refl
join-comm U X = ≡.refl
join-comm T U = ≡.refl
join-comm T T = ≡.refl
join-comm T F = ≡.refl
join-comm T X = ≡.refl
join-comm F U = ≡.refl
join-comm F T = ≡.refl
join-comm F F = ≡.refl
join-comm F X = ≡.refl
join-comm X U = ≡.refl
join-comm X T = ≡.refl
join-comm X F = ≡.refl
join-comm X X = ≡.refl

join-assoc : (x y z : Value) → join (join x y) z ≡ join x (join y z)
join-assoc U y z = ≡.refl
join-assoc T U z = ≡.refl
join-assoc T T U = ≡.refl
join-assoc T T T = ≡.refl
join-assoc T T F = ≡.refl
join-assoc T T X = ≡.refl
join-assoc T F U = ≡.refl
join-assoc T F T = ≡.refl
join-assoc T F F = ≡.refl
join-assoc T F X = ≡.refl
join-assoc T X U = ≡.refl
join-assoc T X T = ≡.refl
join-assoc T X F = ≡.refl
join-assoc T X X = ≡.refl
join-assoc F U z = ≡.refl
join-assoc F T U = ≡.refl
join-assoc F T T = ≡.refl
join-assoc F T F = ≡.refl
join-assoc F T X = ≡.refl
join-assoc F F U = ≡.refl
join-assoc F F T = ≡.refl
join-assoc F F F = ≡.refl
join-assoc F F X = ≡.refl
join-assoc F X U = ≡.refl
join-assoc F X T = ≡.refl
join-assoc F X F = ≡.refl
join-assoc F X X = ≡.refl
join-assoc X U z = ≡.refl
join-assoc X T U = ≡.refl
join-assoc X T T = ≡.refl
join-assoc X T F = ≡.refl
join-assoc X T X = ≡.refl
join-assoc X F U = ≡.refl
join-assoc X F T = ≡.refl
join-assoc X F F = ≡.refl
join-assoc X F X = ≡.refl
join-assoc X X U = ≡.refl
join-assoc X X T = ≡.refl
join-assoc X X F = ≡.refl
join-assoc X X X = ≡.refl

meet-distribˡ-join : (x y z : Value) → meet x (join y z) ≡ join (meet x y) (meet x z)
meet-distribˡ-join U _ _ = ≡.refl
meet-distribˡ-join T U _ = ≡.refl
meet-distribˡ-join T T U = ≡.refl
meet-distribˡ-join T T T = ≡.refl
meet-distribˡ-join T T F = ≡.refl
meet-distribˡ-join T T X = ≡.refl
meet-distribˡ-join T F U = ≡.refl
meet-distribˡ-join T F T = ≡.refl
meet-distribˡ-join T F F = ≡.refl
meet-distribˡ-join T F X = ≡.refl
meet-distribˡ-join T X U = ≡.refl
meet-distribˡ-join T X T = ≡.refl
meet-distribˡ-join T X F = ≡.refl
meet-distribˡ-join T X X = ≡.refl
meet-distribˡ-join F U _ = ≡.refl
meet-distribˡ-join F T U = ≡.refl
meet-distribˡ-join F T T = ≡.refl
meet-distribˡ-join F T F = ≡.refl
meet-distribˡ-join F T X = ≡.refl
meet-distribˡ-join F F U = ≡.refl
meet-distribˡ-join F F T = ≡.refl
meet-distribˡ-join F F F = ≡.refl
meet-distribˡ-join F F X = ≡.refl
meet-distribˡ-join F X U = ≡.refl
meet-distribˡ-join F X T = ≡.refl
meet-distribˡ-join F X F = ≡.refl
meet-distribˡ-join F X X = ≡.refl
meet-distribˡ-join X _ _ = ≡.refl

v≤X : (v : Value) → ≤-Value v X
v≤X U = U≤X
v≤X T = T≤X
v≤X F = F≤X
v≤X X = v≤v

U≤v : (v : Value) → ≤-Value U v
U≤v U = v≤v
U≤v T = U≤T
U≤v F = U≤F
U≤v X = U≤X

𝕍 : BoundedDistributiveLattice 0ℓ 0ℓ 0ℓ
𝕍 = record
    { Carrier = Value
    ; _≈_ = _≡_
    ; _≤_ = ≤-Value
    ; _∨_ = join
    ; _∧_ = meet
    ; ⊤ = X
    ; ⊥ = U
    ; isBoundedDistributiveLattice = record
        { isLattice = record
            { isPartialOrder = record 
                { isPreorder = record
                    { isEquivalence = ≡.isEquivalence
                    ; reflexive = ≤-reflexive
                    ; trans = ≤-transitive
                    }
                ; antisym = ≤-antisymmetric
                }
            ; supremum = ≤-supremum
            ; infimum = ≤-infimum
            }
        ; maximum = v≤X
        ; minimum = U≤v
        ; ∧-distribˡ-∨ = meet-distribˡ-join
        }
    }

module 𝕍 = BoundedDistributiveLattice 𝕍

semiring : Semiring 0ℓ 0ℓ
semiring = 𝕍.semiring

monoid : CommutativeMonoid 0ℓ 0ℓ
monoid = let open Semiring semiring in +-commutativeMonoid
