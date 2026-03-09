{-# OPTIONS --without-K --safe #-}

module Data.WiringDiagram.FinRel where

open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Data.Fin using (Fin; splitAt; _↑ˡ_; _↑ʳ_; cast)
open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ; splitAt-↑ˡ; splitAt-↑ʳ; ↑ˡ-injective; cast-is-id; cast-involutive; cast-trans)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (+-assoc)
open import Data.Product using (_,_; swap)
open import Function using (flip; id; _∘_)
open import Level using (0ℓ; suc)
open import Relation.Binary using (REL; _⇒_; _⇔_)
open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

FinRel : Category 0ℓ (suc 0ℓ) 0ℓ
FinRel = categoryHelper record
    { Obj = ℕ
    ; _⇒_ = λ n m → REL (Fin n) (Fin m) 0ℓ
    ; _≈_ = _⇔_
    ; id = _≡_
    ; _∘_ = flip _;_
    ; assoc = (λ (a , b , c , d , e) → c , (a , b , d) , e) , λ (a , (b , c , d) , e) → b , c , a , d , e
    ; identityˡ = (λ { (_ , f[x,y] , ≡.refl) → f[x,y] }) , λ {x y} f[x,y] → y , f[x,y] , ≡.refl
    ; identityʳ = (λ { (_ , ≡.refl , f[x,y]) → f[x,y] }) , λ {x y} f[x,y] → x , ≡.refl , f[x,y]
    ; equiv = record
        { refl = id , id
        ; sym = swap
        ; trans = λ (x , y) (x′ , y′) → x′ ∘ x , y ∘ y′
        }
    ; ∘-resp-≈ = λ (f⇒h , h⇒i) (g⇒i , i⇒g) → (λ (z , g-x-z , f-z-y) → z , g⇒i g-x-z , f⇒h f-z-y) , λ (z , i-x-z , h-z-y) → z , i⇒g i-x-z , h⇒i h-z-y
    }

open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Data.Nat using (_+_)
open import Data.Product using (_×_; Σ; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import Data.Empty using (⊥)
open _⊎_

opaque
  _+₁_
      : {A B C D : ℕ}
      → REL (Fin A) (Fin B) 0ℓ
      → REL (Fin C) (Fin D) 0ℓ
      → REL (Fin (A + C)) (Fin (B + D)) 0ℓ
  _+₁_ {A} {B} {C} {D} R S x y with splitAt A x | splitAt B y
  ... | inj₁ x | inj₁ y = R x y
  ... | inj₁ x | inj₂ y = ⊥
  ... | inj₂ x | inj₁ y = ⊥
  ... | inj₂ x | inj₂ y = S x y

infixr 7 _+₁_

opaque
  unfolding _+₁_
  +₁-⊎
      : {A B C D : ℕ}
        {R : REL (Fin A) (Fin B) 0ℓ}
        {S : REL (Fin C) (Fin D) 0ℓ}
        {x : Fin (A + C)}
        {y : Fin (B + D)}
      → (R +₁ S) x y
      → Σ[ x′ ∈ Fin A ] Σ[ y′ ∈ Fin B ] (R x′ y′ × x ≡ x′ ↑ˡ C × y ≡ y′ ↑ˡ D)
      ⊎ Σ[ x′ ∈ Fin C ] Σ[ y′ ∈ Fin D ] (S x′ y′ × x ≡ A ↑ʳ x′ × y ≡ B ↑ʳ y′)
  +₁-⊎ {A} {B} {x = x} {y} RS with splitAt A x in eq₁ | splitAt B y in eq₂
  ... | inj₁ x₁ | inj₁ x₂ = inj₁ (x₁ , x₂ , RS , ≡.sym (splitAt⁻¹-↑ˡ eq₁) , ≡.sym (splitAt⁻¹-↑ˡ eq₂))
  ... | inj₂ y₁ | inj₂ y₂ = inj₂ (y₁ , y₂ , RS , ≡.sym (splitAt⁻¹-↑ʳ eq₁) , ≡.sym (splitAt⁻¹-↑ʳ eq₂))

opaque

  unfolding _+₁_

  ↑ˡ-REL
      : {X Y X′ Y′ : ℕ}
        {x : Fin X}
        {y : Fin Y}
        {f : REL (Fin X) (Fin Y) 0ℓ}
        {f′ : REL (Fin X′) (Fin Y′) 0ℓ}
      → f x y
      → (f +₁ f′) (x ↑ˡ X′) (y ↑ˡ Y′)
  ↑ˡ-REL {X} {Y} {X′} {Y′} {x} {y} f-x-y
    rewrite splitAt-↑ˡ X x X′
    rewrite splitAt-↑ˡ Y y Y′ = f-x-y

  ↑ʳ-REL
      : {X Y X′ Y′ : ℕ}
        {x′ : Fin X′}
        {y′ : Fin Y′}
        {f : REL (Fin X) (Fin Y) 0ℓ}
        {f′ : REL (Fin X′) (Fin Y′) 0ℓ}
      → f′ x′ y′
      → (f +₁ f′) (X ↑ʳ x′) (Y ↑ʳ y′)
  ↑ʳ-REL {X} {Y} {X′} {Y′} {x′} {y′} f′-x′-y′
    rewrite splitAt-↑ʳ X X′ x′
    rewrite splitAt-↑ʳ Y Y′ y′ = f′-x′-y′

opaque
  unfolding _+₁_
  +₁-≡ : {A B : ℕ} {x y : Fin (A + B)} → ((_≡_ {A = Fin A}) +₁ _≡_) x y → x ≡ y
  +₁-≡ {A} {B} {x} {y} x≡y₁₂ with splitAt A x in eq₁ | splitAt A y in eq₂
  ... | inj₁ x₁ | inj₁ y₁ = ≡.trans (≡.sym (splitAt⁻¹-↑ˡ eq₁)) (≡.trans (≡.cong (_↑ˡ B) x≡y₁₂) (splitAt⁻¹-↑ˡ eq₂))
  ... | inj₂ x₂ | inj₂ y₂ = ≡.trans (≡.sym (splitAt⁻¹-↑ʳ eq₁)) (≡.trans (≡.cong (A ↑ʳ_) x≡y₁₂) (splitAt⁻¹-↑ʳ eq₂))

opaque
  unfolding _+₁_
  ≡-+₁ : {A B : ℕ} {x y : Fin (A + B)} → x ≡ y → ((_≡_ {A = Fin A}) +₁ _≡_) x y
  ≡-+₁ {A} {B} {x} {y} x≡y with splitAt A x in eq₁ | splitAt A y in eq₂
  ... | inj₁ x′ | inj₁ y′ = inj₁-injective (≡.trans (≡.sym eq₁) (≡.trans (≡.cong (splitAt A) x≡y) eq₂))
  ... | inj₁ x′ | inj₂ y′ with () ← ≡.trans (≡.sym eq₁) (≡.trans (≡.cong (splitAt A) x≡y) eq₂)
  ... | inj₂ x′ | inj₁ y′ with () ← ≡.trans (≡.sym eq₁) (≡.trans (≡.cong (splitAt A) x≡y) eq₂)
  ... | inj₂ x′ | inj₂ y′ = inj₂-injective (≡.trans (≡.sym eq₁) (≡.trans (≡.cong (splitAt A) x≡y) eq₂))

;-+₁
    : {X X′ Y Y′ Z Z′ : ℕ}
      (f : REL (Fin X) (Fin Y) 0ℓ)
      (f′ : REL (Fin X′) (Fin Y′) 0ℓ)
      (g : REL (Fin Y) (Fin Z) 0ℓ)
      (g′ : REL (Fin Y′) (Fin Z′) 0ℓ)
      (x : Fin (X + X′))
      (y : Fin (Z + Z′))
    → (f ; g +₁ f′ ; g′) x y
    → ((f +₁ f′) ; (g +₁ g′)) x y
;-+₁ {X} {X′} {Y} {Y′} {Z} {Z′} f f′ g g′ x y BER with +₁-⊎ BER
... | inj₁ (x′ , z′ , (y , f-x′-y , g-y-z) , eq , eq₂)
        rewrite eq
        rewrite eq₂ = y ↑ˡ Y′ , ↑ˡ-REL f-x′-y , ↑ˡ-REL g-y-z
... | inj₂ (x′ , y′ , (z , f′-x′-z′ , g′-z-y′) , eq₁ , eq₂)
        rewrite eq₁
        rewrite eq₂ = Y ↑ʳ z  , ↑ʳ-REL f′-x′-z′ , ↑ʳ-REL g′-z-y′

opaque
  unfolding _+₁_
  +₁-;
      : {X X′ Y Y′ Z Z′ : ℕ}
        (f : REL (Fin X) (Fin Y) 0ℓ)
        (f′ : REL (Fin X′) (Fin Y′) 0ℓ)
        (g : REL (Fin Y) (Fin Z) 0ℓ)
        (g′ : REL (Fin Y′) (Fin Z′) 0ℓ)
        (x : Fin (X + X′))
        (y : Fin (Z + Z′))
      → ((f +₁ f′) ; (g +₁ g′)) x y
      → (f ; g +₁ f′ ; g′) x y
  +₁-; {X} {X′} {Y} {Y′} {Z} {Z′} f f′ g g′ x z (y , fxygyz)
    with splitAt X x | splitAt Y y | splitAt Z z
  ... | inj₁ x′ | inj₁ y′ | inj₁ z′ = y′ , fxygyz
  ... | inj₂ x′ | inj₂ y′ | inj₂ z′ = y′ , fxygyz

module _ {A A′ B B′ : ℕ} {f g : REL (Fin A) (Fin B) 0ℓ} {f′ g′ : REL (Fin A′) (Fin B′) 0ℓ} where

  +₁-resp-⇒ : f ⇒ g → f′ ⇒ g′ → f +₁ f′ ⇒ g +₁ g′
  +₁-resp-⇒ f⇒g f′⇒g′ f+f′-a-b with +₁-⊎ f+f′-a-b
  ... | inj₁ (a , b , f-a-b , ≡a↑ˡA′ , ≡b↑ˡB′) rewrite ≡a↑ˡA′ rewrite ≡b↑ˡB′ = ↑ˡ-REL (f⇒g f-a-b)
  ... | inj₂ (a , b , f′-a-b , ≡A↑ʳa , ≡B↑ʳb) rewrite ≡A↑ʳa rewrite ≡B↑ʳb = ↑ʳ-REL (f′⇒g′ f′-a-b)

⊗ : Bifunctor FinRel FinRel FinRel
⊗ = record
    { F₀ = λ (n , m) → n + m
    ; F₁ = λ (f , g) → f +₁ g
    ; identity = λ { {A , B} → +₁-≡ {A} {B} , ≡-+₁ {A} {B} }
    ; homomorphism = λ { {X , X′} {Y , Y′} {Z , Z′} {f , f′} {g , g′} →
        (λ { {x} {y} → ;-+₁ f f′ g g′ x y }) , (λ { {x} {y} → +₁-; f f′ g g′ x y }) }
    ; F-resp-≈ = λ { {A , A′} {B , B′} {f , f′} {g , g′} ((f⇒g , g⇒f) , (f′⇒g′ , g′⇒f′))
        → +₁-resp-⇒ f⇒g f′⇒g′ , +₁-resp-⇒ g⇒f g′⇒f′ }
    }

module _ {X : ℕ} where

  ρ⇒ : REL (Fin (X + 0)) (Fin X) 0ℓ
  ρ⇒ x+0 y with inj₁ x ← splitAt X x+0 = x ≡ y

  ρ⇐ : REL (Fin X) (Fin (X + 0)) 0ℓ
  ρ⇐ x y+0 with inj₁ y ← splitAt X y+0 = x ≡ y

  ρ⇒⇐-≡ : ρ⇒ ; ρ⇐ ⇒ _≡_
  ρ⇒⇐-≡ {x+0} {y+0} (z , x≡z , z≡y) with splitAt X x+0 in eq₁ | splitAt X y+0 in eq₂
  ... | inj₁ x | inj₁ y rewrite ≡.sym (splitAt⁻¹-↑ˡ eq₁) rewrite ≡.sym (splitAt⁻¹-↑ˡ eq₂) = ≡.cong (_↑ˡ 0) (≡.trans x≡z z≡y)

  ≡-ρ⇒⇐ : _≡_ ⇒ ρ⇒ ; ρ⇐
  ≡-ρ⇒⇐ {x+0} {y+0} x↑ˡ0≡y↑ˡ0 with splitAt X x+0 in eq₁ | splitAt X y+0 in eq₂
  ... | inj₁ x | inj₁ y rewrite ≡.sym (splitAt⁻¹-↑ˡ eq₁) rewrite ≡.sym (splitAt⁻¹-↑ˡ eq₂) = (x , ≡.refl , ↑ˡ-injective 0 x y x↑ˡ0≡y↑ˡ0)

  ρ⇐⇒-≡ : ρ⇐ ; ρ⇒ ⇒ _≡_
  ρ⇐⇒-≡ {x} {y} (z , x≡z , z≡y) with inj₁ z ← splitAt X z = ≡.trans x≡z z≡y

  ≡-ρ⇐⇒ : _≡_ ⇒ ρ⇐ ; ρ⇒
  ≡-ρ⇐⇒ {x} {y} x≡y = x ↑ˡ 0 , lemma
    where
      lemma : ρ⇐ x (x ↑ˡ 0) × ρ⇒ (x ↑ˡ 0) y
      lemma with splitAt X (x ↑ˡ 0) in eq
      ... | inj₁ x′ = ≡.sym x′≡x , ≡.trans x′≡x x≡y
        where
          x′≡x : x′ ≡ x
          x′≡x = ↑ˡ-injective 0 x′ x (splitAt⁻¹-↑ˡ eq)

open import Categories.Morphism FinRel using (_≅_; module ≅)

module _ {X : ℕ} where

  unitorˡ : 0 + X ≅ X
  unitorˡ = ≅.refl

  unitorʳ : X + 0 ≅ X
  unitorʳ = record
      { from = ρ⇒
      ; to = ρ⇐
      ; iso = record
          { isoˡ = ρ⇒⇐-≡ , ≡-ρ⇒⇐
          ; isoʳ = ρ⇐⇒-≡ , ≡-ρ⇐⇒
          }
      }

module _ {X Y Z : ℕ} where

  α⇒ : REL (Fin (X + Y + Z)) (Fin (X + (Y + Z))) 0ℓ
  α⇒ [xy]z x[yz] = cast (+-assoc X Y Z) [xy]z ≡ x[yz]

  α⇐ : REL (Fin (X + (Y + Z))) (Fin ((X + Y) + Z)) 0ℓ
  α⇐ x[yz] [xy]z = cast (≡.sym (+-assoc X Y Z)) x[yz] ≡ [xy]z

  α⇒;α⇐-⇒ : α⇒ ; α⇐ ⇒ _≡_
  α⇒;α⇐-⇒ {x} {y} (z , cast-x≡z , cast-z≡y) =
      ≡.trans
          (≡.sym (cast-involutive (≡.sym (+-assoc X Y Z)) (+-assoc X Y Z) x))
          (≡.trans (≡.cong (cast _) cast-x≡z) cast-z≡y)

  α⇒;α⇐-⇐ : _≡_ ⇒ α⇒ ; α⇐
  α⇒;α⇐-⇐ {x} {y} x≡y = cast _ x , ≡.refl , ≡.trans (cast-involutive (≡.sym (+-assoc X Y Z)) (+-assoc X Y Z) x) x≡y

  α⇐;α⇒-⇒ : α⇐ ; α⇒ ⇒ _≡_
  α⇐;α⇒-⇒ {x} {y} (z , cast-x≡z , cast-z≡y) =
      ≡.trans
          (≡.sym (cast-involutive (+-assoc X Y Z) (≡.sym (+-assoc X Y Z)) x))
          (≡.trans (≡.cong (cast _) cast-x≡z) cast-z≡y)

  α⇐;α⇒-⇐ : _≡_ ⇒ α⇐ ; α⇒
  α⇐;α⇒-⇐ {x} {y} x≡y = cast _ x , ≡.refl , ≡.trans (cast-involutive (+-assoc X Y Z) (≡.sym (+-assoc X Y Z)) x) x≡y

  associator : (X + Y) + Z ≅ X + (Y + Z)
  associator = record
      { from = α⇒
      ; to = α⇐
      ; iso = record
          { isoˡ = α⇒;α⇐-⇒ , α⇒;α⇐-⇐
          ; isoʳ = α⇐;α⇒-⇒ , α⇐;α⇒-⇐
          }
      }

module _ (X Y : ℕ) (R : REL (Fin X) (Fin Y) 0ℓ) where

  left₁ : (_≡_ +₁ R) ; _≡_ ⇒ _≡_ ; R
  left₁ (_ , e-x-y′ , ≡.refl) with +₁-⊎ e-x-y′
  ... | inj₂ (x , y , xRy , ≡.refl , ≡.refl) = x , ≡.refl , xRy

  right₁ : _≡_ ; R ⇒ (_≡_ +₁ R) ; _≡_
  right₁ {x} {y} (x , ≡.refl , xRy) = y , ↑ʳ-REL xRy , ≡.refl

  unitorˡ-commute-to : (_≡_ +₁ R) ; _≡_ ⇔ _≡_ ; R
  unitorˡ-commute-to = left₁ , right₁

  left₂ : R ; _≡_ ⇒ _≡_ ; (_≡_ +₁ R)
  left₂ {x} {y} (y , xRy , ≡.refl) = x , ≡.refl , ↑ʳ-REL xRy

  right₂ : _≡_ ; (_≡_ +₁ R) ⇒ R ; _≡_
  right₂ (_ , ≡.refl , e-x-y) with +₁-⊎ e-x-y
  ... | inj₂ (x , y , xRy , ≡.refl , ≡.refl) = y , xRy , ≡.refl

  unitorˡ-commute-from : R ; _≡_ ⇔ _≡_ ; (_≡_ +₁ R)
  unitorˡ-commute-from = left₂ , right₂

  left₃ : (R +₁ _≡_) ; ρ⇒ ⇒ ρ⇒ ; R
  left₃ {x+0} {y} (y+0 , e-x-y , y≡y) with +₁-⊎ e-x-y | splitAt X x+0 in eq₁ | splitAt Y y+0 in eq₂ | y≡y
  ... | inj₁ (x″ , y″ , x″Ry″ , x+0≡x″↑ˡ0 , y+0≡y″↑ˡ0) | inj₁ x′ | inj₁ y′ | y≡y′
    rewrite (≡.sym (↑ˡ-injective 0 x′ x″ (≡.trans (splitAt⁻¹-↑ˡ eq₁) x+0≡x″↑ˡ0)))
    rewrite (≡.sym (↑ˡ-injective 0 y′ y″ (≡.trans (splitAt⁻¹-↑ˡ eq₂) y+0≡y″↑ˡ0)))
    rewrite ≡.sym y≡y′ = x′ , ≡.refl , x″Ry″

  right₃ : ρ⇒ ; R ⇒ (R +₁ _≡_) ; ρ⇒
  right₃ {x+0} {y} (x , e-x-y , xRy) with splitAt X x+0 in eq₁
  ... | inj₁ x′
    rewrite ≡.sym (splitAt⁻¹-↑ˡ eq₁)
    rewrite e-x-y = y ↑ˡ 0 , ↑ˡ-REL xRy , lemma
      where
        lemma : ρ⇒ (y ↑ˡ 0) y
        lemma with splitAt Y (y ↑ˡ 0) in eq₂
        ... | inj₁ y′ = ↑ˡ-injective 0 y′ y (splitAt⁻¹-↑ˡ eq₂)

  unitorʳ-commute-from : (R +₁ _≡_) ; ρ⇒ ⇒ ρ⇒ ; R × ρ⇒ ; R ⇒ (R +₁ _≡_) ; ρ⇒
  unitorʳ-commute-from = left₃ , right₃

  left₄ : R ; ρ⇐ ⇒ ρ⇐ ; (R +₁ _≡_)
  left₄ {x} {y+0} (y , xRy′ , y≡y′) with splitAt Y y+0 in eq₁
  ... | inj₁ y′
    rewrite ≡.sym (splitAt⁻¹-↑ˡ eq₁)
    rewrite y≡y′
        = x ↑ˡ 0 , lemma , ↑ˡ-REL xRy′
    where
      lemma : ρ⇐ x (x ↑ˡ 0)
      lemma with splitAt X (x ↑ˡ 0) in eq₂
      ... | inj₁ x′ = ↑ˡ-injective 0 x x′ (≡.sym (splitAt⁻¹-↑ˡ eq₂))

  right₄ : ρ⇐ ; (R +₁ _≡_) ⇒ R ; ρ⇐
  right₄ {x} {y+0} (x+0 , x≡x″ , e-x-y) with +₁-⊎ e-x-y | splitAt X x+0 in eq₁
  ... | inj₁ (x′ , y′ , x′Ry′ , x+0≡x′↑ˡ0 , y+0≡y′↑ˡ0) | inj₁ x″
    rewrite x≡x″
    rewrite (↑ˡ-injective 0 x″ x′ (≡.trans (splitAt⁻¹-↑ˡ eq₁) x+0≡x′↑ˡ0))
        = y′ , x′Ry′ , lemma
      where
        lemma : ρ⇐ y′ y+0
        lemma with splitAt Y y+0 in eq₂
        ... | inj₁ y″ = ↑ˡ-injective 0 y′ y″ (≡.sym (≡.trans (splitAt⁻¹-↑ˡ eq₂) y+0≡y′↑ˡ0))

  unitorʳ-commute-to : R ; ρ⇐ ⇔ ρ⇐ ; (R +₁ _≡_)
  unitorʳ-commute-to = left₄ , right₄

+-↑ʳ : (A B : ℕ) {C : ℕ} (c : Fin C) → cast (+-assoc A B C) (A + B ↑ʳ c) ≡ A ↑ʳ (B ↑ʳ c)
+-↑ʳ ℕ.zero B c = cast-is-id ≡.refl (B ↑ʳ c)
+-↑ʳ (ℕ.suc A) B c = ≡.cong Fin.suc (+-↑ʳ A B c)

↑ˡ-+ : {A : ℕ} (a : Fin A) (B C : ℕ) → cast (+-assoc A B C) (a ↑ˡ B ↑ˡ C) ≡ a ↑ˡ (B + C)
↑ˡ-+ Fin.zero B C = ≡.refl
↑ˡ-+ (Fin.suc a) B C = ≡.cong Fin.suc (↑ˡ-+ a B C)

↑ʳ-↑ˡ : (A : ℕ) {B : ℕ} (b : Fin B) (C : ℕ) → cast (+-assoc A B C) ((A ↑ʳ b) ↑ˡ C) ≡ A ↑ʳ (b ↑ˡ C)
↑ʳ-↑ˡ ℕ.zero b C = cast-is-id ≡.refl (b ↑ˡ C)
↑ʳ-↑ˡ (ℕ.suc A) b C = ≡.cong Fin.suc (↑ʳ-↑ˡ A b C)

cast-↑ˡ : {A B : ℕ} (A≡B : A ≡ B) (x : Fin A) (C : ℕ) → cast A≡B x ↑ˡ C ≡ cast (≡.cong (_+ C) A≡B) (x ↑ˡ C)
cast-↑ˡ ≡.refl x C
  rewrite cast-is-id ≡.refl x
  rewrite cast-is-id ≡.refl (x ↑ˡ C) = ≡.refl

cast-↑ʳ : {B C : ℕ} (B≡C : B ≡ C) (A : ℕ) (x : Fin B) → A ↑ʳ cast B≡C x ≡ cast (≡.cong (A +_) B≡C) (A ↑ʳ x)
cast-↑ʳ ≡.refl A x
  rewrite cast-is-id ≡.refl x
  rewrite cast-is-id ≡.refl (A ↑ʳ x) = ≡.refl

↑ˡ-assoc : {X : ℕ} (x : Fin X) (Y Z W : ℕ) → x ↑ˡ Y + Z + W ≡ cast (≡.cong (X +_) (≡.sym (+-assoc Y Z W))) (x ↑ˡ Y + (Z + W))
↑ˡ-assoc {X} x Y Z W = begin
    x ↑ˡ Y + Z + W                                            ≡⟨ ↑ˡ-+ x (Y + Z) W ⟨
    cast _ (x ↑ˡ Y + Z ↑ˡ W)                                  ≡⟨ ≡.cong (cast _ ∘ (_↑ˡ W)) (↑ˡ-+ x Y Z) ⟨
    cast (+-assoc X (Y + Z) W) (cast _ (x ↑ˡ Y ↑ˡ Z) ↑ˡ W)    ≡⟨ ≡.cong (cast _) (cast-↑ˡ (+-assoc X Y Z) ((x ↑ˡ Y) ↑ˡ Z) W) ⟩
    cast (+-assoc X (Y + Z) W) (cast _ (x ↑ˡ Y ↑ˡ Z ↑ˡ W))    ≡⟨ cast-trans _ (+-assoc X (Y + Z) W) (x ↑ˡ Y ↑ˡ Z ↑ˡ W) ⟩
    cast _ (x ↑ˡ Y ↑ˡ Z ↑ˡ W)                                 ≡⟨ cast-trans (+-assoc (X + Y) Z W) _ (x ↑ˡ Y ↑ˡ Z ↑ˡ W) ⟨
    cast _ (cast (+-assoc (X + Y) Z W) (x ↑ˡ Y ↑ˡ Z ↑ˡ W))    ≡⟨ ≡.cong (cast _) (↑ˡ-+ (x ↑ˡ Y) Z W)  ⟩
    cast _ (x ↑ˡ Y ↑ˡ Z + W)                                  ≡⟨ cast-trans _ (≡.cong (X +_) (≡.sym (+-assoc Y Z W))) (x ↑ˡ Y ↑ˡ Z + W) ⟨
    cast (≡.cong (X +_) (≡.sym (+-assoc Y Z W))) (cast  _ (x ↑ˡ Y ↑ˡ Z + W))  ≡⟨ ≡.cong (cast _) (↑ˡ-+ x Y (Z + W)) ⟩
    cast _ (x ↑ˡ Y + (Z + W)) ∎
  where
    open ≡-Reasoning

assoc-↑ʳ : (X Y Z : ℕ) {W : ℕ} (w : Fin W) → X + Y + Z ↑ʳ w ≡ cast (≡.cong (_+ W) (≡.sym (+-assoc X Y Z))) (X + (Y + Z) ↑ʳ w)
assoc-↑ʳ X Y Z {W} w = begin
    X + Y + Z ↑ʳ w                                                ≡⟨ cast-involutive (≡.sym (+-assoc (X + Y) Z W)) (+-assoc (X + Y) Z W) (X + Y + Z ↑ʳ w) ⟨
    cast _ (cast (+-assoc (X + Y) Z W) (X + Y + Z ↑ʳ w))          ≡⟨ ≡.cong (cast _) (+-↑ʳ (X + Y) Z w) ⟩
    cast _ (X + Y ↑ʳ (Z ↑ʳ w))                                    ≡⟨ cast-trans (+-assoc X Y (Z + W)) eq₂ (X + Y ↑ʳ (Z ↑ʳ w)) ⟨
    cast _ (cast (+-assoc X Y (Z + W)) (X + Y ↑ʳ (Z ↑ʳ w)))       ≡⟨ ≡.cong (cast _) (+-↑ʳ X Y (Z ↑ʳ w)) ⟩
    cast _ (X ↑ʳ Y ↑ʳ Z ↑ʳ w)                                     ≡⟨ cast-trans (≡.cong (_+_ X) (≡.sym (+-assoc Y Z W))) eq (X ↑ʳ Y ↑ʳ Z ↑ʳ w) ⟨
    cast eq (cast _ (X ↑ʳ Y ↑ʳ Z ↑ʳ w))                          ≡⟨ ≡.cong (cast _) (cast-↑ʳ (≡.sym (+-assoc Y Z W)) X (Y ↑ʳ Z ↑ʳ w)) ⟨
    cast _ (X ↑ʳ cast {Y + (Z + W)} {Y + Z + W} _ (Y ↑ʳ Z ↑ʳ w))  ≡⟨ ≡.cong (cast eq ∘ (X ↑ʳ_) ∘ cast _) (+-↑ʳ Y Z w) ⟨
    cast _ (X ↑ʳ cast _ (cast (+-assoc Y Z W) (Y + Z ↑ʳ w)))      ≡⟨ ≡.cong (cast eq ∘ (X ↑ʳ_)) (cast-involutive (≡.sym (+-assoc Y Z W)) (+-assoc Y Z W) (Y + Z ↑ʳ w)) ⟩
    cast eq (X ↑ʳ (Y + Z ↑ʳ w))                                  ≡⟨ ≡.cong (cast eq) (+-↑ʳ X (Y + Z) w) ⟨
    cast eq (cast _ (X + (Y + Z) ↑ʳ w))                          ≡⟨ cast-trans (+-assoc X (Y + Z) W) eq (X + (Y + Z) ↑ʳ w) ⟩
    cast _ (X + (Y + Z) ↑ʳ w)                                     ∎
  where
    open ≡-Reasoning
    eq :  X + (Y + Z + W) ≡ X + Y + Z + W
    eq = begin
        X + (Y + Z + W) ≡⟨ +-assoc X (Y + Z) W ⟨
        X + (Y + Z) + W ≡⟨ ≡.cong (_+ W) (+-assoc X Y Z) ⟨
        X + Y + Z + W   ∎
    eq₂ : X + (Y + (Z + W)) ≡ X + Y + Z + W
    eq₂ = begin
        X + (Y + (Z + W)) ≡⟨ +-assoc X Y (Z + W) ⟨
        X + Y + (Z + W)   ≡⟨ +-assoc (X + Y) Z W ⟨
        X + Y + Z + W     ∎

module _
    {X Y X′ Y′ X″ Y″ : ℕ}
    {R : REL (Fin X) (Fin Y) 0ℓ}
    {S : REL (Fin X′) (Fin Y′) 0ℓ}
    {T : REL (Fin X″) (Fin Y″) 0ℓ}
  where

  +₁-assoc-⇒
      : {x : Fin (X + X′ + X″)}
        {y : Fin (Y + Y′ + Y″)}
      → ((R +₁ S) +₁ T) x y
      → (R +₁ (S +₁ T)) (cast (+-assoc X X′ X″) x) (cast (+-assoc Y Y′ Y″) y)
  +₁-assoc-⇒ xxxRSTyyy with +₁-⊎ xxxRSTyyy
  ... | inj₂ (x , y , xTy , ≡.refl , ≡.refl) rewrite +-↑ʳ X X′ x rewrite +-↑ʳ Y Y′ y
            = ↑ʳ-REL (↑ʳ-REL xTy)
  ... | inj₁ (xx , yy , xxRSyy , ≡.refl , ≡.refl) with +₁-⊎ xxRSyy 
  ...   | inj₁ (x , y , xRy , ≡.refl , ≡.refl) rewrite ↑ˡ-+ x X′ X″ rewrite ↑ˡ-+ y Y′ Y″ = ↑ˡ-REL xRy
  ...   | inj₂ (x , y , xSy , ≡.refl , ≡.refl) rewrite ↑ʳ-↑ˡ X x X″ rewrite ↑ʳ-↑ˡ Y y Y″ = ↑ʳ-REL (↑ˡ-REL xSy)

  +₁-assoc-⇐
      : {x : Fin (X + (X′ + X″))}
        {y : Fin (Y + (Y′ + Y″))}
      → (R +₁ (S +₁ T)) x y
      → ((R +₁ S) +₁ T) (cast (≡.sym (+-assoc X X′ X″)) x) (cast (≡.sym (+-assoc Y Y′ Y″)) y)
  +₁-assoc-⇐ xxxRSTyyy with +₁-⊎ xxxRSTyyy
  ... | inj₁ (x , y , xRy , ≡.refl , ≡.refl)
          rewrite ≡.sym (↑ˡ-+ x X′ X″)
          rewrite ≡.sym (↑ˡ-+ y Y′ Y″)
          rewrite cast-involutive (≡.sym (+-assoc X X′ X″)) (+-assoc X X′ X″) (x ↑ˡ X′ ↑ˡ X″)
          rewrite cast-involutive (≡.sym ((+-assoc Y Y′ Y″))) (+-assoc Y Y′ Y″) (y ↑ˡ Y′ ↑ˡ Y″)
        = ↑ˡ-REL (↑ˡ-REL xRy)
  ... | inj₂ (xx , yy , xxSTyy , ≡.refl , ≡.refl) with +₁-⊎ xxSTyy
  ...   | inj₁ (x , y , xSy , ≡.refl , ≡.refl)
            rewrite ≡.sym (↑ʳ-↑ˡ X x X″)
            rewrite ≡.sym (↑ʳ-↑ˡ Y y Y″)
            rewrite cast-involutive (≡.sym (+-assoc X X′ X″)) (+-assoc X X′ X″) ((X ↑ʳ x) ↑ˡ X″)
            rewrite cast-involutive (≡.sym (+-assoc Y Y′ Y″)) (+-assoc Y Y′ Y″) ((Y ↑ʳ y) ↑ˡ Y″)
          = ↑ˡ-REL (↑ʳ-REL xSy)
  ...   | inj₂ (x , y , xTy , ≡.refl , ≡.refl)
            rewrite ≡.sym (+-↑ʳ X X′ x)
            rewrite ≡.sym (+-↑ʳ Y Y′ y)
            rewrite cast-involutive (≡.sym (+-assoc X X′ X″)) (+-assoc X X′ X″) (X + X′ ↑ʳ x)
            rewrite cast-involutive (≡.sym (+-assoc Y Y′ Y″)) (+-assoc Y Y′ Y″) (Y + Y′ ↑ʳ y)
          = ↑ʳ-REL xTy

module _
    (X Y X′ Y′ X″ Y″ : ℕ)
    (R : REL (Fin X) (Fin Y) 0ℓ)
    (S : REL (Fin X′) (Fin Y′) 0ℓ)
    (T : REL (Fin X″) (Fin Y″) 0ℓ)
  where

  left₅ : ((R +₁ S) +₁ T) ; α⇒ {Y} ⇒ α⇒ {X} ; (R +₁ S +₁ T)
  left₅ {x} {y} (y′ , RST-x-y′ , y′≡y) rewrite ≡.sym y′≡y = cast (+-assoc X X′ X″) x , ≡.refl , +₁-assoc-⇒ RST-x-y′

  right₅ : α⇒ {X} ; (R +₁ S +₁ T) ⇒ ((R +₁ S) +₁ T) ; α⇒ {Y}
  right₅ {x} {y} (x′ , x≡x′ , x′RSTy)
    rewrite ≡.trans (≡.sym (cast-involutive _ (+-assoc X X′ X″) x)) (≡.cong (cast (≡.sym (+-assoc X X′ X″))) x≡x′)
      = cast (≡.sym (+-assoc Y Y′ Y″)) y , +₁-assoc-⇐ x′RSTy , cast-involutive (+-assoc Y Y′ Y″) _ y

  assoc-commute-from : ((R +₁ S) +₁ T) ; α⇒ {Y} ⇔ α⇒ {X} ; (R +₁ S +₁ T)
  assoc-commute-from = left₅ , right₅

  left₆ : (R +₁ S +₁ T) ; α⇐ {Y} ⇒ α⇐ {X} ; ((R +₁ S) +₁ T)
  left₆ {xxx} {yyy} (yyy′ , xxxRSTyyy′ , ≡.refl)
      = cast (≡.sym (+-assoc X X′ X″)) xxx , ≡.refl , +₁-assoc-⇐ xxxRSTyyy′

  right₆ : α⇐ {X} ; ((R +₁ S) +₁ T) ⇒ (R +₁ S +₁ T) ; α⇐ {Y}
  right₆ {xxx} {yyy} (xxx′ , xxx≡xxx′ , xxx′RSTyyy)
    rewrite ≡.trans (≡.sym (cast-involutive (+-assoc X X′ X″) _ xxx)) (≡.cong (cast (+-assoc X X′ X″)) (xxx≡xxx′))
      = cast (+-assoc Y Y′ Y″) yyy , +₁-assoc-⇒ xxx′RSTyyy , cast-involutive (≡.sym (+-assoc Y Y′ Y″)) _ yyy

  assoc-commute-to : (R +₁ S +₁ T) ; α⇐ {Y} ⇔ α⇐ {X} ; ((R +₁ S) +₁ T)
  assoc-commute-to = left₆ , right₆

module _ (X Y : ℕ) where

  triˡ : α⇒ {X} ; (_≡_ {A = Fin X} +₁ _≡_) ⇒ ρ⇒ +₁ _≡_ {A = Fin Y}
  triˡ {[x0]y} {x[0y]} (x[0y]′ , ≡.refl , e-[x0]y-x[0y]) with +₁-⊎ e-[x0]y-x[0y]
  ... | inj₁ (x , x , ≡.refl , cast[x0]y≡x↑ˡY , ≡.refl)
          rewrite ≡.trans
              (≡.sym (cast-involutive (≡.sym (+-assoc X 0 Y)) _ [x0]y))
              (≡.cong (cast _) cast[x0]y≡x↑ˡY)
          rewrite ≡.trans
              (≡.cong (cast (≡.sym (+-assoc X 0 Y))) (≡.sym (↑ˡ-+ x 0 Y)))
              (cast-involutive _ (+-assoc X 0 Y) (x ↑ˡ 0 ↑ˡ Y))
            = ↑ˡ-REL aux
        where
          aux : ρ⇒ (x ↑ˡ 0) x
          aux with splitAt X (x ↑ˡ 0) in eq
          ... | inj₁ x′ = ↑ˡ-injective 0 x′ x (splitAt⁻¹-↑ˡ eq)
  ... | inj₂ (y , y , ≡.refl , cast[x0]y≡X↑ʳy , ≡.refl)
          rewrite ≡.trans
              (≡.sym (cast-involutive (≡.sym (+-assoc X 0 Y)) _ [x0]y))
              (≡.cong (cast _) cast[x0]y≡X↑ʳy)
          rewrite ≡.trans
              (≡.cong (cast (≡.sym (+-assoc X 0 Y))) (≡.sym (+-↑ʳ X 0 y)))
              (cast-involutive (≡.sym (+-assoc X 0 Y)) _ (X + 0 ↑ʳ y))
            = ↑ʳ-REL ≡.refl

  triʳ : ρ⇒ +₁ _≡_ {A = Fin Y} ⇒ α⇒ {X} ; (_≡_ {A = Fin X} +₁ _≡_)
  triʳ {[x0]y} {x[0y]} e-[x0]y-x[0y] with +₁-⊎ e-[x0]y-x[0y]
  ... | inj₂ (y , y , ≡.refl , ≡.refl , ≡.refl) = x[0y] , +-↑ʳ X 0 y , ↑ʳ-REL ≡.refl
  ... | inj₁ (x0 , x , x′≡x , ≡.refl , ≡.refl) with splitAt X x0 in eq
  ... | inj₁ x′ rewrite ≡.sym (splitAt⁻¹-↑ˡ eq) rewrite x′≡x = x[0y] , ↑ˡ-+ x 0 Y , ↑ˡ-REL ≡.refl

  triangle : α⇒ {X} ; (_≡_ {A = Fin X} +₁ _≡_) ⇔ ρ⇒ +₁ _≡_ {A = Fin Y}
  triangle = triˡ , triʳ

module _ (X Y Z W : ℕ) where

  pentˡ
      : ((α⇒ {X} {Y} {Z} +₁ _≡_ {A = Fin W}) ; α⇒ {X}) ; (_≡_ {A = Fin X} +₁ (α⇒ {Y}))
      ⇒ α⇒ {X + Y} ; α⇒ {X}
  pentˡ {xyzw} {x[y[zw]]} (x[[yz]w] , ([x[yz]]w , xyzw~[x[yz]]w , ≡.refl) , [x[yz]]w~x[y[zw]])
    with +₁-⊎ xyzw~[x[yz]]w | +₁-⊎ [x[yz]]w~x[y[zw]]
  ... | inj₁ ([xy]z , x[y]z , ≡.refl , ≡.refl , ≡.refl)
      | inj₁ (x , x′ , ≡.refl , [xy]z↑ˡW≡x↑ˡY+Z+W , ≡.refl)
            = cast (≡.sym (+-assoc X Y (Z + W))) x[y[zw]]
            , eq
            , cast-involutive (+-assoc X Y (Z + W)) (≡.sym (+-assoc X Y (Z + W))) x[y[zw]]
          where
            lemma : cast  _ [xy]z ↑ˡ W ≡ cast _ (x ↑ˡ Y + Z + W)
            lemma = ≡.trans
                (≡.sym (cast-involutive (≡.sym (+-assoc X (Y + Z) W)) (+-assoc X (Y + Z) W) (cast {X + Y + Z} {X + (Y + Z)} _ [xy]z ↑ˡ W)))
                (≡.cong (cast (≡.sym (+-assoc X (Y + Z) W))) [xy]z↑ˡW≡x↑ˡY+Z+W)
            open ≡-Reasoning
            eq : cast {X + Y + Z + W} {X + Y + (Z + W)} _ ([xy]z ↑ˡ W)
                ≡ cast {X + (Y + (Z + W))} {X + Y + (Z + W)} _ x[y[zw]]
            eq = begin
              cast (+-assoc (X + Y) Z W) ([xy]z ↑ˡ W)
                  ≡⟨ cast-trans _ (≡.trans (≡.cong (_+ W) (≡.sym (+-assoc X Y Z))) (+-assoc (X + Y) Z W)) ([xy]z ↑ˡ W) ⟨
              cast (≡.trans (≡.cong (_+ W) (≡.sym (+-assoc X Y Z))) (+-assoc (X + Y) Z W)) (cast _ ([xy]z ↑ˡ W))
                  ≡⟨ ≡.cong (cast _) (cast-↑ˡ (+-assoc X Y Z) [xy]z W) ⟨
              cast _ (cast _ [xy]z ↑ˡ W)
                  ≡⟨ ≡.cong (cast _) lemma ⟩
              cast (≡.trans (≡.cong (_+ W) (≡.sym (+-assoc X Y Z))) (+-assoc (X + Y) Z W))
              (cast (≡.sym (+-assoc X (Y + Z) W)) (x ↑ˡ Y + Z + W))
                  ≡⟨ cast-trans (≡.sym (+-assoc X (Y + Z) W)) (≡.trans (≡.cong (_+ W) (≡.sym (+-assoc X Y Z))) (+-assoc (X + Y) Z W)) (x ↑ˡ Y + Z + W) ⟩
              cast _ (x ↑ˡ Y + Z + W)
                  ≡⟨ ≡.cong (cast _) (↑ˡ-assoc x Y Z W) ⟩
              cast _ (cast (≡.cong (X +_) (≡.sym (+-assoc Y Z W))) (x ↑ˡ Y + (Z + W)))
                  ≡⟨ cast-trans (≡.cong (X +_) (≡.sym (+-assoc Y Z W))) _ (x ↑ˡ Y + (Z + W)) ⟩
              cast _ (x ↑ˡ (Y + (Z + W)))                   ∎
  ... | inj₁ ([xy]z , x[yz] , ≡.refl , ≡.refl , ≡.refl) | inj₂ ([yz]w , y[zw] , ≡.refl , [xy]z↑ˡW≡X↑ʳ[yz]w , ≡.refl)
            = cast (≡.sym (+-assoc X Y (Z + W))) (x[y[zw]])
            , eq
            , cast-involutive (+-assoc X Y (Z + W)) _ (X ↑ʳ cast _ [yz]w)
          where
            open ≡-Reasoning
            lemma₁ : X + (Y + Z + W) ≡ X + Y + Z + W
            lemma₁ = begin
                X + (Y + Z + W) ≡⟨ +-assoc X (Y + Z) W ⟨
                X + (Y + Z) + W ≡⟨ ≡.cong (_+ W) (+-assoc X Y Z) ⟨
                X + Y + Z + W   ∎
            lemma₂ : cast {X + Y + Z + W} {X + (Y + Z) + W} _ ([xy]z ↑ˡ W) ≡ cast _ (X ↑ʳ [yz]w)
            lemma₂ = begin
                cast _ ([xy]z ↑ˡ W)                                     ≡⟨ cast-↑ˡ (+-assoc X Y Z) [xy]z W ⟨
                cast _ [xy]z ↑ˡ W                                       ≡⟨ cast-involutive (≡.sym (+-assoc X (Y + Z) W)) _ (cast _ [xy]z ↑ˡ W) ⟨
                cast _ (cast (+-assoc X (Y + Z) W) (cast _ [xy]z ↑ˡ W)) ≡⟨ ≡.cong (cast _) [xy]z↑ˡW≡X↑ʳ[yz]w ⟩
                cast _ (X ↑ʳ [yz]w)                                     ∎
            lemma₃ : [xy]z ↑ˡ W ≡ cast _ (X ↑ʳ [yz]w)
            lemma₃ = begin
                [xy]z ↑ˡ W                                                  ≡⟨ cast-involutive (≡.sym (≡.cong (_+ W) (+-assoc X Y Z))) _ ([xy]z ↑ˡ W) ⟨
                cast _ (cast (≡.cong (_+ W) (+-assoc X Y Z)) ([xy]z ↑ˡ W))  ≡⟨ ≡.cong (cast _) lemma₂ ⟩
                cast (≡.sym (≡.cong (_+ W) (+-assoc X Y Z))) (cast _ (X ↑ʳ [yz]w))  ≡⟨ cast-trans _ (≡.sym (≡.cong (_+ W) (+-assoc X Y Z))) (X ↑ʳ [yz]w) ⟩
                cast _ (X ↑ʳ [yz]w) ∎
            eq : cast (+-assoc (X + Y) Z W) ([xy]z ↑ˡ W) ≡ cast _ (X ↑ʳ cast _ [yz]w)
            eq = begin
                cast _ ([xy]z ↑ˡ W)                                       ≡⟨ ≡.cong (cast _) lemma₃ ⟩
                cast (+-assoc (X + Y) Z W) (cast _ (X ↑ʳ [yz]w))          ≡⟨ cast-trans lemma₁ (+-assoc (X + Y) Z W) (X ↑ʳ [yz]w) ⟩
                cast _ (X ↑ʳ [yz]w)                                       ≡⟨ cast-trans _ (≡.sym (+-assoc X Y (Z + W))) (X ↑ʳ [yz]w) ⟨
                cast (≡.sym (+-assoc X Y (Z + W))) (cast _ (X ↑ʳ [yz]w))  ≡⟨ ≡.cong (cast _) (cast-↑ʳ (+-assoc Y Z W) X [yz]w) ⟨
                cast _ (X ↑ʳ cast _ [yz]w)                                ∎
  ... | inj₂ (w , w , ≡.refl , ≡.refl , ≡.refl) | inj₁ (x , x , ≡.refl , X+[Y+Z]↑ʳw≡x↑ˡY+Z+W , ≡.refl)
            = cast (≡.sym (+-assoc X Y (Z + W))) x[y[zw]]
            , eq
            , cast-involutive (+-assoc X Y (Z + W)) _ (x ↑ˡ Y + (Z + W))
          where
            open ≡-Reasoning
            lemma₁ : X + (Y + (Z + W)) ≡ X + (Y + Z + W)
            lemma₁ = ≡.cong (X +_) (≡.sym (+-assoc Y Z W))
            lemma₂ : X + (Y + Z + W) ≡ X + Y + (Z + W)
            lemma₂ = ≡.trans (≡.cong (X +_) (+-assoc Y Z W)) (≡.sym (+-assoc X Y (Z + W)))
            lemma₃ : X + (Y + Z) + W ≡ X + Y + Z + W
            lemma₃ = ≡.cong (_+ W) (≡.sym (+-assoc X Y Z))
            eq : cast _ (X + Y + Z ↑ʳ w) ≡ cast (≡.sym (+-assoc X Y (Z + W))) (x ↑ˡ Y + (Z + W))
            eq = begin
                cast _ (X + Y + Z ↑ʳ w)                                 ≡⟨ ≡.cong (cast _) (assoc-↑ʳ X Y Z w) ⟩
                cast _ (cast lemma₃ (X + (Y + Z) ↑ʳ w))                 ≡⟨ cast-trans lemma₃ (+-assoc (X + Y) Z W) (X + (Y + Z) ↑ʳ w) ⟩
                cast _ (X + (Y + Z) ↑ʳ w)                               ≡⟨ cast-trans (+-assoc X (Y + Z) W) _ (X + (Y + Z) ↑ʳ w) ⟨
                cast _ (cast (+-assoc X (Y + Z) W) (X + (Y + Z) ↑ʳ w))  ≡⟨ ≡.cong (cast _) X+[Y+Z]↑ʳw≡x↑ˡY+Z+W ⟩
                cast _ (x ↑ˡ Y + Z + W)                                 ≡⟨ ≡.cong (cast _) (↑ˡ-assoc x Y Z W) ⟩
                cast lemma₂ (cast lemma₁ (x ↑ˡ Y + (Z + W)))            ≡⟨ cast-trans lemma₁ lemma₂ (x ↑ˡ Y + (Z + W)) ⟩
                cast (≡.sym (+-assoc X Y (Z + W))) (x ↑ˡ Y + (Z + W))   ∎
  ... | inj₂ (w , w , ≡.refl , ≡.refl , ≡.refl) | inj₂ ([yz]w , y[zw] , ≡.refl , X+[Y+Z]↑ʳw≡X↑ʳ[yz]w , ≡.refl)
            = cast (≡.sym (+-assoc X Y (Z + W))) x[y[zw]]
            , eq
            , cast-involutive {X + Y + (Z + W)} {X + (Y + (Z + W))} (+-assoc X Y (Z + W)) _ (X ↑ʳ cast _ [yz]w)
          where
            open ≡-Reasoning
            lemma : X + (Y + Z + W) ≡ X + Y + (Z + W)
            lemma = ≡.trans (≡.cong (X +_) (+-assoc Y Z W)) (≡.sym (+-assoc X Y (Z + W)))
            eq : cast (+-assoc (X + Y) Z W) (X + Y + Z ↑ʳ w) ≡ cast (≡.sym (+-assoc X Y (Z + W))) (X ↑ʳ cast (+-assoc Y Z W) [yz]w)
            eq = begin
                cast _ (X + Y + Z ↑ʳ w)                                     ≡⟨ ≡.cong (cast _) (assoc-↑ʳ X Y Z w) ⟩
                cast (+-assoc (X + Y) Z W) (cast _ (X + (Y + Z) ↑ʳ w))      ≡⟨ cast-trans _ (+-assoc (X + Y) Z W) (X + (Y + Z) ↑ʳ w) ⟩
                cast _ (X + (Y + Z) ↑ʳ w)                                   ≡⟨ cast-trans (+-assoc X (Y + Z) W) _ (X + (Y + Z) ↑ʳ w) ⟨
                cast lemma (cast _ (X + (Y + Z) ↑ʳ w))                      ≡⟨ ≡.cong (cast _) X+[Y+Z]↑ʳw≡X↑ʳ[yz]w ⟩
                cast _ (X ↑ʳ [yz]w)                                         ≡⟨ cast-trans (≡.cong (X +_) (+-assoc Y Z W)) _ (X ↑ʳ [yz]w) ⟨
                cast _ (cast (≡.cong (X +_) (+-assoc Y Z W)) (X ↑ʳ [yz]w))  ≡⟨ ≡.cong (cast _) (cast-↑ʳ (+-assoc Y Z W) X [yz]w) ⟨
                cast _ (X ↑ʳ cast _ [yz]w)                                  ∎

  pentʳ
      : α⇒ {X + Y} ; α⇒ {X}
      ⇒ ((α⇒ {X} {Y} {Z} +₁ _≡_ {A = Fin W}) ; α⇒ {X}) ; (_≡_ {A = Fin X} +₁ (α⇒ {Y}))
  pentʳ {xyzw} {x[y[zw]]} (xy[zw] , ≡.refl , ≡.refl)
      = cast (≡.cong (X +_) (≡.sym (+-assoc Y Z W))) x[y[zw]]
      , (cast (≡.cong (_+ W) (+-assoc X Y Z)) xyzw , eq₁ , eq₂)
      , eq₃
    where
      eq₁ : ((λ [xy]z x[yz] → cast _ [xy]z ≡ x[yz]) +₁ _≡_) xyzw (cast {X + Y + Z + W} {X + (Y + Z) + W} (≡.cong (_+ W) (+-assoc X Y Z)) xyzw)
      eq₁ with splitAt (X + Y + Z) xyzw in eq
      ... | inj₁ xyz rewrite ≡.sym (splitAt⁻¹-↑ˡ eq) = lemma
              where
                lemma : ((λ [xy]z x[yz] → cast (+-assoc X Y Z) [xy]z ≡ x[yz]) +₁ _≡_) (xyz ↑ˡ W) (cast (≡.cong (_+ W) (+-assoc X Y Z)) (xyz ↑ˡ W))
                lemma rewrite ≡.sym (cast-↑ˡ (+-assoc X Y Z) xyz W) = ↑ˡ-REL ≡.refl
      ... | inj₂ w rewrite ≡.sym (splitAt⁻¹-↑ʳ eq) = lemma
              where
                open ≡-Reasoning
                lemma′ : X + Y + Z + W ≡ X + (Y + Z) + W
                lemma′ = ≡.cong (_+ W) (+-assoc X Y Z)
                rw : cast lemma′ (X + Y + Z ↑ʳ w) ≡ X + (Y + Z) ↑ʳ w
                rw = begin
                    cast _ (X + Y + Z ↑ʳ w)                                           ≡⟨ ≡.cong (cast _) (assoc-↑ʳ X Y Z w) ⟩
                    cast (≡.cong (_+ W) (+-assoc X Y Z)) (cast _ (X + (Y + Z) ↑ʳ w))  ≡⟨ cast-involutive (≡.cong (_+ W) (+-assoc X Y Z)) _ (X + (Y + Z) ↑ʳ w) ⟩
                    X + (Y + Z) ↑ʳ w                                                  ∎
                lemma : ((λ [xy]z → _≡_ (cast (+-assoc X Y Z) [xy]z)) +₁ _≡_) (X + Y + Z ↑ʳ w) (cast lemma′ (X + Y + Z ↑ʳ w))
                lemma rewrite rw = ↑ʳ-REL ≡.refl
      open ≡-Reasoning
      eq₂ : cast (+-assoc X (Y + Z) W) (cast _ xyzw) ≡ cast (≡.cong (X +_) (≡.sym (+-assoc Y Z W))) (cast (+-assoc X Y (Z + W)) (cast (+-assoc (X + Y) Z W) xyzw))
      eq₂ = begin
          cast _ (cast (≡.cong (_+ W) (+-assoc X Y Z)) xyzw)  ≡⟨ cast-trans (≡.cong (_+ W) (+-assoc X Y Z)) (+-assoc X (Y + Z) W) xyzw ⟩
          cast _ xyzw                   ≡⟨ cast-trans _ (≡.trans (+-assoc X Y (Z + W)) (≡.cong (X +_) (≡.sym (+-assoc Y Z W)))) xyzw ⟨
          cast (≡.trans (+-assoc X Y (Z + W)) (≡.cong (X +_) (≡.sym (+-assoc Y Z W)))) (cast (+-assoc (X + Y) Z W) xyzw)  ≡⟨ cast-trans (+-assoc X Y (Z + W)) (≡.cong (X +_) (≡.sym (+-assoc Y Z W))) (cast (+-assoc (X + Y) Z W) xyzw) ⟨
          cast (≡.cong (X +_) (≡.sym (+-assoc Y Z W))) (cast (+-assoc X Y (Z + W)) (cast _ xyzw)) ∎
      arg₁ : Fin (X + (Y + Z + W))
      arg₁ = cast (≡.cong (X +_) (≡.sym (+-assoc Y Z W))) (cast (+-assoc X Y (Z + W)) (cast (+-assoc (X + Y) Z W) xyzw))
      arg₂ : Fin (X + (Y + (Z + W)))
      arg₂ = cast (+-assoc X Y (Z + W)) (cast (+-assoc (X + Y) Z W) xyzw)
      eq₃ : (_≡_ {A = Fin X} +₁ (λ [yz]w y[zw] → cast (+-assoc Y Z W) [yz]w ≡ y[zw])) arg₁ arg₂
      eq₃ with splitAt X x[y[zw]] in eq
      ... | inj₁ x rewrite ≡.sym (splitAt⁻¹-↑ˡ eq) rewrite ≡.sym (↑ˡ-assoc x Y Z W) = ↑ˡ-REL ≡.refl
      ... | inj₂ yzw rewrite ≡.sym (splitAt⁻¹-↑ʳ eq) rewrite ≡.sym (cast-↑ʳ (≡.sym (+-assoc Y Z W)) X yzw) = ↑ʳ-REL (cast-involutive (+-assoc Y Z W) _ yzw)

  pentagon
      : ((α⇒ {X} {Y} {Z} +₁ _≡_ {A = Fin W}) ; α⇒ {X}) ; (_≡_ {A = Fin X} +₁ (α⇒ {Y}))
      ⇔ α⇒ {X + Y} ; α⇒ {X}
  pentagon = pentˡ , pentʳ

FinRel-Monoidal : Monoidal FinRel
FinRel-Monoidal = record
    { ⊗ = ⊗
    ; unit = 0
    ; unitorˡ = unitorˡ
    ; unitorʳ = unitorʳ
    ; associator = λ {X Y Z} → associator {X} {Y} {Z}
    ; unitorˡ-commute-from = λ {X} {Y} {R} → unitorˡ-commute-to X Y R
    ; unitorˡ-commute-to = λ {X} {Y} {R} → unitorˡ-commute-from X Y R
    ; unitorʳ-commute-from = λ {X} {Y} {R} → unitorʳ-commute-from X Y R
    ; unitorʳ-commute-to = λ {X} {Y} {R} → unitorʳ-commute-to X Y R
    ; assoc-commute-from = λ {X Y R X′ Y′ S X″ Y″ T} → assoc-commute-from X Y X′ Y′ X″ Y″ R S T
    ; assoc-commute-to = λ {X Y R X′ Y′ S X″ Y″ T} → assoc-commute-to X Y X′ Y′ X″ Y″ R S T
    ; triangle = λ {X Y} → triangle X Y
    ; pentagon = λ {X Y Z W} → pentagon X Y Z W
    }
