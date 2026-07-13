{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Cocartesian.Monoidal using (module CocartesianMonoidal)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Functor using (Functor; _∘F_) renaming (id to IdF)
open import Categories.Functor.Cartesian using (CartesianF)
open import Category.Cartesian.Instance.CMonoids using (CMonoids-CC)
open import Category.Dagger.Semiadditive using (IdempotentSemiadditiveDagger)
open import Category.Instance.CMonoids using (CMonoids; CMonoidHomomorphism)
open import Level using (Level; suc)

open CartesianMonoidal using (monoidal)
open CocartesianMonoidal using (+-monoidal)

module Functor.Instance.WiringDiagram.System
    {o ℓ e o′ ℓ′ e′ : Level}
    {c : Level}
    {𝒞 : Category o ℓ e}
    {S : IdempotentSemiadditiveDagger 𝒞}
    (let private module S = IdempotentSemiadditiveDagger S)
    (let 𝒞-CC = record { cartesian = S.cartesian })
    (F : CartesianF 𝒞-CC (CMonoids-CC {c} {c}))
  where

import Data.System.Monoidal as Sys-⊗
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra using (CommutativeMonoid)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Instance.Properties.Setoids.CCC using (Setoids-CCC)
open import Categories.Category.Monoidal.Utilities using (module Shorthands)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor.Cartesian.Properties using (isMonoidalFunctor)
open import Categories.Functor.Monoidal using (MonoidalFunctor)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Categories.Morphism.Reasoning.Iso (CMonoids c c) using (switch-fromtoˡ)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper)
open import Categories.Object.Product (CMonoids c c) using (Product; IsProduct)
open import Data.Product using (_,_)
open import Data.Product.Function.NonDependent.Setoid using (_×-function_; proj₁ₛ; proj₂ₛ; swapₛ)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Setoid using (_⇒ₛ_; ∣_∣)
open import Data.Setoid.Unit using (⊤ₛ)
open import Data.System using (System; _≤_; Systems[_,_]; Systems-SMC; discrete)
open import Data.Unit.Polymorphic using (tt)
open import Data.WiringDiagram.Core S using (Box; WiringDiagram; _□_; _⧈_; _⌻_; _≈-⧈_)
open import Data.WiringDiagram.Directed S using (DWD; Pulsh)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_; id; _$_)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (_∙_)

module F = CartesianF F

module 𝒞 = Category 𝒞

open Box
open CMonoidHomomorphism
open Category 𝒞 using (Obj; _⇒_; _∘_)
open CommutativeMonoid using (setoid; Carrier; refl; sym)
open Func
open IdempotentSemiadditiveDagger S using (_⊕₀_; _⊕₁_; △)
open Shorthands (+-monoidal S.cocartesian) using (α⇒)
open Shorthands (monoidal S.cartesian) using () renaming (α⇒ to α⇒′)
open WiringDiagram using (input; output)

_⟦⊕⟧_ : {A B : Obj} → Carrier (F.₀ A) → Carrier (F.₀ B) → Carrier (F.₀ (A ⊕₀ B))
_⟦⊕⟧_ {A} {B} a b = ⟦ F.×-iso.to A B ⟧ (a , b)

⟦⊕⟧-cong
    : {A B : Obj}
      (let module FA = CommutativeMonoid (F.₀ A))
      (let module FB = CommutativeMonoid (F.₀ B))
      (let module F[A+B] = CommutativeMonoid (F.₀ (A ⊕₀ B)))
      {a a′ : Carrier (F.₀ A)}
      {b b′ : Carrier (F.₀ B)}
    → a FA.≈ a′
    → b FB.≈ b′
    → a ⟦⊕⟧ b F[A+B].≈ a′ ⟦⊕⟧ b′
⟦⊕⟧-cong {A} {B} ≈a ≈b = ⟦⟧-cong (F.×-iso.to A B) (≈a , ≈b)

⟦⊕⟧-commute
    : {A B C D : Obj}
      {f : A ⇒ B}
      {g : C ⇒ D}
      (a : Carrier (F.₀ A))
      (c : Carrier (F.₀ C))
    → (let open CommutativeMonoid (F.₀ (B ⊕₀ D)) using (_≈_))
    → ⟦ F.₁ (f ⊕₁ g) ⟧ (a ⟦⊕⟧ c) ≈ ⟦ F.₁ f ⟧ a ⟦⊕⟧ ⟦ F.₁ g ⟧ c
⟦⊕⟧-commute {A} {B} {C} {D} {f} {g} a c- = begin
    ⟦ F.₁ (f ⊕₁ g) ⟧ (a ⟦⊕⟧ c-)   ≈⟨ F.F-resp-≈ (S.×₁-⊕₁ f g) (a ⟦⊕⟧ c-) ⟨
    ⟦ F.₁ (f ×₁ g) ⟧ (a ⟦⊕⟧ c-)   ≈⟨ ⊗-F.⊗-homo.sym-commute (f , g) (a , c-) ⟩
    ⟦ F.₁ f ⟧ a ⟦⊕⟧ ⟦ F.₁ g ⟧ c-  ∎
  where
    open ≈-Reasoning (setoid (F.₀ (B ⊕₀ D)))
    open CommutativeMonoid (F.₀ (B ⊕₀ D)) using (_≈_)
    module 𝒞-CC = CartesianCategory 𝒞-CC
    open 𝒞-CC using (_×₁_)
    ⊗-F : MonoidalFunctor 𝒞-CC.monoidalCategory (CMonoids-CC.monoidalCategory {c} {c})
    ⊗-F = isMonoidalFunctor {C = 𝒞-CC} {CMonoids-CC {c} {c}} F
    module ⊗-F = MonoidalFunctor ⊗-F

⟦△⟧ : {A : Obj}
      (a : Carrier (F.₀ A))
    → (let open CommutativeMonoid (F.₀ (A ⊕₀ A)) using (_≈_))
    → ⟦ F.₁ △ ⟧ a ≈ a ⟦⊕⟧ a
⟦△⟧ {A} a = begin
    ⟦ F.₁ △ ⟧ a                           ≈⟨ F.identity ((⟦ F.₁ △ ⟧ a)) ⟨
    ⟦ F.₁ 𝒞.id ⟧ (⟦ F.₁ △ ⟧ a)            ≈⟨ F.F-resp-≈ ⊕.identity (⟦ F.₁ △ ⟧ a) ⟨
    ⟦ F.₁ (𝒞.id ⊕₁ 𝒞.id) ⟧ (⟦ F.₁ △ ⟧ a)  ≈⟨ F.homomorphism a ⟨
    ⟦ F.₁ (𝒞.id ⊕₁ 𝒞.id ∘ △) ⟧ a          ≈⟨ switch-fromtoˡ (F.×-iso A A) {h = F.₁ (𝒞.id ⊕₁ 𝒞.id ∘ △)} {k = CMonoids-CC.⟨ F.₁ 𝒞.id , F.₁ 𝒞.id ⟩} (F.F-resp-⟨⟩ 𝒞.id 𝒞.id) a ⟩
    ⟦ F.₁ 𝒞.id ⟧ a ⟦⊕⟧ ⟦ F.₁ 𝒞.id ⟧ a     ≈⟨ ⟦⊕⟧-cong (F.identity a) (F.identity a) ⟩
    a ⟦⊕⟧ a                               ∎
  where
    open ≈-Reasoning (setoid (F.₀ (A ⊕₀ A)))
    open Product (F.F-prod A A) using (⟨⟩-cong₂)
    module ⊕ = Functor S.⊕

⟦α⇒⟧
    : {A B C : Obj}
      (a : Carrier (F.₀ A))
      (b : Carrier (F.₀ B))
      (c : Carrier (F.₀ C))
    → (let open CommutativeMonoid (F.₀ (A ⊕₀ (B ⊕₀ C))) using (_≈_))
    → ⟦ F.₁ α⇒ ⟧ ((a ⟦⊕⟧ b) ⟦⊕⟧ c) ≈ a ⟦⊕⟧ (b ⟦⊕⟧ c)
⟦α⇒⟧ {A} {B} {C} a b c- = begin
    ⟦ F.₁ α⇒ ⟧ ((a ⟦⊕⟧ b) ⟦⊕⟧ c-)   ≈⟨ F.F-resp-≈ S.≈α⇒ ((a ⟦⊕⟧ b) ⟦⊕⟧ c-) ⟨
    ⟦ F.₁ α⇒′ ⟧ ((a ⟦⊕⟧ b) ⟦⊕⟧ c-)  ≈⟨ ⊗-F.associativity ((a , b) , c-) ⟩
    a ⟦⊕⟧ (b ⟦⊕⟧ c-)                ∎
  where
    open ≈-Reasoning (setoid (F.₀ (A ⊕₀ (B ⊕₀ C))))
    module 𝒞-CC = CartesianCategory 𝒞-CC
    ⊗-F : MonoidalFunctor 𝒞-CC.monoidalCategory (CMonoids-CC.monoidalCategory {c} {c})
    ⊗-F = isMonoidalFunctor {C = 𝒞-CC} {CMonoids-CC {c} {c}} F
    module ⊗-F = MonoidalFunctor ⊗-F

⟦⊕⟧-congˡ
    : {A B : Obj}
      (let module FB = CommutativeMonoid (F.₀ B))
      (let module F[A+B] = CommutativeMonoid (F.₀ (A ⊕₀ B)))
      {a : Carrier (F.₀ A)}
      {b b′ : Carrier (F.₀ B)}
    → b FB.≈ b′
    → a ⟦⊕⟧ b F[A+B].≈ a ⟦⊕⟧ b′
⟦⊕⟧-congˡ {A} ≈b = ⟦⊕⟧-cong (refl (F.₀ A)) ≈b


⟦⊕⟧-congʳ
    : {A B : Obj}
      (let module FA = CommutativeMonoid (F.₀ A))
      (let module F[A+B] = CommutativeMonoid (F.₀ (A ⊕₀ B)))
      {a a′ : Carrier (F.₀ A)}
      {b : Carrier (F.₀ B)}
    → a FA.≈ a′
    → a ⟦⊕⟧ b F[A+B].≈ a′ ⟦⊕⟧ b
⟦⊕⟧-congʳ {B = B} ≈a = ⟦⊕⟧-cong ≈a (refl (F.₀ B))

module _ {Aᵢ Aₒ Bᵢ Bₒ : Obj} (i : Aₒ ⊕₀ Bᵢ ⇒ Aᵢ) (o : Aₒ ⇒ Bₒ) where

  A-System B-System : Set (suc c)
  A-System = System (setoid (F.₀ Aᵢ)) (F.₀ Aₒ)
  B-System = System (setoid (F.₀ Bᵢ)) (F.₀ Bₒ)

  A-Systems B-Systems : Category (suc c) c c
  A-Systems = Systems[ setoid (F.₀ Aᵢ) , F.₀ Aₒ ]
  B-Systems = Systems[ setoid (F.₀ Bᵢ) , F.₀ Bₒ ]

  I⇒ : CMonoidHomomorphism c c (F.₀ (Aₒ ⊕₀ Bᵢ)) (F.₀ Aᵢ)
  I⇒ = F.₁ i

  O⇒ : CMonoidHomomorphism c c (F.₀ Aₒ) (F.₀ Bₒ)
  O⇒ = F.₁ o

  wire : A-System → B-System
  wire sys = record
      { S = X.S
      ; fₛ = λg (eval ∙ (X.fₛ ×-function Id X.S) ∙ ⟨ func I⇒ ∙ func (F.×-iso.to Aₒ Bᵢ) ∙ X.fₒ ×-function Id (setoid (F.₀ Bᵢ)) ∙ swapₛ , π₂ ⟩)
      ; fₒ = func O⇒ ∙ X.fₒ
      }
    where
      module X = System sys
      open CartesianClosed (Setoids-CCC c) using (λg; eval; cartesian)
      open Cartesian cartesian using (π₁; π₂; ⟨_,_⟩)

  wire-≤ : {A B : A-System} → A ≤ B → wire A ≤ wire B
  wire-≤ {A} {B} A≤B = record
      { ⇒S = ⇒S
      ; ≗-fₛ = ≗-wfₛ
      ; ≗-fₒ = ≗-wfₒ
      }
    where
      module A = System A
      module B = System B
      module wA = System (wire A)
      module wB = System (wire B)
      open System
      open _≤_ A≤B
      ≗-wfₛ
          : (i : Carrier (F.₀ Bᵢ))
            (s : ∣ wA.S ∣)
          → ⇒S ⟨$⟩ wA.fₛ′ i s B.S.≈ wB.fₛ′ i (⇒S ⟨$⟩ s)
      ≗-wfₛ i s = begin
          ⇒S ⟨$⟩ A.fₛ′ (⟦ I⇒ ⟧ (A.fₒ′ s ⟦⊕⟧ i)) s             ≈⟨ ≗-fₛ (⟦ I⇒ ⟧ (A.fₒ′ s ⟦⊕⟧ i)) s ⟩
          B.fₛ′ (⟦ I⇒ ⟧ (A.fₒ′ s ⟦⊕⟧ i)) (⇒S ⟨$⟩ s)           ≈⟨ cong B.fₛ (⟦⟧-cong I⇒ (⟦⊕⟧-congʳ (≗-fₒ s))) ⟩
          B.fₛ′ (⟦ I⇒ ⟧ (B.fₒ′ (⇒S ⟨$⟩ s) ⟦⊕⟧ i)) (⇒S ⟨$⟩ s)  ∎
        where
          open ≈-Reasoning B.S
      ≗-wfₒ
          : (s : ∣ wA.S ∣)
          → (open CommutativeMonoid (F.₀ Bₒ) using (_≈_))
          → wA.fₒ′ s ≈ wB.fₒ′ (⇒S ⟨$⟩ s)
      ≗-wfₒ s = ⟦⟧-cong O⇒ (≗-fₒ s)

  Wire : Functor A-Systems B-Systems
  Wire = record
      { F₀ = wire
      ; F₁ = wire-≤
      ; identity = λ {X} → System.S.refl X
      ; homomorphism = λ {Z = Z} → System.S.refl Z
      ; F-resp-≈ = id
      }

identity : {Aᵢ Aₒ : Obj} → Wire {Aᵢ} {Aₒ} S.p₂ 𝒞.id ≃ IdF
identity {Aᵢ} {Aₒ} = niHelper record
    { η = ≤X
    ; η⁻¹ = ≥X
    ; commute = λ {_ Y} _ → System.S.refl Y
    ; iso = λ X → record
        { isoˡ = System.S.refl X
        ; isoʳ = System.S.refl X
        }
    }
  where
    module _ (X : System (setoid (F.₀ Aᵢ)) (F.₀ Aₒ)) where
      module X = System X
      open IsProduct F.F-resp-× using (project₂)
      ≤X : wire S.p₂ 𝒞.id X ≤ X
      ≤X = record
          { ⇒S = Id X.S
          ; ≗-fₛ = λ i s → cong X.fₛ (project₂ (X.fₒ′ s , i))
          ; ≗-fₒ = λ s → F.identity (X.fₒ′ s)
          }
      ≥X : X ≤ wire S.p₂ 𝒞.id X
      ≥X = record
          { ⇒S = Id X.S
          ; ≗-fₛ = λ i s → X.S.sym (cong X.fₛ (project₂ (X.fₒ′ s , i)))
          ; ≗-fₒ = λ s → sym (F.₀ Aₒ) (F.identity (X.fₒ′ s))
          }

homomorphism
    : {Xᵢ Xₒ Yᵢ Yₒ Zᵢ Zₒ : Obj}
      {fᵢ : Xₒ ⊕₀ Yᵢ ⇒ Xᵢ}
      {fₒ : Xₒ ⇒ Yₒ}
      {gᵢ : Yₒ ⊕₀ Zᵢ ⇒ Yᵢ}
      {gₒ : Yₒ ⇒ Zₒ}
    → Wire (input ((gᵢ ⧈ gₒ) ⌻ (fᵢ ⧈ fₒ))) (output ((gᵢ ⧈ gₒ) ⌻ (fᵢ ⧈ fₒ)))
    ≃ Wire gᵢ gₒ ∘F Wire fᵢ fₒ
homomorphism {Xᵢ} {Xₒ} {Yᵢ} {Yₒ} {Zᵢ} {Zₒ} {fᵢ} {fₒ} {gᵢ} {gₒ} = niHelper record
    { η = η
    ; η⁻¹ = η⁻¹
    ; commute = λ {_ Y} _ → System.S.refl Y
    ; iso = λ X → record
        { isoˡ = System.S.refl X
        ; isoʳ = System.S.refl X
        }
    }
  where
    module _ (X : System (setoid (F.₀ Xᵢ)) (F.₀ Xₒ)) where
      module X = System X
      module _ (i : Carrier (F.₀ Zᵢ)) (s : ∣ X.S ∣) where
        lem₁
            : (let open CommutativeMonoid (F.₀ Yᵢ) using (_≈_))
            → ⟦ F.₁ (gᵢ ∘ fₒ ⊕₁ 𝒞.id) ⟧ (X.fₒ′ s ⟦⊕⟧ i) ≈ ⟦ F.₁ gᵢ ⟧ (⟦ F.₁ fₒ ⟧ (X.fₒ′ s) ⟦⊕⟧ i)
        lem₁ = begin
            ⟦ F.₁ (gᵢ ∘ fₒ ⊕₁ 𝒞.id) ⟧ (X.fₒ′ s ⟦⊕⟧ i)             ≈⟨ F.homomorphism (X.fₒ′ s ⟦⊕⟧ i) ⟩
            ⟦ F.₁ gᵢ ⟧ (⟦ F.₁ (fₒ ⊕₁ 𝒞.id) ⟧ (X.fₒ′ s ⟦⊕⟧ i))     ≈⟨ ⟦⟧-cong (F.₁ gᵢ) (⟦⊕⟧-commute (X.fₒ′ s) i) ⟩
            ⟦ F.₁ gᵢ ⟧ (⟦ F.₁ fₒ ⟧ (X.fₒ′ s) ⟦⊕⟧ ⟦ F.₁ 𝒞.id ⟧ i)  ≈⟨ ⟦⟧-cong (F.₁ gᵢ) (⟦⊕⟧-congˡ (F.identity i)) ⟩
            ⟦ F.₁ gᵢ ⟧ (⟦ F.₁ fₒ ⟧ (X.fₒ′ s) ⟦⊕⟧ i)               ∎
          where
            open ≈-Reasoning (setoid (F.₀ Yᵢ))
        lem₂
            : (let open CommutativeMonoid (F.₀ (Xₒ ⊕₀ (Xₒ ⊕₀ Zᵢ))) using (_≈_))
            → ⟦ F.₁ (α⇒ 𝒞.∘ △ ⊕₁ 𝒞.id) ⟧ (X.fₒ′ s ⟦⊕⟧ i)
            ≈ X.fₒ′ s ⟦⊕⟧ (X.fₒ′ s ⟦⊕⟧ i)
        lem₂ = begin
            ⟦ F.₁ (α⇒ 𝒞.∘ △ ⊕₁ 𝒞.id) ⟧ (X.fₒ′ s ⟦⊕⟧ i)          ≈⟨ F.homomorphism (X.fₒ′ s ⟦⊕⟧ i) ⟩
            ⟦ F.₁ α⇒ ⟧ (⟦ F.₁ (△ ⊕₁ 𝒞.id) ⟧ (X.fₒ′ s ⟦⊕⟧ i))    ≈⟨ ⟦⟧-cong (F.₁ α⇒) (⟦⊕⟧-commute (X.fₒ′ s) i) ⟩
            ⟦ F.₁ α⇒ ⟧ (⟦ F.₁ △ ⟧ (X.fₒ′ s) ⟦⊕⟧ ⟦ F.₁ 𝒞.id ⟧ i) ≈⟨ ⟦⟧-cong (F.₁ α⇒) (⟦⊕⟧-cong (⟦△⟧ (X.fₒ′ s)) (F.identity i)) ⟩
            ⟦ F.₁ α⇒ ⟧ ((X.fₒ′ s ⟦⊕⟧ X.fₒ′ s) ⟦⊕⟧ i)            ≈⟨ ⟦α⇒⟧ (X.fₒ′ s) (X.fₒ′ s) i ⟩
            X.fₒ′ s ⟦⊕⟧ (X.fₒ′ s ⟦⊕⟧ i)                         ∎
          where
            open ≈-Reasoning (setoid (F.₀ (Xₒ ⊕₀ (Xₒ ⊕₀ Zᵢ))))
        lem₃
            : (let open CommutativeMonoid (F.₀ (Xₒ ⊕₀ Yᵢ)) using (_≈_))
            → ⟦ F.₁ (𝒞.id ⊕₁ (gᵢ ∘ fₒ ⊕₁ 𝒞.id) 𝒞.∘ α⇒ 𝒞.∘ △ ⊕₁ 𝒞.id) ⟧ (X.fₒ′ s ⟦⊕⟧ i)
            ≈ (X.fₒ′ s ⟦⊕⟧ (⟦ F.₁ gᵢ ⟧ (⟦ F.₁ fₒ ⟧ (X.fₒ′ s) ⟦⊕⟧ i)))
        lem₃ = begin
            ⟦ F.₁ (𝒞.id ⊕₁ (gᵢ ∘ fₒ ⊕₁ 𝒞.id) 𝒞.∘ α⇒ 𝒞.∘ △ ⊕₁ 𝒞.id) ⟧ (X.fₒ′ s ⟦⊕⟧ i)          ≈⟨ F.homomorphism (X.fₒ′ s ⟦⊕⟧ i) ⟩
            ⟦ F.₁ (𝒞.id ⊕₁ (gᵢ ∘ fₒ ⊕₁ 𝒞.id)) ⟧ (⟦ F.₁ (α⇒ 𝒞.∘ △ ⊕₁ 𝒞.id) ⟧ (X.fₒ′ s ⟦⊕⟧ i))  ≈⟨ ⟦⟧-cong (F.₁ (𝒞.id ⊕₁ (gᵢ ∘ fₒ ⊕₁ 𝒞.id))) lem₂ ⟩
            ⟦ F.₁ (𝒞.id ⊕₁ (gᵢ ∘ fₒ ⊕₁ 𝒞.id)) ⟧ (X.fₒ′ s ⟦⊕⟧ (X.fₒ′ s ⟦⊕⟧ i))                 ≈⟨ ⟦⊕⟧-commute (X.fₒ′ s) (X.fₒ′ s ⟦⊕⟧ i) ⟩
            ⟦ F.₁ 𝒞.id ⟧ (X.fₒ′ s) ⟦⊕⟧ ⟦ F.₁ (gᵢ ∘ fₒ ⊕₁ 𝒞.id) ⟧ (X.fₒ′ s ⟦⊕⟧ i)              ≈⟨ ⟦⊕⟧-cong (F.identity (X.fₒ′ s)) lem₁ ⟩
            X.fₒ′ s ⟦⊕⟧ ⟦ F.₁ gᵢ ⟧ (⟦ F.₁ fₒ ⟧ (X.fₒ′ s) ⟦⊕⟧ i)                               ∎
          where
            open ≈-Reasoning (setoid (F.₀ (Xₒ ⊕₀ Yᵢ)))
        ≗-fₛ
            : X.fₛ′ (⟦ F.₁ (fᵢ ∘ 𝒞.id ⊕₁ (gᵢ ∘ fₒ ⊕₁ 𝒞.id) 𝒞.∘ α⇒ 𝒞.∘ △ ⊕₁ 𝒞.id) ⟧ (X.fₒ′ s ⟦⊕⟧ i)) s X.S.≈
              X.fₛ′ (⟦ F.₁ fᵢ ⟧ (X.fₒ′ s ⟦⊕⟧ (⟦ F.₁ gᵢ ⟧ (⟦ F.₁ fₒ ⟧ (X.fₒ′ s) ⟦⊕⟧ i)))) s
        ≗-fₛ = cong X.fₛ $ begin
            ⟦ F.₁ (fᵢ ∘ 𝒞.id ⊕₁ (gᵢ ∘ fₒ ⊕₁ 𝒞.id) 𝒞.∘ α⇒ 𝒞.∘ △ ⊕₁ 𝒞.id) ⟧ (X.fₒ′ s ⟦⊕⟧ i)         ≈⟨ F.homomorphism (X.fₒ′ s ⟦⊕⟧ i) ⟩
            ⟦ F.₁ fᵢ ⟧ (⟦ F.₁ (𝒞.id ⊕₁ (gᵢ ∘ fₒ ⊕₁ 𝒞.id) 𝒞.∘ α⇒ 𝒞.∘ △ ⊕₁ 𝒞.id) ⟧ (X.fₒ′ s ⟦⊕⟧ i)) ≈⟨ ⟦⟧-cong (F.₁ fᵢ) lem₃ ⟩
            ⟦ F.₁ fᵢ ⟧ (X.fₒ′ s ⟦⊕⟧ ⟦ F.₁ gᵢ ⟧ (⟦ F.₁ fₒ ⟧ (X.fₒ′ s) ⟦⊕⟧ i))                      ∎
          where
            open ≈-Reasoning (setoid (F.₀ Xᵢ))
      η : wire (input ((gᵢ ⧈ gₒ) ⌻ (fᵢ ⧈ fₒ))) (output ((gᵢ ⧈ gₒ) ⌻ (fᵢ ⧈ fₒ))) X ≤ wire gᵢ gₒ (wire fᵢ fₒ X)
      η = record
          { ⇒S = Id X.S
          ; ≗-fₛ = ≗-fₛ
          ; ≗-fₒ = λ s → F.homomorphism (X.fₒ′ s)
          }
      η⁻¹ : wire gᵢ gₒ (wire fᵢ fₒ X) ≤ wire (input ((gᵢ ⧈ gₒ) ⌻ (fᵢ ⧈ fₒ))) (output ((gᵢ ⧈ gₒ) ⌻ (fᵢ ⧈ fₒ))) X
      η⁻¹ = record
          { ⇒S = Id X.S
          ; ≗-fₛ = λ i s → X.S.sym (≗-fₛ i s)
          ; ≗-fₒ = λ s → sym (F.₀ Zₒ) (F.homomorphism (X.fₒ′ s))
          }

Sys-resp-≈
    : {A B : Box}
      {f g : WiringDiagram A B}
    → f ≈-⧈ g
    → Wire (input f) (output f) ≃ Wire (input g) (output g)
Sys-resp-≈ {A} {B} {f} {g} f≈g = niHelper record
    { η = wf≤wg
    ; η⁻¹ = wg≤wf
    ; commute = λ {_ Y} _ → System.S.refl Y
    ; iso = λ X → record
        { isoˡ = System.S.refl X
        ; isoʳ = System.S.refl X
        }
    }
  where
    module A = Box A
    module B = Box B
    module _ (X : System (setoid (F.₀ A.ᵢ)) (F.₀ A.ₒ)) where

      fᵢ gᵢ : A.ₒ ⊕₀ B.ᵢ ⇒ A.ᵢ
      fᵢ = input f
      gᵢ = input g

      fₒ gₒ : A.ₒ ⇒ B.ₒ
      fₒ = output f
      gₒ = output g

      open _≈-⧈_ f≈g

      module X = System X

      wf≤wg : wire fᵢ fₒ X ≤ wire gᵢ gₒ X
      wf≤wg = record
          { ⇒S = Id X.S
          ; ≗-fₛ = λ i s → cong X.fₛ (F.F-resp-≈ ≈i (X.fₒ′ s ⟦⊕⟧ i))
          ; ≗-fₒ = λ s → F.F-resp-≈ ≈o (X.fₒ′ s)
          }

      wg≤wf : wire (input g) (output g) X ≤ wire (input f) (output f) X
      wg≤wf = record
          { ⇒S = Id X.S
          ; ≗-fₛ = λ i s → X.S.sym (cong X.fₛ (F.F-resp-≈ ≈i (X.fₒ′ s ⟦⊕⟧ i)))
          ; ≗-fₒ = λ s → sym (F.₀ B.ₒ) (F.F-resp-≈ ≈o (X.fₒ′ s))
          }

Sys : Functor DWD (Cats (suc c) c c)
Sys = record
    { F₀ = λ (i □ o) → Systems[ setoid (F.₀ i) , F.₀ o ]
    ; F₁ = λ (input ⧈ output) → Wire input output
    ; identity = identity
    ; homomorphism = homomorphism
    ; F-resp-≈ = Sys-resp-≈
    }
