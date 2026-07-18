{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Level using (Level; levelOfTerm)
open import Level using (_⊔_)

module Category.BinaryBiproducts {o ℓ e : Level} (𝒞 : Category o ℓ e) where

import Categories.Morphism.Reasoning as ⇒-Reasoning

open import Categories.Category.BinaryCoproducts 𝒞 using (BinaryCoproducts)
open import Categories.Category.BinaryProducts 𝒞 using (BinaryProducts)
open import Morphism.Zero using (IsZero⇒)
open import Object.Biproduct 𝒞 using (Biproduct; Biproduct⇒Product; Biproduct⇒Coproduct)

record BinaryBiproducts : Set (levelOfTerm 𝒞) where

  infixr 7 _⊕_

  field
    biproduct : ∀ {A B} → Biproduct A B

  open Category 𝒞

  private
    module biproduct {A} {B} = Biproduct (biproduct {A} {B})

  open biproduct using (π₁∘i₁≈id; π₂∘i₂≈id; permute; 𝟎⇒; 𝟎⇐; π₁∘i₂-isZero; π₂∘i₁-isZero; ⟨⟩-unique; []-unique) public

  _⊕_ : Obj → Obj → Obj
  A ⊕ B = Biproduct.A⊕B (biproduct {A} {B})

  module _ where
    binaryProducts : BinaryProducts
    binaryProducts = record { product = Biproduct⇒Product biproduct }
    open BinaryProducts binaryProducts public
      hiding (_×_)
      renaming (_×₁_ to infixr 10 _×₁_; ×-comm to ⊕-comm; ×-assoc to ⊕-assoc)

  module _ where
    binaryCoproducts : BinaryCoproducts
    binaryCoproducts = record { coproduct = Biproduct⇒Coproduct biproduct }
    open BinaryCoproducts binaryCoproducts public
      hiding (_+_)
      renaming (_+₁_ to infixr 10 _+₁_; +-comm to ⊕-comm′; +-assoc to ⊕-assoc′)

  private
    module π₂i₁ {A} {B} = IsZero⇒ (π₂∘i₁-isZero {A} {B})
    module π₁i₂ {A} {B} = IsZero⇒ (π₁∘i₂-isZero {A} {B})

  open ⇒-Reasoning 𝒞
  open HomReasoning

  π₁i₂≈π₂i₁ : {A B : Obj} → π₁ ∘ i₂ ≈ π₂ {A} {B} ∘ i₁
  π₁i₂≈π₂i₁ {A} {B} = begin
      π₁ ∘ i₂                             ≈⟨ identityʳ ⟨
      (π₁ ∘ i₂) ∘ id                      ≈⟨ π₁i₂.constant id ((π₁ ∘ i₂) ∘ (π₂ ∘ i₁)) ⟩
      (π₁ ∘ i₂) ∘ ((π₁ ∘ i₂) ∘ (π₂ ∘ i₁)) ≈⟨ sym-assoc ⟩
      ((π₁ ∘ i₂) ∘ (π₁ ∘ i₂)) ∘ (π₂ ∘ i₁) ≈⟨ π₂i₁.coconstant ((π₁ ∘ i₂) ∘ (π₁ ∘ i₂)) id ⟩
      id ∘ π₂ ∘ i₁                        ≈⟨ pullˡ identityˡ ⟩
      π₂ ∘ i₁ ∎

  module _ {A B C : Obj} where

    π₁i₂-absorbˡ : (f : A ⇒ C) → f ∘ 𝟎⇐ {A} {B} ≈ 𝟎⇐
    π₁i₂-absorbˡ f = begin
        f ∘ 𝟎⇐          ≈⟨ π₁i₂.coconstant f (𝟎⇐ ∘ 𝟎⇒) ⟩
        (𝟎⇐ ∘ 𝟎⇒) ∘ 𝟎⇐  ≈⟨ assoc ⟩
        𝟎⇐ ∘ (𝟎⇒ ∘ 𝟎⇐)  ≈⟨ π₁i₂.constant (𝟎⇒ ∘ 𝟎⇐) id ⟩
        𝟎⇐ ∘ id         ≈⟨ identityʳ ⟩
        𝟎⇐              ∎

    π₁i₂-absorbʳ : (f : C ⇒ B) → 𝟎⇐ {A} {B} ∘ f ≈ 𝟎⇐
    π₁i₂-absorbʳ f = begin
        𝟎⇐ ∘ f          ≈⟨ π₁i₂.constant f (𝟎⇒ ∘ 𝟎⇐) ⟩
        𝟎⇐ ∘ 𝟎⇒ ∘ 𝟎⇐    ≈⟨ sym-assoc ⟩
        (𝟎⇐ ∘ 𝟎⇒) ∘ 𝟎⇐  ≈⟨ π₁i₂.coconstant (𝟎⇐ ∘ 𝟎⇒) id ⟩
        id ∘ 𝟎⇐         ≈⟨ identityˡ ⟩
        𝟎⇐              ∎

    π₂i₁-absorbˡ : (f : B ⇒ C) → f ∘ 𝟎⇒ {A} {B} ≈ 𝟎⇒
    π₂i₁-absorbˡ f = begin
        f ∘ 𝟎⇒          ≈⟨ π₂i₁.coconstant f (𝟎⇒ ∘ 𝟎⇐) ⟩
        (𝟎⇒ ∘ 𝟎⇐) ∘ 𝟎⇒  ≈⟨ assoc ⟩
        𝟎⇒ ∘ (𝟎⇐ ∘ 𝟎⇒)  ≈⟨ π₂i₁.constant (𝟎⇐ ∘ 𝟎⇒) id ⟩
        𝟎⇒ ∘ id         ≈⟨ identityʳ ⟩
        𝟎⇒              ∎

    π₂i₁-absorbʳ : (f : C ⇒ A) → 𝟎⇒ {A} {B} ∘ f ≈ 𝟎⇒
    π₂i₁-absorbʳ f = begin
        𝟎⇒ ∘ f          ≈⟨ π₂i₁.constant f (𝟎⇐ ∘ 𝟎⇒) ⟩
        𝟎⇒ ∘ 𝟎⇐ ∘ 𝟎⇒    ≈⟨ sym-assoc ⟩
        (𝟎⇒ ∘ 𝟎⇐) ∘ 𝟎⇒  ≈⟨ π₂i₁.coconstant (𝟎⇒ ∘ 𝟎⇐) id ⟩
        id ∘ 𝟎⇒         ≈⟨ identityˡ ⟩
        𝟎⇒              ∎

  module _ {A B : Obj} (f g : A ⇒ B) where

    π₁∘+₁ : π₁ ∘ f +₁ g ≈ f ∘ π₁
    π₁∘+₁ = begin
        π₁ ∘ [ i₁ ∘ f , i₂ ∘ g ]          ≈⟨ ∘[] ⟩
        [ π₁ ∘ i₁ ∘ f , π₁ ∘ i₂ ∘ g ]     ≈⟨ []-congˡ sym-assoc ⟩
        [ π₁ ∘ i₁ ∘ f , (π₁ ∘ i₂) ∘ g ]   ≈⟨ []-cong₂ (cancelˡ π₁∘i₁≈id) (π₁i₂-absorbʳ g) ⟩
        [ f , π₁ ∘ i₂ ]                   ≈⟨ []-cong₂ (insertʳ π₁∘i₁≈id) (Equiv.sym (π₁i₂-absorbˡ f)) ⟩
        [ (f ∘ π₁) ∘ i₁ , f ∘ π₁ ∘ i₂ ]   ≈⟨ []-congˡ sym-assoc ⟩
        [ (f ∘ π₁) ∘ i₁ , (f ∘ π₁) ∘ i₂ ] ≈⟨ +-g-η ⟩
        f ∘ π₁                            ∎

    π₂∘+₁ : π₂ ∘ f +₁ g ≈ g ∘ π₂
    π₂∘+₁ = begin
        π₂ ∘ [ i₁ ∘ f , i₂ ∘ g ]          ≈⟨ ∘[] ⟩
        [ π₂ ∘ i₁ ∘ f , π₂ ∘ i₂ ∘ g ]     ≈⟨ []-congʳ sym-assoc ⟩
        [ (π₂ ∘ i₁) ∘ f , π₂ ∘ i₂ ∘ g ]   ≈⟨ []-cong₂ (π₂i₁-absorbʳ f) (cancelˡ π₂∘i₂≈id) ⟩
        [ π₂ ∘ i₁ , g ]                   ≈⟨ []-cong₂ (Equiv.sym (π₂i₁-absorbˡ g)) (insertʳ π₂∘i₂≈id) ⟩
        [ g ∘ π₂ ∘ i₁ , (g ∘ π₂) ∘ i₂ ]   ≈⟨ []-congʳ sym-assoc ⟩
        [ (g ∘ π₂) ∘ i₁ , (g ∘ π₂) ∘ i₂ ] ≈⟨ +-g-η ⟩
        g ∘ π₂                            ∎

    ×₁-+₁ : f ×₁ g ≈ f +₁ g
    ×₁-+₁ = ⟨⟩-unique π₁∘+₁ π₂∘+₁

  ∇-assoc : {A : Obj} → ∇ {A} ∘ ∇ +₁ id ≈ ∇ ∘ id +₁ ∇ ∘ +-assocˡ
  ∇-assoc = begin
      ∇ ∘ ∇ +₁ id             ≈⟨ ∇∘+₁ ⟩
      [ ∇ , id ]              ≈⟨ []∘+-assocʳ ⟨
      [ id , ∇ ] ∘ +-assocˡ   ≈⟨ pushˡ (Equiv.sym ∇∘+₁) ⟩
      ∇ ∘ id +₁ ∇ ∘ +-assocˡ  ∎

  Δ-assoc : {A : Obj} → id ×₁ Δ ∘ Δ {A} ≈ assocˡ ∘ Δ ×₁ id ∘ Δ
  Δ-assoc = begin
      id ×₁ Δ ∘ Δ           ≈⟨ ×₁∘Δ ⟩
      ⟨ id , Δ ⟩            ≈⟨ assocˡ∘⟨⟩ ⟨
      assocˡ ∘ ⟨ Δ , id ⟩   ≈⟨ refl⟩∘⟨ ×₁∘Δ ⟨
      assocˡ ∘ Δ ×₁ id ∘ Δ  ∎

  module _ {A : Obj} where

    ∇-identityˡ : ∇ ∘ i₂ ≈ id {A}
    ∇-identityˡ = inject₂

    ∇-identityʳ : ∇ ∘ i₁ ≈ id {A}
    ∇-identityʳ = inject₁

    Δ-identityˡ : π₂ ∘ Δ ≈ id {A}
    Δ-identityˡ = project₂

    Δ-identityʳ : π₁ ∘ Δ ≈ id {A}
    Δ-identityʳ = project₁

  ∇-comm : {A : Obj} → ∇ {A} ∘ +-swap ≈ ∇
  ∇-comm = []∘+-swap

  Δ-comm : {A : Obj} → swap ∘ Δ {A} ≈ Δ
  Δ-comm = swap∘⟨⟩

  ⇒∇ : {A B : Obj} {f : A ⇒ B} → f ∘ ∇ ≈ ∇ ∘ f +₁ f
  ⇒∇ {f = f} = begin
      f ∘ ∇       ≈⟨ ∘∇ ⟩
      [ f , f ]   ≈⟨ ∇∘+₁ ⟨
      ∇ ∘ f +₁ f  ∎

  ⇒Δ : {A B : Obj} {f : A ⇒ B} → Δ ∘ f ≈ f ×₁ f ∘ Δ
  ⇒Δ {A} {B} {f} = begin
      Δ ∘ f       ≈⟨ Δ∘ ⟩
      ⟨ f , f ⟩   ≈⟨ ×₁∘Δ ⟨
      f ×₁ f ∘ Δ  ∎
