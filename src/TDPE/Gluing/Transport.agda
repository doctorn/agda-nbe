{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)

module TDPE.Gluing.Transport {o ℓ e} (𝒞 : Category o ℓ e) where

open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open Category 𝒞

private
  variable
    A A' A'' B B' B'' C C' : Obj

transport : A ≡ A' → B ≡ B' → A ⇒ B → A' ⇒ B'
transport PE.refl PE.refl f = f

transport′ : A ≡ A' → B ≡ B' → A' ⇒ B' → A ⇒ B
transport′ p q f = transport (PE.sym p) (PE.sym q) f

transport-∘ : {p : A ≡ A'} {q : B ≡ B'} {r : C ≡ C'} (g : B ⇒ C) (f : A ⇒ B)
              → transport q r g ∘ transport p q f ≡ transport p r (g ∘ f)
transport-∘ {p = PE.refl} {PE.refl} {PE.refl} g f = PE.refl

transport-≈ : {p : A ≡ A'} {q : B ≡ B'} (f : A ⇒ B) (f' : A ⇒ B)
              → f ≈ f'
              → transport p q f ≈ transport p q f'
transport-≈ {p = PE.refl} {PE.refl} f f' x = x

flip-transport : {p : A ≡ A'} {q : B ≡ B'} (f : A ⇒ B) (f' : A' ⇒ B')
                 → transport p q f ≈ f'
                 → f ≈ transport′ p q f'
flip-transport {p = PE.refl} {PE.refl} f f' x = x

flip-transport′ : {p : A ≡ A'} {q : B ≡ B'} (f : A ⇒ B) (f' : A' ⇒ B')
                 → f ≈ transport′ p q f'
                 → transport p q f ≈ f'
flip-transport′ {p = PE.refl} {PE.refl} f f' x = x

transport-trans : {p₁ : A ≡ A'} {p₂ : A' ≡ A''} {q₁ : B ≡ B'} {q₂ : B' ≡ B''} (f : A ⇒ B)
                  → transport p₂ q₂ (transport p₁ q₁ f) ≡ transport (PE.trans p₁ p₂) (PE.trans q₁ q₂) f
transport-trans {p₁ = PE.refl} {PE.refl} {PE.refl} {PE.refl} f = PE.refl

transport-≡₂ : {p p' : A ≡ A'} {q q' : B ≡ B'} (f : A ⇒ B) → p ≡ p' → q ≡ q' → transport p q f ≡ transport p' q' f
transport-≡₂ f PE.refl PE.refl = PE.refl

trans-refl : (p : A ≡ A') → PE.trans p PE.refl ≡ p
trans-refl PE.refl = PE.refl