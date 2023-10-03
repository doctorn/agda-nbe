{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Transport.Functor where

open import Level
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)

open import TDPE.Gluing.Transport

private
  variable
    o o' ℓ ℓ' e e' : Level


module _
  {𝒞 : Category o ℓ e}
  {𝒟 : Category o' ℓ' e'}
  (F : Functor 𝒞 𝒟)
  where

  private
    module 𝒞 = Category 𝒞
    module F = Functor F

    variable
      A A' B B' : 𝒞.Obj

  transport-F : (f : Category._⇒_ 𝒞 A B) (p : A ≡ A') (q : B ≡ B')
                → F.₁ (transport 𝒞 p q f) ≡ transport 𝒟 (PE.cong F.₀ p) (PE.cong F.₀ q) (Functor.₁ F f)
  transport-F f PE.refl PE.refl = PE.refl

  transport′-F : (f : Category._⇒_ 𝒞 A' B') (p : A ≡ A') (q : B ≡ B')
                → F.₁ (transport′ 𝒞 p q f) ≡ transport′ 𝒟 (PE.cong F.₀ p) (PE.cong F.₀ q) (Functor.₁ F f)
  transport′-F f PE.refl PE.refl = PE.refl
