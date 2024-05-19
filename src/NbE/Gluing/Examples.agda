{-# OPTIONS --without-K --safe #-}

module NbE.Gluing.Examples {a} (𝒰 : Set a) (ι : 𝒰) where

open import NbE.Gluing.Contexts 𝒰
open import NbE.Gluing.Syntax 𝒰

open import NbE.Gluing.Glue.Relation 𝒰 using (complete)

ι⁺ = ` ι `

Γ = 𝟙 · ((ι⁺ ⇒ ι⁺) ⇒ (ι⁺ ⇒ ι⁺)) · (ι⁺ ⇒ ι⁺) · ι⁺

f : 𝔗𝔪₀ Γ ((ι⁺ ⇒ ι⁺) ⇒ (ι⁺ ⇒ ι⁺))
f = p (p 𝓏)

g : 𝔗𝔪₀ Γ (ι⁺ ⇒ ι⁺)
g = p 𝓏

x : 𝔗𝔪₀ Γ ι⁺
x = 𝓏

LHS : 𝔗𝔪 Γ (𝟙 · ι⁺)
LHS = ! ∷ (f ⦅ g ⦆)  ⦅ x ⦆

RHS : 𝔗𝔪 Γ (𝟙 · ι⁺)
RHS = ! ∷ ((Λ (Λ ((p 𝓏 ⦅ 𝓏 ⦆) ⦅ p (p x) ⦆)) ⦅ f ⦆) ⦅ g ⦆)

example : LHS S.≈ RHS
example = complete S.refl

_ = {!example!}
