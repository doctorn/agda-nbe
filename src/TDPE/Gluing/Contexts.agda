{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Contexts {a} (𝒰 : Set a) where

data 𝒰ᵀ : Set a where
  `_` : 𝒰 → 𝒰ᵀ
  _⇒_ : 𝒰ᵀ → 𝒰ᵀ → 𝒰ᵀ

infixl 5 _·_

data ℭ : Set a where
  𝟙 : ℭ
  _·_ : ℭ → 𝒰ᵀ → ℭ
