{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel)

module TDPE.Gluing.Util.Equivalence {a ℓ} {A : Set a} (R : Rel A ℓ) where

open import Level

open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Symmetric; Transitive)

private
  variable
    x y z : A

infix 4 _~_ _≈_

data _~_ : Rel A (a ⊔ ℓ) where
  fwd : R x y → x ~ y
  bwd : R y x → x ~ y

data _≈_ : Rel A (a ⊔ ℓ) where
  refl : x ≈ x
  step : x ≈ y → y ~ z → x ≈ z

unit : R x y → x ≈ y
unit p = step refl (fwd p)

sym-unit : R y x → x ≈ y
sym-unit p = step refl (bwd p)

flip : Symmetric _~_
flip (fwd p) = bwd p
flip (bwd p) = fwd p

sym : Symmetric _≈_
sym p = I p refl
  where I : x ≈ y → z ≈ y → z ≈ x
        I refl        q = q
        I (step ps p) q = I ps (step q (flip p))

trans : Transitive _≈_
trans p refl        = p
trans p (step qs q) = step (trans p qs) q

is-equiv : IsEquivalence _≈_
is-equiv = record { refl = refl ; sym = sym ; trans = trans }

setoid : Setoid a (a ⊔ ℓ)
setoid = record { Carrier = A ; _≈_ = _≈_ ; isEquivalence = is-equiv }

import Relation.Binary.Reasoning.Setoid as Reasoning

module ≈-Reasoning = Reasoning setoid
