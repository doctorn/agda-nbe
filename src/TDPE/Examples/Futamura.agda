module TDPE.Examples.Futamura where

-- Futamura projection for a simple interpreter (Jeremy Yallop)

open import Data.Nat using (ℕ; _+_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import TDPE.Base
open import TDPE.Eval using (normalise)

-- type of variables
𝕍 = 𝒪
-- type of Church encoding of expressions
𝔼 = (𝒪 ⇒ 𝒪 ⇒ 𝒪) ⇒ (𝒪 ⇒ 𝒪) ⇒ (𝕍 ⇒ 𝒪) ⇒ 𝒪

-- Church encoding of variables
var : 𝔗𝔪 𝟙 (𝕍 ⇒ 𝔼)
var = Λ (Λ (Λ (Λ (𝓏 ⦅ π (π (π 𝓏)) ⦆)))) -- λ x add int var.var x

-- Church encoding of addition
add : 𝔗𝔪 𝟙 (𝔼 ⇒ 𝔼 ⇒ 𝔼)
add = Λ (Λ (Λ (Λ (Λ (add' ⦅ x ⦅ add' ⦆ ⦅ int ⦆ ⦅ var' ⦆ ⦆ ⦅ y ⦅ add' ⦆ ⦅ int ⦆ ⦅ var' ⦆ ⦆)))))
  -- λx y add int var.add (x add int var) (y add int var)
  where x = π (π (π (π 𝓏)))
        y = π (π (π 𝓏))
        add' = π (π 𝓏)
        int = π 𝓏
        var' = 𝓏

-- Church encoding of literals
int : 𝔗𝔪 𝟙 (𝒪 ⇒ 𝔼)
int = Λ (Λ (Λ (Λ ((π 𝓏) ⦅ π (π (π 𝓏)) ⦆))))

-- evaluator
eval : 𝔗𝔪 𝟙 (𝔼 ⇒ (𝕍 ⇒ 𝒪) ⇒ 𝒪)
eval = Λ (Λ (exp ⦅ 𝓁 _+_ ⦆ ⦅ Λ 𝓏 ⦆ ⦅ 𝓏 ⦆))
  where exp = π 𝓏

-- example
example : 𝔗𝔪 𝟙 ((𝒪 ⇒ 𝒪) ⇒ 𝒪)
example = eval ⦅ add ⦅ add ⦅ int ⦅ 𝓁 3 ⦆ ⦆ ⦅ var ⦅ 𝓁 0 ⦆ ⦆ ⦆ ⦅ int ⦅ 𝓁 2 ⦆ ⦆ ⦆

residualised : 𝔗𝔪 𝟙 ((𝒪 ⇒ 𝒪) ⇒ 𝒪)
residualised = Λ (𝓁 (λ env → suc (suc (suc (_+_ (env 0) 2)))) ⦅ 𝓏 ⦆)

_ : normalise example ≡ residualised
_ = refl
