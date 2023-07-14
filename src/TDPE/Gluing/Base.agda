{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Base where

-- NOTE(@doctorn)
-- Proof of correctness of the TDPE algorithm via a formal categorical gluing construction.
-- For the proof, we're going to need the following ingredients:

--- a notion of cartesian closed category with chosen products and exponentials (𝒞𝒞𝒞);
import TDPE.Gluing.Categories.Category.ContextualCartesian
import TDPE.Gluing.Categories.Category.ContextualCartesianClosed

--- a notion of strictly structure prserving functor;

--- natural transformations between these;

--- an initial object in the induced 2-category;
import TDPE.Gluing.Syntax

--- construction of classifying objects;

--- a category of weakenings;
import TDPE.Gluing.Weakenings

--- a presheaf construction;
import TDPE.Gluing.Categories.Category.Instance.Presheaves

--- the definition of the glued universe;
import TDPE.Gluing.Glue.Base

--- proof that it supports the necessary structure;
import TDPE.Gluing.Glue.CartesianClosed

--- construction of the interpretation;
import TDPE.Gluing.Interpretation

--- construction of the normalisation map and proof of the correctness.
import TDPE.Gluing.Glue.Relation
