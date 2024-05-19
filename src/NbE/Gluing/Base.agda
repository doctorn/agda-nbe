{-# OPTIONS --without-K --safe #-}

module NbE.Gluing.Base where

-- NOTE(@doctorn)
-- Proof of correctness of the NbE algorithm via a formal categorical gluing construction.
-- For the proof, we're going to need the following ingredients:

--- a notion of cartesian closed category with chosen products and exponentials (𝒞𝒞𝒞);
import NbE.Gluing.Categories.Category.ContextualCartesian
import NbE.Gluing.Categories.Category.ContextualCartesianClosed

--- a notion of strictly structure prserving functor;

--- natural transformations between these;

--- an initial object in the induced 2-category;
import NbE.Gluing.Syntax

--- construction of classifying objects;

--- a category of weakenings;
import NbE.Gluing.Weakenings

--- a presheaf construction;
import NbE.Gluing.Categories.Category.Instance.Presheaves

--- the definition of the glued universe;
import NbE.Gluing.Glue.Base

--- proof that it supports the necessary structure;
import NbE.Gluing.Glue.CartesianClosed

--- construction of the interpretation;
import NbE.Gluing.Interpretation

--- construction of the normalisation map and proof of the correctness.
import NbE.Gluing.Glue.Relation
