{-# OPTIONS --without-K --safe #-}


module TDPE.Gluing.Base {a} (𝒰 : Set a) where

{-
NOTE(@doctorn)
Proof of correctness of the TDPE algorithm via a formal categorical gluing construction.
For the proof, we're going to need the following ingredients:
 - a notion of cartesian closed category with chosen products and exponentials (𝒞𝒞𝒞);
-}
import TDPE.Gluing.Categories.Category.ContextualCartesian
import TDPE.Gluing.Categories.Category.ContextualCartesianClosed
{-
 - a notion of strictly structure prserving functor;
 - natural transformations between these;
 - an initial object in the induced 2-category;
 - construction of classifying objects;
 - a category of weakenings;
-}
import TDPE.Gluing.Weakenings
{-
 - a presheaf construction;
 - the definition of the glued universe;
 - proof that it supports the necessary structure;
 - construction of the interpretation;
 - construction of the normalisation map;
 - proof of the correctness condition.
-}
