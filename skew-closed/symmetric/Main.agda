{-# OPTIONS --rewriting #-}

module Main where

open import Utilities

-- The free symmetric skew closed category as a Hilbert-style
-- deductive system, called categorical calculus
open import Fsk

-- The cut-free sequent calculus
open import SeqCalc

-- Equations satisfied by the admissible cut rules
open import CutEqs


-- Soundness
open import Sound

-- Completeness
open import Complete

-- Adequacy: Proof of bijection between derivations in categorical
-- calculus and derivations in sequent calculus
open import Adequacy1
open import Adequacy2

-- The focused sequent calculus
open import Focusing

