
module Main where

-- =======================================================================
-- "Coherence via Focusing for Symmetric Skew Monoidal Categories"
-- Niccolò Veltri

-- Agda formalization associated to the WoLLIC'21 paper
-- =======================================================================

open import Utilities

-- The free symmetric skew monoidal category as a Hilbert-style
-- deductive system, called categorical calculus
open import Fsk

-- The categorical calculus satisfy the universal property of the free
-- symm. skew monoidal category
open import UniversalProperty

-- The cut-free sequent calculus
open import SeqCalc

-- Equations satisfied by the admissible cut
open import CutEqs

-- Soundness
open import Sound
open import EqSound

-- Completeness
open import Complete
open import EqComplete
open import StrongComplete

-- Proof of bijection between derivations in categorical calculus and
-- derivations in sequent calculus
open import SoundComplete
open import CompleteSound

-- The focused sequent calculus
open import Focusing
