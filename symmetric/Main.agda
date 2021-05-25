
module Main where

open import Utilities

-- The free symmetric skew monoidal category as a Hilbert-style
-- deductive system, called categorical calculus
open import Fsk

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
