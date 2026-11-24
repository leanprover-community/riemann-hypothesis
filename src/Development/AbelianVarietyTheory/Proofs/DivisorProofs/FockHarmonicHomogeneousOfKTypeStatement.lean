module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fockHarmonic_homogeneous_of_KType : ∀ (p q r s : ℕ), (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P → P ∈ harm1 p q r s → ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧ (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P → P ∈ harm2 p q r s → ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d) := by
  first | exact @GlobalTheory.FockAlg.harmonic_homog_of_type | exact GlobalTheory.FockAlg.harmonic_homog_of_type | (intros; apply GlobalTheory.FockAlg.harmonic_homog_of_type <;> assumption)
