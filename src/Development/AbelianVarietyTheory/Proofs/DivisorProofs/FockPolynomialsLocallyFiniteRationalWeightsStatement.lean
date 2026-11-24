module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights : ∀ (p q r s : ℕ), (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct1 p q r s) W) ∧ P ∈ ⨆ μ : Ix p q → ℚ, wtSub (fockAct1 p q r s) μ) ∧ (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct2 p q r s) W) ∧ P ∈ ⨆ μ : Ix r s → ℚ, wtSub (fockAct2 p q r s) μ) := by
  first | exact @GlobalTheory.FockPolGK.pol_locFin_weights | exact GlobalTheory.FockPolGK.pol_locFin_weights | (intros; apply GlobalTheory.FockPolGK.pol_locFin_weights <;> assumption)
