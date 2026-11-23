module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliCoeffDualWeylEqCoeffProd
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink

theorem _root_.GlobalTheory.T.capelliCoeff_dualWeyl_eq_coeff_prod : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ), ∃ F : ℕ → FreeAlgebra O (Fin N × Fin N), ∀ ν : Fin N → ℕ, Antitone ν → ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν, ∀ k : ℕ, evalPol O N (F k) f = (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((ν a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • f := by
  first | exact @GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl | exact GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl | (intros; apply GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl <;> assumption)
