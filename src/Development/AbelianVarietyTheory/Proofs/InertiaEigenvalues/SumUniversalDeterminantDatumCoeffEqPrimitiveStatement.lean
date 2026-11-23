module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumUniversalDeterminantDatumCoeffEqPrimitive
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Matrix GlobalTheory.ExportSeries

theorem _root_.GlobalTheory.T.sum_universalDeterminantDatumCoeff_eq_primitive : ∀ (k C : Type) [Field k] [Finite k] [AddCommGroup C] [Fintype C] (r n : ℕ), r ≤ n → ∀ (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (y : Matrix (Fin r) (Fin n) k), ∑ c, univCoef β κ c y = prim y := by
  first | exact @GlobalTheory.ExportSeries.sum_univCoef_eq_prim | exact GlobalTheory.ExportSeries.sum_univCoef_eq_prim | (intros; apply GlobalTheory.ExportSeries.sum_univCoef_eq_prim <;> assumption)
