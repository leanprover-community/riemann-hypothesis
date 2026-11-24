module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsOfSeparable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open Filter Topology

theorem _root_.GlobalTheory.T.exists_lifts_of_separable_reduction : ∀ (D : ℕ) (P : Polynomial (MvPowerSeries (Fin D) ℂ)), P.Monic → (P.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ))).Separable → ∃ θ : Fin P.natDegree → MvPowerSeries (Fin D) ℂ, Function.Injective θ ∧ ∀ j, P.IsRoot (θ j) := by
  first | exact @GlobalTheory.HenselSplitPS.exists_lifts_of_separable | exact GlobalTheory.HenselSplitPS.exists_lifts_of_separable | (intros; apply GlobalTheory.HenselSplitPS.exists_lifts_of_separable <;> assumption)
