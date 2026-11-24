module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PoissonSummationInfinitePlaceGaussianLattice
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.poisson_summation_infinitePlaceGaussian_lattice : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (L : Submodule ℤ (VecInf E j)) [DiscreteTopology L], IsZLattice ℝ L → Summable (fun x : L => gaussV E j x) ∧ Summable (fun y : dualAt E j L => gaussV E j y) ∧ ∑' x : L, gaussV E j x = (covAt E j L)⁻¹ * ∑' y : dualAt E j L, gaussV E j y ∧ ∫ x, gaussV E j x = 1 := by
  first | exact @GlobalTheory.FlagBase.poisson_gaussV | exact GlobalTheory.FlagBase.poisson_gaussV | (intros; apply GlobalTheory.FlagBase.poisson_gaussV <;> assumption)
