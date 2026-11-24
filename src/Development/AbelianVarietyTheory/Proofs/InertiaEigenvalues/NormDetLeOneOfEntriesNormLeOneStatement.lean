module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDetLeOneOfEntriesNormLeOne
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommOfBezout

@[expose] public section

open GlobalTheory.UnitDiscAlg

theorem _root_.GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ ≤ 1 := by
  first | exact @GlobalTheory.norm_det_le_one_of_entries_le_one | exact GlobalTheory.norm_det_le_one_of_entries_le_one | (intros; apply GlobalTheory.norm_det_le_one_of_entries_le_one <;> assumption)
