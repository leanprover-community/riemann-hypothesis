module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupMapMulRightUnitary
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.isRiemannianHaarOnSubgroup_map_mul_right_unitary : ∀ (n : ℕ) (ε : Fin n → Bool) (M : Subgroup (Formalism.REAL.UJ ε)) (d : ℕ) (μ : Measure (Formalism.REAL.UJ ε)), IsClosed (M : Set (Formalism.REAL.UJ ε)) → IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) d μ → ∀ l ∈ M, l ∈ maxK ε → μ.map (fun g => g * l) = μ := by
  first | exact @GlobalTheory.GaugeRightInv.isGaugeSub_map_mul_right | exact GlobalTheory.GaugeRightInv.isGaugeSub_map_mul_right | (intros; apply GlobalTheory.GaugeRightInv.isGaugeSub_map_mul_right <;> assumption)
