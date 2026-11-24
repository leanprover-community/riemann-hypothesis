module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.CuspRep

namespace GlobalTheory.KinfCompactness

theorem norm_entry_le_one {E : Type} [Field E] {a : ℕ} {M : Matrix (Fin a) (Fin a) (Cinf E)}
    (hM : star M * M = 1) (i j : Fin a) (w : NumberField.InfinitePlace E) : ‖M i j w‖ ≤ 1 := by
  have h := congrFun (congrFun (congrFun hM j) j) w
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Finset.sum_apply, Pi.mul_apply,
    Pi.star_apply, Pi.one_apply, Complex.star_def, Complex.conj_mul'] at h
  have h2 : ∑ x, ‖M x j w‖ ^ 2 = 1 := by exact_mod_cast h
  have h3 : ‖M i j w‖ ^ 2 ≤ 1 :=
    h2 ▸ Finset.single_le_sum (f := fun x => ‖M x j w‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  nlinarith [norm_nonneg (M i j w)]

theorem isClosed_unitaryGroup (E : Type) [Field E] (a : ℕ) :
    IsClosed (Matrix.unitaryGroup (Fin a) (Cinf E) : Set (Matrix (Fin a) (Fin a) (Cinf E))) := by
  have e : (Matrix.unitaryGroup (Fin a) (Cinf E) : Set (Matrix (Fin a) (Fin a) (Cinf E))) =
      {M | star M * M = 1} := by
    ext M; exact Matrix.mem_unitaryGroup_iff'
  rw [e]
  exact isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const

theorem compactSpace_Kinf (E : Type) [Field E] (a : ℕ) : CompactSpace (Kinf E a) := by
  let B : Set (Matrix (Fin a) (Fin a) (Cinf E)) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) 1
  have hB : IsCompact B :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hsub : (Matrix.unitaryGroup (Fin a) (Cinf E) : Set (Matrix (Fin a) (Fin a) (Cinf E))) ⊆ B := by
    intro M hM i _ j _ w _
    simpa [Metric.mem_closedBall, dist_zero_right] using
      norm_entry_le_one (Matrix.mem_unitaryGroup_iff'.1 hM) i j w
  exact isCompact_iff_compactSpace.1 (hB.of_isClosed_subset (isClosed_unitaryGroup E a) hsub)

end GlobalTheory.KinfCompactness
