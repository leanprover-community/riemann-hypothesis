module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

theorem UpperTheory.Reformulated.B.Qi6.det_ne_zero :
    ∀ {F : Type} [inst : NormedField F] [IsUltrametricDist F] {m : ℕ}
    (t : F),
    ‖t‖ = (1 : ℝ) →
      ∀ (E : Matrix (Fin m) (Fin m) F),
        (∀ (a b : Fin m), ‖E a b‖ < (1 : ℝ)) → (t • (1 : Matrix (Fin m) (Fin m) F) + E).det ≠ (0 : F) := by
  intro F _ _ m t ht E hE hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  haveI : Nonempty (Fin m) := ⟨i⟩
  obtain ⟨a, ha⟩ := Finite.exists_max (fun j => ‖v j‖)
  have hpos : 0 < ‖v a‖ := lt_of_lt_of_le (norm_pos_iff.mpr hi) (ha i)
  have hrow : t * v a = -∑ b, E a b * v b := by
    have h := congrFun hMv a
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    exact eq_neg_of_add_eq_zero_left h
  obtain ⟨b, -, hb⟩ := IsUltrametricDist.exists_norm_finsetSum_le (Finset.univ : Finset (Fin m))
    (fun b => E a b * v b)
  have h1 : ‖v a‖ = ‖∑ b, E a b * v b‖ := by
    rw [← norm_neg (∑ b, E a b * v b), ← hrow, norm_mul, ht, one_mul]
  have h2 : ‖E a b * v b‖ < ‖v a‖ := by
    rw [norm_mul]
    calc ‖E a b‖ * ‖v b‖ ≤ ‖E a b‖ * ‖v a‖ :=
          mul_le_mul_of_nonneg_left (ha b) (norm_nonneg _)
      _ < 1 * ‖v a‖ := mul_lt_mul_of_pos_right (hE a b) hpos
      _ = ‖v a‖ := one_mul _
  exact absurd (h1.le.trans hb) (not_le.mpr h2)
