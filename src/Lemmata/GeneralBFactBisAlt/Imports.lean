module

public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Bl.general_b_fact_bis_other

theorem goal1 :
  ∀ {K : Type} [inst : Field.{0} K] [NumberField.{0} K] {r n : Nat} (v : Fin n → Fin r → K) {x : Fin r → K},
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (Set.range.{0, 1} v)) x →
    Exists.{1} fun (d : Int) ↦
      And (Ne.{1} d 0)
        (Membership.mem.{0, 0} (Submodule.span.{0, 0} (NumberField.RingOfIntegers.{0} K) (Set.range.{0, 1} v))
          (HSMul.hSMul.{0, 0, 0} d x)) := by
  intro K _ _ r n v x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨d, hd, hd'⟩ := hy
    obtain ⟨e, he, he'⟩ := hz
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]
      exact zsmul_mem hd' e
    · rw [mul_smul]
      exact zsmul_mem he' d
  | smul c y _ hy =>
    obtain ⟨d, hd, hd'⟩ := hy
    obtain ⟨e, he, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c)).exists_integral_multiple
    refine ⟨e * d, mul_ne_zero he hd, ?_⟩
    have key : ((⟨e • c, hint⟩ : NumberField.RingOfIntegers K)) • (d • y) = (e * d) • (c • y) := by
      rw [← algebraMap_smul K]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]
      change ((e : K) * c) * ((d : K) * y i) = ((e * d : ℤ) : K) * (c * y i)
      push_cast
      ring
    rw [← key]
    exact Submodule.smul_mem _ _ hd'

end Bl.general_b_fact_bis_other
