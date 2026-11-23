module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.FrobeniusNormBounds.ResiduePadicIntegersToIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.crystallineComparison.PinP

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem close_dvd (r : Res l K) [FiniteDimensional ℚ_[l] K] (f : ℕ) (hf : 0 < f) :
    ∃ N : ℕ, f ∣ N ∧ ∀ x : OK l K,
      ‖((okToOC l K x ^ l ^ N - PreTilt.untilt (r.s (r.ρ x)) : OC l) : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨fr, hfr, hfz⟩ := Pb.G3.res_frob r
  obtain ⟨c, hc1, hc⟩ := Pb.G3.exists_teichmuller_close r
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0)
  have hl : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hl) hc1
  have hN : ∀ (M : ℕ) (z : r.k), z ^ l ^ (fr * M) = z := by
    intro M z
    induction M with
    | zero => simp
    | succ M ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hfz]
  have hjN : j ≤ l ^ (fr * (f * j)) :=
    (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le.trans (Nat.pow_le_pow_right (Fact.out : l.Prime).pos
      ((Nat.le_mul_of_pos_left j hf).trans (Nat.le_mul_of_pos_left (f * j) hfr)))
  refine ⟨fr * (f * j), ⟨fr * j, by ring⟩, fun x => ?_⟩
  have ht : PreTilt.untilt (r.s (r.ρ x)) ^ l ^ (fr * (f * j)) = PreTilt.untilt (r.s (r.ρ x)) := by
    rw [← map_pow, ← map_pow, hN]
  have hp := Pb.G3.pow_close (okToOC l K x) (PreTilt.untilt (r.s (r.ρ x))) c (hc x) (fr * (f * j))
  rw [ht] at hp
  refine hp.trans (max_le le_rfl ?_)
  exact (pow_le_pow_of_le_one hc0 hc1.le hjN).trans hj.le

theorem teich_dvd (r : Res l K) [FiniteDimensional ℚ_[l] K] (f : ℕ) (hf : 0 < f) :
    ∃ N : ℕ, f ∣ N ∧ Pb.Mid.TeichmullerCongruence r N := by
  obtain ⟨N, hfN, hN⟩ := close_dvd r f hf
  refine ⟨N, hfN, fun n x => ?_⟩
  rw [Pb.Mid.phiQ_pow, Pb.G3.struct, ← Pb.G3.cong n _ _ (hN x)]
  rw [map_pow, map_pow]
  rfl

end CrystallineSemistableComparison.crystallineComparison.PinP
