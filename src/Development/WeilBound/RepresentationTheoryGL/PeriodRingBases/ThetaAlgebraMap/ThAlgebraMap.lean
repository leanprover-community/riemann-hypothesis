module

public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

namespace EstT

variable {l : ℕ} [Fact l.Prime]

theorem qB_mem_ainf (q : ℚ_[l]) : qB l q ∈ Ainf' l := by
  have key : ∀ z : ℤ_[l], qB l (algebraMap ℤ_[l] ℚ_[l] z) ∈ Ainf' l := fun z => by
    have e : qB l (algebraMap ℤ_[l] ℚ_[l] z) = zB l z := IsLocalization.lift_eq _ _
    rw [e]
    exact Subring.subset_closure (Or.inl ⟨ainfMap l (zA l z), rfl⟩)
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors ℤ_[l]) q
  have hs : (s : ℤ_[l]) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hsu := PadicInt.unitCoeff_spec hs
  set u := PadicInt.unitCoeff hs
  set n := (s : ℤ_[l]).valuation
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have e : IsLocalization.mk' ℚ_[l] z s =
      algebraMap ℤ_[l] ℚ_[l] (z * ↑u⁻¹) * ((l : ℚ_[l])⁻¹) ^ n := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, hsu]
    simp only [map_mul, map_pow, map_natCast]
    have hx : ((l : ℚ_[l])⁻¹) ^ n * (l : ℚ_[l]) ^ n = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hl0, one_pow]
    have hu : algebraMap ℤ_[l] ℚ_[l] (↑u⁻¹ : ℤ_[l]) * algebraMap ℤ_[l] ℚ_[l] (u : ℤ_[l]) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-(algebraMap ℤ_[l] ℚ_[l] z) * ((l : ℚ_[l])⁻¹) ^ n * (l : ℚ_[l]) ^ n) * hu -
      algebraMap ℤ_[l] ℚ_[l] z * hx
  show qB l (IsLocalization.mk' ℚ_[l] z s) ∈ _
  rw [e, map_mul, map_pow]
  exact (Ainf' l).mul_mem (key _) ((Ainf' l).pow_mem (Subring.subset_closure (Or.inr rfl)) _)

end EstT

end period_ring_base
