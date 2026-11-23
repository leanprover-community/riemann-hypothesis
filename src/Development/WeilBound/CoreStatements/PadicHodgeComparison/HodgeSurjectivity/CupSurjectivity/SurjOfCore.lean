module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.ProperGenMap
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem surj_of_core (hC : CupLaws) (P : HTPre l K) (M : Model l K) (n : ℕ)
    (h : ∀ a' (x : Hdg M.q a' n), ∃ N : ℚ_[l], N ≠ 0 ∧ tgt hC x N ∈ Sp P M n) : Surj P M n := by
  intro m b z hz a' ha'
  funext s0
  let L : GF M n →ₗ[ℂ_[l]] ℂ_[l] :=
    { toFun := fun g => ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * g a ((b a).coord s)
      map_add' := by
        intro f g
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
        ring }
  have hL : Sp P M n ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, rfl⟩
    exact hz v
  obtain ⟨N, hN, hmem⟩ := h a' (b a' s0)
  have h0 : L (tgt hC (b a' s0) N) = 0 := hL hmem
  have hGe : ∀ s, Gx hC (b a' s0) ((b a').coord s) (oneH M.q) = (b a').coord s (b a' s0) := by
    intro s
    unfold Gx
    rw [dite_eq_left (Nat.zero_add a')]
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]
    rw [(hC _ _ M.q).2.2.2.1]
  have hGn : ∀ a, a ≠ a' → ∀ s, Gx hC (b a' s0) ((b a).coord s) (oneH M.q) = 0 := by
    intro a ha s
    unfold Gx
    rw [dite_eq_right (by omega)]
    rfl
  have hv : L (tgt hC (b a' s0) N) = z a' s0 * qC l N := by
    show ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * (qC l N * kC K (Gx hC (b a' s0) ((b a).coord s) (oneH M.q))) = _
    rw [Finset.sum_eq_single a']
    · simp only [hGe, Module.Basis.coord_apply, Module.Basis.repr_self]
      rw [Finset.sum_eq_single s0]
      · simp
      · intro s _ hs
        simp [Ne.symm hs]
      · simp
    · intro a _ ha
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [hGn a ha]
      simp
    · intro ha
      exact absurd (Finset.mem_range.2 (by omega)) ha
  rw [hv] at h0
  have hq : qC l N ≠ 0 := (map_ne_zero (qC l)).2 hN
  simpa [hq] using h0

end CrystallineSemistableComparison.Onto

end
