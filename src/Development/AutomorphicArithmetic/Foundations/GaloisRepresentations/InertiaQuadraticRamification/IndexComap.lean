module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem indexComap : IndexComap := by
  intro Γ Γ' _ _ f H H' hc hle hp ⟨τ, hτ, hτ'⟩
  have hN : H'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ H' :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    have h2 : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
    rw [h2]
    exact H'.mul_mem h1 hn
  rw [Subgroup.relIndex_comap]
  set J := (H.comap f).map f with hJ
  have hJH : J ≤ H := Subgroup.map_comap_le _ _
  have hmul : H'.relIndex (H' ⊔ J) * (H' ⊔ J).relIndex H = H'.relIndex H :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hle hJH)
  rw [Subgroup.relIndex_sup_left] at hmul
  have hne : H'.relIndex J ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact hτ' (h ⟨τ, hτ, rfl⟩)
  exact (hp.eq_one_or_self_of_dvd _ ⟨_, hmul.symm⟩).resolve_left hne

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
