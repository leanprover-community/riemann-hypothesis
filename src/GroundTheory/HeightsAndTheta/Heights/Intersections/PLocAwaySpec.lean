module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocAwaySpec
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter


open Classical in
theorem LocAwaySpec.proof : LocAwaySpec.Statement := by
  intro R _ Φ _ φ S hrep
  choose f g hg hfg using hrep
  have hE0 : IsUnit (φ (∏ c ∈ S, g c)) := by
    rw [map_prod]
    exact (Finset.prod_ne_zero_iff.mpr fun c _ => hg c).isUnit
  refine ⟨∏ c ∈ S, g c, hE0, ?_, ?_⟩
  · intro c hc
    set E := ∏ d ∈ S, g d with hEdef
    have hE : IsUnit (φ E) := by
      rw [hEdef, map_prod]
      exact (Finset.prod_ne_zero_iff.mpr fun c _ => hg c).isUnit
    have hunitE : IsUnit (algebraMap R (Localization.Away E) E) :=
      IsLocalization.Away.algebraMap_isUnit E
    have hu : IsUnit (algebraMap R (Localization.Away E) (g c)) :=
      isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem g hc)) hunitE
    refine ⟨algebraMap R (Localization.Away E) (f c) * ↑hu.unit⁻¹, ?_⟩
    have h1 : (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ↑hu.unit = φ (g c) := by
      rw [IsUnit.unit_spec, IsLocalization.Away.lift_eq]
    have h2 : (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ↑hu.unit⁻¹ = (φ (g c))⁻¹ := by
      rw [← h1, ← map_units_inv]
    rw [map_mul, IsLocalization.Away.lift_eq, h2, ← div_eq_mul_inv]
    exact (hfg c).symm
  · intro B _ ψ hψ hker z hz
    rw [RingHom.mem_ker] at hz ⊢
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (∏ c ∈ S, g c)) z
    have hsφ := congrArg (IsLocalization.Away.lift (∏ c ∈ S, g c) hE0 : Localization.Away (∏ c ∈ S, g c) →+* Φ) hs
    simp only [map_mul, IsLocalization.Away.lift_eq, hz, zero_mul] at hsφ
    have ha : ψ a = 0 := hker (RingHom.mem_ker.mpr hsφ.symm)
    have hsψ := congrArg (IsLocalization.Away.lift (∏ c ∈ S, g c) hψ :
      Localization.Away (∏ c ∈ S, g c) →+* B) hs
    simp only [map_mul, IsLocalization.Away.lift_eq, ha] at hsψ
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp s.2
    have hsu : IsUnit (ψ (s : R)) := by
      rw [← hn, map_pow]
      exact hψ.pow n
    exact (hsu.mul_left_eq_zero).mp hsψ

end GroundTheory.Heights₂.Heights.Inter
