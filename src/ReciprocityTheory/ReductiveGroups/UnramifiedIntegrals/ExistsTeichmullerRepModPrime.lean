module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KurDefs
import Mathlib.Algebra.Order.Star.Int
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsPowerMulUnitNorm
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FrobFixNegOne
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormNatCastClOfNotDvd

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem kmu_le_kur {x : ℂ_[l]} (hx : x ∈ Kmu l) : x ∈ MaximalUnramifiedExtension l := (Kmu l).le_topologicalClosure hx

theorem tch_mem_kur {ξ : ℂ_[l]} (hξ : ξ ∈ Tch l) : ξ ∈ MaximalUnramifiedExtension l := by
  rcases Set.mem_insert_iff.mp hξ with rfl | h
  · exact (MaximalUnramifiedExtension l).zero_mem
  · exact kmu_le_kur l (Subfield.subset_closure h)

theorem norm_eq_of_norm_sub_lt_max {x y : ℂ_[l]} (h : ‖x - y‖ < max ‖x‖ ‖y‖) : ‖x‖ = ‖y‖ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 := _root_.ReciprocityTheory.ChartRestriction.L1.norm_sub_le_max_Cl l x (x - y)
    rw [sub_sub_cancel] at h1
    rw [max_eq_right hlt.le] at h
    have h2 : max ‖x‖ ‖x - y‖ < ‖y‖ := max_lt hlt h
    linarith
  · have h1 := _root_.ReciprocityTheory.ChartRestriction.L1.norm_sub_le_max_Cl l y (y - x)
    rw [sub_sub_cancel] at h1
    rw [max_eq_left hgt.le, norm_sub_rev] at h
    have h2 : max ‖y‖ ‖y - x‖ < ‖x‖ := max_lt hgt h
    linarith

theorem norm_prime_lt_one_complexPadic : ‖(l : ℂ_[l])‖ < 1 := by
  rw [_root_.ReciprocityTheory.ChartRestriction.L1.norm_l_Cl l]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : Nat.Prime l).one_lt)

theorem kur_approx {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (e : ℝ) (he : 0 < e) :
    ∃ y ∈ Kmu l, ‖x - y‖ < e := by
  have hc : x ∈ closure ((Kmu l : Set ℂ_[l])) := hx
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp hc e he
  exact ⟨y, hy, by rwa [dist_eq_norm] at hd⟩

end ReciprocityTheory.ChartRestriction.L1
