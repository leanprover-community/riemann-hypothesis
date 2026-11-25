module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KurDefs
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsPowerMulUnitNorm
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsTeichmullerRepModPrime
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormLeOneOfIntegralInt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormNatCastClOfNotDvd

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem tch_of_integral (δ : ℂ_[l]) (hδ : IsIntegral (Rmu l) δ) : ∃ ξ ∈ Tch l, ‖δ - ξ‖ < 1 := by
  have hZ := KE.isIntegral_int_of_rmu (l := l) δ hδ
  have h1 : ‖δ‖ ≤ 1 := KE.norm_le_one_of_integral_int δ hZ
  have hl : ‖(l : ℂ_[l])‖ < 1 := by
    rw [norm_l_Cl (l := l)]
    have h1l : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact inv_lt_one_of_one_lt₀ h1l
  obtain ⟨f, hf, hfr⟩ := KE.frob_fix_of_integral l (Fact.out : l.Prime) hl δ hZ
  obtain ⟨ξ, hξ, hd⟩ := tch_near (l := l) δ h1 f hf _ hfr le_rfl
  exact ⟨ξ, hξ, lt_of_le_of_lt hd hfr⟩

end ReciprocityTheory.ChartRestriction.L1
