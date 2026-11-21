import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdealClassArtinSymbolOfGlobalArtin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmLatticeGoodModelUnramified
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModChebOm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne

section
section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem chebOmSt_holds : ReciprocityTheory.ChartRestriction.L1.ChebOmSt := by
  intro E Ω _ _ _ _ _ S hS H hn ho _ σ
  obtain ⟨v, hv, hd, -, B, hB, -, φ, hφ, hφσ⟩ := GlobalTheory.Published.cheb_holds E Ω H ho hn σ hS.toFinset
  refine ⟨B, v, φ, ?_, by simpa using hv, ?_, ?_, ?_⟩
  · intro x
    rw [ValuationSubring.mem_nonunits_iff]
    exact hB x
  · have := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
  · refine ⟨hφ.1, fun x hx => ?_⟩
    rw [ValuationSubring.mem_nonunits_iff]
    exact hφ.2 x ((B.valuation_le_one_iff x).2 hx)
  · have := hn.conj_mem _ hφσ σ⁻¹
    simpa [mul_assoc] using this

end GlobalTheory
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chebotarev_degreeOne_valuationSubrings : ReciprocityTheory.ChartRestriction.L1.ChebOmSt := by
  atlas_forward_decl GlobalTheory.chebOmSt_holds
end

section
namespace GlobalTheory.Corev.CmTwoClosing

theorem cmGoodModel_of_globalArtinReciprocity (hA : GlobalTheory.Published.GlobalArtinReciprocity) : Formalism.L2.Th1.CM.CM2 :=
  GlobalTheory.T.cmLattice_good_model_unramified (GlobalTheory.T.exists_idealClass_artinSymbol_of_globalArtin hA) GlobalTheory.T.chebotarev_degreeOne_valuationSubrings

end GlobalTheory.Corev.CmTwoClosing
end
