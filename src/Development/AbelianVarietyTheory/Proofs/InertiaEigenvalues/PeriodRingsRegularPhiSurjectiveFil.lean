import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBcrisBasicTheoremsProofStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TiedRegular

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem regular_onto (h : GlobalTheory.Published.FontaineBcris) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) :
    (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧
    (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧
    ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 := by
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  refine ⟨fun K b hb hg => ?_, fun u => ?_, fun K w => ?_⟩
  · have hu : IsUnit (T.eB b) := by
      refine h.regular C K (T.eB b) (fun h0 => hb (T.eB.injective (h0.trans (map_zero _).symm))) fun g hgK => ?_
      obtain ⟨x, hx⟩ := hg g hgK
      refine ⟨x, ?_⟩
      rw [← T.actB, hx, Algebra.smul_def, map_mul,
        IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B, hC.u]
      rfl
    simpa using hu.map T.eB.symm
  · obtain ⟨x, hx⟩ := GlobalTheory.Published.FontaineBcris.oneSubPhiOnto_of_filZero (h.ontoFilZero C) (T.eB u)
    refine ⟨T.eB.symm x, T.eB.injective ?_⟩
    rw [map_sub, T.frob, RingEquiv.apply_symm_apply, hx]
  · obtain ⟨x, hx, hF⟩ := h.fundOnto C (T.eD w)
    refine ⟨T.eB.symm x, T.eB.injective ?_, ?_⟩
    · rw [T.frob, RingEquiv.apply_symm_apply, hx]
    · rw [T.fil, map_sub, hC.ι, RingEquiv.apply_symm_apply]
      exact hF

end GlobalTheory.MemLoc.TiedRegular
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_regular_surjections_of_fontaine_theorem : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧ (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧ ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 := by
  atlas_forward_decl GlobalTheory.MemLoc.TiedRegular.regular_onto
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.MemLoc

theorem tied_regular_and_onto :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
      (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 →
        (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧
      (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧
      ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 :=
  GlobalTheory.T.bcris_regular_surjections_of_fontaine_theorem GlobalTheory.T.fontaineBcrisBasicTheorems_proof

end GlobalTheory.MemLoc
end
