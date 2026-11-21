import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenGoodOfAdmissibilityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenStringOfAgreementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyJoinOfAgreementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartsGiveDimensionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsAOfJumpCountStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsBAndLocalLifts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsCOfLocalLiftsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeNonzeroRecursionOfEigenStatement

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RankTw

open GlobalTheory.RowCopy GlobalTheory.NRows

theorem used_loc (D : D7) (i : D.nd.Loc) : D.nd.mu i = D.what₂.mu0 ∨ ∃ w, D.nd.mu i = D.what₂.muAt w :=
  Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩

theorem lamPos_of_used {D : D7} (h : LamUsed D) {μ} (hμ : μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : LamPos D μ j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact h μ hμ ⟨k, by omega⟩

theorem lamLoc {D : D7} (h : LamUsed D) (i : D.nd.Loc) : LamPos D (D.nd.mu i) (D.nd.j i) :=
  lamPos_of_used h (used_loc D i) (D.nd.j_range i).1 (D.nd.j_range i).2

theorem up_injective {D : D7} {μ} {j : ℕ} (h : LamPos D μ j) (hI : DirectSum.IsInternal (D.what₂.isot j)) :
    Function.Injective (D.what₂.thetaT μ j) := by
  have hs : Function.Surjective (D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hI.submodule_iSup_eq_top, iSup_le_iff]
    intro σ f hf
    by_cases h0 : D.what₂.isot j σ = ⊥
    · rw [h0] at hf
      rw [(Submodule.mem_bot ℂ).1 hf]
      exact zero_mem _
    · have hl : ((D.what₂.lamP μ j σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ((h σ).2 h0).ne'
      refine ⟨((D.what₂.lamP μ j σ : ℝ) : ℂ)⁻¹ • f, ?_⟩
      rw [map_smul, LinearMap.comp_apply, (h σ).1 f hf, smul_smul, inv_mul_cancel₀ hl, one_smul]
  have hi := LinearMap.injective_iff_surjective.2 hs
  rw [LinearMap.coe_comp] at hi
  exact hi.of_comp

theorem rank_of {D : D7} (hI : SumRepresentations.adm8 D) (h : LamUsed D) (L : SizeData₂ D) : TwistedPlaces.adm3 L := by
  intro j hj w hw
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  have e : D.what₂.muTw w = D.what₂.muAt w := ((D.what₂.muAt_or w).resolve_left hw).symm
  have a := up_injective (lamPos_of_used h (Or.inr ⟨w, e⟩) h1 h2) (hI j h1 h2)
  have b := up_injective (lamPos_of_used h (Or.inl rfl) h1 h2) (hI j h1 h2)
  unfold SizeData₂.zeroSpaceRankAtPlace SizeData₂.dZ0 Rows.Data.Zj
  rw [LinearMap.finrank_range_of_inj a, LinearMap.finrank_range_of_inj b]

theorem main : ∀ D : D7, Formalism.MainNotions.SumRepresentations.adm8 D → GlobalTheory.NRows.LamUsed D →
    (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) ∧ ∀ L : SizeData₂ D, Formalism.MainNotions.TwistedPlaces.adm3 L :=
  fun _ hI h => ⟨GlobalTheory.RankTw.lamLoc h, GlobalTheory.RankTw.rank_of hI h⟩

end GlobalTheory.RankTw

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftSpaces_rank_const_and_localisation_scalars : ∀ D : D7, Formalism.MainNotions.SumRepresentations.adm8 D → GlobalTheory.NRows.LamUsed D → (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) ∧ ∀ L : SizeData₂ D, Formalism.MainNotions.TwistedPlaces.adm3 L := by
  atlas_forward_decl GlobalTheory.RankTw.main
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowsAll

theorem main : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), GlobalTheory.NRows.Inputs hL D → JumpsCard D.nd D.naut → GlobalTheory.NRows.Rows D := by
  intro hP hHC hCusp hL D I hJ
  have a : GlobalTheory.NRows.RowsA D := GlobalTheory.T.rows_a_of_jump_count hP hL D I.P hJ
  obtain ⟨J⟩ := GlobalTheory.T.nonempty_join_of_agreement hHC hCusp hL D I.P I.X I.agree
  obtain ⟨lamLoc, rank⟩ := GlobalTheory.T.thetaLiftSpaces_rank_const_and_localisation_scalars D I.isot I.lam
  obtain ⟨b, trip⟩ := GlobalTheory.T.rows_b_and_local_lifts hP hL D I.P J a I.adm1 lamLoc
  have Conclusion1 : Formalism.MainNotions.SumRepresentations.Conclusion1 D := I.Conclusion1 (GlobalTheory.T.parts_give_dimension D) a b
  have c : GlobalTheory.NRows.RowsC D := GlobalTheory.T.rows_c_of_local_lifts hL D I.P J a b I.adm1 I.isot Conclusion1 trip
  refine ⟨a, b, c, fun i => ?_, rank⟩
  exact GlobalTheory.T.type_nonzero_recursion_of_eigen hL D I.P I.X I.agree I.typeNZ i
    (GlobalTheory.T.eigen_string_of_agreement hP.fin hL D I.P I.X I.agree Conclusion1.1 a.temp a.tieLab i)
    (GlobalTheory.T.eigen_good_of_admissibility hL D I.P I.X Conclusion1.1 a.tieLab I.mtPar I.adm1 a.tie0 b.a4 a.a5 I.e0loc I.e0read i)

end GlobalTheory.RowsAll
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_of_inputs_and_jumps : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), GlobalTheory.NRows.Inputs hL D → JumpsCard D.nd D.naut → GlobalTheory.NRows.Rows D := by
  atlas_forward_decl GlobalTheory.RowsAll.main
end
