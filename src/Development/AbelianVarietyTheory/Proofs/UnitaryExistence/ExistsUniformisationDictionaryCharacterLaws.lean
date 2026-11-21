import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlagDomainModelsExponentsLevelM
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArithmeticGroupCuspCentreLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryInvariantRationalLevelStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpenStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDictionaryByMarkingRule
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryRealEquivariantOntoTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemLevelKOfSameMarkAndFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryAdelicCharOfHeckeChar

section
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem adel_leftInv_and_continuous : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ mu : GA D V → ℂ, (∀ g g', mu (g * g') = mu g * mu g') → (∀ γ ∈ GQ V, mu γ = 1) → Continuous mu → ∀ (la : ∀ k, Wt (C.M.X k).Ψ r) (P : FDSec C.M.X), IsHolCusp C.M.X la P → (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P) := by
  intro D H Dw l Xo c σ V r C hC dict hd mu hmul hrat hm la P hP
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨⟨Kf, hKf⟩, hnb⟩ := GlobalTheory.T.exists_principalLevel_subgroup_open D V l.M
  obtain ⟨h1, -, h3, -, h5⟩ := GlobalTheory.T.memberDictionary_invariant_rational_level D H Dw l Xo c σ V r C hC dict hd Kf hKf
  have hχ := hC.base.chi
  have hsec : ∀ k, (C.M.X k).IsSec (la k) (P k) := fun k => (hP k).1.1
  constructor
  · intro γ hγ g
    obtain ⟨γ', hγ', he⟩ := h1 γ hγ g
    show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
    rw [he, hmul, hrat γ hγ, one_mul]
    show mu g * P (dict g).1 (lact γ' (dict g).2) = _
    rw [(hsec _).2.2 γ' hγ' _ (h3 g), hχ, one_mul]
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨γ, hmk, -⟩ := hd.1 g₀
    generalize (dict g₀).1 = k at hmk
    have hfr := fun h => GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC h k
    have hPc : ContinuousOn (P k) (C.M.X k).dom := (hsec k).1.continuousOn
    have hx : Continuous (fun g : GA D V => C.fr (γ * g) k) :=
      (hfr 1).2.2.2.1.comp (continuous_const.mul continuous_id)
    have hc : Continuous (fun g => mu g * P k (C.fr (γ * g) k)) :=
      hm.mul (hPc.comp_continuous hx fun g => (hfr _).2.1)
    have hN : {g : GA D V | FinCong V l.M (g₀⁻¹ * g)} ∈ 𝓝 g₀ := by
      have hcont : ContinuousAt (fun g : GA D V => g₀⁻¹ * g) g₀ :=
        (continuous_const.mul continuous_id).continuousAt
      have h0 := hnb hM
      rw [← inv_mul_cancel g₀] at h0
      exact hcont h0
    have heq : (fun g => mu g * P k (C.fr (γ * g) k)) =ᶠ[𝓝 g₀] adel V dict mu P := by
      filter_upwards [hN] with g hg
      have hmk' := (GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC g₀ k γ hmk).2.1 _ hg
      rw [mul_inv_cancel_left] at hmk'
      obtain ⟨δ, hδ, he⟩ := h5 g k γ hmk'
      show mu g * P k (C.fr (γ * g) k) = mu g * P (dict g).1 (dict g).2
      rw [he]
      show _ = mu g * P k (lact δ (C.fr (γ * g) k))
      rw [(hsec k).2.2 δ hδ _ (hfr _).2.1, hχ, one_mul]
    exact hc.continuousAt.congr heq

end GlobalTheory.Member
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspSection_adelic_leftInvariant_continuous : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ mu : GA D V → ℂ, (∀ g g', mu (g * g') = mu g * mu g') → (∀ γ ∈ GQ V, mu γ = 1) → Continuous mu → ∀ (la : ∀ k, Wt (C.M.X k).Ψ r) (P : FDSec C.M.X), IsHolCusp C.M.X la P → (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P) := by
  atlas_forward_decl GlobalTheory.Member.adel_leftInv_and_continuous
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dictionary_by_marking_rule : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∃ dict, C.IsDict dict := by
  first | exact @GlobalTheory.Member.Ctx.exists_isDict | exact GlobalTheory.Member.Ctx.exists_isDict | (intros; apply GlobalTheory.Member.Ctx.exists_isDict <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberDictionary_real_equivariant_onto_triangular : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → (∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V C.th C.hr (fun k => C.fr 1 k) h (dict g).1))⟩) ∧ ∀ k, ∀ x ∈ (C.M.X k).dom, ∃ g, ∃ γ ∈ (C.M.X k).Γ, ∃ b ∈ Bor (C.M.X k).Ψ r, dict g = ⟨k, rmul (lact γ x) b⟩ := by
  first | exact @GlobalTheory.Member.dict_real_equivariant_onto | exact GlobalTheory.Member.dict_real_equivariant_onto | (intros; apply GlobalTheory.Member.dict_real_equivariant_onto <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_levelK_of_same_mark_and_frame : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ (Kf : Subgroup (GA D V)), IsLevelK V l.M Kf → ∀ h h' k γ γ', C.Mark h k γ → C.Mark h' k γ' → C.fr (γ * h) k = C.fr (γ' * h') k → (γ * h)⁻¹ * (γ' * h') ∈ Kf := by
  first | exact @GlobalTheory.Member.mem_level_of_mark_of_frame_eq | exact GlobalTheory.Member.mem_level_of_mark_of_frame_eq | (intros; apply GlobalTheory.Member.mem_level_of_mark_of_frame_eq <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem dictIsUnif_of_isDict : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → DictIsUnif V dict Kf C.th C.hr := by
  intro D H Dw l Xo c σ V r C hC dict hd Kf hK
  obtain ⟨h1, h2, h3, -, -⟩ := GlobalTheory.T.memberDictionary_invariant_rational_level D H Dw l Xo c σ V r C hC dict hd Kf hK
  obtain ⟨h4, h5⟩ := GlobalTheory.T.memberDictionary_real_equivariant_onto_triangular D H Dw l Xo c σ V r C hC dict hd
  refine ⟨h1, h2, ⟨fun k => C.fr 1 k, fun k => ⟨(GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC 1 k).2.1, hd.2 k⟩, h4⟩,
    h3, h5, ?_⟩
  rintro g g' ⟨δ, hδ, he⟩
  obtain ⟨γ, hγ, hf⟩ := hd.1 g
  obtain ⟨γ', hγ', hf'⟩ := hd.1 g'
  rw [he] at hγ' hf'
  dsimp only at hγ' hf'
  obtain ⟨γ₁, hγ₁, hm, hfr⟩ := (GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC g _ γ hγ).2.2.2 δ hδ
  have hk := GlobalTheory.T.mem_levelK_of_same_mark_and_frame D H Dw l Xo c σ V r C hC Kf hK g g' _ _ _ hm hγ' (by rw [hfr, ← hf, hf'])
  refine ⟨γ'⁻¹ * (γ₁ * γ), mul_mem (inv_mem hγ'.1) hm.1, _, hk, ?_⟩
  group

end GlobalTheory.Member
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictIsUnif_of_markingRule_dictionary : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → DictIsUnif V dict Kf C.th C.hr := by
  first | exact @GlobalTheory.Member.dictIsUnif_of_isDict | exact GlobalTheory.Member.dictIsUnif_of_isDict | (intros; apply GlobalTheory.Member.dictIsUnif_of_isDict <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryAdelicChar_of_heckeChar : ∀ (D : D7) (V : HSp D), ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a, χ (idF D a) = 1) → ∃ mu : GA D V → ℂ, MuVal V χ mu ∧ (∀ g g', mu (g * g') = mu g * mu g') ∧ (∀ g, ‖mu g‖ = 1) ∧ (∀ γ ∈ GQ V, mu γ = 1) ∧ Continuous mu := by
  first | exact @GlobalTheory.Member.exists_muVal | exact GlobalTheory.Member.exists_muVal | (intros; apply GlobalTheory.Member.exists_muVal <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem exists_pkgLaws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a, χ (idF D a) = 1) → ∃ un dict mu, C.IsDict dict ∧ GlobalTheory.FrameUnif.FramesOK C.e C.F C.M un ∧ PkgLaws V C.hr C.ι Kf χ (C.unf un) dict mu C.x₀ := by
  intro D H Dw l Xo c σ V r C hC Kf hK χ hχ hχF
  have hS := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hT := GlobalTheory.firstFiveLaws.2.1.secTwist
  have hneg : GlobalTheory.FrameUnif.NegXi C.M :=
    (GlobalTheory.T.exists_memberDictionaryContext_goodEmbedding D H Dw l Xo c σ V r C.hr C.ι hC.iota hC.pos hC.lA hC.good).2.1 C hC
  obtain ⟨un, hun⟩ := GlobalTheory.FrameUnif.exists_framesOK hS hT _ H Dw l Xo c σ C.g C.e C.F r C.M hC.good hC.base hneg
  obtain ⟨dict, hd⟩ := GlobalTheory.T.exists_dictionary_by_marking_rule D H Dw l Xo c σ V r C hC
  obtain ⟨mu, hval, hmul, hnorm, hrat, hcont⟩ := GlobalTheory.T.exists_unitaryAdelicChar_of_heckeChar D V χ hχ hχF
  have hU := GlobalTheory.FrameUnif.isUnf_built hS _ H Dw l Xo c σ C.g C.e C.F r C.M un hC.good hC.base hneg hun
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  refine ⟨un, dict, mu, hd, hun, ?_⟩
  refine
    { unf := (Formalism.L2.PjFree.isUnf_ofPj (C.unf un)).1 hU
      unTest := fun k x => GlobalTheory.Frames.allTest_of_secBaseChange hS _ H Dw l Xo c (CAt σ) (un k x)
      chi1 := hC.base.chi
      modelW := hC.modelW
      familyUniformisationBasePointOrthogonal := hC.orth
      muUnit := ⟨hmul, hnorm, hrat, (GlobalTheory.T.memberDictionary_invariant_rational_level D H Dw l Xo c σ V r C hC dict hd Kf hK).2.2.2.1⟩
      muCont := hcont
      muVal := hval
      adelAut := GlobalTheory.T.cuspSection_adelic_leftInvariant_continuous D H Dw l Xo c σ V r C hC dict hd mu hmul hrat hcont
      expo := fun ρ => ⟨GlobalTheory.CuspCentre.latZ _ r ρ _ C.M.X,
        GlobalTheory.ExpoModels.expoMatch_models _ H Dw l Xo _ C.g _ C.F r C.M ρ hC.base hC.lA⟩
      dictLaws := ⟨C.g, C.e, C.F, id, C.M.φ, C.th, fun _ τ => hC.inf τ.1,
        GlobalTheory.T.dictIsUnif_of_markingRule_dictionary D H Dw l Xo c σ V r C hC dict hd Kf hK, ⟨hC.base.ef, fun k x => ?_⟩, fun h => ?_⟩ }
  · obtain ⟨Pm, h1, h2, h3, h4, -⟩ := hun.1 k x
    exact ⟨Pm, h1, h2, h3, h4⟩
  · obtain ⟨γ, ⟨h1, h2, h3⟩, h4⟩ := hd.1 h
    refine ⟨γ, h1, h2, h3, fun τ => ?_⟩
    exact congrFun h4 τ

end GlobalTheory.Member
end
end
