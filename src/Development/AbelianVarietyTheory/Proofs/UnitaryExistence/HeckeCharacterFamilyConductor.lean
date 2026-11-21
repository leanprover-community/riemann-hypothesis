import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LinearIndependentSingleAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDataNonemptyComponent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AlgebraicLawsModuliSchemeGoodLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelEqHalfMarkingStabilizerStatement
import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndHalfEqPrimeProduct
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpenStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDictionaryCharacterLaws

section
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory

theorem exists_unf_nonempty_comp_all : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → ∀ j (σ : Q.c.F →+* ℂ), ∃ U : Unf (Q.Xo j) Q.c σ D.R.r, Nonempty U.Comp := by
  intro D Q _ h j σ
  obtain ⟨X⟩ := DefiniteData.nonempty_data D.host.E D.R.r
  obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws
    GlobalTheory.firstFiveLaws.2.1.secTwist _ _ _ _ (Q.Xo j) Q.c (h j) σ
  exact ⟨{ Comp := Unit, X := fun _ => X, un := fun _ _ => y }, ⟨()⟩⟩

end GlobalTheory
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_with_component_at_every_embedding : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → ∀ j (σ : Q.c.F →+* ℂ), ∃ U : Unf (Q.Xo j) Q.c σ D.R.r, Nonempty U.Comp := by
  atlas_forward_decl GlobalTheory.exists_unf_nonempty_comp_all
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_laws_moduli_scheme_good_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ∧ UnitIndep Xo c ∧ IntFrNe Xo c (algCls Xo c) ∧ IntAll Xo c ∧ AllTest Xo c ∧ ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), regular₂ Xo c U ∧ CuspMul Xo c U ∧ ((∀ σ, GoodEmb c σ → IsUnf (U σ)) → CuspFD Xo c U ∧ SupDef Xo c U) := by
  first | exact @GlobalTheory.Member.algebraic_laws_of_good_level | exact GlobalTheory.Member.algebraic_laws_of_good_level | (intros; apply GlobalTheory.Member.algebraic_laws_of_good_level <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeEmbedding_liftDatum_hermitianSpace : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → (∃ ι, IotaOK (Q.Dw j) (D.sp.W j) ι) ∧ (Q.Dw j).p + (Q.Dw j).q = D.R.r ∧ (Q.Dw j).q = WeightFamilies.rho D j ∧ 2 * (Q.Dw j).q < D.R.r := by
  first | exact @GlobalTheory.Member.exists_iotaOK | exact GlobalTheory.Member.exists_iotaOK | (intros; apply GlobalTheory.Member.exists_iotaOK <;> assumption)
end

section
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem norm_embedding_xi_zero (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = xiR D := by
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, ← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

theorem finVol_and_cuspL2_of_pkgLaws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (V : HSp D) (hr : V.rank = r) ι Kf χ (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) mu x₀, VolTieG D → V.SigOK → GoodEmb c σ → SupDef Xo c U → PkgLaws V hr ι Kf χ (U σ) dict mu x₀ → FinVol V ∧ (∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D) ∧ ∃ h : CuspL2 U σ V dict mu, L2DefiniteCuspForms U σ V dict mu h := by
  intro D H Dw l Xo c r U σ V hr ι Kf χ dict mu x₀ hT hs hσ hsup P
  obtain ⟨g, e, F, ik, φ, th, -, hd, -⟩ := P.dictLaws
  have hA : AdelAut V dict mu := P.adelAut
  have hV : FinVol V := finVol_of_volTie hT V hs
  have hL : CuspL2 U σ V dict mu :=
    cusp_L2_of_measurable hσ (dict_dom_of hd) P.muUnit (adelMeas_of_aut Xo c hA)
  refine ⟨hV, fun k τ => ?_, hL, l2Def_of_cusp hσ hsup (aeDom_of hA hV (volPair_of_tie hT V hs) P.muUnit hd) hL⟩
  exact (congrArg (fun z => ‖τ z‖) (P.modelW k).2).trans (by rw [map_neg, norm_neg]; exact norm_embedding_xi_zero D τ)

end GlobalTheory.Member
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finVol_xiR_norm_and_cuspL2_of_pkgLaws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (V : HSp D) (hr : V.rank = r) ι Kf χ (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) mu x₀, VolTieG D → V.SigOK → GoodEmb c σ → SupDef Xo c U → PkgLaws V hr ι Kf χ (U σ) dict mu x₀ → FinVol V ∧ (∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D) ∧ ∃ h : CuspL2 U σ V dict mu, L2DefiniteCuspForms U σ V dict mu h := by
  atlas_forward_decl GlobalTheory.Member.finVol_and_cuspL2_of_pkgLaws
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_dictionary_character_laws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a, χ (idF D a) = 1) → ∃ un dict mu, C.IsDict dict ∧ GlobalTheory.FrameUnif.FramesOK C.e C.F C.M un ∧ PkgLaws V C.hr C.ι Kf χ (C.unf un) dict mu C.x₀ := by
  first | exact @GlobalTheory.Member.exists_pkgLaws | exact GlobalTheory.Member.exists_pkgLaws | (intros; apply GlobalTheory.Member.exists_pkgLaws <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_iotaAll (Q : Par D) (hQ : Q.Pins) (j : ℕ) :
    ∃ ι₀ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), InR D j → ∀ hr : (D.sp.W j).rank = D.R.r,
      IotaOK (Q.Dw j) (D.sp.W j) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) := by
  by_cases hj : InR D j
  · obtain ⟨⟨ι, hι⟩, -⟩ := GlobalTheory.T.exists_latticeEmbedding_liftDatum_hermitianSpace D Q hQ j hj
    refine ⟨LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) ∘ₗ ι,
      fun _ hr => ?_⟩
    have e : LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ
        (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) ∘ₗ ι) = ι := by
      ext x i
      rfl
    rw [e]
    exact hι
  · exact ⟨0, fun h => absurd h hj⟩

theorem exists_pkgAll (Q : Par D) (hQ : Q.Pins) (hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) (j : ℕ)
    (σ : Q.c.F →+* ℂ) (ι₀ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E))
    (hι : InR D j → ∀ hr : (D.sp.W j).rank = D.R.r,
      IotaOK (Q.Dw j) (D.sp.W j) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀))
    (Kf : Subgroup (GA D (D.sp.W j))) (hK : IsLevelK (D.sp.W j) Q.l.M Kf) (χ : (AE D)ˣ →* Circle)
    (hχ : InR D j → GoodEmb Q.c σ → IsHeckeChar D χ ∧ ∀ a, χ (idF D a) = 1) :
    ∃ (U : Unf (Q.Xo j) Q.c σ D.R.r) (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r)
      (mu : GA D (D.sp.W j) → ℂ) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ),
      ∀ hj : InR D j, GoodEmb Q.c σ → (∀ k, (U.X k).p0 = (Q.Dw j).q) ∧
        PkgLaws (D.sp.W j) (D.sp.W_rank j hj.1 hj.2)
          (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2)) ∘ₗ ι₀) Kf χ U dict mu x₀ := by
  by_cases h : InR D j ∧ GoodEmb Q.c σ
  · obtain ⟨hj, hσ⟩ := h
    obtain ⟨⟨C, hC, hCι⟩, -⟩ := GlobalTheory.T.exists_memberDictionaryContext_goodEmbedding D Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c σ (D.sp.W j) D.R.r
      (D.sp.W_rank j hj.1 hj.2) _ (hι hj (D.sp.W_rank j hj.1 hj.2)) (hpq j) hQ.2.1.2 hσ
    obtain ⟨un, dict, mu, -, -, hP⟩ := GlobalTheory.T.exists_uniformisation_dictionary_character_laws D Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c σ (D.sp.W j) D.R.r C hC Kf hK χ
      (hχ hj hσ).1 (hχ hj hσ).2
    rw [hCι] at hP
    exact ⟨C.unf un, dict, mu, C.x₀, fun _ _ => ⟨fun k => (hC.base.type k).1, hP⟩⟩
  · obtain ⟨U, ⟨k⟩⟩ := GlobalTheory.T.exists_uniformisation_with_component_at_every_embedding D Q hQ hpq j σ
    exact ⟨U, fun _ => ⟨k, fun _ _ _ => 0⟩, fun _ => 1, fun _ => 1, fun hj hσ => absurd ⟨hj, hσ⟩ h⟩

theorem exists_coreJ : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → VolTieG D → ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) → Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) → ∀ chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle, (∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj Q.c.F.val.toRingHom σ (chiW j Q.c.F.val.toRingHom) (chiW j σ)) → ∃ T : CoreJ D, LawsJ T ∧ LawsCore T.toCore ∧ T.pb = pb ∧ T.Q = Q ∧ HEq T.chiW chiW := by
  intro D Q hQ hpq hV pb hpb hMb chiW hchi
  have hM : Q.l.M = D.host.g 0 * D.host.g 1 := hQ.2.1.1
  choose iota hiota using exists_iotaAll Q hQ
  choose Kf hKf using fun j => (GlobalTheory.T.exists_principalLevel_subgroup_open D (D.sp.W j) Q.l.M).1
  choose U dict mu x₀ hS using fun j σ => exists_pkgAll Q hQ hpq j σ (iota j) (hiota j) (Kf j) (hKf j) (chiW j σ)
    (fun hj hσ => ⟨(hchi j hj σ hσ).1, (hchi j hj σ hσ).2.1⟩)
  have hgood := (GlobalTheory.T.level_good_and_half_eq_prime_product D Q.H Q.l hQ.1.2.1 hM).1
  have hB := fun j => GlobalTheory.T.algebraic_laws_moduli_scheme_good_level D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c (hpq j) hgood
  have hF := fun j (hj : InR D j) => ((hB j).2.2.2.2.2 D.R.r (U j)).2.2 fun σ hσ => (hS j σ hj hσ).2.unf
  have hL := fun j (hj : InR D j) σ (hσ : GoodEmb Q.c σ) =>
    GlobalTheory.T.finVol_xiR_norm_and_cuspL2_of_pkgLaws D Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c D.R.r (U j) σ (D.sp.W j) _ _ _ _ (dict j σ) (mu j σ) (x₀ j σ) hV
      (D.sp.W_sig j) hσ (hF j hj).2 (hS j σ hj hσ).2
  let T : CoreJ D :=
    { Q := Q, U := U, V := fun j _ => D.sp.W j, dict := dict, mu := mu, Kf := fun j _ => Kf j, pb := pb,
      cE := fun _ _ _ => 1, chiW := chiW, x₀ := x₀, iota := iota }
  have h0 : GoodEmb Q.c T.toCore.σ₀ := T.toCore.good_σ₀
  have hLM : LawsM T.toCore :=
    { pins := hQ
      half := ⟨hpb, hMb⟩
      evalWD := fun j _ => (hB j).1
      unf := fun j hj σ hσ => (hS j σ hj hσ).2.unf
      unTest := fun j hj σ hσ => (hS j σ hj hσ).2.unTest
      chiTriv := fun j hj σ hσ _ _ _ k γ _ => (hS j σ hj hσ).2.chi1 k _ γ
      dictU := fun j hj σ hσ => by
        obtain ⟨g, e, F, ik, φ, th, h1, h2, -⟩ := (hS j σ hj hσ).2.dictLaws
        exact ⟨th, _, h1, h2⟩
      spaceW := fun _ _ _ _ => rfl
      levelK := fun j _ _ _ => hM ▸ hKf j
      xiAbs := fun j hj σ hσ => (hL j hj σ hσ).2.1
      muUnit := fun j hj σ hσ => (hS j σ hj hσ).2.muUnit
      muCont := fun j hj σ hσ => (hS j σ hj hσ).2.muCont
      finVol := fun j hj σ hσ => (hL j hj σ hσ).1
      cuspFD := fun j hj => (hF j hj).1
      supDef := fun j hj => (hF j hj).2
      cuspidalL2Subspace := fun j hj σ hσ => (hL j hj σ hσ).2.2.choose
      l2Def := fun j hj σ hσ => (hL j hj σ hσ).2.2.choose_spec
      unitIndep := fun j _ => (hB j).2.1
      ptNe := fun j _ => (hB j).2.2.1 }
  refine ⟨T, ?_, ?_, rfl, rfl, HEq.rfl⟩
  · exact
      { toLawsM := hLM
        cUnit := fun _ _ _ _ _ => norm_one
        muVal := fun j hj σ hσ => (hS j σ hj hσ).2.muVal
        muConj := fun j hj σ hσ => (hchi j hj σ hσ).2.2
        intAll := fun j _ => (hB j).2.2.2.1
        modelW := fun j hj σ hσ => ⟨_, (hS j σ hj hσ).2.modelW⟩
        familyUniformisationBasePointOrthogonal := fun j hj σ hσ => (hS j σ hj hσ).2.familyUniformisationBasePointOrthogonal
        kfHalf := fun j _ _ _ => (GlobalTheory.T.principalLevel_eq_halfMarking_stabilizer D Q.H Q.l (D.sp.W j)).2 (Kf j) (hKf j)
        adPin := fun j hj σ hσ => by
          obtain ⟨g, e, F, ik, φ, th, h1, -, h3⟩ := (hS j σ hj hσ).2.dictLaws
          have hi := hiota j hj (D.sp.W_rank j hj.1 hj.2)
          refine ⟨D.sp.W_rank j hj.1 hj.2, g, e, F, ik, φ, th, hi.emb, ⟨1, fun x y => ?_⟩, h1, h3⟩
          rw [Units.val_one, Int.cast_one, one_mul]
          exact hi.isom x y }
  · exact
      { toLawsM := hLM
        cuspMul := fun j _ => ((hB j).2.2.2.2.2 D.R.r (U j)).2.1
        latZ := fun j hj => ((hS j _ hj h0).2.expo _).1
        cuNe := fun j hj k => by
          obtain ⟨-, h1, h2, h3⟩ := GlobalTheory.T.exists_latticeEmbedding_liftDatum_hermitianSpace D Q hQ j hj
          have hp : (T.toCore.X₀ j k).p0 = (Q.Dw j).q := (hS j _ hj h0).1 k
          exact GlobalTheory.CuspExist.nonempty_cuspFD GlobalTheory.QNorm.hasseNormSt _ _ _ _ (by omega) (by omega) (by omega)
        expo := fun j hj => hM ▸ ((hS j _ hj h0).2.expo _).2 }

end GlobalTheory.Member
end
end
