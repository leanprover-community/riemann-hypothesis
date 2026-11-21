import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsParPinsCanon
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HeckeCharacterFamilyConductor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdelStatement

section
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2.L2

theorem norm_complexEmbedding_traceElement_const (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = xiR D := by
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, ← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

theorem petersson_squareIntegrable_definite_of_laws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (V : HSp D) (hr : V.rank = r) ι Kf χ (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) mu x₀, V.SigOK → GoodEmb c σ → SupDef Xo c U → PkgLaws V hr ι Kf χ (U σ) dict mu x₀ → FinVol V ∧ (∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D) ∧ ∃ h : CuspL2 U σ V dict mu, L2DefiniteCuspForms U σ V dict mu h := by
  intro D H Dw l Xo c r U σ V hr ι Kf χ dict mu x₀ hs hσ hsup P
  obtain ⟨g, e, F, ik, φ, th, -, hd, -⟩ := P.dictLaws
  have hA : AdelAut V dict mu := P.adelAut
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hL : CuspL2 U σ V dict mu :=
    cusp_L2_of_measurable hσ (dict_dom_of hd) P.muUnit (adelMeas_of_aut Xo c hA)
  refine ⟨hV, fun k τ => ?_, hL, l2Def_of_cusp hσ hsup (aeDom_of hA hV hP P.muUnit hd) hL⟩
  exact (congrArg (fun z => ‖τ z‖) (P.modelW k).2).trans
    (by rw [map_neg, norm_neg]; exact norm_complexEmbedding_traceElement_const D τ)

end GlobalTheory.FinalJoin2.L2
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finVol_and_exists_L2DefiniteCuspForms_of_pkgLaws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (V : HSp D) (hr : V.rank = r) ι Kf χ (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) mu x₀, V.SigOK → GoodEmb c σ → SupDef Xo c U → PkgLaws V hr ι Kf χ (U σ) dict mu x₀ → FinVol V ∧ (∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D) ∧ ∃ h : CuspL2 U σ V dict mu, L2DefiniteCuspForms U σ V dict mu h := by
  atlas_forward_decl GlobalTheory.FinalJoin2.L2.petersson_squareIntegrable_definite_of_laws
end

section
section
noncomputable section

namespace GlobalTheory.FinalJoin2

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_coreJ_noVol : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) → Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) → ∀ chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle, (∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj Q.c.F.val.toRingHom σ (chiW j Q.c.F.val.toRingHom) (chiW j σ)) → ∃ T : CoreJ D, LawsJ T ∧ LawsCore T.toCore ∧ T.pb = pb ∧ T.Q = Q ∧ HEq T.chiW chiW := by
  intro D Q hQ hpq pb hpb hMb chiW hchi
  have hM : Q.l.M = D.host.g 0 * D.host.g 1 := hQ.2.1.1
  choose iota hiota using exists_iotaAll Q hQ
  choose Kf hKf using fun j => (GlobalTheory.T.exists_principalLevel_subgroup_open D (D.sp.W j) Q.l.M).1
  choose U dict mu x₀ hS using fun j σ => exists_pkgAll Q hQ hpq j σ (iota j) (hiota j) (Kf j) (hKf j) (chiW j σ)
    (fun hj hσ => ⟨(hchi j hj σ hσ).1, (hchi j hj σ hσ).2.1⟩)
  have hgood := (GlobalTheory.T.level_good_and_half_eq_prime_product D Q.H Q.l hQ.1.2.1 hM).1
  have hB := fun j => GlobalTheory.T.algebraic_laws_moduli_scheme_good_level D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c (hpq j) hgood
  have hF := fun j (hj : InR D j) => ((hB j).2.2.2.2.2 D.R.r (U j)).2.2 fun σ hσ => (hS j σ hj hσ).2.unf
  have hL := fun j (hj : InR D j) σ (hσ : GoodEmb Q.c σ) =>
    GlobalTheory.T.finVol_and_exists_L2DefiniteCuspForms_of_pkgLaws D Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c D.R.r (U j) σ (D.sp.W j) _ _ _ _ (dict j σ) (mu j σ) (x₀ j σ)
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

end GlobalTheory.FinalJoin2
end
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicCore_without_volumeNormalisation : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) → Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) → ∀ chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle, (∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj Q.c.F.val.toRingHom σ (chiW j Q.c.F.val.toRingHom) (chiW j σ)) → ∃ T : CoreJ D, LawsJ T ∧ LawsCore T.toCore ∧ T.pb = pb ∧ T.Q = Q ∧ HEq T.chiW chiW := by
  atlas_forward_decl GlobalTheory.FinalJoin2.exists_coreJ_noVol
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2

theorem exists_coreJ_of_chiOK_noVol : ∀ (D : D7), OFull D → OZeta D → ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) → ∀ chi₀, ChiOK D chi₀ → ∃ J : CoreJ D, LawsJ J ∧ LawsCore J.toCore ∧ J.Q.Canon ∧ J.pb = pb ∧ (∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q) ∧ (∀ j, J.chiW j J.σ₀ = chi₀ j) := by
  intro D hO hZ pb hg chi₀ hchi
  classical
  obtain ⟨Q, hP, hCan, hpq, hM⟩ := GlobalTheory.Member.ParExist.exists_par_pins_canon D hO hZ pb hg
  have hle : FO D ≤ Q.c.F := by
    rw [FO, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := Q.eO.surjective y
    have h : D.what₂.phiO (Q.eO x) = ((x : Q.c.F) : ℂ) := hP.2.2.1 x
    rw [h]
    exact (x : Q.c.F).2
  have key : ∀ j, ∃ χ : (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle,
      χ Q.c.F.val.toRingHom = chi₀ j ∧ (InR D j → ∀ σ,
        IsHeckeChar D (χ σ) ∧ (∀ a, χ σ (idF D a) = 1) ∧
          MuConj Q.c.F.val.toRingHom σ (chi₀ j) (χ σ)) := by
    intro j
    by_cases hj : InR D j
    · obtain ⟨h1, h2, h3⟩ := hchi j hj
      obtain ⟨χ, hχ, hσ⟩ := GlobalTheory.T.exists_galoisConjugates_heckeChar_trivialOnRealIdeles D Q (chi₀ j) h1 h2
        (fun x hx => ⟨⟨_, hle (h3 x hx)⟩, rfl⟩)
      exact ⟨χ, hχ, fun _ => hσ⟩
    · exact ⟨fun _ => chi₀ j, rfl, fun h => absurd h hj⟩
  choose chiW h0 hW using key
  obtain ⟨T, hJ, hC, hp, hQ, hH⟩ := GlobalTheory.T.exists_adelicCore_without_volumeNormalisation D Q hP hpq pb hg hM chiW
    (fun j hj σ _ => by rw [h0 j]; exact hW j hj σ)
  subst hQ
  refine ⟨T, hJ, hC, hCan, hp, hpq, fun j => ?_⟩
  rw [eq_of_heq hH]
  exact h0 j

end GlobalTheory.FinalJoin2
end
