import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphyOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwJoin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesRealizationOfPublishedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesRealizationOfPublished
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealizationOfPublishedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealizationOfPublished
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRationalRowsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRationalRows
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaximalIdealIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SGalRead
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisHypothesesOfIsTriple
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SatakeIdentityOfIsTriple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SHodgeDghOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaEigenvalueTheoremOfHyp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistOfCuspParamsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalLocTripleWithLocalization
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistOfCuspParams
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkOfBuilt

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleAdm
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.CyclotomicNorms (Fbar rootsBar IsGood IrredOn BB primeToPart)
open GlobalTheory.TameLabels GlobalTheory.TripleResidual
section Algebra
variable {g : ℕ} [Fact g.Prime]
end Algebra
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf IsReduction Zbar GalE toFb)
open GlobalTheory.Triple (IsParam IsResidual Reading IsChars IsTripleWith IsTripleFor IsTripleOf IsTriple muBase hframe jIdx)
open GlobalTheory.TwistDet GlobalTheory.GalChar Formalism.L2.Host
variable {D : D7}
section Row
variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {w : D.what₂.places.Pl}
end Row
section Comparison₂
variable {Y : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : Y.Tw} {b : Bool}
variable {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}
theorem exists_kappa_of_isTripleWith (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) {s : Y.Sig i} {ρ : Reading Y i (Y.side i s)}
    (hχ : IsChars C art ρ) {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {r : GalE D →* GL (Fin D.R.r) (Qbar (Y.l i))}
    {ν : GalE D →* (Y.O0 i)ˣ} {w : D.what₂.places.Pl} {red : Zbar (Y.l i) →+* FbAt D w}
    (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) : ∃ κ, IsRowOfTriple Y i s σ w κ := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hl := h.induces.resChar
  obtain ⟨κ, hκ⟩ := exists_residue_lift ρ (red.comp (toZ ρ)) (by rw [← hl]; exact CharP.cast_eq_zero _ _)
  refine ⟨κ, h.good, h.occurs, hl, fun x => ?_,
    ⟨(Units.map (red.comp (toZ ρ)).toMonoidHom).comp ν, fun v hv A hA t ht => ?_, fun g => ?_⟩, fun k hk v => ?_⟩
  · obtain ⟨-, -, hint, -⟩ := GlobalTheory.CoefEmbed.embedding_closed_integral _ _ (Y.twistBaseCoefficientRing_isAdic i) ρ.κ ρ.κ_alg
    have e : ∀ y : ↥D.LL0, ρ.ι.symm (D.what₂.embLL (y : D.what₂.LL)) = ρ.κ (GlobalTheory.Triple.embSide Y i (Y.side i s) y) :=
      fun y => by rw [RingEquiv.symm_apply_eq, ρ.read]; rfl
    have h1 : 0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) ↔
        ‖ρ.κ (GlobalTheory.Triple.embSide Y i (Y.side i s) (x : ↥D.LL0))‖ < 1 := by
      rw [← e]
      generalize ((x : ↥D.LL0) : D.what₂.LL) = y
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      have h2 := h.induces y⁻¹
      have h3 : 0 < ‖ρ.ι.symm (D.what₂.embLL y)‖ := by simpa using hy
      rw [map_inv₀ D.what₂.embLL, map_inv₀ ρ.ι.symm, norm_inv, inv_le_one₀ h3] at h2
      rw [← not_le, ← not_le, ← h2, not_iff_not, AddValuation.map_inv]
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 ((D.what₂.places.val w).ne_top_iff.2 hy)
      rw [← hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_zero, WithTop.coe_le_coe,
        WithTop.coe_le_coe, neg_nonneg]
    rw [h1]
    refine ⟨?_, fun h2 => ?_⟩
    · rintro ⟨y, hy, e1⟩
      rw [GlobalTheory.Triple.embSide, ← e1]
      exact (mem_maximalIdeal_iff ρ y).1 hy
    · obtain ⟨y, hy⟩ := hint _ h2.le
      exact ⟨y, (mem_maximalIdeal_iff ρ y).2 (by rw [← hy] at h2; exact h2), hy⟩
  · obtain ⟨n, hn⟩ := h.shift
    rw [MonoidHom.comp_apply, (hn.unr_iff ha (Or.inl hv) hA).2 (GlobalTheory.Triple.shiftChar_unr C v) t ht, map_one]
  · obtain ⟨p, h1, h2⟩ := h.residual.charpoly g
    let M : Matrix (Fin D.R.r) (Fin D.R.r) (Y.O0 i) := (((ν g)⁻¹ : (Y.O0 i)ˣ) : Y.O0 i) •
      ((Y.rhoS i s g : GL (Fin D.R.r) (Y.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (Y.O0 i))
    have e1 : (M.map (toZ ρ)).map (Zbar (Y.l i)).subtype = (r g : GL (Fin D.R.r) (Qbar (Y.l i))) := by
      ext x y
      have := congrFun (congrFun (h.rho g) x) y
      change toQ ρ.κ (_ * _) = _
      rw [map_mul]
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this
      rw [this, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    have e2 : p = (M.map (toZ ρ)).charpoly :=
      Polynomial.map_injective (Zbar (Y.l i)).subtype Subtype.val_injective (by rw [h1, ← Matrix.charpoly_map, e1])
    rw [e2, ← Matrix.charpoly_map] at h2
    rw [← charpoly_smul_congr _ h2]
    congr 1
    ext x y
    change κ (IsLocalRing.residue _ _) = red (toZ ρ (ν g : (Y.O0 i)ˣ)) * red (toZ ρ (_ * _))
    rw [hκ, ← map_mul, ← map_mul, ← mul_assoc, Units.mul_inv, one_mul]
    rfl
  · obtain ⟨u, hu, e⟩ := hχ.tame (jIdx s) k hk.symm v
    refine ⟨u, hu, (hκ _).trans (h.residual.teich k hk.symm v _ (toFb_ne_zero k u) _ ?_)⟩
    rw [← e, GlobalTheory.Triple.jIdx_add_one, Reading.toC_apply, RingEquiv.symm_apply_apply]
    rfl
variable {Z : NExp D.R D.host D.what₂ D.LL0 D.nd Y}
theorem blockCharConj_of_isTripleOf (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Z) : BlockCharConj Y := by
  obtain ⟨C, art, h⟩ := h
  intro i hi j b h1 h2 k hk v hv A hA t ht t' ht'
  obtain ⟨ρ, hχ, -⟩ := h.evidence i hi b
  obtain ⟨j, rfl⟩ : ∃ j' : Fin D.R.m, j = j'.1 + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨n, hn⟩ := hχ.chi j
  obtain ⟨n0, h0⟩ := exists_isAlgPos_mu0 (hframe C) GlobalTheory.Triple.eExp_int j
  obtain ⟨r, hr, hL⟩ := h.artin.exists_isLAdicOf ρ.ι (isAlgPos_mul h0 (del_alg (hframe C) (Y.l i)))
  have hanti : AntiHom Y.cc r := antiHom_of_isLAdicOf h.artin hr hL
    (((hframe C).isMu0 j).triv.mul (inertialOrderFifteenChar_auxiliaryPrime_spec (hframe C) (l := Y.l i)).2.2.2.2.triv)
  have key : ∀ v, v ∉ placesOver D.host.E (Y.l i) → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
      ∀ t ∈ Ine (F := D.host.E) A, inQ ρ.κ (Y.chi1 i (j.1 + 1) b) t = r t := fun v hv A hA t ht => by
    obtain ⟨x, hx, e⟩ := exists_unit h.artin hA ht
    have e1 := hn.loc (Or.inl hv) e
    rw [GlobalTheory.Triple.blockChar, block_loc (C.isEta.unr v) hx] at e1
    apply Units.ext
    rw [hL.loc_away (Or.inl hv) x t e, inQ_val, RingEquiv.eq_symm_apply]
    exact e1
  have hvl : v ∉ placesOver D.host.E (Y.l i) := notMem_of_ne (D.host.g_prime k) (Y.lPrime i).out hk hv
  obtain ⟨bar, -, hbar⟩ := GlobalTheory.ConjPoly.exists_conj D
  obtain rfl : t' = cConj Y t := AlgEquiv.ext ht'
  rw [← map_inv]
  refine inQ_inj ρ.κ ?_
  rw [map_inv, key v hvl A hA t ht, key (bar v) (fun hm => hvl (mem_placesOver_conj (TwistDet.isConjPl_symm (hbar v).1) hm)) _
    (isPlaceOver_moveVal_cc Y (hbar v).1 hA) _ (cConj_mem_ine Y ht), hanti t _ ht']
theorem gen_adm2_of_isTripleOf (hT : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Z) (hW : WildOne D) : BlochKatoReduction.Gen.adm2 Y := by
  intro i hi s
  have hχ := _root_.GlobalTheory.TripleAdm.blockCharConj_of_isTripleOf hT
  obtain ⟨C, art, h⟩ := hT
  obtain ⟨ρ, h1, σ, π, r, ν, w, red, h2⟩ := h.triple hi s
  obtain ⟨κ, h3⟩ := _root_.GlobalTheory.TripleAdm.exists_kappa_of_isTripleWith h.artin h1 h2
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hl := h2.induces.resChar
  obtain ⟨hirr, hrow⟩ := _root_.GlobalTheory.TripleAdm.irredOn_rbar_and_inertia_of_residual Y hW h2.good h2.param hl h2.gal h2.residual
  refine admissible_at_of_irreducible_tame h3 hirr fun k hk v hv A hA => ?_
  refine tameOff_all Y (fun e => hk (e.symm.trans hl)) (D.ntypes.rbar_open σ w) (fun v => (hrow k hk.symm v).1)
    (fun v t ht => ?_) (fun v => ⟨(hrow k hk.symm v).2.1, ?_⟩) hv hA
  · have := hχ i hi _ (Y.side i s) (Y.jS_range i s).1 (Y.jS_range i s).2 k hk _ (D.naut.plGw_over k v) _
      (D.nd.plOm.2 _) t ht _ (cConj_apply Y t)
    rw [← map_inv, MonoidHom.comp_apply, MonoidHom.comp_apply, map_inv]
    exact congrArg _ this
  · obtain ⟨u, hu, e⟩ := h3.2.2.2.2.2 k hk v
    exact ⟨_, D.ntypes.tg_mem k v, fun h0 => (hrow k hk.symm v).2.2 _ u hu (e ▸ h0)⟩
end Comparison₂
theorem adm2_of_isTriple_wildOne (D : D7) (hT : _root_.GlobalTheory.Triple.IsGaloisTriple D) (hW : WildOne D) : BlochKatoReduction.adm2 D := _root_.GlobalTheory.TripleAdm.gen_adm2_of_isTripleOf hT hW
end GlobalTheory.TripleAdm
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.SettingHypotheses
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
theorem setHyp_of_isTriple_of_nonzeroIndexPlace (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (C₀ : Formalism.L2.Host.CharFrame D) (S : GlobalTheory.HeightCounting.CharSide D C₀)
    (hG : _root_.UpperTheory.GalS.GalHodgeN D T) (h2 : Formalism.MainNotions.BlochKatoReduction.adm2 D) (h : _root_.GlobalTheory.Triple.IsGaloisTriple D)
    (Z : GlobalTheory.LamTie.LamDat D) (hZ : Z.Ok) (hL : GlobalTheory.LamTie.IsLamTie D.ntw Z)
    (hr : 100 ≤ D.R.r) (hg : ∀ k, 2 * D.R.r ≤ D.host.g k) :
    ∀ i, D.ntw.NonzeroIndexPlace i → SetHyp (bk0 D) i := fun i hi =>
  have hA := (_root_.GlobalTheory.TripleLocal.adm1_adm8_selfDual_noJump_of_isTriple S
    (GlobalTheory.SplitFrobDense.frobDense D (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 hC)) hG h2 h).2.2 i hi
  have hT := GlobalTheory.LamTie.sum_th_empty_ne_zero D D.nd D.ntw Z hZ
    (GlobalTheory.LamTieWeak.isLamTie0_of_isLamTie D D.nd D.ntw Z hL) i hi
  ⟨hA.1, fun s _ => (hA.2 s).1, fun s _ => (hA.2 s).2, fun lam => (hT lam).1, fun lam => (hT lam).2, hr, hg⟩
end GlobalTheory.SettingHypotheses
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 800000
namespace GlobalTheory.TwGalInputs
theorem galois_inputs_alt : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → ∀ (D : D7) (G : _root_.GlobalTheory.TwInputs.GalSideAlt D), _root_.UpperTheory.GalS.GalHodgeN D G.wd → BlochKatoReduction.adm1 (BlochKatoReduction.bk0 D) ∧ BlochKatoReduction.adm2 D ∧ BlochKatoReduction.adm8 D ∧ AllGood D.nexp ∧ D.nexp.sig_all ∧ (∃ N0, BlochKatoReduction.adm9 D N0) ∧ BlochKatoReduction.adm10 D ∧ ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i := by
  intro hC hArt hTor D G hGH
  have h2 : BlochKatoReduction.adm2 D := _root_.GlobalTheory.TripleAdm.adm2_of_isTriple_wildOne D G.triple (GlobalTheory.T.full_degree_label_forces_trivial_wild_inertia D G.wd G.lab)
  have hF : GlobalTheory.TypeLeaf.FrobDense D :=
    GlobalTheory.SplitFrobDense.frobDense D (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 hC)
  have hg := _root_.GlobalTheory.TripleLocal.adm1_adm8_selfDual_noJump_of_isTriple G.chr hF hGH h2 G.triple
  have hs := _root_.GlobalTheory.Triple.adm8_allGood_sig_of_isTriple D G.triple
  have hL := GlobalTheory.LamTie.isToricElt_of_isLamTie D _ D.ntw G.lam G.lamOk G.lamTie
  obtain ⟨N0, h9, h10, -⟩ := GlobalTheory.ToricAssembly.toric_properties hArt hTor D hL.1
  exact ⟨hg.1, h2, hg.2.1, hs.2.1, hs.2.2, ⟨N0, h9⟩, h10,
    _root_.GlobalTheory.SettingHypotheses.setHyp_of_isTriple_of_nonzeroIndexPlace hC D G.wd G.cf G.chr hGH h2 G.triple G.lam G.lamOk G.lamTie G.rank G.primes⟩
end GlobalTheory.TwGalInputs
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwInputs
theorem exists_inputs_of_hkSup_galHodge : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator →
    ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ G : _root_.GlobalTheory.TwInputs.GalSideAlt D,
      (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → XiBdd Y.Z.rd →
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → _root_.UpperTheory.GalS.GalHodgeN D G.wd →
      (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) →
      ∃ N0, Inputs D E N0 := by
  intro hCh hArt hTor D X E Y G hRat hBdd hSup hHodge hRoots
  obtain ⟨a1, a2, a8, good, sig, ⟨N0, a9⟩, a10, hyp⟩ := _root_.GlobalTheory.TwGalInputs.galois_inputs_alt hCh hArt hTor D G hHodge
  have hL : Laws Y.Z.good Y.Z.rd := laws_of_serSide D X E Y hRat
  have hXi : XiType Y.Z.rd := GlobalTheory.XiTypeProof.xiType D Y.Z.ρ Y.Z.good Y.Z.rd hL.faithful hL.act (levelOf_of_serSide Y)
  obtain ⟨supG, supFull, supHk, commG, comm⟩ := supLaws_of_sides D X E Y hSup
  exact ⟨N0,
    { a1 := a1
      a2 := a2
      a8 := a8
      good := good
      sig := sig
      a9 := a9
      a10 := a10
      univChar := Y.Z.univ
      off := Y.off
      rel := GlobalTheory.T.universalTwistedSeriesDistribution_of_compatibility D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL
      l3 := GlobalTheory.SeriesTie.thetaLatticeCondition_of_fullSeriesComparison D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL
      t4 := GlobalTheory.T.admT4_of_roots_in_field D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hRoots E
      type := GlobalTheory.ExportType.typeKept_of_fullTie D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL.act E
      univ := univSup_of_xi D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL hXi hBdd E
      supG := supG
      supFull := supFull
      supHk := supHk
      commG := commG
      comm := comm
      ss := GlobalTheory.TwHkSS.hkSS_of_sides D X E Y commG comm supFull
      hyp := hyp }⟩
end GlobalTheory.TwInputs
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inputs_of_galHodgeN_roots : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ G : _root_.GlobalTheory.TwInputs.GalSideAlt D, (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → XiBdd Y.Z.rd → (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → _root_.UpperTheory.GalS.GalHodgeN D G.wd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) → ∃ N0, Inputs D E N0 := by
  atlas_forward_decl _root_.GlobalTheory.TwInputs.exists_inputs_of_hkSup_galHodge
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published
namespace GlobalTheory.ExportClose
open Classical in
theorem exportAt_of_bundles_alt : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (X : RealSide D) (Y : SerSide X (twEOf xd)) (G : _root_.GlobalTheory.TwInputs.GalSideAlt D), (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → XiBdd Y.Z.rd → (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → _root_.UpperTheory.GalS.GalHodgeN D G.wd → LocalSituation.Conclusion5 D → IsGalois ℚ ↥D.LL0 → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) → NChTie D nch → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)) → GlobalTheory.Mem.Top.ExportAt D nch xd := by
  intro hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 hGW hRC hDec hCh1 hArt hTor D nch xd X Y G hRat hXi hHk hHodge h5 hGal hRoots hTie hBase
  obtain ⟨N0, hI⟩ := _root_.GlobalTheory.T.exists_inputs_of_galHodgeN_roots hCh1 hArt hTor D X (twEOf xd) Y G hRat hXi hHk hHodge hRoots
  have hW : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → D.ntw.NonzeroIndexPlace (nch.twI w) :=
    GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice D nch hTie hGal
  let S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b) := fun i j b =>
    if h : D.ntw.NonzeroIndexPlace i ∧ j ∈ Finset.Icc 1 D.R.m then
      Classical.choose (GlobalTheory.T.exists_basis_averaged_series_of_class_sums D (twEOf xd) hI.t4 i h.1 j h.2 b) else ∅
  refine ⟨N0, S, fun i hi => ?_, fun w hw => ⟨hI.hyp _ (hW w hw), ?_, ?_⟩⟩
  · exact GlobalTheory.TwExportTop.twistAllPowers_of_galoisCohomology_classField hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 hGW hRC D (twEOf xd) N0 h5
      hI.a1 hI.a2 hI.a8 hI.good hI.sig hI.a9 hI.a10 hI.univChar hI.off hI.rel hI.l3 hI.t4 hI.type hI.univ hI.supG
      hI.supFull hI.supHk hI.commG hI.comm hI.ss i hi
  · intro j hj b
    exact GlobalTheory.T.fullRank_thetaSeries_forms_of_rational_scalars hDec D X (twEOf xd) Y (nch.twI w) (hBase w hw) (hRat _ (hW w hw)) j hj b
  · intro j hj b
    have h : D.ntw.NonzeroIndexPlace (nch.twI w) ∧ j ∈ Finset.Icc 1 D.R.m := ⟨hW w hw, hj⟩
    show IntegralHeckeForms.BasisOf D.nexp (nch.twI w) j b (IntegralHeckeForms.SgJ D.nexp (twEOf xd) (nch.twI w) j b) (S (nch.twI w) j b)
    simp only [S, dif_pos h]
    exact Classical.choose_spec (GlobalTheory.T.exists_basis_averaged_series_of_class_sums D (twEOf xd) hI.t4 _ h.1 j h.2 b)
end GlobalTheory.ExportClose
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_of_published_alt : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (X : RealSide D) (Y : SerSide X (twEOf xd)) (G : _root_.GlobalTheory.TwInputs.GalSideAlt D), (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → XiBdd Y.Z.rd → (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → _root_.UpperTheory.GalS.GalHodgeN D G.wd → LocalSituation.Conclusion5 D → IsGalois ℚ ↥D.LL0 → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) → NChTie D nch → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)) → GlobalTheory.Mem.Top.ExportAt D nch xd := by
  atlas_forward_decl _root_.GlobalTheory.ExportClose.exportAt_of_bundles_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published
namespace GlobalTheory.ExportClose0
theorem exportAt_bundles_alt : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (X : RealSide D) (Y : SerSide X (twEOf xd)) (G : _root_.GlobalTheory.TwInputs.GalSideAlt D), FieldOk X → _root_.UpperTheory.GalS.GalHodgeN D G.wd → LocalSituation.Conclusion5 D → NChTie D nch → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)) → GlobalTheory.Mem.Top.ExportAt D nch xd := by
  intro hCheb hPT hCD hTame hLF hLTD hLEC hGF hGEC hUO hadm hGW hRCA hCusp hCheb1 hGAR hTor hSR hSI hHI hHT hHRT
  intro D nch xd X Y G hF hGH hconds hTie hBase
  exact _root_.GlobalTheory.T.realization_of_published_alt hCheb hPT hCD hTame hLF hLTD hLEC hGF hGEC hUO hadm hGW hRCA hCusp hCheb1 hGAR hTor D nch xd X Y G
    (GlobalTheory.T.thetaSeries_rationality_and_coefficientBound hCusp hGAR hSR hSI D X (twEOf xd) Y hF).1
    (GlobalTheory.T.thetaSeries_rationality_and_coefficientBound hCusp hGAR hSR hSI D X (twEOf xd) Y hF).2
    (GlobalTheory.T.heckeOperator_preserves_supLattice_realSide hCusp hHI hHT hHRT D X)
    hGH hconds hF.galois hF.roots hTie hBase
end GlobalTheory.ExportClose0
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_realization_of_published_alt : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (X : RealSide D) (Y : SerSide X (twEOf xd)) (G : _root_.GlobalTheory.TwInputs.GalSideAlt D), FieldOk X → _root_.UpperTheory.GalS.GalHodgeN D G.wd → LocalSituation.Conclusion5 D → NChTie D nch → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)) → GlobalTheory.Mem.Top.ExportAt D nch xd := by
  atlas_forward_decl _root_.GlobalTheory.ExportClose0.exportAt_bundles_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TwSys GlobalTheory.LiftLeaf GlobalTheory.TwAll GlobalTheory.SupLaw
namespace GlobalTheory.ExportFirst
abbrev _root_.GlobalTheory.ExportFirst.exportF_isBuiltE_tyz : Prop :=  GlobalTheory.TwSys.Cheb → GlobalTheory.Published.PoitouTateTotallyComplex → GlobalTheory.Published.CohDimTwo → GlobalTheory.Published.TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → GlobalTheory.Published.RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.GalS.CuspUAlt → GlobalTheory.Published.DeRhamPotSemistable → _root_.UpperTheory.GalS.CarUAlt → (∀ D : D7, LocalSituation.Conclusion5 D) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), (GlobalTheory.Mem.Top.EvLgG fun K B f T => GlobalTheory.Mem.Top.Bl.KPx B f → T = GlobalTheory.Mem.Top.TwDat.untw B T.pl → ∀ w Z Wt p0 t nch n xd c, Nonempty (p.N K B f T w Z Wt p0 t nch n xd c) → Nonempty (p.R K B f T w Z Wt p0 t) → GlobalTheory.Mem.Top.Bl.ColPin w → Nonempty (_root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c)) → GlobalTheory.Mem.Top.GroupRetwisting.ExportF GlobalTheory.Mem.Top.Bl.KPx (GlobalTheory.Mem.Top.Bl.IsBuiltE p.s)
end GlobalTheory.ExportFirst
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TwSys GlobalTheory.LiftLeaf GlobalTheory.TwAll GlobalTheory.SupLaw
namespace GlobalTheory.ExportFirst
theorem exportF_isBuiltE_alt_alt : _root_.GlobalTheory.ExportFirst.exportF_isBuiltE_tyz := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 hA hG hR hLG hconds hL p H
  refine H.imp fun K _ _ _ _ hK => hK.imp fun B f T _ hp hKP hT C W V S N G c hc => ?_
  obtain ⟨w, Z, c', ⟨b, -⟩, e⟩ := hc
  suffices hs : ∀ y : Σ (C : GlobalTheory.Mem.Cols B) (Y : GlobalTheory.Mem.Col2.TC.Later B C),
      GlobalTheory.Mem.Top.V4.Core K ⟨B, C, Y.W, Y.V, Y.S, Y.N, Y.G⟩ f T, y = ⟨w.C, Z, c'⟩ →
      GlobalTheory.Mem.Top.ExportAt (GlobalTheory.Mem.assemble B y.1 y.2.1.W y.2.1.V y.2.1.S y.2.1.N y.2.1.G) y.2.2.O.nch y.2.2.O.xd from
    hs _ e
  rintro _ rfl
  obtain ⟨cn, en⟩ := b.nx
  obtain ⟨j⟩ := hp hKP hT w Z c'.Wt c'.O.p0 b.what₂ c'.O.nch b.n c'.O.xd cn ⟨en⟩ ⟨b.rx⟩ b.pin
  exact _root_.GlobalTheory.T.series_realization_of_published_alt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 (w.st Z).toD7 c'.O.nch c'.O.xd
    j.X j.Y j.gal j.field (_root_.UpperTheory.GalS.ghOf'_alt hL hA hG hR hLG _ _ j.cg j.gal.lab) (hconds _) c'.nch_tie (j.base hT)
end GlobalTheory.ExportFirst
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TwInputs.AtLayer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting GlobalTheory.SeriesTie GlobalTheory.TwInputs.JoinModel
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
section General
variable {D : D7}
theorem exists_frob_unit_and_hkF_zero_eq_of_built {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D) (h0 : ∀ j P, b.hL j 0 P = 1) :
    (∃ u, IsFrobUnit D u) ∧
      ∀ i j s P x, 1 ≤ j → j ≤ D.R.m → P ∉ D.ntw.S0 i → IsSplitPl D.host P → D.nexp.hkF i j s 0 P x = x := by
  obtain ⟨D0, cf, jE, A, cg, au, rep, row, low, Pq, S, hl, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  have h := hkF_zero_of_sideB (D := D0) Bs h0
  exact ⟨⟨Bs.cHk, Bs.cHk_del⟩, fun i j s P x => h i j s P x⟩
end General
section Rows
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch}
  {xd : ThData (w.D Z)} {c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n}
theorem nonempty_twOf_of_hecke_stable_reads {hH hV hs} (e : _root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) (hF : FieldOk (realOf t hH hV hs))
    (hG : ∃ G : _root_.GlobalTheory.TwInputs.GalSideAlt (w.st Z).toD7, G.cf = TC.cf w.I w.l Z ∧ G.lam.C = TC.cf w.I w.l Z ∧ Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL _ G.wd))
    (hR : ∀ (D : D7) (X : RealSide D) (S : RatDat D.ntw) (YS : NExpRealS X.R X.cG S),
      ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧
        (∀ j P, hL j 0 P = 1) ∧ GlobalTheory.ExportPin.Reads X.R X.cG S YS hL) :
    Nonempty (_root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c) := by
  obtain ⟨g, h1, h2, ⟨cg⟩⟩ := hG
  obtain ⟨k1, k2⟩ := _root_.GlobalTheory.TwInputs.JoinModel.embB_hk_commute_and_hEig_zero_of_built c.a.nt.toNBuilt
  obtain ⟨⟨u, hu⟩, hz⟩ := _root_.GlobalTheory.TwInputs.AtLayer.exists_frob_unit_and_hkF_zero_eq_of_built c.a.nt.toNBuilt (c.a.ratIn_hL ▸ c.a.ratIn.hL_zero)
  obtain ⟨f', s1, s2, s3⟩ := hR _ (realOf t hH hV hs) _ c.row.nexp
  obtain ⟨H, r1, r2⟩ := exists_hecke (realOf t hH hV hs) _ c.row.nexp e.ser.ex f' s1 s2 s3 u hu hz
  exact ⟨_root_.GlobalTheory.TwInputs.JoinModel.twistInputsOfBaseTuples (_root_.GlobalTheory.TwInputs.JoinModel.heckeSeriesOfRealHeight e H r1 r2 k1 k2) rfl HEq.rfl g h1 h2 hF cg fun hT v hv => base_of_untw _ hT v hv⟩
end Rows
end GlobalTheory.TwInputs.AtLayer
namespace GlobalTheory.TwInputs.AtLayer
end GlobalTheory.TwInputs.AtLayer
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.TwInputs.AtLayer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting GlobalTheory.SeriesTie GlobalTheory.TwInputs.JoinModel
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
section General
variable {D : D7}
end General
section Rows
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch}
  {xd : ThData (w.D Z)} {c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n}
end Rows
end GlobalTheory.TwInputs.AtLayer
namespace GlobalTheory.TwInputs.AtLayer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
theorem nonempty_twOf_of_law_rx_colPin : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ _ _ c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw) → EvLgG fun K B f T => KPx B f → T = TwDat.untw B T.pl → ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RX K B f T w Z Wt p0 t) → ColPin w → Nonempty (_root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c) := by
  intro hP hS hL _
  have e1 := (evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).inter (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)
  have e2 := EvG.inter (_root_.GlobalTheory.T.exists_galSide_cf_eq_cgTrue_at_members hP hS hL) (_root_.GlobalTheory.TwInputs.SmallField.fieldOk_and_exists_lamDat_ok_teich_valuesIn hP)
  refine (e1.inter e2).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨hV, hH⟩, hG, hF⟩ := H
  refine (hG.inter hF).imp fun B f T hO G hK _ w Z Wt p0 t nch n xd c ⟨e⟩ hR hC => ?_
  exact _root_.GlobalTheory.TwInputs.AtLayer.nonempty_twOf_of_hecke_stable_reads (hH := (hH (w.st Z) hO).1) (hV := (hV (w.st Z) hO).1) (hs := (hV (w.st Z) hO).2) e.1
    ((G.2 hK T w Z).1 _ t.r.z.lev.C) (G.1 hK w Z Wt p0 t nch n xd c ⟨e.1⟩ hR hC) (GlobalTheory.T.exists_rationalHeckeOperators_adelicReading hP.decay hS.hkTr hS.hkRead)
end GlobalTheory.TwInputs.AtLayer
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_twOf_of_extensionWithLaw : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ _ _ c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw) → EvLgG fun K B f T => KPx B f → T = TwDat.untw B T.pl → ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RX K B f T w Z Wt p0 t) → ColPin w → Nonempty (_root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c) := by
  first | exact @_root_.GlobalTheory.TwInputs.AtLayer.nonempty_twOf_of_law_rx_colPin | exact _root_.GlobalTheory.TwInputs.AtLayer.nonempty_twOf_of_law_rx_colPin | (intros; apply _root_.GlobalTheory.TwInputs.AtLayer.nonempty_twOf_of_law_rx_colPin <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TwSys GlobalTheory.LiftLeaf GlobalTheory.TwAll GlobalTheory.SupLaw
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.Mem.Top.ExportTrue
theorem exportF_prmR_alt_alt : GlobalTheory.TwSys.Cheb → GlobalTheory.Published.PoitouTateTotallyComplex → GlobalTheory.Published.CohDimTwo → GlobalTheory.Published.TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → GlobalTheory.Published.RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.GalS.CuspUAlt → GlobalTheory.Published.DeRhamPotSemistable → _root_.UpperTheory.GalS.CarUAlt → (∀ D : D7, LocalSituation.Conclusion5 D) → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ _ _ c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw) → ∀ (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → GlobalTheory.Mem.Top.GroupRetwisting.ExportF KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 hPr hSer hL hAt N S Γ hN =>
    _root_.GlobalTheory.ExportFirst.exportF_isBuiltE_alt_alt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ)
      (EvG.imp (_root_.GlobalTheory.T.nonempty_twOf_of_extensionWithLaw hPr hSer hL hAt) fun K _ _ _ _ H =>
        H.imp fun B f T _ G hK hT w Z Wt p0 t nch n xd c hn hR hP =>
          G hK hT w Z Wt p0 t nch n xd c (hn.elim (hN K B f T w Z Wt p0 t nch n xd c)) hR hP)
end GlobalTheory.Mem.Top.ExportTrue
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TwSys GlobalTheory.LiftLeaf GlobalTheory.TwAll GlobalTheory.SupLaw
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphy_of_hypotheses_alt_alt : GlobalTheory.TwSys.Cheb → GlobalTheory.Published.PoitouTateTotallyComplex → GlobalTheory.Published.CohDimTwo → GlobalTheory.Published.TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → GlobalTheory.Published.RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.GalS.CuspUAlt → GlobalTheory.Published.DeRhamPotSemistable → _root_.UpperTheory.GalS.CarUAlt → (∀ D : D7, LocalSituation.Conclusion5 D) → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ _ _ c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw) → ∀ (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → GlobalTheory.Mem.Top.GroupRetwisting.ExportF KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) := by
  first | exact @_root_.GlobalTheory.Mem.Top.ExportTrue.exportF_prmR_alt_alt | exact _root_.GlobalTheory.Mem.Top.ExportTrue.exportF_prmR_alt_alt | (intros; apply _root_.GlobalTheory.Mem.Top.ExportTrue.exportF_prmR_alt_alt <;> assumption)
end
end
end
