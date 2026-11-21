import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DtTiedTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryUnramifiedUnit
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelCharactersEqReference
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroTrivialStabilisersTrueColumns
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConditionsAtStandardKernelComparisonTrueColumns
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelClassSumsCarryChainComplexForms
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodIdealFgAndSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralOffPrimesMatrixStepEntryData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrecedingStepDatumIntegralAwayFromLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDataIntegralAwayFromLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepKernelDataIntegralAwayFromLevels
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.OrbitAdmissibleOfSplitBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsStandardBasesLatticeAtPlaceOfAdaptedBases
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtLinAdaptedCoefEqStandardSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesBConditionsLargePrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedFamilyStandardBasesIntegrality
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CombOfTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusConjugationConditionsAdaptedKernelDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundStandardSeriesInertPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumEntriesIntegralAwayFromD
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumThetaSeriesShapeAtDAdaptedBases
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaCMCurveTheoremsOfAlgebraicTransla
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.JetsOrth
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelRationalReferenceTuple

section
section
noncomputable section

namespace GlobalTheory.Pdv.UnStd

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.KerJ
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

theorem mtType_of_frame_mul {D : D7} {C : CharFrame D} (Dt : DtTied D C) (ξ : HChar D.host.E) {n : ℕ} (hn : 0 < n)
    (hord : ξ.OrderDvd n) (mt : ℕ → D.Dt →* ℂˣ)
    (h : ∀ (j : Fin D.R.m) a, IsFinIdele a → mt (j.1 + 1) (Dt.eDt a) = (C.mu0 j * ξ).1 a) (u : D.what₂.Word) :
    MtType u mt := by
  letI := D.host.cmStar
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  intro i hi
  have hun : (C.mu0 ⟨i, hi⟩ * ξ).IsUnitary := fun x => by
    have e : (C.mu0 ⟨i, hi⟩ * ξ).1 x = (C.mu0 ⟨i, hi⟩).1 x * ξ.1 x := rfl
    rw [e, Units.val_mul, norm_mul, (C.isMu0 ⟨i, hi⟩).unitary x, CharModel.isUnitary_of_orderDvd hn hord x, one_mul]
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (Dt.UO_eq k).1 hk
    obtain ⟨m, hm, hu⟩ := GlobalTheory.UnUnitCmp.Val.finUnit_pow _ hun
    refine ⟨m, hm, Units.ext ?_⟩
    rw [← CharModel.eDt_finPart Dt a, h ⟨i, hi⟩ _ (CharModel.isFin_finPart a), Units.val_pow_eq_pow_val]
    exact hu _ (CharModel.isFin_finPart a) ha
  · choose e he using fun τ => (D.hcW u τ).e_int ⟨i, hi⟩
    refine ⟨e, fun τ => (he τ).symm, fun z => ?_⟩
    obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj D.host z
    obtain ⟨m, hm, hinf⟩ := (C.isMu0 ⟨i, hi⟩).inf
    rw [← Dt.rat k z hk, ← CharModel.eDt_finPart Dt, h ⟨i, hi⟩ _ (CharModel.isFin_finPart _), GlobalTheory.Mem.Chr.DetGroupModel.fin_diag,
      HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one _ hn hord, mul_one, Units.val_inv_eq_inv_val, hinf k,
      ← Finset.prod_inv_distrib, ← D.eTau.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hme : m (D.eTau τ) = 2 * -e τ := by
      have h1 := hm (D.eTau τ)
      have h2 : eExp D ⟨i, hi⟩ (D.eTau τ) = e τ := by
        rw [← he τ, D.hcW_e]; simp [eExp]
      simp only [h2] at h1
      exact_mod_cast h1
    have h1 := congrArg (embPsi D.host (D.eTau τ)) hk
    rw [map_mul, GlobalTheory.Mem.Chr.DetGroupModel.emb_conj] at h1
    have h0 : embPsi D.host (D.eTau τ) (k : D.host.E) ≠ 0 := by simp
    show _ = embPsi D.host (D.eTau τ) z.1 ^ e τ
    generalize embPsi D.host (D.eTau τ) (k : D.host.E) = a at *
    generalize embPsi D.host (D.eTau τ) z.1 = b at *
    have hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
    have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b := by
      rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]
      linear_combination (-a) * h1
    rw [hme, zpow_mul, h3, zpow_neg, inv_inv]

end GlobalTheory.Pdv.UnStd

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Pdv.UnStd

open Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.KerJ

theorem mtType_stdO {B : Base} {X : PreX B.toPre} (I : TC B X) (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ} {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)}
    (hO : I.StdO l Z Qp O) (u : (I.rec7 l Z).what₂.Word) (a : (I.rec7 l Z).what₂.Tup) : MtType u (O u a).mt := by
  obtain ⟨T, hT⟩ := TC.dtTied_true I hok hp l Z
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  have hk : KDq B.host I.SQ ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).2.2 a).1
  refine mtType_of_frame_mul T (I.xi a) hn ((hok.xi_reads a).orderDvd hpow) _ (fun j x hx => ?_) u
  have hm : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ B.R.m := ⟨by omega, j.2⟩
  have e1 : (O u a).mt (j.1 + 1) = (I.rec7 l Z).muTil (j.1 + 1) * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) := by
    rw [hO.mt u a]
    exact if_pos hm
  rw [e1, MonoidHom.mul_apply, T.muTil_eq j x hx, hT x]
  have e2 : (tildeQ B.host I.SQ (I.xi a)) (QuotientGroup.mk x) = (I.xi a).1 x :=
    (tildeQ_mk B.host I.SQ hk x).trans (congrArg _ (finPartI_eq_self hx))
  exact congrArg _ e2

end GlobalTheory.Pdv.UnStd

open GlobalTheory.Pdv.UnStd in

theorem GlobalTheory.Pdv.unUnit_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → t.ent.UnUnit := by
  intro B X I hok hp l Z L hT Gi Gl K Y cX ex t hs
  exact GlobalTheory.KerJ.unUnit_of_mtType _ L hT Gi Gl K Y cX ex t (fun u μ => mtType_stdO I hok hp l Z hs.O u μ)

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelPairScalars_isUnit_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → t.ent.UnUnit := by
  atlas_forward_decl GlobalTheory.Pdv.unUnit_stdKer
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stab0_rec7_of_levelData : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), LevelData (I.rec7 l Z) → OrbitPlaces.Stab0 (I.rec7 l Z) := by
  first | exact @GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns | exact GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns | (intros; apply GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDatum_periodIdeal_fg_and_selfDual : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.amb.AA.FG ∧ ∀ u μ i c, IsSdLat ((t.rd u μ).N i c) := by
  first | exact @GlobalTheory.TieLat.tie_AA_fg_and_sd | exact GlobalTheory.TieLat.tie_AA_fg_and_sd | (intros; apply GlobalTheory.TieLat.tie_AA_fg_and_sd <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralOffPrimes_matrixStepEntryData : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < t.m2 → ∀ al be p p' x, IntOff (t.O u μ).S (t.seam.σ₀ (XiEntry (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i al be p p' x)) := by
  first | exact @GlobalTheory.KerTie.intOff_xiEntry | exact GlobalTheory.KerTie.intOff_xiEntry | (intros; apply GlobalTheory.KerTie.intOff_xiEntry <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.precedingStepDatum_integral_away_from_levels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ al p₀ p Yb x, IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl1 (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 al p₀ p Yb x)) := by
  first | exact @GlobalTheory.xiCpl1_intOff | exact GlobalTheory.xiCpl1_intOff | (intros; apply GlobalTheory.xiCpl1_intOff <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_data_integralAwayFrom_levels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ p Yb d x, Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N → IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl2 (R := D.R) (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 p Yb d x)) := by
  first | exact @GlobalTheory.CplTwoInt.xiCpl2_intOff_tied | exact GlobalTheory.CplTwoInt.xiCpl2_intOff_tied | (intros; apply GlobalTheory.CplTwoInt.xiCpl2_intOff_tied <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory

theorem forall_val_of_heq_hom {E : Type} [Field E] {a b b' : ℕ} (hb : b = b') (P : ℂ → Prop)
    {f : HomE E a b → ℂ} {g : HomE E a b' → ℂ} (h : HEq f g) (hg : ∀ x, P (g x)) : ∀ x, P (f x) := by
  subst hb
  rw [eq_of_heq h]
  exact hg

theorem kernel_datum_of_hecke_character_values : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.Hyp0 := by
  intro D L hT Gi Gl K Y cX ex t h1 h2 hQ
  obtain ⟨hFG, hsd⟩ := GlobalTheory.T.kernelDatum_periodIdeal_fg_and_selfDual D L hT Gi Gl K Y cX ex t
  refine ⟨hFG, fun u μ i hi c c' hpin => ⟨hsd u μ i c, hsd u μ (i + 1) c', ?_⟩⟩
  have hm : D.R.m = t.m2 + 2 := (t.idx_ok μ).hm
  obtain ⟨-, -, pt, ix, yb, row, -, hyb, hE, hC1, -, hC2, -, hp⟩ := t.rd_chain u μ
  rcases lt_trichotomy i t.m2 with hlt | heq | hgt
  · intro x
    rw [hE i hlt c c' x]
    exact GlobalTheory.T.isIntegralOffPrimes_matrixStepEntryData D L hT Gi Gl K Y cX ex t h1 h2 u μ (hQ μ) i hlt _ _ _ _ x
  · subst heq
    intro x
    rw [hC1 c c' x]
    exact GlobalTheory.T.precedingStepDatum_integral_away_from_levels D L hT Gi Gl K Y cX ex t h1 h2 u μ (hQ μ) _ _ _ _ x
  · have hi' : i = t.m2 + 1 := by omega
    subst hi'
    obtain ⟨d, hd⟩ := (hp c').1 hpin
    refine forall_val_of_heq_hom (congrArg D.R.N (by omega : t.m2 + 1 + 1 = D.R.m))
      (IntOff (t.O u μ).S) (hC2 c c' d hd) fun x => ?_
    exact GlobalTheory.T.lastStep_data_integralAwayFrom_levels D L hT Gi Gl K Y cX ex t u μ _ _ d x (hyb c)

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDatum_periodLatticeIdeal_fg_of_heckeCharacters : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.Hyp0 := by
  atlas_forward_decl GlobalTheory.kernel_datum_of_hecke_character_values
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepKernelData_integral_awayFromLevels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.TopPinned → t.TopInt := by
  first | exact @GlobalTheory.TopInt.topInt | exact GlobalTheory.TopInt.topInt | (intros; apply GlobalTheory.TopInt.topInt <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory

theorem hypFree_of_top_int : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.TopPinned → t.TopInt → t.HypFree := by
  intro D L hT Gi Gl K Y cX ex t hTop hInt u μ i hi c c' hnp
  have hsd := (GlobalTheory.TieLat.tie_AA_fg_and_sd D L hT Gi Gl K Y cX ex t).2 u μ
  refine ⟨hsd i c, hsd (i + 1) c', ?_⟩
  have hm : D.R.m = t.m2 + 2 := (t.idx_ok μ).hm
  obtain ⟨-, -, pt, ix, yb, pT, -, -, -, -, -, hpin, -⟩ := hTop u μ
  have hi' : i = t.m2 + 1 := by
    by_contra hne
    exact hnp (hpin (i + 1) (by omega) c')
  subst hi'
  exact hInt u μ c c' hnp

theorem kerEntTied_hyp : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.TopPinned → t.Hyp := by
  intro D L hT Gi Gl K Y cX ex t h1 h2 hQ hTop
  have h0 : t.Hyp0 := by
    first
      | exact GlobalTheory.T.kernelDatum_periodLatticeIdeal_fg_of_heckeCharacters D L hT Gi Gl K Y cX ex t h1 h2 hQ
      | exact GlobalTheory.T.kernelDatum_periodLatticeIdeal_fg_of_heckeCharacters D L hT Gi Gl K Y cX ex t h1 h2
  exact hypotheses_of_base_hypotheses D L hT Gi Gl K Y cX ex t h0
    (hypFree_of_top_int D L hT Gi Gl K Y cX ex t hTop (GlobalTheory.T.lastStepKernelData_integral_awayFromLevels D L hT Gi Gl K Y cX ex t hTop))

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelEntries_hyp_of_heckeCharacterConditions : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.TopPinned → t.Hyp := by
  atlas_forward_decl GlobalTheory.kerEntTied_hyp
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.L2.DIV

namespace GlobalTheory.KerJ.ColSideHyp

theorem plc_dvd_iff' {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Formalism.EigenvalueLevelCeiling.plc v ∣ n ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

theorem g_not_mem_Qp (t : KerEntTied ex) (hC : GlobalTheory.KerJ.ColSide t) (μ : D.what₂.Tup) (k : Fin 2) : D.host.g k ∉ Y.Qp μ := by
  classical
  intro hk
  obtain ⟨hp, P, hPQ, hgP⟩ := (t.Q_rec μ (D.host.g k)).1 hk
  unfold QE at hPQ
  split_ifs at hPQ with h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPQ
    rw [Set.Finite.mem_toFinset] at hv
    have hgood : GoodPl t.X.E t.S v := by
      by_contra hg
      apply hv
      have h2 := (Subgroup.mem_inf.1 (t.tup μ).2).2
      exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 v) hg
    have hvF : ((D.host.g k : ℕ) : 𝓞 t.X.F) ∈ v.asIdeal := by
      rw [← hC.sel v]
      change algebraMap (𝓞 t.X.F) (𝓞 t.X.E) _ ∈ (t.sel v).asIdeal
      rw [map_natCast]
      exact hgP
    have hd := (plc_dvd_iff' v _).2 hvF
    have hpl : Formalism.EigenvalueLevelCeiling.plc v = D.host.g k :=
      ((Nat.dvd_prime hp).1 hd).resolve_left fun e => by
        have h1 := (plc_dvd_iff' v 1).1 (by rw [e])
        rw [Nat.cast_one] at h1
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    apply hgood.2.2
    rw [hpl, ← t.g_rec k]
    exact hC.bad.1 k
  · simp at hPQ

end GlobalTheory.KerJ.ColSideHyp

namespace GlobalTheory

theorem colSide_hyp : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.KerJ.ColSide t → t.TopPinned → t.Hyp := by
  intro D L hT Gi Gl K Y cX ex t hC hTop
  obtain ⟨eta, hTied⟩ := hC.chars
  rw [t.glob_σ] at hTied
  refine GlobalTheory.T.kernelEntries_hyp_of_heckeCharacterConditions D L hT Gi Gl K Y cX ex t (fun j => ⟨_, hTied.mu0 j⟩) (fun j v hv => hTied.muVal j v hv) ?_ hTop
  intro μ k
  exact GlobalTheory.KerJ.ColSideHyp.g_not_mem_Qp t hC μ k

end GlobalTheory
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelEntries_hyp_of_columnSideProperties : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.KerJ.ColSide t → t.TopPinned → t.Hyp := by
  atlas_forward_decl GlobalTheory.colSide_hyp
end

section
section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem exists_beFam_evenConditionsInert_of_kerEnt : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∃ ep be, BeFam D ep be ∧ OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be (fun _ _ => -1)) Y := by
  intro hAlg hHost D L hT Gi Gl K Y cX ex t hHyp hAd h3
  have hOrb := (Formalism.MainNotions.DIV.Inh.orbit_admissible_of_split_bound D h3).1
  have key : ∀ w : D.what₂.places.Pl, ∃ (e : ℂ_[D.what₂.places.resChar w])
      (b : MvPowerSeries (ZMod (nP D (D.what₂.places.resChar w))) ℂ_[D.what₂.places.resChar w]),
      ((IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)) →
      ‖e‖ = 1 ∧ BeStd (D.what₂.places.resChar w) (nP D (D.what₂.places.resChar w)) b ∧
      ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
        (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E),
        admitted D N N' L L' → StdBases D (t.ent.lam w) L P → StdBases D (t.ent.lam w) L' P' →
        ∀ G, IsComb D t.B.tor (t.B.eNat t.χ) (t.ent.lam w) L L' G → ∀ R, OrbitPlaces.IsReps D (D.what₂.places.resChar w) R →
          OrbitPlaces.ThetaExpansionAllPlaces D (D.what₂.places.resChar w) R e (fun _ => -1) (fun _ => b) (stdSer D (t.ent.lam w) (fun _ => 1) P P' G) := by
    intro w
    by_cases hc : (IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)
    · have hO := hOrb _ (D.what₂.places.resChar_prime w) hc
      have hH := hHost D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (D.what₂.places.resChar w) (t.ent.lam w) hO.five
        (hc.imp_left And.left)
      obtain ⟨e, b, he, hb, hB⟩ := GlobalTheory.T.normalisedFamily_standardBases_integrality_alt D t.cc t.δ t.B t.χ _ (t.ent.lam w) hH hO (hc.imp_left (And.imp_right HEv.ne_zero))
      exact ⟨e, b, fun _ => ⟨he, hb, hB⟩⟩
    · exact ⟨1, 0, fun h => absurd h hc⟩
  choose ep be hbe using key
  refine ⟨ep, fun w _ => be w, ?_, ?_⟩
  · intro w hc
    obtain ⟨he, hb, -⟩ := hbe w hc
    exact ⟨he, fun _ => hb⟩
  · intro u μ w hLev hc R hR
    obtain ⟨he, hb, hB⟩ := hbe w hc
    have hO := hOrb _ (D.what₂.places.resChar_prime w) hc
    refine ⟨⟨he, fun _ _ => Or.inr rfl, fun _ _ => GlobalTheory.T.standard_series_b_conditions_large_prime _ _ _ hO.five hO.two hO.even hb⟩, ?_⟩
    intro i hi _ c c'
    have hAdPl : Formalism.L2.Ker.AdPl D w := by
      rcases hc with h | h
      · exact Or.inl h.1
      · exact Or.inr (Or.inl h)
    obtain ⟨Pm, hBas, -, hConj, hTh⟩ := hAd w hAdPl u μ hLev
    have hcomb := GlobalTheory.Ggeo.KerComb.comb_of_tied hAlg D L hT Gi Gl K Y cX ex t hHyp u μ w hLev i hi c c'
    have hS : ∀ j, j ≤ D.R.m → ∀ c, StdBases D (t.ent.lam w) ((t.O u μ).lat j c).1 (Pm j c) := fun j hj c =>
      GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat j c).2.1 (fun τ => hBas j hj c τ)
        (fun τ τ' h => hConj j hj c τ τ' h)
    show OrbitPlaces.ThetaExpansionAllPlaces D _ R (ep w) (fun _ => -1) (fun _ => be w) (t.ent.Th u μ w i c c')
    rw [hTh i hi c c', GlobalTheory.T.atLin_adaptedCoef_eq_standardSeries]
    exact hB _ _ _ _ _ _ hcomb.1 (hS i hi.le c) (hS (i + 1) hi c') _ hcomb.2 R hR

end GlobalTheory.KerStd
end
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleKernelSeries_inertPrime_nonConjugateFrobenius : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∃ ep be, BeFam D ep be ∧ OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be (fun _ _ => -1)) Y := by
  atlas_forward_decl GlobalTheory.KerStd.exists_beFam_evenConditionsInert_of_kerEnt
end

section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HostInert

open Formalism.InvariantFactorPaths.G7 (lgF at1) in
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp) in

theorem inParamK_eq {l : ℕ} [Fact l.Prime] {ι : Type} (f : MvPowerSeries ι ℂ_[l]) :
    @Formalism.MainNotions.FormalGroupSystem.inParamK l _ ι ℂ_[l] _ (wittFractionAlgebraCp l) f = MvPowerSeries.subst (fun i => at1 i (lgF ℂ_[l] l)) f := by
  unfold Formalism.MainNotions.FormalGroupSystem.inParamK
  have hlog : PowerSeries.map (k0ToC l) (Formalism.MainNotions.FormalGroupSystem.logF l) = lgF ℂ_[l] l := by
    ext n
    rw [PowerSeries.coeff_map]
    simp only [Formalism.MainNotions.FormalGroupSystem.logF, lgF, PowerSeries.coeff_mk, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_mul]
    split_ifs <;> simp
  congr 1
  funext i
  rw [show @algebraMap (Formalism.MainNotions.FormalGroupSystem.K0 l) ℂ_[l] _ _ (wittFractionAlgebraCp l) = k0ToC l from rfl, hlog]
  rfl

theorem jacobi_of_class (D : D7) (p : ℕ) [Fact p.Prime] (h : IsResidueClassZero D p ∨ IsSg D p) :
    jacobiSym (-(D.host.d : ℤ)) p = -1 := by
  have hp : p.Prime := Fact.out
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have key : p ≠ D.host.d ∧ jacobiSym (-(D.host.d : ℤ)) p ≠ 1 := by
    have h' : D.host.cls p = PrimeClass.inertClass ∨
        D.host.cls p = PrimeClass.signal := h
    rcases h' with h' | h'
    · obtain ⟨-, -, h3, h4, -⟩ := (primeClass_eq_inert_iff _).1 h'
      exact ⟨h3, h4⟩
    · obtain ⟨-, -, h3, h4, -⟩ := (primeClass_eq_signal_iff _).1 h'
      exact ⟨h3, h4⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rcases jacobiSym.trichotomy (-(D.host.d : ℤ)) p with h0 | h1 | h1
  · exfalso
    rw [jacobiSym.eq_zero_iff_not_coprime] at h0
    apply h0
    have : Nat.Coprime D.host.d p := (Nat.coprime_primes hd hp).2 key.1.symm
    simpa [Int.gcd_neg, Int.gcd_natCast_natCast] using this
  · exact absurd h1 key.2
  · exact h1

theorem hostAt_inert : Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam := by
  intro h1 h2 h3 D cc δ B χ hc hδ hχ p _ lam h5 hcl
  have hin := jacobi_of_class D p hcl
  obtain ⟨cc', δ', g, -, -, hL, hlam, hAt, hM, hLT⟩ := h1 D cc δ hc hδ p h5 hin lam
  obtain ⟨g2, g3, ε, s2, -, -, -, -, hn, ⟨a1, a2, a3, a4, a5, -, F, hF, -⟩, hD⟩ := h2 D cc' δ' p g hLT hAt h5 hin hM
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.fieldDataCM p h5
  refine ⟨_, g2, g3, s2, ε, σ, F, hn, ⟨h5, a1, a2, a3, a4, hσ, hF, a5 σ hσ⟩, ?_⟩
  intro N N' L L' hA
  obtain ⟨r, b, hb, ho⟩ := Formalism.L2.KerInert.orthBasisExists_of Formalism.L2.KerInert.global_orthonormal_basis_four
    Formalism.L2.KerInert.weakApprox_of_approx_and_separation D p h5 hin N N' L L' hA
  refine ⟨r, b, hb, ho, fun G hG => ?_⟩
  obtain ⟨C, wq, hC, hw, hd⟩ := hD D
  have hΛ : g.abelian₂ = B.tor.abelian₂ := hAt.2.2.2.1.trans hL
  subst hlam
  rw [hΛ] at hC hw hd
  have := hd N N' r b G (h3 D cc δ B hc hδ χ hχ p h5 hin g.lam N N' L L' hA G hG C wq r b hC hw hb ho)
  rw [HostLog.iff_phSum]
  rw [inParamK_eq] at this
  exact this

end GlobalTheory.KerStd.HostInert
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PdvClose

theorem at_of_true_columns : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → I.StdKer l Z t → GlobalTheory.Pdv.IsEntC t → t.Adapted → t.TopPinned → 3 ≤ B.host.splitBound → 5 ≤ K.dl1 → 4 ≤ K.dl2 → (∀ Ee : OrbitPlaces.Ent (I.rec7 l Z), OrbitPlaces.Shape (I.rec7 l Z) L Gi Ee ∧ ∀ u, ∀ j < B.R.m, ∀ s ∈ B.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * L.sc.a) → GlobalTheory.Pdv.At ex t.ent := by
  intro hAlg hG1 hCD hII B X I hOk hPins l Z l0 L hT Gi Gl K Y cX ex t hNorm hJets htw hStd hEntC hAd hTop hsplit hdl1 hdl2 hSh
  have hDuty : GlobalTheory.Pdv.Duty t := GlobalTheory.T.conditions_at_standardKernelComparison_trueColumns I hOk hPins l Z l0 L hT Gi Gl K Y cX ex t hNorm hJets htw hStd hEntC
  have hHyp : t.Hyp := GlobalTheory.T.kernelEntries_hyp_of_columnSideProperties _ L hT Gi Gl K Y cX ex t hDuty.col hTop
  have hInp : GlobalTheory.ThLoc.Inputs := GlobalTheory.T.normalisedThetaCMCurveTheorems_of_algebraicTranslates hAlg
  have hHost := GlobalTheory.KerStd.HostInert.hostAt_inert hG1 hCD hII
  obtain ⟨P, Bf, hK, he⟩ := hEntC
  obtain ⟨t', hc', hf'⟩ := hDuty.forms
  obtain ⟨ep, be, hBe, h0⟩ := GlobalTheory.T.admissibleKernelSeries_inertPrime_nonConjugateFrobenius hAlg hHost _ L hT Gi Gl K Y cX ex t hHyp hAd hsplit
  refine ⟨⟨GlobalTheory.T.kernelPairScalars_isUnit_trueColumns I hOk hPins l Z L hT Gi Gl K Y cX ex t hStd,
    GlobalTheory.PdvKm.kmapRat_kerEntC' t P Bf hK he hDuty.rk,
    GlobalTheory.T.kernelClassSums_carry_chainComplexForms _ L hT Gi Gl K Y cX ex t' hc' hf',
    GlobalTheory.T.stab0_rec7_of_levelData I hOk hPins l Z ex.lev⟩, ep, be, (fun _ _ => -1), h0,
    GlobalTheory.T.frobeniusConjugation_conditions_adaptedKernelDatum hAlg hHost _ L hT Gi Gl K Y cX ex t hHyp hAd hsplit ep be _, ?_,
    GlobalTheory.T.jetIntegralityBis_ofKer_of_hyp hInp _ L hT Gi Gl K Y cX ex t hHyp hsplit ep be _,
    GlobalTheory.T.kernelDatum_thetaSeries_shape_at_d_adaptedBases hInp _ L hT Gi Gl K Y cX ex t hHyp hAd ep be _,
    (hSh _).1⟩
  exact GlobalTheory.T.orbitBound_standardSeries_inertPlaces _ L Gi K _ (hSh _).1 (hSh _).2 hdl1 hdl2 hBe rfl

end GlobalTheory.PdvClose
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Pdv

open Classical in

theorem stepRep_eq_one_at_typePrimes {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 j : ℕ)
    (b : (twSt Ch sel mu cst m2 j).β) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    (twSt Ch sel mu cst m2 j).h b P = 1 := by
  cases j with
  | zero => rfl
  | succ i =>
    by_cases h1 : i + 1 ≤ m2
    · revert b
      rw [show twSt Ch sel mu cst m2 (i+1) = twNext Ch sel mu cst (twSt Ch sel mu cst m2 i) by simp [twSt, h1]]
      intro b
      have hq : P.1 ∉ twQOff (Pr := Pr) sel mu := fun hq => (Finset.mem_sdiff.1 hq).2 hP
      simp only [twNext, hq, dif_neg, not_false_eq_true]
    · by_cases h2 : i + 1 = m2 + 1
      · revert b
        rw [show twSt Ch sel mu cst m2 (i+1) = twUnitSt _ (i+1) by simp [twSt, h1, h2]]
        intro b; rfl
      · revert b
        rw [show twSt Ch sel mu cst m2 (i+1) = twEmptySt _ (i+1) by simp only [twSt, if_neg h1, if_neg h2]]
        intro b; exact b.elim

theorem colNorm_of_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), (∀ a, I.cst a = twCst I.Ch I.sel (I.tup a) I.glob ∧ I.idx a = twIdx I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 2)) → GlobalTheory.Pdv.ColNorm I := by
  intro B X I H a
  obtain ⟨hc, hi⟩ := H a
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]; show B.R.m ≤ B.R.m + 1; omega
  · rw [hc]; show B.R.m ≤ B.R.m; exact le_rfl
  · rw [hi]
    intro j _ b P hP
    exact stepRep_eq_one_at_typePrimes _ _ _ _ _ _ b P hP

end GlobalTheory.Pdv
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.PdvTie

theorem at_of_stdTie : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ (D : D7) (O : Obj D) (t : KerEntTied O.ex), StdTie D O t → 3 ≤ D.host.splitBound → 5 ≤ O.K.dl1 → 4 ≤ O.K.dl2 → (∀ Ee : OrbitPlaces.Ent D, OrbitPlaces.Shape D O.L O.Gx Ee ∧ ∀ u, ∀ j < D.R.m, ∀ s ∈ D.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * O.L.sc.a) → GlobalTheory.Pdv.At O.ex t.ent := by
  intro hA hG hC hI D O t hT hs h1 h2 hE
  refine StdTie.ind (R := fun D O t => 3 ≤ D.host.splitBound → 5 ≤ O.K.dl1 → 4 ≤ O.K.dl2 →
      (∀ Ee : OrbitPlaces.Ent D, OrbitPlaces.Shape D O.L O.Gx Ee ∧ ∀ u, ∀ j < D.R.m, ∀ s ∈ D.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * O.L.sc.a) →
      GlobalTheory.Pdv.At O.ex t.ent) ?_ hT hs h1 h2 hE
  intro B X I l l0 Z O t h hs h1 h2 hE
  exact GlobalTheory.PdvClose.at_of_true_columns hA hG hC hI I h.ok h.pins l Z l0 O.L O.gatT O.Gx O.Gy O.K O.X O.cX O.ex t
    (GlobalTheory.Pdv.colNorm_of_tw I h.isTw) h.jets h.tw h.ker h.entC h.adapted h.top hs h1 h2 hE

end GlobalTheory.PdvTie
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDatumConditions_at_standardKernelComparison : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ (D : D7) (O : Obj D) (t : KerEntTied O.ex), StdTie D O t → 3 ≤ D.host.splitBound → 5 ≤ O.K.dl1 → 4 ≤ O.K.dl2 → (∀ Ee : OrbitPlaces.Ent D, OrbitPlaces.Shape D O.L O.Gx Ee ∧ ∀ u, ∀ j < D.R.m, ∀ s ∈ D.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * O.L.sc.a) → GlobalTheory.Pdv.At O.ex t.ent := by
  atlas_forward_decl GlobalTheory.PdvTie.at_of_stdTie
end
