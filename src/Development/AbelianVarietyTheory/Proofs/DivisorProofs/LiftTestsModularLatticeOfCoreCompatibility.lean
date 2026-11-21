import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeChoiceClausesOfWeakCharacterisationAtFaceAl
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PbEqOfPins
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvaluatesOfUnif
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatOfOneMapOverL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNormalisedTupleDataOverCoefficientField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientMapExtensionRationalValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSideOfModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceTupleLiftsSpanAllTuples
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsSpanOfOnto
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftTestBOfRatG
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvInjOfIsModelsOfTie
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCuspFormsFullLattice
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinsOverClauses

open GlobalTheory.CoverHalf GlobalTheory.TwistField GlobalTheory.PinnedData GlobalTheory.PinsOverField
open scoped nonZeroDivisors

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (R : RealDat D A Ks) (i : Fin D.R.m)

set_option maxHeartbeats 1000000 in

theorem exists_phi_core {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) (hV : VStd D i) (t : T0) {La : Type} [AddCommGroup La]
    [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (hι : LatEmb (Wc D i) ι)
    (M : IntermediateField ℚ ℂ) (hM : M = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hP : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (J : Ideal (𝓞 D.host.E))
    (hJ : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) :
    ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M, PhiIs R i M.val.toRingHom t ι (J • ⊤) φ := by
  have hv : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
      omegaK R.Pg y * omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y ∈ M := fun y => by
    refine mul_mem ?_ ?_
    · unfold omegaK
      split_ifs
      exacts [one_mem _, zero_mem _]
    · unfold omegaQ
      split_ifs
      · exact prod_mem fun PP _ => zpow_mem (hM ▸ xiR_mem R hR.lev hR.fam t PP.1 PP.2 _) _
      · exact zero_mem _
  obtain ⟨-, e, he, -⟩ := hR.thP.vP i t
  have hβ := GlobalTheory.T.inverse_selfDual_frame_standard_space_integral D i _ _ hV (hR.lev.βV i)
  have hi : ∀ x a, rowP (Wc D i) (R.βW i) e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun x a =>
    rowP_int _ _ _ (hR.lev.βW i) e _ he (fun PP h => hP PP (by simpa using h)) _
      (hι.2.le (LinearMap.mem_range_self ι x)) a
  refine ⟨fun q => ⟨_, hv fun PP => redM PP
    (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (q b).out)⟩, e, he, fun x =>
    ⟨(redM_uMat (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e (fun b => ι (x b)) fun b a => hi (x b) a).1, ?_⟩⟩
  exact omega_congr _ _ _ _ _ _ _ fun PP hPP => exists_datum (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e ι hi J PP (hJ PP hPP) x _
    fun b => (Submodule.Quotient.eq _).1 (Quotient.out_eq _)

set_option maxHeartbeats 2000000 in

theorem pinsOverL_of_clauses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → QGuard R → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.PinsOverL T R κ v₀ i := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O i hR _hoff _hused hfw hO hG hC
  obtain ⟨fw⟩ := id hfw
  have hT := fw.laws
  have hpb : T.pb = R.C.P.pb := GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R hT.toLawsM hR.lev (hO.2.tuple ()).half
  obtain ⟨hc', hP⟩ := hO
  have hV : VStd D i := hP.lift.std
  have hB0 := (hP.tuple ()).B
  have hb0 := hP.bad ()
  have hjL := hP.lift.field
  have hlev := hP.lift.lev
  have hio := hP.io
  have hact := hP.act
  choose l₂ hl₁ hl₂ using exists_half_tupPrime T.toCore R hT.toLawsM hR.lev hpb hG
  obtain ⟨dδ, U₂, dict₂, xi, -, hcov, hhalf, hxi, hcxi, hmod, -⟩ :=
    GlobalTheory.CoverOverField.coversAt D G Pl0 T0 A T R hT hR.lev hR.fam.roots
      (GlobalTheory.TwistValues.xiVal D G Pl0 T0 A _ R hR.lev hR.fam) hC i (Vc D i).rank _ l₂ hl₁ hl₂ (O i).c' (O i).hle hc'
  obtain ⟨gramR, c0R, c0L, hTie⟩ := hR.fam.tie
  obtain ⟨c0', hcb, hplace⟩ := GlobalTheory.Div.CoefExtension.exists_ext_placeEx D G Pl0 T0 A _ R hR.lev hR.grp.chiW hR.fam hR.models
    gramR c0R c0L hTie i (O i).c'.F (O i).jL (inC (O i).c') hjL
  have hc0 : ∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧ CoefficientBaseChange R i (O i).jL (inC (O i).c') (c0L i) c0' :=
    ⟨gramR, c0R, c0L, hTie, hcb⟩
  choose Cl fCl h J' bad Lh gam vol La Nc hrep hdv hvol hok hlat using fun t =>
    GlobalTheory.SplitReps.exists_repsR_repsOK R i (hR.lev.βV i) hV (O i).c'.F t (dδ t).l₂ hb0.1
  have hbad : ∀ t, 0 < bad t ∧ BadPin (bad t) (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1) := fun t =>
    ⟨Nat.pos_of_ne_zero (hrep t).1, hb0.2.1.trans (hdv t), hb0.2.2.1.trans (hdv t), hb0.2.2.2.1.trans (hdv t),
      hb0.2.2.2.2.trans (hdv t)⟩
  choose B hBis using fun t => exists_BIs R i hR.lev hR.fam (O i).c'.F hc' hB0 t (hdv t)
  have hodd : Odd ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) := by
    obtain ⟨e1, e2, -⟩ := hT.pins.2.2.2 _ (inR i)
    have h5 := Formalism.L2.NTheta.odd_r D.R
    have h6 := i.2
    have h7 := D.R.m_add_three_le_k
    rw [e1, e2]
    convert h5 using 1
    simp only [Ranks.sigW, Ranks.r]
    omega
  choose epF hepF using fun t => (GlobalTheory.ClassTieCompare.exists_epIs_iff (n := (Vc D i).rank) (Dw := T.Q.Dw ((i : ℕ) + 1))
    (bad t) (B t)).2 fun L cc g d => GlobalTheory.T.law_of_squares_selfDual_splitLattice _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  choose φ hφis using fun t => exists_phi_core R i hR hV t (iotaW T i) (latEmb_iotaW T hT i) (O i).c'.F hc'
    (hhalf t).2.2 (Mfr (dδ t).l₂) fun PP hPP c hc => by
    have hM : (dδ t).l₂.Mb ≤ PP.asIdeal := by
      rw [(hcov t).1.2.2.2.1]
      rcases hPP with hPP | hPP
      · rw [(hhalf t).1]
        exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
      · exact Ideal.mul_le_right.trans ((hhalf t).2.1 PP hPP)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ T.Q.H.bar.surjective).1 hc
    refine ⟨b, hM hb, ?_⟩
    change _ = star ((T.Q.H.bar b : 𝓞 D.host.E) : D.host.E)
    rw [T.Q.H.bar_eq]
    exact (star_star _).symm
  choose thAd hth using fun t => GlobalTheory.AdelicSide.exists_thAd_of_models D G Pl0 T0 A _ R hR.models i t _ _ c0' _ (h t) _
    (hrep t).2.2.1 (hrep t).2.2.2.2.2.1 (v₀ i (sg0 D A))
  refine ⟨{ c' := (O i).c', hle := (O i).hle, jL := (O i).jL, hV := (O i).hV, c0' := c0', lev := (O i).lev, dδ := dδ, Cl' := Cl,
            bad := bad, Lh := Lh, La := La, Nc := Nc, gam := gam, vol := vol, ep := fun t k => epF t (Lh t k), B := B,
            epF := epF, io := (O i).io, hw := (O i).hw, φ := φ,
            w := fun t _ q => (dδ t).eF.symm (phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q),
            U₂ := U₂, dict₂ := dict₂, xi := xi, thAd := thAd,
            Plc := fun t x => ∃ x₀, Place R i t (h t) c0' (jVx R i t x₀) x }, hc',
    ⟨hjL, hV, fw.hv₀ i _, hc0, hlev⟩,
    fun t => ⟨⟨h t, J' t, hrep t, hplace t _ _, hth t, fun _ => Iff.rfl⟩, hBis t, hxi t, hφis t, hhalf t⟩,
    hact, hbad, fun t => ⟨hok t, hlat t⟩, fun t => ⟨fun _ => rfl, hepF t⟩, hio,
    fun t k q => AlgEquiv.apply_symm_apply _ _, hcov, hcxi, hmod⟩

end GlobalTheory.PinsOverClauses
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedTupleData_over_rowField_conditions : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → QGuard R → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.PinsOverL T R κ v₀ i := by
  atlas_forward_decl GlobalTheory.PinsOverClauses.pinsOverL_of_clauses
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_lifts_span_all_tuples : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i → QGuard R → GlobalTheory.OneMapTuples.LiftsSpan R i (v₀ i (sg0 D A)) := by
  first | exact @GlobalTheory.LiftSpanClauses.liftsSpan_all_clauses | exact GlobalTheory.LiftSpanClauses.liftsSpan_all_clauses | (intros; apply GlobalTheory.LiftSpanClauses.liftsSpan_all_clauses <;> assumption)
end

section
section
noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.TwistField

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

theorem oneMapOverL_of_clauses (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m)
    (hC : GlobalTheory.Hk3.Core R F) (h1 : R.tup_mu_off) (h2 : R.tup_mu_used) (hW : Nonempty (FWTie T R κ v₀)) (hpb : T.pb = R.C.P.pb)
    (hO : OMPins T R κ v₀ O i) (hph : PhaseTie T R κ v₀ O ph i) (hio : IoExt R) (h0 : OneMapRow0 T R κ v₀ O i)
    (hex : PinsOverL T R κ v₀ i) (hsp : LiftsSpan R i (v₀ i (sg0 D A))) : OneMapOverL T R κ v₀ (ph i) i := by
  have hrow := hph h0
  obtain ⟨w⟩ := id hW
  have hT := w.laws
  have hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i := (O i).hV
  have hn : (κ i).n = (Vc D i).rank :=
    (w.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have hP : (O i).Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hO.2
  obtain ⟨gramR, c0R, c0L, hFT, hc⟩ := hP.lift.c0
  obtain ⟨lam, z₀, hlam, hU⟩ := GlobalTheory.T.adelicLift_eq_factor_mul_geometricClassSum D G Pl0 T0 A T R F κ v₀ hC h1 h2 hW hpb hio i (O i).lev gramR c0R c0L hFT
  obtain ⟨O₀, hF₀, hP₀⟩ := hex
  obtain ⟨O₁, e₁, hP₁, hlev₁, hc₁⟩ := GlobalTheory.LiftSpanClauses.exists_retie_core O₀ hC
    (show O₀.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) from hP₀) (O i).lev hP.lift.lev hP.act.1 hFT
  have hF₁ : O₁.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange := e₁ ▸ hF₀
  have hle₁ : D.what₂.embLL.toRatAlgHom.fieldRange ≤ O₁.c'.F := hF₁.ge
  obtain ⟨c0, hr, hx⟩ := hP.cxi
  obtain ⟨c1, hr₁, hx₁⟩ := hP₁.cxi
  have hid := hU _ _ (O i) hO.1.ge hP rfl hc c0 hx
  have hid₁ := hU _ _ O₁ hle₁ hP₁ hlev₁ hc₁ c1 hx₁
  have hE₁ := GlobalTheory.LiftSpanClauses.clsEx_of_core D G Pl0 T0 A T R κ v₀ hC.lev hC.fam hW hpb i _ _ O₁ hle₁ hP₁
  have n0 := ne_zero_of_root hr
  have n1 := ne_zero_of_root hr₁
  by_cases hz : ∀ y, liftQ R i (v₀ i (sg0 D A)) A.μ0 y = 0
  · exact ⟨O₁, hF₁, hP₁, oneMapOf_of_ptIdent hT hV hn hP hrow hle₁ hP₁ hlev₁ hE₁ hsp hlam n0 n1 hid hid₁ (Or.inr hz)⟩
  · obtain ⟨y, hy⟩ := not_forall.1 hz
    have hu := const_ratio_mem hT hV hn hO.1 hP hrow hle₁ hP₁ hlev₁ hE₁ hlam n1 hid hid₁ hy
    have e : ((⟨c0 / c1, hu⟩ : O₁.c'.F) : ℂ) * c1 = c0 := div_mul_cancel₀ _ n1
    have hx₂ := xiConst_scaleXi O₁ ⟨c0 / c1, hu⟩ hx₁
    have hP₂ := pins_scaleXi O₁ ⟨c0 / c1, hu⟩ (fun h => div_ne_zero n0 n1 (congrArg Subtype.val h)) hx₁ (e.symm ▸ hr) hP₁
    rw [e] at hx₂
    exact ⟨scaleXi O₁ ⟨c0 / c1, hu⟩, hF₁, hP₂, oneMapOf_of_ptIdent (O' := scaleXi O₁ ⟨c0 / c1, hu⟩) hT hV hn hP hrow hle₁ hP₂ hlev₁
      (GlobalTheory.LiftSpanClauses.clsEx_of_core D G Pl0 T0 A T R κ v₀ hC.lev hC.fam hW hpb i _ _ (scaleXi O₁ ⟨c0 / c1, hu⟩) hle₁ hP₂) hsp hlam n0 n0 hid
      (hU _ _ (scaleXi O₁ ⟨c0 / c1, hu⟩) hle₁ hP₂ hlev₁ hc₁ c0 hx₂) (Or.inl rfl)⟩

end GlobalTheory.TwistField
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneFormMap_allTuples_coeffField_of_clauses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → IoExt R → OneMapRow0 T R κ v₀ O i → GlobalTheory.TwistField.PinsOverL T R κ v₀ i → GlobalTheory.OneMapTuples.LiftsSpan R i (v₀ i (sg0 D A)) → GlobalTheory.TwistField.OneMapOverL T R κ v₀ (ph i) i := by
  atlas_forward_decl GlobalTheory.TwistField.oneMapOverL_of_clauses
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistField

set_option maxHeartbeats 2000000 in

theorem ratG_of_clauses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → (∀ i, OMPins T R κ v₀ O i) → (∀ i, PhaseTie T R κ v₀ O ph i) → IoExt R → (∀ i, OneMapRow0 T R κ v₀ O i) → QGuard R → R.LUnif → EvInj T R v₀ → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.RatG R ph := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hC hoff hused hW hO hph hio h0 hQ hU hinj hcov i t x
  obtain ⟨fw⟩ := id hW
  have hpb : T.pb = R.C.P.pb := GlobalTheory.PinsFixHalf.pb_eq_of_pins T R κ v₀ O hC.lev fw.laws hO
  have hex : PinsOverL T R κ v₀ i := GlobalTheory.T.exists_normalisedTupleData_over_rowField_conditions D G Pl0 T0 A T R F κ v₀ O i hC hoff hused hW (hO i) hQ hcov
  have hsp : GlobalTheory.OneMapTuples.LiftsSpan R i (v₀ i (sg0 D A)) :=
    GlobalTheory.T.referenceTuple_lifts_span_all_tuples D G Pl0 T0 A T R F κ v₀ O i hnV hC hoff hused hW hio (hO i) (h0 i) hQ
  have hone : OneMapOverL T R κ v₀ (ph i) i :=
    GlobalTheory.T.oneFormMap_allTuples_coeffField_of_clauses D G Pl0 T0 A T R F κ v₀ O ph i hC hoff hused hW hpb (hO i) (hph i) hio (h0 i) hex hsp
  have hev : fw.Evaluates := GlobalTheory.evaluates_of_unif D G Pl0 T0 A T R F κ v₀ fw hU
  have hrat := GlobalTheory.TwistField.Read.rat_of_oneMapOverL D G Pl0 T0 A T R F κ v₀ fw (ph i) i hC.lev hC.grp hC.models hC.thP hU
    hev hinj hone t x
  obtain ⟨y, -, hy⟩ := hrat
  exact ⟨_, hy.symm⟩

end GlobalTheory.TwistField
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLifts_of_rationalForms_rational_of_clauses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → (∀ i, OMPins T R κ v₀ O i) → (∀ i, PhaseTie T R κ v₀ O ph i) → IoExt R → (∀ i, OneMapRow0 T R κ v₀ O i) → QGuard R → R.LUnif → EvInj T R v₀ → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.RatG R ph := by
  atlas_forward_decl GlobalTheory.TwistField.ratG_of_clauses
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodLat.Obj3

theorem mLat3_of_tie {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (fw : FWTie T R.toRealDat κ v₀) : (R.toCx3 F).MLat false :=
  fun j => GlobalTheory.GoodLat.Obj.mLat_of_tie fw F.lv2 false j

end GlobalTheory.GoodLat.Obj3
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

noncomputable section

namespace GlobalTheory.PrimIn

theorem liftTests_and_mLat_of_ties : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) ∧ Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false ∧ (R.toCx3 F).MLat false := by
  intro D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O hB hG
  obtain ⟨hCore, hOff, hUsed⟩ :=
    GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D G Pl0 I0 T0 A3 _ R F hB.char hB.ex
  obtain ⟨fw, -⟩ := hG.fw
  have hM : R.toRealDat.IsModels := hB.char.base.models
  have hEv : EvInj T R.toRealDat v₀ := GlobalTheory.EvalAtUnitVectorFinal.evInj_of_isModels_of_tie T R.toRealDat κ v₀ hM fw
  have hRat : GlobalTheory.TwistField.RatG R.toRealDat (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) :=
    GlobalTheory.T.thetaLifts_of_rationalForms_rational_of_clauses D G Pl0 T0 A3.A T R.toRealDat F.lv2 κ v₀ O _ hB.nV hCore hOff hUsed ⟨fw⟩ hG.pins
      (fun i => hG.phase i hG.unif) hG.ioExt (fun i => (hG.oneMap i).1) hB.guard hG.unif hEv hG.cover
  have hLB : Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false :=
    GlobalTheory.TwistField.liftTestB_of_ratG D G Pl0 I0 T0 A3 _ R F false hG.unif hRat
  exact ⟨GlobalTheory.LiftTestCompare.liftTest_of_liftTestB _ hLB, hLB,
    GlobalTheory.GoodLat.Obj3.mLat3_of_tie T R F κ v₀ fw⟩

end GlobalTheory.PrimIn

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftTests_modularLattice_of_coreCompatibility : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) ∧ Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false ∧ (R.toCx3 F).MLat false := by
  atlas_forward_decl GlobalTheory.PrimIn.liftTests_and_mLat_of_ties
end
