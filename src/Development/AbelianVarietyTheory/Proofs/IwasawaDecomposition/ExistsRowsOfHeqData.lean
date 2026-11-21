import Mathlib
import Formalism.LocalToGlobal.Divisibility.MemberDIV
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.Divisibility.ColPins
import Formalism.LocalToGlobal.NumberFieldFamilies.EvRowSurjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
import Formalism.LocalToGlobal.Columns.KernelEquivCharacterTrivialTuple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EvGSDOkOfEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnPeriodLatticeVacuumSmooth
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IdxMatNF
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ToLinNfMatEqSumNfGen
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeSandwichOfLatticeNormalForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NuRowSuccEqWt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RamifiedColumnsTrueColumnsEqConcrete
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColMatchAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NrmStepZeroEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
import BuildAid.D3

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.Proof.TwistedNormalForms

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm GlobalTheory.QNormal

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem sum_ite_zero_eq_atN {n c : ℕ} (y : Fin (n + c) → E) :
    ∑ i : Fin c, (if i.1 = 0 then y (Fin.natAdd n i) else 0) = Loc.atN y n := by
  cases c with
  | zero => simp [Loc.atN]
  | succ c =>
    rw [Fin.sum_univ_succ]
    have h0 : ∀ i : Fin c, ¬ ((Fin.succ i).1 = 0) := fun i => by simp
    simp only [Fin.val_zero, if_true, h0, if_false, Finset.sum_const_zero, add_zero]
    unfold Loc.atN
    rw [dif_pos (by omega)]
    congr 1

theorem comb_natAdd (q : ℕ) {n c : ℕ} (e : Fin c → ℤ) (z : Sp E n) (l : Sp E n) (s : Fin c → E) (b : Fin c) :
    (Loc.inX E n c l + ∑ i, s i • nfGen q n c e z i) (Fin.natAdd n b) = (q : E) ^ e b * s b := by
  have hx : ∀ w : Sp E n, Loc.inX E n c w (Fin.natAdd n b) = 0 := fun w => by
    rw [inX_apply, dif_neg (by simp)]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, nfGen, smul_eq_mul, hx, zero_add]
  rw [Finset.sum_eq_single b]
  · have : (if b.1 = 0 then Loc.inX E n c z else 0) (Fin.natAdd n b) = 0 := by
      split_ifs <;> simp [hx]
    simp [Loc.eN, this]
    ring
  · intro i _ hib
    have hne : ¬ ((Fin.natAdd n b).1 = n + i.1) := by
      intro h; apply hib; ext; simp at h; omega
    have : (if i.1 = 0 then Loc.inX E n c z else 0) (Fin.natAdd n b) = 0 := by
      split_ifs <;> simp [hx]
    have hne' : ¬ (b.1 = i.1) := fun h => hib (Fin.ext h).symm
    simp [Loc.eN, hne', this]
  · simp

theorem comb_castAdd (q : ℕ) {n c : ℕ} (e : Fin c → ℤ) (z : Sp E n) (l : Sp E n) (s : Fin c → E) (a : Fin n) :
    (Loc.inX E n c l + ∑ i, s i • nfGen q n c e z i) (Fin.castAdd c a) =
      l a + (∑ i : Fin c, (if i.1 = 0 then (q : E) ^ e i * s i else 0)) * z a := by
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, nfGen, smul_eq_mul, inX_castAdd, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hne : ¬ (a.1 = n + i.1) := by omega
  split_ifs with hi
  · simp [Loc.eN, hne, inX_castAdd]; ring
  · simp [Loc.eN, hne]

end Lattice

theorem twNF_imp_matNF : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)),
    P ∉ Pr.vGs → ∀ h : AutY X R j, TwNF (Pr := Pr) j P h → GlobalTheory.QNF.MatNF Pr R j P h := by
  intro X Pr R j P hP h hT
  refine (GlobalTheory.QNF.nf_iff_matNF X Pr R j P hP h).1 ?_
  obtain ⟨n, z, hn, hz, hcrit⟩ := hT
  refine ⟨fun i => n i.1, z, fun i => hn i.1, hz, ?_⟩
  have hq := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  have hzV := (mem_stdAt_iff z).1 hz
  ext y
  have hmem : y ∈ h '' (lamYat (Pr := Pr) (R := R) j P : Set _) ↔ h⁻¹ y ∈ lamYat (Pr := Pr) (R := R) j P := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨h⁻¹ y, hy, by simp⟩
  rw [hmem, hcrit y]
  constructor
  · rintro ⟨hX, hN⟩
    refine ⟨fun a => y (Fin.castAdd _ a) - Loc.atN y (R.N j) * z a, (mem_stdAt_iff _).2 hX,
      fun i => ((qOf P : X.E) ^ n i.1)⁻¹ * y (Fin.natAdd _ i), hN, ?_⟩
    funext p
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · rw [comb_castAdd]
      have : ∀ i : Fin (cOf R j), (if i.1 = 0 then (qOf P : X.E) ^ n i.1 * (((qOf P : X.E) ^ n i.1)⁻¹ * y (Fin.natAdd _ i)) else 0)
          = (if i.1 = 0 then y (Fin.natAdd _ i) else 0) := fun i => by
        rw [mul_inv_cancel_left₀ (zpow_ne_zero _ hq)]
      simp only [this, sum_ite_zero_eq_atN]
      ring
    · rw [comb_natAdd, mul_inv_cancel_left₀ (zpow_ne_zero _ hq)]
  · rintro ⟨l, hl, s, hs, rfl⟩
    have hlV := (mem_stdAt_iff l).1 hl
    have hb := comb_natAdd (qOf P) (fun i : Fin (cOf R j) => n i.1) z l s
    have hat : Loc.atN (Loc.inX X.E (R.N j) (cOf R j) l + ∑ i, s i • nfGen (qOf P) (R.N j) (cOf R j) (fun i => n i.1) z i) (R.N j)
        = ∑ i : Fin (cOf R j), (if i.1 = 0 then (qOf P : X.E) ^ n i.1 * s i else 0) := by
      rw [← sum_ite_zero_eq_atN]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb i]
    refine ⟨fun a => ?_, fun i => ?_⟩
    · rw [comb_castAdd, hat, add_sub_cancel_right]
      exact hlV a
    · rw [hb i, inv_mul_cancel_left₀ (zpow_ne_zero _ hq)]
      exact hs i

end GlobalTheory.Proof.TwistedNormalForms
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.RcHyp

theorem n1_span_unitary {D : D7} (z : unitary D.host.E) : TaylorLogMetric.N1 D (Submodule.span (𝓞 D.host.E) {(z : D.host.E)}) := by
  refine (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.normOne_ideal_iff_mul_conj (D := D) _).2 ?_
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.cS_span (D := D), Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.span_singleton_mul_span_singleton_host (D := D)]
  have hz : (z : D.host.E) * D.host.conj (z : D.host.E) = 1 := by
    rw [← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj (D := D)]
    exact Unitary.mul_star_self_of_mem z.2
  rw [hz, ← Submodule.one_eq_span]

end GlobalTheory.Mem.Col2.TC.RcHyp

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.RcHyp

variable {B : Base} {X : PreX B.toPre}

theorem n1_detStd (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {n : ℕ}
    {N : Submodule (𝓞 B.fields.E) (Sp B.fields.E n)} (hN : IsSdLat N) :
    TaylorLogMetric.N1 (I.rec7 l Z) (TaylorLogMetric.detId (I.rec7 l Z) (StandardLatticesGL3.stdL (I.rec7 l Z) n) N) := by
  have h := GlobalTheory.CharValCompare.normOne_detIdeal_transportedLattice (seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G) hN
  rwa [seamOf_lat] at h

set_option maxHeartbeats 1000000 in

theorem jetsRat_chi (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (hJ : ColIn.JetsIn I)
    (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞) (a : I.ι) (u : B.Word)
    (i : ℕ) (hi : i < B.R.m) :
    (I.J.amb B χ).JetsRatDeg (B.R.N i) (B.R.N (i + 1)) (Sall (Pr := B.primes X) I.sel (I.tup a) u)
      (cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) * cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u)
      (stepDeg (Pr := B.primes X) B.wts u i) := by
  intro N N' c x hx m hm
  have hf : Th.chiFac B.host χ (B.R.N i) (B.R.N (i + 1)) N N' = Th.chiFac B.host I.chi (B.R.N i) (B.R.N (i + 1)) N N' := by
    unfold Th.chiFac
    rw [hχ (Th.detId B.host (Th.stdL B.host _) N) (n1_detStd I l Z hx.1),
      hχ (Th.detId B.host (Th.stdL B.host _) N') (n1_detStd I l Z hx.2.1)]
  have e3 : (I.J.amb B χ).e (B.R.N i) (B.R.N (i + 1)) N N' = I.A.e (B.R.N i) (B.R.N (i + 1)) N N' := by
    show I.J.V.eNat χ _ _ N N' = I.J.V.eNat I.chi _ _ N N'
    unfold Th.VacIn.eNat
    rw [hf]
  have e4 : (I.J.amb B χ).thInd (Sall (Pr := B.primes X) I.sel (I.tup a) u) N N' c x =
      I.A.thInd (Sall (Pr := B.primes X) I.sel (I.tup a) u) N N' c x := by
    funext z
    unfold Amb.thInd
    rw [e3]
    rfl
  obtain ⟨y, hy⟩ := hJ a u i hi N N' c x hx m fun τ => by
    show ((degAt m τ : ℕ) : ℤ) = _
    rw [hm τ]
    exact chain_degree_eq B.fields (B.primes X) B.R B.wts u i hi τ
  refine ⟨y, ?_⟩
  rw [e4]
  exact hy.trans (by rw [show I.A.chiF (B.R.N i) (B.R.N (i + 1)) N N' = (I.J.amb B χ).chiF (B.R.N i) (B.R.N (i + 1)) N N' from hf.symm]; rfl)

end GlobalTheory.Mem.Col2.TC.RcHyp

namespace GlobalTheory.Mem.Col2.TC.RcHyp

variable {B : Base} {X : PreX B.toPre}

theorem idxMatNF_of_isTw (I : TC B X) (h : I.Ok) (ht : I.IsTw) (a : I.ι) : GlobalTheory.QNF.IdxMatNF (I.idx a) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hm : B.R.m = (B.R.m - 2) + 2 := h.hm
  have hD := ht.deep
  have hK : TwCstQ (Pr := B.primes X) I.sel (I.tup a) I.glob :=
    twCstQ_of (fun P _ => degOne_of_ok h a P) (root_of_ok h hD a) (fun P _ => sqrt_of_ok h a P) (fun P _ => (h.idx_ok a).xiUnitAtPrime P)
  have hN := twNormAt_all (twNormDC_of (unfoldingNonvanishingDoubleCoset_holds (Ch := I.Ch) I.glob hm hK)) (fun P _ => degOne_of_ok h a P)
  rw [ht.idx_eq a]
  intro j b v hv hj1 hj2
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have H := twSt_cand (Ch := I.Ch) (sel := I.sel) (mu := I.tup a) (by omega) (hN i (by omega)) b v hv
  exact GlobalTheory.Proof.TwistedNormalForms.twNF_imp_matNF _ _ _ _ _ hv _ H.2.1

theorem evaluationDatum_ok_baseTuple (I : TC B X) (u : B.Word) :
    (evGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) I.Ps u).Ok := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have := hX.cplxK
  exact GlobalTheory.CoreHt.evGSD_ok_of_eq_one B.fields hX (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup I.mu0) I.Ps u hPr I.trueColumn_tuple_trivial_eq_one

end GlobalTheory.Mem.Col2.TC.RcHyp

namespace GlobalTheory.Mem.Col2.TC.RcHyp

variable {B : Base} {X : PreX B.toPre}

set_option maxHeartbeats 1000000 in

theorem chTh_ok_chi (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (hJ : ColIn.JetsIn I) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞)
    (a : I.ι) (u : B.Word) :
    ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.J.amb B χ) u (B.R.m - 2)) := by
  obtain ⟨hX, hPr, hW, -⟩ := base_fields_primes_ok B X
  have hX1 : B.fields.AbelianUnramifiedExtensionConditions := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1
  have hm : B.R.m = (B.R.m - 2) + 2 := h.hm
  have hL := h.idx_ok a
  have hs := seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G
  have hδ := ((I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok).1
  have hcc : TaylorLogMetric.IsCurveIdeal (I.rec7 l Z) ⊤ := ⟨top_ne_bot, by simp⟩
  have hχ0 : TaylorLogMetric.IsChi (I.rec7 l Z) I.chi := GlobalTheory.Mem.ChiIdeal.isChi_chiId _ _ I.C.isChi
  have hχ1 : TaylorLogMetric.IsChi (I.rec7 l Z) χ := by
    refine ⟨fun 𝔞 𝔟 h𝔞 h𝔟 => ?_, fun z => ?_⟩
    · rw [hχ _ h𝔞, hχ _ h𝔟, hχ _ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.normOne_ideal_mul (D := I.rec7 l Z) h𝔞 h𝔟)]
      exact hχ0.1 𝔞 𝔟 h𝔞 h𝔟
    · rw [hχ _ (n1_span_unitary (D := I.rec7 l Z) z)]
      exact hχ0.2 z
  have he : ∀ k, Even (B.R.N k) := fun k => Formalism.L2.Ker.even_rankN B.R k
  have hg : XiOffG (B.primes X) (I.tup a : Chr B.fields.F B.fields.E B.fields.K) := xiOffG_of_mem hPr h.g_mem
  have hTies : LawTies B.wts I.Ch I.sel (I.tup a) (I.cst a) I.glob :=
    lawTies_of_ok B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) hL hW ⟨I.C.eta, h.ch_tied⟩
  have hLa : ∀ i, (I.J.amb B χ).LaHyp (B.R.N i) (B.R.N (i + 1)) (ColIn.Sb I a u) := fun i => by
    have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem
    have hL0 := Formalism.L2.Ker.laHyp_ambOf_top (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) χ I.J.cD (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      hs hδ (he i) (he (i + 1)) ∅ (fun P hP => absurd hP (Finset.notMem_empty P)) (fun P hP => absurd hP (Finset.notMem_empty P))
    rw [AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
    exact ⟨hL0.1, hL0.2.1, fun P hP => (bad P hP).1, fun P hP => GlobalTheory.PeriodIdealUnit.locP_AA_eq_one _ _ _ _ _ _ _ _ P (bad P hP).2.1
      (bad P hP).2.2.1 (by simp), hL0.2.2.2.2⟩
  have hSm : ∀ i, (I.J.amb B χ).ESmooth (B.R.N i) (B.R.N (i + 1)) := fun i => by
    rw [AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
    exact Formalism.L2.Ker.Cd.ambOf_eSmooth (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar χ I.J.cD hs hcc hδ I.J.δ_ne_zero (he i) (he (i + 1))
  have hRat := jetsRat_chi I l Z hJ χ hχ a u
  have hst : ∀ i, i < B.R.m → ThEquivP (stepT (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.J.amb B χ) u i (B.wts.lamTrue u (i + 1)))
      (Sall (Pr := B.primes X) I.sel (I.tup a) u) (cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) * cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u)
      (colValF (Pr := B.primes X) B.wts I.sel (I.tup a) u i).rho (colValF (Pr := B.primes X) B.wts I.sel (I.tup a) u (i + 1)).rho := fun i hi => by
    choose e he' using fun τ => (B.hc τ).e_int ⟨i, hi⟩
    have hLa' := hLa i
    have hRat' := hRat i hi
    rw [AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G] at hLa' hRat' ⊢
    exact Cd.CarC.thEquivP_ambOf_tiesD (X := B.fields) (Pr := B.primes X) (R := B.R) (W := B.wts) (Ch := I.Ch) (sel := I.sel)
      (mu := I.tup a) (cst := I.cst a) (G := I.glob) u (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar χ I.J.cD hs hcc hδ hχ1 hX1 hPr h.sel_ok hg hTies
      (hPr.T_prime u).pos hi e (fun τ => (he' τ).symm) hLa' hRat'
  have hlaws := chThT_laws_of (Pr := B.primes X) (W := B.wts) (Ch := I.Ch) (sel := I.sel) (mu := I.tup a) (cst := I.cst a)
    (A := I.J.amb B χ) (u := u) hm hst
  have hTh : ThHypD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.J.amb B χ) u (B.R.m - 2) := by
    refine ⟨fun i hi => ⟨hLa i, hSm i, hRat i (by omega)⟩, ?_, hlaws.1, hlaws.2⟩
    have e' : B.R.N B.R.m = B.R.N (B.R.m - 2 + 1 + 1) := by rw [← hm]
    rw [e']
    exact ⟨hLa _, hSm _, hRat _ (by omega)⟩
  exact chTh_ok_ambD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.J.amb B χ) u (B.R.m - 2) (by omega) (hPr.T_prime u).pos
    (muqTie_of_ok I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) hL) hTh

end GlobalTheory.Mem.Col2.TC.RcHyp

namespace GlobalTheory.Mem.Col2.TC.RcHyp

theorem hyps_of_isTw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), I.IsTw → ColIn.JetsIn I → ∀ (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ), (∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞) → ∀ (a : I.ι) (u : B.Word), (∀ j, (chF (Pr := B.primes X) B.wts I.sel (I.tup a) (I.idx a) u j).Ok) ∧ (evGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) I.Ps u).Ok ∧ GlobalTheory.QNF.IdxMatNF (I.idx a) ∧ ∀ b hY, KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (I.J.amb B χ) u (B.R.m - 2) b hY I.Ps := by
  intro B X I h _ l Z ht hJ χ hχ a u
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  exact ⟨ht.chF_ok h B.wts a u, evaluationDatum_ok_baseTuple I u, idxMatNF_of_isTw I h ht a, fun b hY =>
    KerRat.kerEquivC (Pr := B.primes X) B.wts (I.J.amb B χ) u hX hPr h.sel_ok ⟨h.T_mem u, h.g_mem⟩ (h.idx_ok a) (h.sharp a)
      (chTh_ok_chi I h l Z hJ χ hχ a u) b hY⟩

end GlobalTheory.Mem.Col2.TC.RcHyp
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev cstT (τ : Tup B.fields.F B.fields.E B.fields.K I.S) : LocCst B.fields (rowSG (B.primes X) I.sel τ) :=
  twCst I.Ch I.sel τ I.glob

abbrev idxT (τ : Tup B.fields.F B.fields.E B.fields.K I.S) :
    ChIdx B.fields (B.primes X) B.R (QE I.sel (τ : Chr B.fields.F B.fields.E B.fields.K)) :=
  twIdx I.Ch I.sel τ (cstT I τ) (B.R.m - 2)

variable {I}

theorem cstT_tup (ht : I.IsTw) (a : I.ι) : cstT I (I.tup a) = I.cst a := (ht.cst_eq a).symm

theorem idxT_tup (ht : I.IsTw) (a : I.ι) : idxT I (I.tup a) = I.idx a := (ht.idx_eq a).symm

theorem of_forall_ix (ht : I.IsTw) {U : Set I.ι}
    (p : ∀ τ : Tup B.fields.F B.fields.E B.fields.K I.S, LocCst B.fields (rowSG (B.primes X) I.sel τ) →
      ChIdx B.fields (B.primes X) B.R (QE I.sel (τ : Chr B.fields.F B.fields.E B.fields.K)) → Prop)
    (hp : ∀ a, p (I.tup a) (I.cst a) (I.idx a)) (t : TupU I U) : p t.1 (cstT I t.1) (idxT I t.1) := by
  rw [← tup_ixOf I t, cstT_tup ht, idxT_tup ht]
  exact hp _

theorem idxT_ok (h : I.Ok) (ht : I.IsTw) {U : Set I.ι} (t : TupU I U) :
    (idxT I t.1).Ok I.Ch I.sel t.1 (cstT I t.1) I.glob (B.R.m - 2) :=
  of_forall_ix ht (fun τ c L => L.Ok I.Ch I.sel τ c I.glob (B.R.m - 2)) h.idx_ok t

variable (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞)
  (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)

def colRecC : ColRec3 B.fields (famC I hX U Xg tr) (lev1 I) (chr1 I) where
  Pr := B.primes X
  Rk := B.R
  W := B.wts
  Ch := I.Ch
  sel := I.sel
  Sg := I.S
  hX := hX
  Lv := rPsymF (R := B.R) I.Ch
  Xg := Xg
  m2 := B.R.m - 2
  Gc := I.glob
  mu := fun t => t.1
  cst := fun t => cstT I t.1
  Li := fun t => idxT I t.1
  hL := fun t => idxT_ok h ht t
  hP := fun t => mtildeOk (Pr := B.primes X) B.wts I.Ch I.sel t.1 hX _
  Mem := B.Word
  wd := fun u => u
  b := fun t _ => (idxT_ok h ht t).last_uniq.choose
  hY := fun t u => coupling_index_set_finite (Pr := B.primes X) I.sel t.1 (cstT I t.1) (idxT I t.1) u (B.R.m - 2) _
  Am := I.J.amb B χ
  hK := fun t u => of_forall_ix ht
    (fun τ c L => ∀ b hY, KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel τ c L (I.J.amb B χ) u (B.R.m - 2) b hY I.Ps)
    (fun a => (RcHyp.hyps_of_isTw I h hp l Z ht hJ χ hχ a u).2.2.2) t _ _
  hF := fun t u => of_forall_ix ht (fun τ _ L => ∀ j, (chF (Pr := B.primes X) B.wts I.sel τ L u j).Ok)
    (fun a => (RcHyp.hyps_of_isTw I h hp l Z ht hJ χ hχ a u).1) t
  hE := fun u => by
    have e := RcHyp.evaluationDatum_ok_baseTuple I u
    rw [I.trueColumn_tuple_trivial_eq_one] at e
    exact e
  ev := evC (X := B.fields) (Pr := B.primes X) B.wts I.Ch I.sel hX (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ (xiValOf I) tr
    (rPsymF (R := B.R) I.Ch)



end GlobalTheory.Mem.R3.SelC

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

theorem mem_iff_trace {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] (Xg : Finset (G → K))
    (hXg : ∀ χ ∈ Xg, IsAbsIrrChar χ) {χ : G → K} (hχ : IsAbsIrrChar χ) :
    χ ∈ Xg ↔ ∑ g, (idemOf Xg).coeff g * χ g = χ 1 := by
  classical
  have hN : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h1 : χ 1 ≠ 0 := by
    intro h0
    have h := conv_char hχ hχ
    obtain ⟨n, ρ, hi, hρ⟩ := hχ
    have e := hρ 1
    rw [h0, map_zero, Representation.char_one, Module.finrank_fin_fun, Nat.cast_eq_zero] at e
    subst e
    exact (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have hterm : ∀ ψ ∈ Xg, ∑ g, (chiIdem ψ).coeff g * χ g = if ψ = χ then χ 1 else 0 := by
    intro ψ hψ
    have h := conv_char (hXg ψ hψ) hχ 1
    simp only [mul_one] at h
    have e : ∑ g, (chiIdem ψ).coeff g * χ g = ψ 1 / (Fintype.card G : K) * ∑ g, ψ g⁻¹ * χ g := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by rw [coeff_chiIdem, mul_assoc]
    rw [e]
    split_ifs at h ⊢ with hc
    · rw [mul_right_cancel₀ h1 h, hc]
      field_simp
    · rw [(mul_eq_zero.1 h).resolve_right h1, mul_zero]
  have hsum : ∑ g, (idemOf Xg).coeff g * χ g = if χ ∈ Xg then χ 1 else 0 := by
    unfold idemOf
    simp only [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  rw [hsum]
  split_ifs with hc
  · exact iff_of_true hc rfl
  · exact iff_of_false hc h1.symm

theorem mem_iff_XgE {K G H : Type} [Field K] [CharZero K] [Group G] [Fintype G] [Group H] [Fintype H] (σ : K →+* ℂ) (eG : G ≃* H)
    (e : MonoidAlgebra ℂ H) (Xg : Finset (G → K)) (hXg : ∀ χ ∈ Xg, IsAbsIrrChar χ)
    (he : ∀ g, σ ((idemOf Xg).coeff g) = e.coeff (eG g)) (χ : G → K) :
    χ ∈ Xg ↔ (fun g => χ (eG.symm g)) ∈ XgE σ e := by
  rw [mem_XgE, isAbsIrrChar_comp_iff eG.symm, ← Equiv.sum_comp eG.toEquiv]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulEquiv.symm_apply_apply, map_one, ← he, ← map_mul, ← map_sum]
  rw [σ.injective.eq_iff]
  exact ⟨fun h => ⟨hXg χ h, (mem_iff_trace Xg hXg (hXg χ h)).1 h⟩, fun h => (mem_iff_trace Xg hXg h.1).2 h.2⟩

theorem exists_coord {K W : Type} [Field K] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) {n d : ℕ}
    (Ψ : (Fin n → K) ≃ₗ[K] (Fin d → K)) (j : (Fin n → K) →ₛₗ[σ] W)
    (li : LinearIndependent ℂ fun i => j (Pi.single i 1)) (sp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) :
    ∃ ι : W ≃ₗ[ℂ] (Fin d → ℂ), ∀ y, ι (j y) = fun a => σ (Ψ y a) := by
  classical
  let b : Module.Basis (Fin n) ℂ W := Module.Basis.mk li sp.ge
  have hb : ∀ y, b.equivFun (j y) = fun i => σ (y i) := by
    intro y
    rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [pi_eq_sum_univ' y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, Module.Basis.mk_apply]
  let A := LinearMap.toMatrix' Ψ.toLinearMap
  let A' := LinearMap.toMatrix' Ψ.symm.toLinearMap
  have h1 : A * A' = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  have h2 : A' * A = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  let E : (Fin n → ℂ) ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofLinear (Matrix.toLin' (A.map σ)) (Matrix.toLin' (A'.map σ))
    (by rw [← Matrix.toLin'_mul, ← Matrix.map_mul, h1]; simp) (by rw [← Matrix.toLin'_mul, ← Matrix.map_mul, h2]; simp)
  refine ⟨b.equivFun.trans E, fun y => ?_⟩
  rw [LinearEquiv.trans_apply, hb]
  funext a
  show (A.map σ).mulVec (σ ∘ y) a = _
  rw [← RingHom.map_mulVec]
  exact congrArg σ (congrFun (LinearMap.toMatrix'_mulVec Ψ.toLinearMap y) a)

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem rowCast_lin {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (e : Pr.vGs = SG') (A : LevFam X.E X.K (R.N R.m - 1) Pr.vGs)
    (Λ' : LevFam X.E X.K (R.N R.m - 1) SG') (hΛ : Λ' = e ▸ A) :
    ((formGSD (rowVal W SG') Λ').Ok → (rowGSD W A).Ok) ∧
      ∃ L : (formGSD (rowVal W SG') Λ').EqFun ≃ₗ[X.K] (rowGSD W A).EqFun, ∀ F, L F = rowCast W e A Λ' hΛ F := by
  subst hΛ
  subst e
  exact ⟨id, LinearEquiv.refl _ _, fun _ => rfl⟩

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (hX : X.Ok) (P : LevFam X.E X.K R.r Pr.vGs)

include hX in

theorem rowG_ok (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) : (rowGSD W (rowTyG Ch P).inv).Ok :=
  (rowCast_lin W (rcol_rowSG_eq sel mu hQ) (rowTyG Ch P).inv _ (rowTy_inv_cast Ch sel mu hQ P)).1 (mtildeOk W Ch sel mu hX P)

theorem exists_lvlEquiv : ∃ Φ : (Fin ((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlDim
      (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr) → X.K) ≃ₗ[X.K] MtildeV W Ch sel mu P,
    ∀ y, ∃ hK : (Φ y).1 ∈ (mtildeKGSD W Ch sel mu).EqFun,
      (mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX) ⟨(Φ y).1, hK⟩ =
        (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).basis.equivFun.symm
          (((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlE (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr).mulVec y) := by
  set h := mtildeKOk W Ch sel mu hX
  have hr : LinearMap.range ((MtildeKCSD W Ch sel mu h).lvlE (g0Act W Ch sel mu h) P.grp P.chr).mulVecLin =
      (MtildeKCSD W Ch sel mu h).lvlPart (g0Act W Ch sel mu h) P.grp P.chr :=
    (image_idempotent_spec X.K _ _).2.trans (level_part_spec X.K _ _ _ _ _)
  let c := (mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec
  let f0 := c.symm.toLinearMap ∘ₗ ((MtildeKCSD W Ch sel mu h).lvlE (g0Act W Ch sel mu h) P.grp P.chr).mulVecLin
  have hf0 : ∀ y, c (f0 y) = ((MtildeKCSD W Ch sel mu h).lvlE (g0Act W Ch sel mu h) P.grp P.chr).mulVec y :=
    fun y => c.apply_symm_apply _
  have hm : ∀ y, ((mtildeKGSD W Ch sel mu).EqFun.subtype ∘ₗ f0) y ∈ (mtildeGSD W Ch sel mu P).EqFun := fun y => by
    refine (mem_lvlPartX_iff W Ch sel mu P h (f0 y)).1 ?_
    rw [← hr]
    exact ⟨y, (hf0 y).symm⟩
  let f := LinearMap.codRestrict _ _ hm
  have hinj : Function.Injective f := fun y y' e => by
    have e1 : f0 y = f0 y' := Subtype.ext (congrArg Subtype.val e :)
    exact (image_idempotent_spec X.K _ _).1 ((hf0 y).symm.trans ((congrArg c e1).trans (hf0 y')))
  have hsurj : Function.Surjective f := fun x => by
    obtain ⟨hK, -⟩ := (mem_MtildeV_iff W Ch sel mu P x.1).1 x.2
    have h1 := (mem_lvlPartX_iff W Ch sel mu P h ⟨x.1, hK⟩).2 x.2
    rw [← hr] at h1
    obtain ⟨y, hy⟩ := h1
    have e1 : f0 y = ⟨x.1, hK⟩ := c.injective ((hf0 y).trans hy)
    exact ⟨y, Subtype.ext (congrArg Subtype.val e1 :)⟩
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun y => ⟨(f0 y).2, ?_⟩⟩
  rw [← hf0]
  exact (LinearEquiv.symm_apply_apply _ _).symm

theorem exists_read (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (σ : X.K →+* ℂ) (hM : (rowGSD W (rowTyG Ch P).inv).Ok)
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (j : (Fin ((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlDim
      (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr) → X.K) →ₛₗ[σ] V)
    (li : LinearIndependent ℂ fun i => j (Pi.single i 1)) (sp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) :
    ∃ ι : V ≃ₗ[ℂ] (Fin ((rowGSD W (rowTyG Ch P).inv).hDim hM) → ℂ), ∀ y,
      ∃ (F' : (mtildeKGSD W Ch sel mu).EqFun) (hm : F'.1 ∈ (mtildeGSD W Ch sel mu P).EqFun),
        (mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX) F' =
          (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).basis.equivFun.symm
            (((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlE (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr).mulVec y) ∧
        ι (j y) = zOfRow W Ch sel mu hQ P σ hM ⟨F'.1, hm⟩ := by
  obtain ⟨Φ, hΦ⟩ := exists_lvlEquiv W Ch sel mu hX P
  obtain ⟨L, hL⟩ := (rowCast_lin W (rcol_rowSG_eq sel mu hQ) (rowTyG Ch P).inv _ (rowTy_inv_cast Ch sel mu hQ P)).2
  obtain ⟨ι, hι⟩ := exists_coord σ ((Φ.trans L).trans ((rowGSD W (rowTyG Ch P).inv).hB hM).equivFun) j li sp
  refine ⟨ι, fun y => ?_⟩
  obtain ⟨hK, e⟩ := hΦ y
  refine ⟨⟨(Φ y).1, hK⟩, (Φ y).2, e, (hι y).trans ?_⟩
  unfold zOfRow zOfRow0
  rw [← hL]
  rfl

end Rows

section Weights

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem nuT_eq (u : B.Word) {i : ℕ} (hi : i < B.R.m) (τ : Tau B.R) (r : Fin (B.R.N i)) :
    ((nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) = (B.wts.nuW u (i + 1) τ).w r := by
  have e1 : ((nuT (I.rec7 l Z) u i τ r : ℕ) : ℝ) = DV.nuRow (I.rec7 l Z) u (i + 1) τ r := (nu_t_identity (I.rec7 l Z) u i hi τ r).1
  have e2 := GlobalTheory.ColPeriod.nuRow_succ_eq_wt (I.rec7 l Z) u i hi τ r r.2
  have e3 := B.wts.nuW_eq u hi τ r
  have e4 := lamOf_wtN (B.wts.hc u τ) hi.le r
  have key : (((nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) : ℝ) = (((B.wts.nuW u (i + 1) τ).w r : ℤ) : ℝ) := by
    rw [Int.cast_natCast, e1, e2, ← Rat.cast_intCast, e3]
    unfold Wts.lamN at e3 ⊢
    rw [e4]
    rfl
  exact_mod_cast key

theorem wtTie_base {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) :
    t.WtTie (fun u i τ => B.wts.lamTrue u i τ) (fun u i τ => (B.wts.lamTrue u i τ).detShift)
      (fun u i τ => nuLast (Pr := B.primes X) B.wts u i τ) := by
  intro (u : B.Word) μ i hi
  have hi' : i < B.R.m := hi
  have hN : 0 < B.R.N i := B.R.N_pos i
  have hN' : 0 < B.R.N (i + 1) := B.R.N_pos (i + 1)
  have hlt : B.R.N i < B.R.N (i + 1) := by unfold Ranks.N; rw [Nat.succ_mul]; omega
  have d0 : ∀ τ, (B.wts.lamTrue u i τ).detShift = (B.wts.lamTrue u i τ).w ⟨B.R.N i - 1, by omega⟩ := fun τ => dif_pos hN
  have d' : ∀ τ, (B.wts.lamTrue u (i + 1) τ).detShift = (B.wts.lamTrue u (i + 1) τ).w ⟨B.R.N (i + 1) - 1, by omega⟩ :=
    fun τ => dif_pos hN'
  have dn : ∀ τ, (B.wts.nuW u (i + 1) τ).detShift = (B.wts.nuW u (i + 1) τ).w (⟨B.R.N i - 1, by omega⟩ : Fin (B.R.N i)) :=
    fun τ => dif_pos hN
  have hs : ∀ (τ : Tau B.R) (r : Fin (B.R.N i)),
      (B.wts.nuW u (i + 1) τ).w r = (B.wts.lamTrue u i τ).w r + ((I.rec7 l Z).chTw u μ).sSharp i τ := fun τ r => by
    have e1 := B.wts.nuW_eq_true u hi' τ r
    have e2 : ((((I.rec7 l Z).chTw u μ).sSharp i τ : ℤ) : ℚ) = sExp' B.R ((B.wts.hc u τ).e ⟨i, hi'⟩) (i + 1) :=
      ((I.rec7 l Z).chTw u μ).sSharp_eq i hi τ
    rw [← e2] at e1
    exact_mod_cast e1
  have hl : ∀ τ, ((nuLast (Pr := B.primes X) B.wts u i τ : ℕ) : ℤ) =
      (B.wts.lamTrue u i τ).detShift + ((I.rec7 l Z).chTw u μ).sSharp i τ := fun τ => by
    rw [nuLast_eq (Pr := B.primes X) B.wts u i hi' τ, dn, hs, d0]
  refine ⟨fun (τ : Tau B.R) (r : Fin (B.R.N i)) => ?_, fun τ => (hl τ).symm, fun (τ : Tau B.R) => ?_, jet_in_weight_space_chain (Pr := B.primes X) B.wts u hi'⟩
  · have e1 := nuT_eq I l Z u hi' τ r
    have e2 := hs τ r
    have e3 := hl τ
    have hanti : (B.wts.lamTrue u i τ).detShift ≤ (B.wts.lamTrue u i τ).w r := by
      refine (d0 τ).trans_le ?_
      exact (B.wts.lamTrue u i τ).anti (by show r.1 ≤ B.R.N i - 1; have : r.1 < B.R.N i := r.2; omega)
    show ((B.wts.lamTrue u i τ).w r - (B.wts.lamTrue u i τ).detShift).toNat + nuLast (Pr := B.primes X) B.wts u i τ = nuT (I.rec7 l Z) u i τ r
    omega
  · have e1 := B.wts.lamTrue_new u hi' τ ⟨B.R.N (i + 1) - 1, by omega⟩ (by show ¬ B.R.N (i + 1) - 1 < B.R.N i; omega)
    have e2 : ((((I.rec7 l Z).chTw u μ).sDiv i τ : ℤ) : ℚ) = sExp B.R ((B.wts.hc u τ).e ⟨i, hi'⟩) (i + 1) :=
      ((I.rec7 l Z).chTw u μ).sDiv_eq i hi τ
    rw [← e2] at e1
    refine (d' τ).trans ?_
    exact_mod_cast e1

end Weights

section Chi

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem isSelfDualLattice_normOne_ideal_rankOne {D : D7} {𝔞 : TaylorLogMetric.IdE D} (h : TaylorLogMetric.N1 D 𝔞) :
    IsSDLat D.host.E 1 (Submodule.pi Set.univ fun _ : Fin 1 => 𝔞) := by
  obtain ⟨𝔟, hb, hab⟩ := h
  have hc : ∀ x : D.host.E, star x = D.host.conj x := fun x => bridge_star_holds D.R D.host x
  have hfg : 𝔞.FG := Submodule.fg_of_isUnit (IsUnit.of_mul_eq_one 𝔟 hab)
  refine ⟨Submodule.fg_pi fun _ => hfg, ?_, fun y => ?_⟩
  · obtain ⟨x, hx, h0⟩ : ∃ x ∈ 𝔞, x ≠ 0 := by
      by_contra hn
      push Not at hn
      have : 𝔞 = ⊥ := (Submodule.eq_bot_iff _).2 hn
      rw [this, Submodule.bot_mul] at hab
      have h1 : (1 : D.host.E) ∈ (1 : TaylorLogMetric.IdE D) := Submodule.one_le.1 le_rfl
      rw [← hab] at h1
      exact one_ne_zero ((Submodule.mem_bot _).1 h1)
    rw [eq_top_iff]
    intro v _
    have : v = (v 0 / x) • (fun _ : Fin 1 => x) := by
      funext i
      rw [Subsingleton.elim i 0]
      simp [h0]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span fun _ _ => hx)
  · constructor
    · intro hy x hx
      have h1 : y 0 * star (x 0) ∈ 𝔞 * 𝔟 := Submodule.mul_mem_mul (hy 0 trivial) ((hb _).2 (by rw [← hc, star_star]; exact hx 0 trivial))
      rw [hab, Submodule.mem_one] at h1
      obtain ⟨r, hr⟩ := h1
      exact ⟨r, by rw [hr]; simp [stdH, mul_comm]⟩
    · intro hy i _
      rw [Subsingleton.elim i 0]
      have h1 : Submodule.span (𝓞 D.host.E) {y 0} * 𝔟 ≤ 1 := by
        rw [Submodule.span_singleton_mul]
        intro z hz
        obtain ⟨b, hb', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
        obtain ⟨r, hr⟩ := hy (fun _ => star b) fun _ _ => by rw [hc]; exact (hb b).1 hb'
        exact Submodule.mem_one.2 ⟨r, by rw [hr]; simp [stdH, mul_comm]⟩
      have h2 : Submodule.span (𝓞 D.host.E) {y 0} ≤ 𝔞 := by
        calc Submodule.span (𝓞 D.host.E) {y 0} = 𝔞 * (Submodule.span (𝓞 D.host.E) {y 0} * 𝔟) := by
              rw [mul_left_comm, hab, mul_one]
          _ ≤ 𝔞 * 1 := mul_le_mul_right h1 𝔞
          _ = 𝔞 := mul_one _
      exact h2 (Submodule.mem_span_singleton_self _)

theorem detId_rank_one {R : Ranks} (H : Host R) (𝔞 : Submodule (𝓞 H.E) H.E) :
    Th.detId H (Th.stdL H 1) (Submodule.pi Set.univ fun _ : Fin 1 => 𝔞) = 𝔞 := by
  rw [GlobalTheory.Mem.ChiDet.detId_stdL]
  unfold GlobalTheory.Mem.Chr.detSub
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [Matrix.det_unique]
    exact hx _ _ trivial
  · intro a ha
    exact Submodule.subset_span ⟨fun _ _ => a, fun _ _ _ => ha, by rw [Matrix.det_unique]; rfl⟩

theorem chiRec_eq_chi {idl : (I.rec7 l Z).Dt ⧸ (I.rec7 l Z).UO → TaylorLogMetric.IdE (I.rec7 l Z)} (hidl : TaylorLogMetric.RelDetPinned (I.rec7 l Z) idl)
    (𝔞 : TaylorLogMetric.IdE (I.rec7 l Z)) (h : TaylorLogMetric.N1 (I.rec7 l Z) 𝔞) : TaylorLogMetric.chiRec (I.rec7 l Z) idl 𝔞 = I.chi 𝔞 := by
  have h1 : TaylorLogMetric.N1 (I.rec7 l Z) 1 := by
    have := RcHyp.n1_span_unitary (D := I.rec7 l Z) 1
    rwa [OneMemClass.coe_one, ← Submodule.one_eq_span] at this
  have hs := isSelfDualLattice_normOne_ideal_rankOne h
  have h2 := hidl.2.2.2.2 1 ⟨_, isSelfDualLattice_normOne_ideal_rankOne h1⟩ ⟨_, hs⟩
  have h3 : TaylorLogMetric.detId (I.rec7 l Z) (Submodule.pi Set.univ fun _ : Fin 1 => (1 : TaylorLogMetric.IdE (I.rec7 l Z)))
      (Submodule.pi Set.univ fun _ : Fin 1 => 𝔞) = 𝔞 := detId_rank_one B.host 𝔞
  have h4 := h2.trans h3
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (relDetQ B.host I.SQ 1 (Th.stdL B.host 1) (Submodule.pi Set.univ fun _ : Fin 1 => 𝔞))
  have h5 : idl (QuotientGroup.mk x) = 𝔞 := (congrArg idl hx).trans h4
  have h6 := GlobalTheory.Mem.ChiDet.tildeD_eq_chiId B.R B.host I.C.chiPsi I.C.isChi 1 (Submodule.pi Set.univ fun _ : Fin 1 => 𝔞) ⟨hs.1, hs.2.1⟩
    (toDtT B.host I.SQ x) (congrArg (toDtTMod B.host I.SQ) hx)
  replace h6 := h6.trans (congrArg (chiId I.C.chiPsi) (detId_rank_one B.host 𝔞))
  refine ((congrArg _ h5.symm).trans (TaylorLogMetric.chiRec_idl _ _ hidl.1 _)).trans (Eq.trans ?_ h6)
  show ((tildeQ B.host I.SQ I.C.chiPsi x : ℂˣ) : ℂ) = _
  rw [tildeQ_eq_comp B.host I.SQ (KD_le_ker_of_isChiPsi I.C.isChi)]
  rfl

theorem ker_chi_eq {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) :
    ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → t.χ 𝔞 = I.chi 𝔞 := fun 𝔞 h => by
  rw [t.χ_rec]
  exact chiRec_eq_chi I l Z t.idl_ok 𝔞 h

end Chi

end GlobalTheory.Mem.R3.SelC

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

section Congr

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  {A A' : Amb X} (hA : ∀ (a b : ℕ) T (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) c x,
    IsSdLat N → IsSdLat N' → A.jetK T N N' c x = A'.jetK T N N' c x)

include hA in

theorem kerOf_congr (u : Pr.Word) (i : ℕ) {b : ℕ} (lam' : X.Tau → DomWeight b) (T cA cB) {N : Submodule (𝓞 X.E) (Sp X.E (R.N i))}
    {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N') (fr fr' Ξ) :
    kerOf (stepC W Ch sel mu cst A u i lam') T cA cB N fr N' fr' Ξ = kerOf (stepC W Ch sel mu cst A' u i lam') T cA cB N fr N' fr' Ξ := by
  unfold kerOf stepC thDistC
  simp only [hA _ _ _ _ _ _ _ hN hN']

include hA in

theorem chKerC_congr (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : LevFam X.E X.K R.r Pr.vGs)
    (h : KerEquivC W Ch sel mu cst L A u m2 b hY P) (h' : KerEquivC W Ch sel mu cst L A' u m2 b hY P) :
    chKerC W Ch sel mu cst L A u m2 b hY P h = chKerC W Ch sel mu cst L A' u m2 b hY P h' := by
  classical
  have e1 : matK W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) = matK W Ch sel mu cst L (chTh W Ch sel mu cst A' u m2) := by
    funext i al be p p'
    exact kerOf_congr W Ch sel mu cst hA u i _ _ _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨p'.deco.2.lat, p'.deco.2.uni⟩ _ _ _
  have e2 : cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) = cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A' u m2) := by
    funext al p p' Y
    unfold cp1K
    exact if_congr Iff.rfl
      (kerOf_congr W Ch sel mu cst hA u m2 _ _ _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨p'.deco.2.lat, p'.deco.2.uni⟩ _ _ _) rfl
  have e3 : cp2K W Ch sel mu cst (chTh W Ch sel mu cst A u m2) = cp2K W Ch sel mu cst (chTh W Ch sel mu cst A' u m2) := by
    funext p Y d
    unfold cp2K
    exact if_congr Iff.rfl
      (kerOf_congr W Ch sel mu cst hA u (m2 + 1) _ _ _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩
        ⟨(tilQ sel mu u d).2.lat, (tilQ sel mu u d).2.uni⟩ _ _ _) rfl
  unfold chKerC chKer
  congr 1
  · funext i al be
    split_ifs
    · congr 1
      rw [e1]
    · rfl
  · funext al
    congr 1
    rw [e2]

end Congr

section True

open GlobalTheory.Core.Ht2 GlobalTheory.Mem.Col2.KerRat

variable {B : Base} {X : PreX B.toPre} {I : TC B X} (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
  (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞) (hX : B.fields.Ok)

include hχ in

theorem jetK_chi (a b : ℕ) (T) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E a)) (N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E b)) (c x)
    (hN : IsSdLat N) (hN' : IsSdLat N') : (I.J.amb B χ).jetK T N N' c x = I.A.jetK T N N' c x := by
  have hf : Th.chiFac B.host χ a b N N' = Th.chiFac B.host I.chi a b N N' := by
    unfold Th.chiFac
    rw [hχ (Th.detId B.host (Th.stdL B.host _) N) (RcHyp.n1_detStd I l Z hN),
      hχ (Th.detId B.host (Th.stdL B.host _) N') (RcHyp.n1_detStd I l Z hN')]
  have e3 : (I.J.amb B χ).e a b N N' = I.A.e a b N N' := by
    show I.J.V.eNat χ _ _ N N' = I.J.V.eNat I.chi _ _ N N'
    unfold Th.VacIn.eNat
    rw [hf]
  have e4 : (I.J.amb B χ).thInd T N N' c x = I.A.thInd T N N' c x := by
    funext z
    unfold Amb.thInd
    rw [e3]
    rfl
  funext m
  unfold Amb.jetK
  rw [e4, show (I.J.amb B χ).chiF a b N N' = I.A.chiF a b N N' from hf]
  rfl

include hp ht hJ hχ in

theorem exists_cpl (u : B.Word) (a : I.ι) (cst : LocCst B.fields (rowSG (B.primes X) I.sel (I.tup a)))
    (L : ChIdx B.fields (B.primes X) B.R (I.Q a)) (e1 : cst = I.cst a) (e2 : L = I.idx a) (b : L.β (B.R.m - 2 + 1))
    (hY : YbHyp (Pr := B.primes X) (R := B.R) I.sel (I.tup a) cst L u (B.R.m - 2) b)
    (hK : KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) cst L (I.J.amb B χ) u (B.R.m - 2) b hY I.Ps)
    (hF : ∀ j, (chF (Pr := B.primes X) B.wts I.sel (I.tup a) L u j).Ok) (hL : L.Ok I.Ch I.sel (I.tup a) cst I.glob (B.R.m - 2)) :
    ∃ c : CplData I u a, ∀ (φ : ColsK I u) (z : RowsK I a),
      PtilFF (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (mtildeOk (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) hX I.Ps) u
        (colC (chKerC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) cst L (I.J.amb B χ) u (B.R.m - 2) b hY I.Ps hK) hF hL φ).1 z.1 =
        c.per h hX φ z := by
  subst e1 e2
  have hK' := (RcHyp.hyps_of_isTw I h hp l Z ht hJ I.chi (fun _ _ => rfl) a u).2.2.2 b hY
  refine ⟨⟨b, hY, hK', hF⟩, fun φ z => ?_⟩
  rw [chKerC_congr (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (jetK_chi l Z χ hχ) u _ b hY I.Ps hK hK']
  rfl

theorem exists_eNu (l0 : I.Law0 l) (u : B.Word) :
    ∃ e : (Fin (ramDim (Pr := B.primes X) B.wts I.Ch hX u) → B.LL) ≃ₗ[B.LL] (Z.V.div.Nu u).V,
      (∀ v x y, Formalism.HermitianLatticesTheory.majAt (Z.V.div.Nu u).b (Z.V.div.Nu u).X v (e x) (e y) =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL _) (MramH (Pr := B.primes X) B.wts I.Ch hX u).X v x y) ∧
      ∀ x, Z.V.nuIn u (e x) = colForm I l h u I.mu0 (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x) := by
  obtain ⟨eM, hs, -, hn, -⟩ := GlobalTheory.AtG.ramCols_true I h l Z l0 u
  let eL : (Z.V.div.Nu u).V ≃ₗ[B.LL] MramV (Pr := B.primes X) B.wts I.Ch u := { eM with map_smul' := hs }
  let bs := ramBas (Pr := B.primes X) B.wts I.Ch hX u
  have hin : ∀ x, Z.V.nuIn u ((bs.equivFun.symm.trans eL.symm) x) =
      colForm I l h u I.mu0 (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x) := fun x =>
    (hn _).trans (congrArg (fun φ : MramV (Pr := B.primes X) B.wts I.Ch u => colForm I l h u I.mu0 φ.1) (eL.apply_symm_apply _))
  refine ⟨bs.equivFun.symm.trans eL.symm, fun v x y => ?_, hin⟩
  haveI : IsTotallyComplex B.LL := hX.cplxK
  refine GlobalTheory.Mem.RowSides.majAt_eq_of_normAt _ _ _ _ v (bs.equivFun.symm.trans eL.symm).toLinearMap (fun x => congrArg (· ^ 2) ?_) x y
  refine (Z.V.nuIn_norm u v _).trans ?_
  rw [LinearEquiv.coe_coe, hin]
  refine (GlobalTheory.Core.ColNorm.nrm_stepZero_eq I h hX l u I.mu0 _ (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x) (fun _ => rfl) v).trans ?_
  refine (ramInclH_norm (Pr := B.primes X) B.wts I.Ch hX u v (bs.equivFun.symm x)).symm.trans ?_
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  congr 2
  funext i
  exact congrArg v.embedding (congrFun (bs.equivFun.apply_symm_apply x) i)

include hJ in

theorem perCol_eq (l0 : I.Law0 l) (e : ∀ a : (I.cols l).Tup, Df.MtCx I a ≃ₗ[ℂ] Z.W.Amb a)
    (h0 : ∀ u F, Df.SameForm I l u I.mu0 F ((Z.W.eMt0 u).symm (e (I.cols l).mu0 F)))
    (h1 : ∀ u (a : (I.cols l).Tup) F, Df.SameForm I l u a F ((Z.W.eMtTw u a).symm (e a F)))
    (u : B.Word) (a : I.ι) (c : CplData I u a) (n : (Z.V.div.Nu u).V) (φ : ColsK I u) (hn : Z.V.nuIn u n = colForm I l h u I.mu0 φ)
    (z : RowsK I a) : Z.W.perCol u a (Z.V.jN u n) (e a (Df.toCx I hX a z)) = B.embLL (c.per h hX φ z) := by
  obtain ⟨-, -, -, -, hT⟩ := GlobalTheory.AtG.ramCols_true I h l Z l0 u
  have hM := (colMatchAll I h hX l Z hJ u a).2 c (colForm I l h u a φ) φ
  have hj := (Z.V.nuIn_jN u n).trans (congrArg ((I.fm l u I.mu0).emb 0) hn)
  by_cases ha : a = I.mu0
  · subst ha
    refine (Z.W.perCol_base_eq_PtilCol u _ _).trans ?_
    rw [hj]
    exact hM _ z (fun _ => rfl) fun p => h0 u _ p
  · refine (Z.W.perCol_tie u a ha _ _).trans ?_
    rw [hj, ← hT a φ]
    exact hM _ z (fun _ => rfl) fun p => h1 u a _ p

set_option maxHeartbeats 1000000 in

theorem face_pt (l0 : I.Law0 l) (e : ∀ a : (I.cols l).Tup, Df.MtCx I a ≃ₗ[ℂ] Z.W.Amb a)
    (h0 : ∀ u F, Df.SameForm I l u I.mu0 F ((Z.W.eMt0 u).symm (e (I.cols l).mu0 F)))
    (h1 : ∀ u (a : (I.cols l).Tup) F, Df.SameForm I l u a F ((Z.W.eMtTw u a).symm (e a F)))
    (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)
    (Zs : DefSub (famC I hX U Xg tr).fam3.amb3) (u : B.Word) (a : I.ι) (ha) (x : Fin (ramDim (Pr := B.primes X) B.wts I.Ch hX u) → B.LL)
    (n : (Z.V.div.Nu u).V) (hn : Z.V.nuIn u n = colForm I l h u I.mu0 (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x))
    (f : Fin (((famC I hX U Xg tr).side3 (lev1 I) (chr1 I) Zs).nV ⟨I.tup a, ha⟩) → B.LL) (z : RowsK I a)
    (hz : z.1 = ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).ev Zs ⟨I.tup a, ha⟩ f).1.1) :
    B.embLL (((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).face Zs).Pt u ⟨I.tup a, ha⟩ x f) =
      Z.W.perCol u a (Z.V.jN u n) (e a (Df.toCx I hX a z)) := by
  obtain ⟨c, hc⟩ := exists_cpl h hp l Z ht hJ χ hχ hX u a _ _ (cstT_tup ht a) (idxT_tup ht a)
    ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).b ⟨I.tup a, ha⟩ u) ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hY ⟨I.tup a, ha⟩ u)
    ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hK ⟨I.tup a, ha⟩ u) ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hF ⟨I.tup a, ha⟩ u)
    ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hL ⟨I.tup a, ha⟩)
  rw [perCol_eq h l Z hJ hX l0 e h0 h1 u a c n _ hn z, ← hc, hz]
  rfl

end True

end GlobalTheory.Mem.R3.SelC

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

theorem exists_moved {K T : Type} [Field K] {σ : K →+* ℂ} {n : ℕ} {A : T → Type} [∀ t, AddCommGroup (A t)] [∀ t, Module ℂ (A t)]
    {V : Type} [AddCommGroup V] [Module ℂ V] {a b : T} (h : a = b) (E : V ≃ₗ[ℂ] A b) (j : (Fin n → K) →ₛₗ[σ] A a)
    (li : LinearIndependent ℂ fun i => j (Pi.single i 1)) (sp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) :
    ∃ j' : (Fin n → K) →ₛₗ[σ] V, (∀ y, j' y = E.symm (h ▸ j y)) ∧ (LinearIndependent ℂ fun i => j' (Pi.single i 1)) ∧
      Submodule.span ℂ (Set.range fun i => j' (Pi.single i 1)) = ⊤ := by
  subst h
  refine ⟨E.symm.toLinearMap.comp j, fun _ => rfl, li.map' E.symm.toLinearMap E.symm.ker, ?_⟩
  have := congrArg (Submodule.map E.symm.toLinearMap) sp
  rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at this

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
  (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem exists_read_fam {s : ℕ} (hOk : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.Ok s)
    (σ : X.K →+* ℂ) (hM : (rowGSD W (rowTyG Ch P).inv).Ok) {T : Type} {A : T → Type} [∀ t, AddCommGroup (A t)] [∀ t, Module ℂ (A t)]
    {V : Type} [AddCommGroup V] [Module ℂ V] {b : T} (E : V ≃ₗ[ℂ] A b) (tup : TupF TU → T) (h0 : tup (mu0F TU) = b)
    (inj : Function.Injective tup)
    (j : ∀ t : TupF TU, (Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlDim
      ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r P.grp P.chr) → X.K) →ₛₗ[σ] A (tup t))
    (li : ∀ t, LinearIndependent ℂ fun i => j t (Pi.single i 1))
    (sp : ∀ t, Submodule.span ℂ (Set.range fun i => j t (Pi.single i 1)) = ⊤)
    (Zs : DefSub (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.amb3) :
    ∃ ι : V ≃ₗ[ℂ] (Fin ((rowGSD W (rowTyG Ch P).inv).hDim hM) → ℂ),
      (∀ (t : TupF TU) (ht : tup t = b) (hQ : QE sel (t.1 : Chr X.F X.E X.K) = ∅) y,
        ∃ (F' : (mtildeKGSD W Ch sel t.1).EqFun) (hm : F'.1 ∈ (mtildeGSD W Ch sel t.1 P).EqFun),
          HEq ((mtildeKGSD W Ch sel t.1).res (mtildeKOk W Ch sel t.1 hX) F')
            (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.basis.equivFun.symm
              ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.cutE ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r
                (lvlIdem P.grp P.chr)).mulVec y)) ∧
          ι (E.symm (ht ▸ j t y)) = zOfRow W Ch sel t.1 hQ P σ hM ⟨F'.1, hm⟩) ∧
      ∀ (t : TupF TU) (ht : tup t = b) (hQ : QE sel (t.1 : Chr X.F X.E X.K) = ∅)
        (F : Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t) → X.K),
        ∃ hm : (evC W Ch sel hX v0 TU Xg S0 xiVal trIv P Zs t F).1.1 ∈ (mtildeGSD W Ch sel t.1 P).EqFun,
          ι (E.symm (ht ▸ j t ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlPr
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r P.grp P.chr *
            ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).vE
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F))) =
            zOfRow W Ch sel t.1 hQ P σ hM ⟨_, hm⟩ := by
  have hQ0 := Formalism.L2.DIV.twistPrimes_trivialTuple_empty (X := X) (S := S) sel
  obtain ⟨j', hj, li', sp'⟩ := exists_moved (A := A) h0 E (j (mu0F TU)) (li _) (sp _)
  obtain ⟨ι, hι⟩ := exists_read W Ch sel (mu0F TU).1 hX P hQ0 σ hM j' li' sp'
  refine ⟨ι, fun t e hQ y => ?_, fun t e hQ F => ?_⟩
  · obtain rfl : t = mu0F TU := inj (e.trans h0.symm)
    obtain ⟨F', hm, e1, e2⟩ := hι y
    exact ⟨F', hm, heq_of_eq e1, (congrArg ι (hj y)).symm.trans e2⟩
  · obtain rfl : t = mu0F TU := inj (e.trans h0.symm)
    obtain ⟨F', hm, e1, e2⟩ := hι ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R (mu0F TU)).S.lvlPr
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R (mu0F TU)).r P.grp P.chr *
            ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R (mu0F TU)).vE
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F)
    have e3 : F' = (evC W Ch sel hX v0 TU Xg S0 xiVal trIv P Zs (mu0F TU) F).1 :=
      ((mtildeKGSD W Ch sel (mu0F TU).1).res (mtildeKOk W Ch sel (mu0F TU).1 hX)).injective
        (e1.trans (evC_res_lvl W Ch sel hX v0 TU Xg S0 xiVal trIv P hOk Zs (mu0F TU) F).symm)
    subst e3
    exact ⟨hm, (congrArg ι (hj _)).symm.trans e2⟩

end Gen

section Main

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem tup_heq (ht : I.IsTw) (U : Set I.ι) (X' : Fields) (hx : X' = B.fields) (Pr : Primes X')
    (sel : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)) (S : Set ℕ) (tup : I.ι → Tup X'.F X'.E X'.K S)
    (cst : ∀ a, LocCst X' (rowSG Pr sel (tup a))) (idx : ∀ a, ChIdx X' Pr B.R (QE sel (tup a : Chr X'.F X'.E X'.K)))
    (h1 : HEq Pr (B.primes X)) (h2 : HEq sel I.sel) (h3 : S = I.S) (h4 : HEq tup I.tup) (h5 : HEq cst I.cst) (h6 : HEq idx I.idx) :
    HEq (fun t : TupU I U => t.1) (fun t => tup (ixOf I U t)) ∧ HEq (fun t : TupU I U => cstT I t.1) (fun t => cst (ixOf I U t)) ∧
      HEq (fun t : TupU I U => idxT I t.1) (fun t => idx (ixOf I U t)) := by
  subst hx h3
  cases h1
  cases h2
  cases h4
  cases h5
  cases h6
  refine ⟨heq_of_eq (funext fun t => (tup_ixOf I t).symm), Function.hfunext rfl fun t t' e => ?_, Function.hfunext rfl fun t t' e => ?_⟩
  · cases e
    rw [← cstT_tup ht, tup_ixOf]
  · cases e
    rw [← idxT_tup ht, tup_ixOf]

variable (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)
  {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
  {Kc : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX}

theorem iT_heq {t : KerEntTied ex} (hS : I.StdKer l Z t) (τ : (I.rec7 l Z).what₂.Tau) : HEq (t.seam.iT.symm τ) τ := by
  have key : ∀ (X' : Fields) (_ : X' = B.fields) (s : Seam (I.rec7 l Z) X'),
      HEq s (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) → HEq (s.iT.symm τ) τ := by
    intro X' hx s hs
    subst hx
    cases hs
    rfl
  exact key _ hS.X_eq _ hS.seam

abbrev colRecK (t : KerEntTied ex) : ColRec3 B.fields (famC I hX U Xg tr) (lev1 I) (chr1 I) :=
  colRecC h hp l Z ht hJ t.χ (ker_chi_eq I l Z t) hX U Xg tr

def colK (hOk : (famC I hX U Xg tr).fam3.Ok3 1) (T : Formalism.L2.TiedDataSK ex) (hS : I.StdKer l Z T.ker)
    (Sp : ∀ Zs, SPer ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs))
    (R : Member.ExtendedDataRemainder ex (famC I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) (colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Sp)
    (htup : R.I.tup = ixOf I U) (hw : ∀ u, R.I.wU u = u) : SquareIntegrableColumnsCompatible T R.extendedDatum where
  X := B.fields
  e := B.tauLL
  c := colRecK h hp l Z ht hJ hX U Xg tr T.ker
  Sp := Sp
  colTie := ⟨rfl, HEq.rfl⟩
  kerTie := by
    obtain ⟨h1, h2, h3⟩ := tup_heq ht U T.ker.X hS.X_eq T.ker.Pr T.ker.sel T.ker.S T.ker.tup T.ker.cst T.ker.idx hS.Pr hS.sel hS.S hS.tup
      hS.cst hS.idx
    rw [← htup] at h1 h2 h3
    exact ⟨hS.X_eq, rfl, hS.Pr.symm, hS.Ch.symm, hS.sel.symm, heq_of_eq hS.S.symm, h1, h2, h3, hS.m2.symm, hS.glob.symm, hS.amb.symm, rfl,
      hS.word.symm⟩
  wTie := fun u => heq_of_eq (hw u)
  lvTie := rfl
  sgTie := rfl
  v0 := InfinitePlace.mk B.embLL
  TU := tuOf I U
  xiVal := xiValOf I
  trIv := tr
  famEq := HEq.rfl
  gEq := rfl
  plEq := rfl
  i0Eq := rfl
  tEq := rfl
  muTie := fun _ => rfl
  ok1 := hOk

section Pins

variable {h hp l Z ht hJ hX U Xg tr} {hOk : (famC I hX U Xg tr).fam3.Ok3 1} {T : Formalism.L2.TiedDataSK ex} {hS : I.StdKer l Z T.ker}
  {Sp : ∀ Zs, SPer ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs)}
  {R : Member.ExtendedDataRemainder ex (famC I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) (colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Sp}
  {htup : R.I.tup = ixOf I U} {hw : ∀ u, R.I.wU u = u}

theorem lamOfCol_colK : lamOfCol (colK h hp l Z ht hJ hX U Xg tr hOk T hS Sp R htup hw) = fun u i τ => B.wts.lamTrue u i τ := by
  funext u i τ
  exact congrArg (B.wts.lamTrue u i) (eq_of_heq ((cast_heq _ _).trans (iT_heq l Z hS τ)))

theorem colPins_colK : ColPins (colK h hp l Z ht hJ hX U Xg tr hOk T hS Sp R htup hw) where
  grpTie := HEq.rfl
  psTie := ⟨HEq.rfl, HEq.rfl⟩
  pointCharacterEq := ⟨HEq.rfl, HEq.rfl⟩
  wOk := (base_fields_primes_ok B X).2.2.1
  chOk := h.ch_ok
  hcTie := fun u τ => heq_of_eq (congrArg (B.hcW u) (eq_of_heq ((cast_heq _ _).trans (iT_heq l Z hS τ))))
  wtTie := by
    rw [lamOfCol_colK]
    exact ⟨_, _, wtTie_base I l Z T.ker⟩
  xgTie := fun χ => @mem_iff_XgE _ _ _ _ _ _ _ _ (_) B.embLL R.I.eG _ Xg hOk.ok2.irr R.tied.div.grp.e0 χ
  qNF := fun t => of_forall_ix ht (fun _ _ L => GlobalTheory.QNF.IdxMatNF L) (RcHyp.idxMatNF_of_isTw I h ht) t
  columnEvaluationOk := ⟨rowG_ok (Pr := B.primes X) B.wts I.Ch I.sel _ hX I.Ps (Formalism.L2.DIV.twistPrimes_trivialTuple_empty (X := B.fields) (S := I.S) I.sel), fun u => by
    have H := exists_read_fam (X := B.fields) (Pr := B.primes X) B.wts I.Ch I.sel hX (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ (xiValOf I) tr
      I.Ps hOk.ok2 B.embLL (rowG_ok (Pr := B.primes X) B.wts I.Ch I.sel _ hX I.Ps (Formalism.L2.DIV.twistPrimes_trivialTuple_empty (X := B.fields) (S := I.S) I.sel))
      (A := (I.rec7 l Z).what₂.Amb) ((I.rec7 l Z).eMt u) R.I.tup R.tied.div.tup.mu0 R.tied.div.tup.inj R.I.jA
      (fun t => (R.tied.div.sharp.forms t).li) (fun t => (R.tied.div.sharp.forms t).span) R.Zs
    exact H⟩

end Pins

end Main

set_option maxHeartbeats 1000000 in

theorem exists_rowsKC_colPins : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I) (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL))
    (tr : TrI B X) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z))
    (Kc : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX),
    (famC I hX U Xg tr).fam3.Ok3 1 → ∀ (T : Formalism.L2.TiedDataSK ex), I.StdKer l Z T.ker →
    ∀ (Sp : ∀ Zs, SPer ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs)) (P : Formalism.L2.Rows.RowSideFamily ex),
    P.Gp = Gc B X → HEq P.grp (inferInstance : Group (Gc B X)) → P.Pl0 = PlS B X → P.I0 = PlI B X → P.T = TupU I U →
    HEq P.A3 (famC I hX U Xg tr) → HEq P.P0 (lev0 I) → HEq P.ψ0 (chr0 I) → HEq P.Ps (lev1 I) → HEq P.ψs (chr1 I) →
    HEq P.I.tup (ixOf I U) → (∀ u, HEq (P.I.wU u) u) →
    ∀ Zs : DefSub (famC I hX U Xg tr).fam3.amb3, HEq P.Zs Zs → HEq P.Dc ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs) →
    HEq P.Sp (Sp Zs) →
    ∃ K : SquareIntegrableColumnsCompatible T P, ColPins K ∧ HEq K.c (colRecK h hp l Z ht hJ hX U Xg tr T.ker) ∧ HEq K.Sp Sp ∧ HEq K.c.W B.wts ∧
      HEq (fun Zs => K.c.face Zs) (colRecK h hp l Z ht hJ hX U Xg tr T.ker).face ∧ HEq K.c.Xg Xg := by
  intro B X I h hp l Z ht hJ hX U Xg tr L hT Gi Gl Kc Y cX ex hOk T hS Sp P
  obtain @⟨Gp, grp, fin, Pl0, I0, Tt, A3, P0, ψ0, Ps, ψs, Zs', S0, S1, Dc, Sp', C, NuC, J, JA, JM, tied⟩ := P
  intro e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 Zs e13 e14 e15
  dsimp only at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  subst e1 e3 e4 e5
  obtain rfl := eq_of_heq e2
  obtain rfl : fin = fintype_GLs B.fields.E (B.primes X).vGs B.R.r := Subsingleton.elim _ _
  cases e6
  cases e7
  cases e8
  cases e9
  cases e10
  cases e13
  cases e14
  cases e15
  exact ⟨colK h hp l Z ht hJ hX U Xg tr hOk T hS Sp ⟨Zs, S0, S1, C, NuC, J, JA, JM, tied⟩ (eq_of_heq e11) fun u => eq_of_heq (e12 u),
    colPins_colK, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory.Mem.R3.SelC

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.SelC

theorem pack_heq {D : D7} (p q : Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
      (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : Formalism.L2.Pj.CoreJ D) (_ : Algebra C.Q.c.F D.what₂.LL)
      (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3), G0 R.Pg D.R.r ≃* G0g D.nd) (e : p = q) :
    letI := p.2.1; letI := p.2.2.1; letI := p.2.2.2.2.2.2.2.2.1; letI := q.2.1; letI := q.2.2.1; letI := q.2.2.2.2.2.2.2.2.1
    (p.1 = q.1 ∧ HEq p.2.1 q.2.1 ∧ p.2.2.2.1 = q.2.2.2.1 ∧ p.2.2.2.2.1 = q.2.2.2.2.1 ∧ p.2.2.2.2.2.1 = q.2.2.2.2.2.1 ∧
      HEq p.2.2.2.2.2.2.1 q.2.2.2.2.2.2.1) ∧
    (HEq p.2.2.2.2.2.2.2.2.2.2.1.P0 q.2.2.2.2.2.2.2.2.2.2.1.P0 ∧ HEq p.2.2.2.2.2.2.2.2.2.2.1.ψ0 q.2.2.2.2.2.2.2.2.2.2.1.ψ0 ∧
      HEq p.2.2.2.2.2.2.2.2.2.2.1.P1 q.2.2.2.2.2.2.2.2.2.2.1.P1 ∧ HEq p.2.2.2.2.2.2.2.2.2.2.1.ψ1 q.2.2.2.2.2.2.2.2.2.2.1.ψ1 ∧
      HEq p.2.2.2.2.2.2.2.2.2.2.1.Dc q.2.2.2.2.2.2.2.2.2.2.1.Dc ∧ HEq p.2.2.2.2.2.2.2.2.2.2.1.Sp q.2.2.2.2.2.2.2.2.2.2.1.Sp) ∧
    HEq (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1) (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1) ∧
    HEq (p.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1))
      (q.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1)) ∧
    HEq (p.2.2.2.2.2.2.2.2.2.2.1.Sp (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1))
      (q.2.2.2.2.2.2.2.2.2.2.1.Sp (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1)) ∧
    (p.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1)).Mem =
      (q.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1)).Mem := by
  subst e
  exact ⟨⟨rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl⟩, ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩, HEq.rfl, HEq.rfl, HEq.rfl, rfl⟩

theorem heq_app {A M M' : Type} (e : M = M') {f : A → M} {g : A → M'} (h : HEq f g) (u : A) : HEq (f u) (g u) := by
  subst e
  cases h
  rfl

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}

set_option maxHeartbeats 1000000 in

theorem jA_row {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) (r : RXs t) (pin : ColPin w)
    (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (w.D Z) 𝔞 → χ 𝔞 = w.I.chi 𝔞) (a : w.I.ι) (ha)
    (j : (Fin (rDim (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) ⟨w.I.tup a, ha⟩) → B.LL) → Z.W.Amb a)
    (hj : SameOn (r.all.jA a) j) (Zs : DefSub (famT t).fam3.amb3)
    (F : Fin (((famT t).side3 (lev1 w.I) (chr1 w.I) Zs).nV ⟨w.I.tup a, ha⟩) → B.LL) :
    ∃ z : GlobalTheory.Core.Ht2.RowsK w.I a,
      z.1 = ((colRecC w.ok w.pins w.l Z pin.isTw pin.jets χ hχ t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).ev Zs ⟨w.I.tup a, ha⟩ F).1.1 ∧
      j ((rV0 (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) ⟨w.I.tup a, ha⟩).mulVec F) = r.e a (Df.toCx w.I t.hX a z) := by
  obtain ⟨z, ⟨F', hF', e1, e2⟩, e3⟩ := r.crd a ((rV0 (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) ⟨w.I.tup a, ha⟩).mulVec F)
  have e4 := evC_res_lvl (X := B.fields) (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel t.hX (InfinitePlace.mk B.embLL)
    (tuOf w.I (usedOf w.I T Wt)) t.r.z.Xg ∅ (xiValOf w.I) t.r.z.tr (TC.Ps w.I) t.r.intersectionNumber_baseChange.ok.ok2 Zs ⟨w.I.tup a, ha⟩ F
  have e5 := LinearEquiv.injective _ (eq_of_heq (e1.trans (heq_of_eq e4.symm)))
  refine ⟨z, ?_, (hj.2 _ _ fun i i' e => congrArg _ (Fin.ext e)).symm.trans e3⟩
  rw [e2]
  exact congrArg Subtype.val e5

variable {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}

set_option maxHeartbeats 1000000 in

theorem exists_readC (t : RowsT K w Z Wt ex.p0) (r : RXs t) (pin : ColPin w) (k : Formalism.L2.Ker.KerEntTied ex) (Sp Zsc) :
    ∃ C : ReadC t.r.z.R (reFace t.r.z.F
      (colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr k).face Sp Zsc) ex.p0 t.r.Y,
      C.wU = fun u => u := by
  choose e he hn using exists_eNu w.ok w.l Z t.hX w.l0
  refine ⟨{ wU := fun u => u
            bij := Function.bijective_id
            eNu := e
            NuC := fun u => (Z.V.div.Nu u).L.comap ((e u).toLinearMap.restrictScalars (𝓞 B.LL))
            nu := fun u => ⟨(Submodule.map_comap_eq_of_surjective (f := (e u).toLinearMap.restrictScalars (𝓞 B.LL)) (e u).surjective _).symm, he u⟩
            pt := fun u s x F => ?_ }, rfl⟩
  have key : ∀ (a : w.I.ι) (s : TupU w.I (usedOf w.I T Wt)) (_ : w.I.tup a = s.1)
      (j : (Fin (rDim (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) s) → B.LL) → Z.W.Amb a) (_ : SameOn (r.all.jA a) j)
      (Zs : DefSub (famT t).fam3.amb3) (F : Fin (((famT t).side3 (lev1 w.I) (chr1 w.I) Zs).nV s) → B.LL),
      B.embLL (((colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr k).face Zs).Pt u s x F) =
        Z.W.perCol u a (Z.V.jN u (e u x)) (j ((rV0 (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) s).mulVec F)) := by
    rintro a ⟨τ, ha⟩ (rfl : w.I.tup a = τ) j hj Zs F
    obtain ⟨z, hz, e1⟩ := jA_row t r pin k.χ (ker_chi_eq w.I w.l Z k) a ha j hj Zs F
    rw [e1]
    exact face_pt w.ok w.pins w.l Z pin.isTw pin.jets k.χ (ker_chi_eq w.I w.l Z k) t.hX w.l0 r.e r.eMt0 r.eMtTw _ _ _ Zs u a ha x _
      (hn u x) F z hz
  exact key (t.r.Y.tup s) s ((congrArg w.I.tup (t.r.tup_ix s)).trans (tup_ixOf w.I s)) (t.r.Y.jA s) (r.jA_use s) _ F

set_option maxHeartbeats 400000 in

theorem args_pins (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t) :
    (a.x.G = Gc B w.px ∧ HEq a.x.grp (inferInstance : Group (Gc B w.px)) ∧ a.x.Pl0 = PlS B w.px ∧ a.x.I0 = PlI B w.px ∧
      a.x.T = TupU w.I (usedOf w.I T Wt) ∧ HEq a.x.A3 (famC w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr)) ∧
    (HEq a.x.F.P0 (lev0 w.I) ∧ HEq a.x.F.ψ0 (chr0 w.I) ∧ HEq a.x.F.P1 (lev1 w.I) ∧ HEq a.x.F.ψ1 (chr1 w.I) ∧ HEq a.x.F.Dc a.Dc ∧
      HEq a.x.F.Sp a.Sp) ∧
    ∃ Zs : DefSub (famT t).fam3.amb3, HEq (zsOf a.x.R a.x.F) Zs ∧ HEq (a.x.F.Dc (zsOf a.x.R a.x.F)) (a.Dc Zs) ∧
      HEq (a.x.F.Sp (zsOf a.x.R a.x.F)) (a.Sp Zs) ∧ (a.x.F.Dc (zsOf a.x.R a.x.F)).Mem = (a.Dc Zs).Mem :=
  ⟨by kexactB (@pack_heq (w.st Z).toD7 _ _ a.pack).1, by kexactB (@pack_heq (w.st Z).toD7 _ _ a.pack).2.1,
    zsOf ((t.r.z.R.updS t.r.z.R.kap a.lam).withErr a.err) (reFace t.r.z.F a.Dc a.Sp a.Zsc),
    by kexactB (@pack_heq (w.st Z).toD7 _ _ a.pack).2.2⟩

set_option maxHeartbeats 400000 in

theorem exists_cols (t : RowsT K w Z Wt ex.p0) (pin : ColPin w) (S : Formalism.L2.TiedDataSK ex) (hS : TC.StdKer w.I w.l Z S.ker)
    (a : TwArgs ex t) (hD : a.Dc = (colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr S.ker).face)
    (hw : HEq a.x.C.wU fun u : B.Word => u) :
    ∃ C : GlobalTheory.Cp.SquareIntegrableColumnsCompatible S (divisionPairOfAdelicFormsFaceColumnsData a.x), HEq (fun Zs => C.c.face Zs) a.x.F.Dc ∧ HEq C.Sp a.x.F.Sp ∧ HEq C.c.W B.wts ∧
      HEq C.c.Xg t.r.z.Xg ∧ Formalism.L2.DIV.ColPins C.toS := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨h7, h8, h9, h10, g11, g12⟩, Zs, g13, g14, g15, g16⟩ := args_pins t a
  obtain ⟨Sp, hSp⟩ : ∃ Sp : ∀ Zs, SPer ((colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr S.ker).face Zs),
      HEq a.Sp Sp ∧ ∀ Zs, HEq (a.Sp Zs) (Sp Zs) := by
    have key : ∀ Dc : type_of% a.Dc, a.Dc = Dc → ∃ Sp : ∀ Zs, SPer (Dc Zs), HEq a.Sp Sp ∧ ∀ Zs, HEq (a.Sp Zs) (Sp Zs) := by
      rintro _ rfl
      exact ⟨a.Sp, HEq.rfl, fun _ => HEq.rfl⟩
    kexactB key _ hD
  have e1 := congrFun hD Zs
  have e2 : (a.x.F.Dc (zsOf a.x.R a.x.F)).Mem = B.Word := by kexactB g16.trans (congrArg DefCols.Mem e1)
  have e3 : HEq a.x.Y.tup (ixOf w.I (usedOf w.I T Wt)) := by kexactB a.tup.trans (heq_of_eq (funext t.r.tup_ix))
  have e4 : ∀ u, HEq (a.x.C.wU u) u := fun u => heq_app e2 hw u
  have e5 := g14.trans (heq_of_eq e1)
  have e6 := g15.trans (hSp.2 Zs)
  obtain ⟨C, c1, -, c3, c4, c5, c6⟩ := exists_rowsKC_colPins w.I w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr
    L hT Gi Gl Kc Yd cX ex t.r.intersectionNumber_baseChange.ok S hS Sp (divisionPairOfAdelicFormsFaceColumnsData a.x) (by kexactB h1) (by kexactB h2) (by kexactB h3) (by kexactB h4) (by kexactB h5)
    (by kexactB h6) (by kexactB h7) (by kexactB h8) (by kexactB h9) (by kexactB h10) (by kexactB e3) (by kexactB e4) Zs (by kexactB g13)
    (by kexactB e5) (by kexactB e6)
  have d1 := (heq_of_eq hD.symm).trans g11.symm
  refine ⟨GlobalTheory.Cp.SquareIntegrableColumnsCompatible.ofS C, HEq.trans (b := (colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr S.ker).face)
    ?_ ?_, ?_, ?_, ?_, ?_⟩
  · kexactB c5
  · kexactB d1
  · kexactB c3.trans (hSp.1.symm.trans g12.symm)
  · kexactB c4
  · kexactB c6
  · kexactB c1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem cols_of_witnesses : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K) (t : Formalism.L2.Ker.KerEntTied q.O.ex), KPin q t → Nonempty (RXs q.x.what₂) → ∃ Dc Sp₀ Zsc₀, ∃ C₀ : ReadC q.x.what₂.r.z.R (reFace q.x.what₂.r.z.F Dc Sp₀ Zsc₀) q.O.ex.p0 q.x.what₂.r.Y, ∀ (T : Formalism.L2.TiedDataSK q.O.ex), T.ker = t → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → a.Dc = Dc → HEq x.C.wU C₀.wU → HEq x.C.eNu C₀.eNu → ∃ C : GlobalTheory.Cp.SquareIntegrableColumnsCompatible T (divisionPairOfAdelicFormsFaceColumnsData x), HEq (fun Zs => C.c.face Zs) x.F.Dc ∧ HEq C.Sp x.F.Sp ∧ HEq C.c.W q.B.wts ∧ HEq C.c.Xg q.x.what₂.r.z.Xg ∧ Formalism.L2.DIV.ColPins C.toS := by
  intro 𝒮 K q t hk ⟨r⟩
  obtain ⟨C₀, hC⟩ := exists_readC (ex := q.O.ex) q.x.what₂ r q.x.pin t (fun _ => ⟨ℂ, inferInstance, inferInstance, fun _ => 0, ⊥⟩)
    q.x.what₂.r.z.F.Zsc
  refine ⟨_, _, _, C₀, fun S hS a x hx hD hw _ => ?_⟩
  subst hS
  cases hx
  exact exists_cols (ex := q.O.ex) q.x.what₂ q.x.pin S hk.std a hD (hw.trans (heq_of_eq hC))

end GlobalTheory.Mem.R3.SelC

end
end
