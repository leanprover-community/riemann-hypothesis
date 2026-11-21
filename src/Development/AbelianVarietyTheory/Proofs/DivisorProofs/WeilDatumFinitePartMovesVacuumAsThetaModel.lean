import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairMovesPhasedHeisenbergTranslate
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsPairMass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairUnitModulusFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockVacuumOfReadsGaussianEntire
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroStandardThetaLineReadAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateFixesThetaDeepLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeOIffScaleMulFinitePartMemIdealLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartRationalTensorZeroAtPrimeIffPlaceIdemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumConstantTrivialFinitePairs

section
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact

theorem closeTo_of_mul {D : D7} {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} {g : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)}
    {g' : GL (Fin N') (Formalism.MainNotions.StandardLatticesGL3.AE D)} {z z' : Matrix (Fin N') (Fin N) D.host.E} (m k : ℕ)
    (h : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc (m * k) g g' z z') : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc m g g' z z' := by
  intro i j
  obtain ⟨y, hy, e⟩ := h i j
  refine ⟨(k : Formalism.MainNotions.StandardLatticesGL3.AE D) * y, ?_, by rw [e]; push_cast; ring⟩
  rw [← nsmul_eq_mul]; exact nsmul_mem hy k

theorem exists_closeTo {D : D7} {cc : Ideal (𝓞 D.host.K)} (hc : cc ≠ ⊥) {N N' : ℕ} (g : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D))
    (g' : GL (Fin N') (Formalism.MainNotions.StandardLatticesGL3.AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) (n : ℕ) (hn : 0 < n) :
    ∃ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n g g' z z' := by
  obtain ⟨c, hc1, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  obtain ⟨a, ha0, ha⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (GlobalTheory.NormSum.MovedLattice.inverseHalfDifferent_ne_zero D)
  set b : D.host.E := ((c : D.host.K) : D.host.E) * algebraMap (𝓞 D.host.E) D.host.E a with hb
  have hb0 : b ≠ 0 := by
    refine mul_ne_zero ?_ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 ha0)
    intro h0
    apply hc0
    have : (c : D.host.K) = 0 := by exact_mod_cast h0
    exact_mod_cast this
  obtain ⟨v, hv⟩ : ∃ v, Formalism.MainNotions.StandardLatticesGL3.inc D b * v = 1 := by
    have hb1 : b * b⁻¹ = 1 := mul_inv_cancel₀ hb0
    exact ⟨Formalism.MainNotions.StandardLatticesGL3.inc D b⁻¹, by rw [← map_mul, hb1, map_one]⟩
  set t : Matrix (Fin N') (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D) := (g' : Matrix (Fin N') (Fin N') (Formalism.MainNotions.StandardLatticesGL3.AE D)) *
    z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) * ((g⁻¹ : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with ht
  choose e w hw he using fun i j => GlobalTheory.NormSum.Expand.approx (t i j * v) n hn
  refine ⟨Matrix.of fun i j => e i j * b, fun i j => ⟨Formalism.MainNotions.StandardLatticesGL3.inc D b * w i j,
    AddSubgroup.subset_closure ⟨c, hc1, _, ha, w i j, hw i j, rfl⟩, ?_⟩⟩
  have h1 : t i j * v * Formalism.MainNotions.StandardLatticesGL3.inc D b = t i j := by
    rw [mul_assoc, mul_comm v, hv, mul_one]
  rw [Matrix.sub_apply, ← ht, Matrix.map_apply, Matrix.of_apply, map_mul]
  linear_combination (Formalism.MainNotions.StandardLatticesGL3.inc D b) * he i j + h1

theorem reads_om_of_vacuum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d) →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ (c : ℂ) (f₀ : WO S T → ℂ), Reads ψ θ hS hT cc δ r e0 f₀ → Reads ψ θ hS hT cc δ r (c • W.Om x y e0) (om (g, h) f₀) →
  ∀ G ∈ TT D (tor0 D cc δ) a d, ∀ f, Reads ψ θ hS hT cc δ r G f → Reads ψ θ hS hT cc δ r (c • W.Om x y G) (om (g, h) f) := by
  intro D ψ θ S T a d hS hT cc δ r hSet e0 W χS χT om hW he0 x y g h hg hh c f₀ hf₀ hc G hG f hf
  have hC := hSet.crv
  have hSD0 : ∀ N : ℕ, Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D N) := by
    intro N
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    rw [← h2]; exact (h1 1).2
  obtain ⟨-, hWL, hint, -⟩ := GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC a d
    (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D cc δ) a d) (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)
  have hfix : ∀ v ∈ Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D cc δ) a d, Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) v e0 = e0 := by
    intro v hv
    rw [hWL v hv]; funext w; exact he0.2 v hv w
  have heT : e0 ∈ TT D (tor0 D cc δ) a d :=
    ⟨he0.1, 1, one_pos, fun v hv => by rw [one_nsmul]; exact hfix v hv⟩
  have hTT : ∀ z, Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0 ∈ TT D (tor0 D cc δ) a d := by
    intro z
    obtain ⟨Q, hQ, hz⟩ := GlobalTheory.NormSum.RatExtend.exists_nsmul_mem hC.1.1 δ z
    refine ⟨GlobalTheory.NormSum.RatExtend.Wd_diff _ he0.1, Q, hQ, fun v hv => ?_⟩
    obtain ⟨m, hm⟩ := hint v hv _ hz
    rw [GlobalTheory.NormSum.RatExtend.Hf_nsmul_right, ← GlobalTheory.NormSum.RatExtend.Hf_nsmul_left] at hm
    rw [GlobalTheory.NormSum.RatExtend.Wd_comm _ _ m hm, hfix _ (nsmul_mem hv _)]
  have hRt : ∀ (F : VC D a d → ℂ) (f' : WO S T → ℂ), Reads ψ θ hS hT cc δ r F f' → ∀ z,
      Reads ψ θ hS hT cc δ r (Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F)
        (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) • heisO ψ S T (finPt hS hT r z) f') := by
    intro F f' hF z
    exact (GlobalTheory.T.heisenbergFinitePoint_reads_classicalTranslation ψ θ S T hS hT cc δ r hSet F f' hF z).smul _
  have hR0 : Reads ψ θ hS hT cc δ r (0 : VC D a d → ℂ) (0 : WO S T → ℂ) :=
    ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  have hRsum : ∀ {k : ℕ} (rr : Fin k → ℂ) (F : Fin k → VC D a d → ℂ) (f' : Fin k → WO S T → ℂ),
      (∀ i, Reads ψ θ hS hT cc δ r (F i) (f' i)) →
        Reads ψ θ hS hT cc δ r (∑ i, rr i • F i) (∑ i, rr i • f' i) := by
    intro k rr F f' hF
    have : ∀ s : Finset (Fin k), Reads ψ θ hS hT cc δ r (∑ i ∈ s, rr i • F i) (∑ i ∈ s, rr i • f' i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hR0
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact ((hF i).smul (rr i)).add ih
    exact this Finset.univ
  have key : ∀ zz : Matrix (Fin d) (Fin a) D.host.E, ∃ z',
      W.Om x y (Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ zz) e0) =
        Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') (W.Om x y e0) ∧
      Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ zz) • om (g, h) (heisO ψ S T (finPt hS hT r zz) f₀) =
        Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') • heisO ψ S T (finPt hS hT r z') (om (g, h) f₀) := by
    intro zz
    obtain ⟨m, hm, hl⟩ := W.lift x y zz e0 heT
    obtain ⟨n, hn, hL⟩ := GlobalTheory.T.weilPair_moves_phasedHeisenbergTranslate ψ θ S T hS hT cc δ r hSet χS χT om hW x y g h hg hh f₀ hf₀.1 zz
    obtain ⟨z', hz'⟩ := exists_closeTo hC.1.1 (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D))
      zz (m * n) (Nat.mul_pos hm hn)
    refine ⟨z', hl z' (closeTo_of_mul m n hz'), hL z' (closeTo_of_mul n m ?_)⟩
    rwa [mul_comm] at hz'
  choose z' hz1 hz2 using key
  obtain ⟨k, rr, z, rfl⟩ := GlobalTheory.ThetaSpan.theta_span D cc δ hC a d e0 he0 W.nz G hG
  have hfG := Reads.unique hf (hRsum rr _ _ fun i => hRt e0 f₀ hf₀ (z i))
  subst hfG
  have e1 : c • W.Om x y (∑ i, rr i • Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0) =
      ∑ i, rr i • Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z' (z i))) (c • W.Om x y e0) := by
    rw [(GlobalTheory.NormSum.RatExtend.Om_sum W x y Finset.univ rr _ fun i => hTT (z i)).2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz1, GlobalTheory.NormSum.RatExtend.Wd_smul, smul_comm]
  have e2 : om (g, h) (∑ i, rr i • (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) •
        heisO ψ S T (finPt hS hT r (z i)) f₀)) =
      ∑ i, rr i • (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z' (z i))) •
        heisO ψ S T (finPt hS hT r (z' (z i))) (om (g, h) f₀)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, hz2]
  rw [e1, e2]
  exact hRsum rr _ _ fun i => hRt _ _ hc (z' (z i))

end GlobalTheory.NormExact
end
end

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedThetaFunctions_read_of_movedVacuum_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d) →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ (c : ℂ) (f₀ : WO S T → ℂ), Reads ψ θ hS hT cc δ r e0 f₀ → Reads ψ θ hS hT cc δ r (c • W.Om x y e0) (om (g, h) f₀) →
  ∀ G ∈ TT D (tor0 D cc δ) a d, ∀ f, Reads ψ θ hS hT cc δ r G f → Reads ψ θ hS hT cc δ r (c • W.Om x y G) (om (g, h) f) := by
  atlas_forward_decl GlobalTheory.NormExact.reads_om_of_vacuum
end

section
noncomputable section

section Entire
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.FockPos

namespace GlobalTheory.VacLine

theorem fock_real_entire : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 →
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) →
    ∃ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ ∧ ∀ w : WO S T, w.map (finPart D) = 0 →
      f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w) := by
  intro D ψ θ S T frS frT hS hT hψ hθ f hft hff
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨hF, hann⟩ := GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ hσ ψ hψ S T (fun _ => 1) (fun _ => 1) f
    hft hff
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hFdef
  set X := frLin frS frT with hX
  set r := Formalism.L2.Pj.xiR D with hr
  set E : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ := fun Z =>
    Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) with hE
  have hU : ∀ {k : ℕ} (fr : GL (Fin k) D.host.E) τ, IsUnit (frAt fr τ).det := fun fr τ =>
    isUnit_iff_ne_zero.2 (frAt_det_ne fr τ)
  have hG : Differentiable ℝ (fun Z => F (X Z)) := hF.comp (X.restrictScalars ℝ).differentiable
  have hdG : ∀ Z Y, fderiv ℝ (fun Z => F (X Z)) Z Y = fderiv ℝ F (X Z) (X Y) := fun Z Y => by
    have h : HasFDerivAt (fun Z => F (X Z)) ((fderiv ℝ F (X Z)).comp (X.restrictScalars ℝ)) Z :=
      (hF (X Z)).hasFDerivAt.comp Z (X.restrictScalars ℝ).hasFDerivAt
    rw [h.fderiv]
    rfl
  refine ⟨fun Z => F (X Z) * E Z,
    differentiable_mul_of_cr (fun Z => F (X Z)) E
      (fun Z Y => (2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ))
      hG (gauss_cr r).1 (fun Z Y => ?_) (gauss_cr r).2, fun w hw => ?_⟩
  · rw [hdG, hdG]
    have hj : jO S T (fun _ => 1) (fun _ => 1) (X Y) = X (Complex.I • Y) := by
      rw [X.map_smul]
      funext τ
      rw [jO_apply]
      change Complex.I • ((1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) * Matrix.of (X Y τ) *
        (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) = _
      rw [Matrix.one_mul, Matrix.mul_one]
      rfl
    have h := hann (X Z) (X Y)
    rw [hj] at h
    have hom : ∀ Y' : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank, omO S T (X Z) (X Y') =
        ∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y' τ a b)).re := by
      intro Y'
      rw [omO_apply]
      refine Finset.sum_congr rfl fun τ _ => ?_
      show 2 * (tauE D τ D.host.xi0 * hAt S T τ (X Z τ) (X Y' τ)).re = _
      unfold hAt
      rw [hX, frLin_apply, frLin_apply, trace_frames _ _ _ _ (frAt_on frS hS τ) (frAt_on frT hT τ), xi_zero_eq_host τ]
      rfl
    rw [hom, hom] at h
    have hs2 : ∀ τ, (∑ a, ∑ b, Z τ a b * starRingEnd ℂ ((Complex.I • Y) τ a b)) =
        -Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) := fun τ => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    simp only [hs2] at h
    have key : ((∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)).re : ℝ) : ℂ) +
        Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * (-Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b))).re : ℝ) : ℂ) =
        2 * Complex.I * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) := by
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      set s := ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)
      apply Complex.ext <;> simp <;> ring
    show _ = -((2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ) * F (X Z))
    have h' : fderiv ℝ F (X Z) (X Y) - Real.pi * Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)).re : ℝ) : ℂ) * F (X Z) +
      Complex.I * (fderiv ℝ F (X Z) (X (Complex.I • Y)) - Real.pi * Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * (-Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b))).re : ℝ) : ℂ) * F (X Z)) = 0 := h
    linear_combination h' + Real.pi * Complex.I * F (X Z) * key +
      2 * Real.pi * r * (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)) * F (X Z) * Complex.I_sq
  · have e1 : X (zCo θ frS frT w) = piW θ T S w := by
      funext τ
      rw [hX, frLin_apply]
      change frAt frT τ * ((frAt frT τ)⁻¹ * compAt θ τ w * frAt frS τ) * (frAt frS τ)⁻¹ = _
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.mul_one]
      rfl
    show f w = gaussO θ frS frT w * (f (iotaW σ T S (X (zCo θ frS frT w))) * E (zCo θ frS frT w))
    rw [e1, hσ.iota_pi hw, ← mul_assoc, mul_comm _ (f w), mul_assoc, hE, gaussO, ← Complex.exp_add]
    have e2 : -((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ) +
        ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ) = 0 := by
      rw [hr]; push_cast; ring
    rw [e2, Complex.exp_zero, mul_one]

end GlobalTheory.VacLine
end Entire

section Classical
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.VacMove
open scoped BigOperators Pointwise

namespace GlobalTheory.VacLine

theorem mem_thSp_of_lift {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ}
    {e0 : VC D N N' → ℂ} (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (hne : e0 ≠ 0)
    (g : GA D N) (g' : GA D N') {L₁ L₁'} (h : Moves D (g : GL (Fin N) (AE D)) L₁)
    (h' : Moves D (g' : GL (Fin N') (AE D)) L₁') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G)
    (hlift : ∀ z : Matrix (Fin N') (Fin N) D.host.E, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0 = e0 →
      ∃ m : ℕ, 0 < m ∧ ∀ z', CloseTo D cc m (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) z z' →
        G = Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') G) :
    G ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') := by
  have hcc : cc ≠ ⊥ := hc.1.1
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := klat _ (moves_one D N) (moves_one D N')
  have k1 := klat (tor0 D cc δ) h h'
  obtain ⟨-, hF, -, hinv⟩ := GlobalTheory.T.intertwinerUnitary_all D cc δ hc N N' _ _ k0 k1 e0 he
  have hF0 : Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 ≠ 0 := by
    intro h0
    rw [h0, iop_zero] at hinv
    exact hne hinv.symm
  obtain ⟨-, hW, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hc N N' _ k1
  refine ⟨hG, fun x hx => ?_⟩
  suffices hs : Wd D (tor0 D cc δ) x G = G by
    rw [hW x hx] at hs; exact congrFun hs
  have hmul : ∀ a ∈ La D (tor0 D cc δ) L₁ L₁', ∀ b ∈ La D (tor0 D cc δ) L₁ L₁', ∀ F,
      Wd D (tor0 D cc δ) a (Wd D (tor0 D cc δ) b F) = Wd D (tor0 D cc δ) (a + b) F := by
    intro a ha b hb F
    obtain ⟨φ, hφ⟩ := wd_wd D (tor0 D cc δ) a b
    have h2 := hφ (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0)
    rw [wd_fix (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc k1 hF hb, wd_fix (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc k1 hF ha, wd_fix (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc k1 hF (add_mem ha hb)] at h2
    have h3 : φ = 1 := by
      by_contra hne
      apply hF0
      have : (φ - 1) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 = 0 := by
        rw [sub_smul, one_smul, ← h2, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    rw [hφ, h3, one_smul]
  obtain ⟨z', rfl, hz'⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hcc N N' g g' L₁ L₁' h h' x hx
  have hlatb := GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hcc N N' g g' L₁ L₁' h h'
  have hlat0 := GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hcc N N' 1 1 _ _ (moves_one D N) (moves_one D N')
  simp only [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at hlat0
  simp only [← MI_one] at hz' hlatb hlat0
  obtain ⟨m0, hm0, hl0⟩ := hlift 0 (by rw [VacMove.pt_zero, VacMove.wd_zero])
  set P : Matrix (Fin N') (Fin N') (AE D) := ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) with hP
  set P' : Matrix (Fin N') (Fin N') (AE D) :=
    (((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) with hP'
  set Q : Matrix (Fin N) (Fin N) (AE D) := ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) with hQ
  set Q' : Matrix (Fin N) (Fin N) (AE D) :=
    (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) with hQ'
  have ePP : P * P' = 1 := Units.mul_inv _
  have eP'P : P' * P = 1 := Units.inv_mul _
  have eQQ : Q * Q' = 1 := Units.mul_inv _
  have eQ'Q : Q' * Q = 1 := Units.inv_mul _
  have e1 : ∀ M : Matrix (Fin N') (Fin N) (AE D), P * (P' * M * Q) * Q' = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ePP, Matrix.one_mul, Matrix.mul_assoc, eQQ, Matrix.mul_one]
  have e2 : ∀ M : Matrix (Fin N') (Fin N) (AE D), P' * (P * M * Q') * Q = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, eP'P, Matrix.one_mul, Matrix.mul_assoc, eQ'Q, Matrix.mul_one]
  obtain ⟨n, hn, hb⟩ := MI_bound hcc P Q'
  obtain ⟨n', hn', hb'⟩ := MI_bound hcc P' Q
  obtain ⟨z, hz⟩ := MI_approx hcc (P' * z'.map (inc D) * Q) (n * m0) (Nat.mul_pos hn hm0)
  have hz0 : MI D cc 1 (z.map (inc D)) := by
    simpa using (hz.of_dvd (one_dvd _)).add hz'
  obtain ⟨m, hm, hl⟩ := hlift z (wd_fix (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc k0 he (hlat0 z hz0))
  obtain ⟨w, hw⟩ := MI_approx hcc (P * z.map (inc D) * Q') (n' * (m * m0)) (by positivity)
  have hw1 : MI D cc 1 (P' * w.map (inc D) * Q) := by
    have := ((hb' _ _ hw).of_dvd (one_dvd _)).add hz0
    rwa [Matrix.mul_sub, Matrix.sub_mul, e2, sub_add_cancel] at this
  have hd : (w - z').map (inc D) = w.map (inc D) - z'.map (inc D) := by
    ext i j; simp
  have hd' : (z' - w).map (inc D) = z'.map (inc D) - w.map (inc D) := by
    ext i j; simp
  have hdiff : MI D cc m0 ((z' - w).map (inc D)) := by
    have h1 := hb _ _ hz
    rw [Matrix.mul_sub, Matrix.sub_mul, e1] at h1
    have h2 : MI D cc m0 (0 : Matrix (Fin N') (Fin N) (AE D)) := fun i j => ⟨0, zero_mem _, by simp⟩
    have := (h2.sub h1).sub (hw.of_dvd (m := m0) ⟨n' * m, by ring⟩)
    rw [hd']
    convert this using 1
    abel
  have f1 := hl w (hw.of_dvd (m := m) ⟨n' * m0, by ring⟩)
  have f2 := hl0 (z' - w) (by
    intro i j
    have h0 : (0 : Matrix (Fin N') (Fin N) D.host.E).map (inc D) = 0 := by ext; simp
    rw [h0, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    exact hdiff i j)
  have hdl : MI D cc 1 (P' * (z' - w).map (inc D) * Q) := by
    rw [hd', Matrix.mul_sub, Matrix.sub_mul]
    exact hz'.sub hw1
  have := hmul _ (hlatb w hw1) _ (hlatb _ hdl) G
  rw [← f2, ← f1, ← pt_add, add_sub_cancel] at this
  exact this.symm

theorem eq_smul_of_lift {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ}
    {e0 : VC D N N' → ℂ} (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0)
    (g : GA D N) (g' : GA D N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G)
    (hlift : ∀ z : Matrix (Fin N') (Fin N) D.host.E, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0 = e0 →
      ∃ m : ℕ, 0 < m ∧ ∀ z', CloseTo D cc m (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) z z' →
        G = Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') G) :
    ∃ c : ℂ, G = c • W.Om g g' e0 := by
  obtain ⟨Lt, h1, -⟩ := exists_lattice_of_adelic_point D N
  obtain ⟨Lt', h1', -⟩ := exists_lattice_of_adelic_point D N'
  have h := (h1 g).1
  have h' := (h1' g').1
  have hT := vac_TT (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc he
  have hO := mem_thSp_of_lift hc he W.nz g g' h h' (W.maps g g' e0 hT).1 (fun z hz => by
    obtain ⟨m, hm, hl⟩ := W.lift g g' z e0 hT
    rw [hz] at hl
    exact ⟨m, hm, hl⟩)
  have hO0 : W.Om g g' e0 ≠ 0 := by
    intro h0
    have h2 := W.mul g⁻¹ g g'⁻¹ g' e0 hT
    have h3 := W.smul g⁻¹ g'⁻¹ 0 e0 hT
    rw [zero_smul, zero_smul] at h3
    rw [inv_mul_cancel, inv_mul_cancel, W.one e0 hT, h0, h3] at h2
    exact W.nz h2
  exact (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hc N N' _ (klat (tor0 D cc δ) h h')).1 _
    (mem_thSp_of_lift hc he W.nz g g' h h' hG hlift) _ hO hO0

end GlobalTheory.VacLine
end Classical

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacLine

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem factor_ne (hset : Setup ψ θ S T cc δ r) (τ : D.what₂.Tau) : δ * embT D τ r ≠ 0 :=
  mul_ne_zero (delta_ne_zero hset.crv) ((map_ne_zero _).2 (hset.scale.ne_zero hset.crv.1.1))

theorem reads_inj {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} (hset : Setup ψ θ S T cc δ r) {G G' : VC D a d → ℂ}
    {f : WO S T → ℂ} (h : Reads ψ θ hS hT cc δ r G f) (h' : Reads ψ θ hS hT cc δ r G' f) : G = G' := by
  subst hS hT
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hset.inf
  funext Y
  set Z : GlobalTheory.FockCompare.RW T S := fun τ i j => (δ * embT D τ r)⁻¹ * Y τ i j with hZ
  have hw : (GlobalTheory.FockCompare.iotaW σ T S Z).map (finPart D) = 0 := by funext i j; exact hσ.fin _
  have hY : coordY θ rfl rfl δ r (GlobalTheory.FockCompare.iotaW σ T S Z) = Y := by
    funext τ i j
    show δ * embT D τ r * θ τ (infPart D (σ fun τ' => Z τ' i j)) = _
    rw [hσ.comp, hZ]
    exact mul_inv_cancel_left₀ (factor_ne hset τ) _
  have h1 := (h.2 _ hw).symm.trans (h'.2 _ hw)
  rw [hY] at h1
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) h1

theorem exists_reads {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (hset : Setup ψ θ S T cc δ r) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) :
    ∃ G : VC D a d → ℂ, Differentiable ℂ G ∧ Reads ψ θ hS hT cc δ r G f := by
  subst hS hT
  have hon : ∀ V : HSp D, V.gram = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)
      (1 : GL (Fin V.rank) D.host.E).1 * V.gram * (1 : GL (Fin V.rank) D.host.E).1 = 1 := by
    intro V hV
    rw [hV, Units.val_one, Matrix.mul_one, Matrix.mul_one]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, hij, Ne.symm hij, Matrix.one_apply]
  obtain ⟨Φ, hΦ, hw⟩ := fock_real_entire ψ θ S T 1 1 (hon S hset.gS) (hon T hset.gT) hset.std hset.inf f hf hv
  refine ⟨fun Y => Φ fun τ i j => (δ * embT D τ r)⁻¹ * Y τ i j, hΦ.comp (by fun_prop), ?_⟩
  rw [reads_iff hset.crv hset.scale]
  refine ⟨hf, fun w hw0 => ?_⟩
  rw [hw w hw0]
  congr 2
  funext τ i j
  exact (inv_mul_cancel_left₀ (factor_ne hset τ) _).symm

theorem moved_vacuum_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∃ c : ℂ, Reads ψ θ hS hT cc δ r (c • W.Om x y e0) (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hset e0 W χS χT om hom _ t0 _ _ he _ _ f₀ hf₀ x y g h hg hh
  have hθ := hset.inf
  have hv0 := GlobalTheory.T.isFockVacuum_of_readsGaussianEntire ψ θ S T hS hT cc δ r hset e0 f₀ he.1.1 hf₀
  have e : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (om (g, h) f₀) =
      om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀) := by
    intro τ z
    rw [GlobalTheory.OrientedHeis.om_dRho hom hθ g h τ z hf₀.1, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hh.1,
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S (inv_mem hg.1), Matrix.one_mul, Matrix.mul_one]
  have hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) (om (g, h) f₀) := by
    intro τ z
    have h0 := hv0 τ z
    unfold annih at h0 ⊢
    rw [e, e, ← map_smul, ← map_add, h0, map_zero]
  obtain ⟨G, hG, hR⟩ := exists_reads hS hT hset (hom.om_pres (g, h) f₀ hf₀.1) hv
  have hRt : ∀ (F : VC D a d → ℂ) (f' : WO S T → ℂ), Reads ψ θ hS hT cc δ r F f' → ∀ z,
      Reads ψ θ hS hT cc δ r (Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F)
        (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) • heisO ψ S T (finPt hS hT r z) f') := by
    intro F f' hF z
    exact (GlobalTheory.NormExact.heisO_finPt_reads ψ θ S T hS hT cc δ r hset F f' hF z).smul _
  obtain ⟨c, hc⟩ := eq_smul_of_lift hset.crv he.1 W x y hG (fun z hz => by
    obtain ⟨n, hn, hL⟩ := GlobalTheory.T.weilPair_moves_phasedHeisenbergTranslate ψ θ S T hS hT cc δ r hset χS χT om hom x y g h hg hh f₀ hf₀.1 z
    refine ⟨n, hn, fun z' hz' => ?_⟩
    have h1 := hRt e0 f₀ hf₀ z
    rw [hz] at h1
    have h2 := hL z' hz'
    rw [← map_smul, ← hf₀.unique h1] at h2
    have h3 := hRt G _ hR z'
    rw [← h2] at h3
    exact reads_inj hset hR h3)
  exact ⟨c, hc ▸ hR⟩

end GlobalTheory.VacLine

end
end

section
section
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacInertMove

open GlobalTheory.WeilParts GlobalTheory.IdemSupport GlobalTheory.LocalGlobalChar Filter Topology
open GlobalTheory.BotClassDict (finQ)
open GlobalTheory.VacRead (lsB)

variable {D : D7}

def congrGroup (V : HSp D) (I : NonUnitalSubring (AE D)) : Subgroup (GA D V) where
  carrier := {g | ∀ i j, (mt V g - 1) i j ∈ I ∧ (mt V g⁻¹ - 1) i j ∈ I}
  one_mem' := fun i j => by
    rw [inv_one, mt_one, sub_self, Matrix.zero_apply]
    exact ⟨zero_mem _, zero_mem _⟩
  mul_mem' := by
    have key : ∀ M N : Matrix (Fin V.rank) (Fin V.rank) (AE D), (∀ i j, (M - 1) i j ∈ I) → (∀ i j, (N - 1) i j ∈ I) →
        ∀ i j, (M * N - 1) i j ∈ I := fun M N hM hN i j => by
      have e : M * N - 1 = (M - 1) * (N - 1) + (M - 1) + (N - 1) := by noncomm_ring
      rw [e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply]
      exact add_mem (add_mem (sum_mem fun k _ => mul_mem (hM i k) (hN k j)) (hM i j)) (hN i j)
    intro a b ha hb i j
    rw [_root_.mul_inv_rev, mt_mul, mt_mul]
    exact ⟨key _ _ (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j,
      key _ _ (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j⟩
  inv_mem' := fun {a} ha i j => by
    rw [inv_inv]
    exact ⟨(ha i j).2, (ha i j).1⟩

theorem piece_mem_congrGroup (V : HSp D) (I : NonUnitalSubring (AE D)) {f : AE D} (hf : f * f = f) (hc : cA D f = f)
    (hI : ∀ z ∈ I, f * z ∈ I) {g g₁ : GA D V} (hg : g ∈ congrGroup V I)
    (e : mt V g₁ = f • mt V g + (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) : g₁ ∈ congrGroup V I := by
  obtain ⟨q, hq⟩ := exists_piece V hf hc g⁻¹
  have hpq : g₁⁻¹ = q := by
    refine inv_eq_of_mul_eq_one_right (mt_inj V ?_)
    rw [mt_mul, e, hq, mix_mul hf, ← mt_mul, mul_inv_cancel, mt_one, one_mul, mix_self]
  have key : ∀ (M : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j,
      (f • M + (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) - 1) i j = f * (M - 1) i j := fun M i j => by
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  intro i j
  rw [hpq, e, hq, key, key]
  exact ⟨hI _ (hg i j).1, hI _ (hg i j).2⟩

theorem ind_mem_intAf (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (b : Ainf D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F b (ind S))) ∈ intAE D := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  rw [hΦ.int]
  intro Q
  rw [hΦ.base]
  change GlobalTheory.AdeleBaseChange.locMap D.host.F Q (evalV D.host.F _ (ind S)) ∈ _
  rw [ev_ind]
  split_ifs
  · rw [map_one]; exact one_mem _
  · rw [map_zero]; exact zero_mem _

def inertInt (D : D7) : NonUnitalSubring (AE D) where
  carrier := {z | infPart D z = 0 ∧ finPart D z ∈ intAE D ∧
    ∀ v ε, IsPlaceIdem D v ε → ¬ NonSplitAt D v ε → algebraMap (AF D.host.F) (AE D) ε * z = 0}
  zero_mem' := ⟨RingHom.map_zero _, by rw [RingHom.map_zero]; exact zero_mem _, fun _ _ _ _ => mul_zero _⟩
  add_mem' := fun {a b} ha hb => ⟨by rw [RingHom.map_add, ha.1, hb.1, add_zero], by rw [RingHom.map_add]; exact add_mem ha.2.1 hb.2.1,
    fun v ε h h' => by rw [mul_add, ha.2.2 v ε h h', hb.2.2 v ε h h', add_zero]⟩
  neg_mem' := fun {a} ha => ⟨by rw [RingHom.map_neg, ha.1, neg_zero], by rw [RingHom.map_neg]; exact neg_mem ha.2.1,
    fun v ε h h' => by rw [mul_neg, ha.2.2 v ε h h', neg_zero]⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [RingHom.map_mul, ha.1, zero_mul],
    by rw [RingHom.map_mul]; exact GlobalTheory.HostAdeleIso.intAE_mul_mem D ha.2.1 hb.2.1,
    fun v ε h h' => by rw [← mul_assoc, ha.2.2 v ε h h', zero_mul]⟩

theorem mul_mem_inertInt {f : AE D} (hf : finPart D f ∈ intAE D) : ∀ z ∈ inertInt D, f * z ∈ inertInt D :=
  fun z hz => ⟨by rw [RingHom.map_mul, hz.1, mul_zero], by rw [RingHom.map_mul]; exact GlobalTheory.HostAdeleIso.intAE_mul_mem D hf hz.2.1,
    fun v ε h h' => by rw [mul_left_comm, hz.2.2 v ε h h', mul_zero]⟩

set_option maxHeartbeats 800000 in

theorem congrGroup_le (V : HSp D) (H : Subgroup (GA D V)) (hH : IsClosed (H : Set (GA D V)))
    (hpl : ∀ v ε, NonSplitAt D v ε → ∀ g ∈ congrGroup V (inertInt D), SuppPl ε V g → g ∈ H) :
    congrGroup V (inertInt D) ≤ H := by
  have h1 : ∀ g : GA D V, (∀ i j, (mt V g - 1) i j = 0) → g ∈ H := fun g hg => by
    have : g = 1 := mt_inj V (by rw [mt_one, ← sub_eq_zero]; exact Matrix.ext hg)
    rw [this]; exact one_mem _
  have hS : ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ g ∈ congrGroup V (inertInt D), SuppPl (eps S) V g → g ∈ H := by
    intro S
    induction S using Finset.cons_induction with
    | empty =>
      intro g hg hs
      refine h1 g fun i j => GlobalTheory.PlaceIdem.parts_inj D _ _ (by rw [(hg i j).1.1, RingHom.map_zero]) ?_
      have h1 : (finPart D).mapMatrix (mt V g) = 1 := congrArg Units.val (mem_GinfC V hs)
      have h2 : (finPart D).mapMatrix (mt V g - 1) = 0 := by
        rw [RingHom.map_sub, h1, RingHom.map_one, sub_self]
      rw [RingHom.map_zero]
      exact congrFun (congrFun h2 i) j
    | cons v S hv ih =>
      intro g hK hg
      obtain ⟨h1', h2'⟩ := eps_cons S v hv
      have h1' := congrArg (algebraMap (AF D.host.F) (AE D)) h1'
      have h2' := congrArg (algebraMap (AF D.host.F) (AE D)) h2'
      rw [RingHom.map_mul] at h1' h2'
      rw [RingHom.map_sub, RingHom.map_one] at h2'
      have hi := alg_idem (D := D) (pl_mul_self v)
      obtain ⟨g₁, e₁⟩ := exists_piece V hi (cA_algebraMap _) g
      have s₁ := (suppF_iff V _ g₁).2 (smul_mix hi e₁)
      have k₁ := piece_mem_congrGroup V _ hi (cA_algebraMap _) (mul_mem_inertInt (ind_mem_intAf _ _)) hK e₁
      have h3 : (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (ind {v}))) *
        (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (ind {v}))) =
        1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (ind {v})) := by linear_combination hi
      obtain ⟨g₂, e₂⟩ := exists_piece V h3 (by rw [RingHom.map_sub, RingHom.map_one, cA_algebraMap]) g
      have s₂ := (suppF_iff V _ g₂).2 (smul_mix h3 e₂)
      rw [sub_sub_cancel] at e₂
      have e : g = g₁ * g₂ := mt_inj V ((mt_mul V g₁ g₂).trans (mix_split hi e₁ e₂)).symm
      have k₂ : g₂ ∈ congrGroup V (inertInt D) := by
        have := mul_mem (inv_mem k₁) hK
        rwa [e, inv_mul_cancel_left] at this
      have t₁ : g₁ ∈ suppGroup V (algebraMap (AF D.host.F) (AE D) (eps (S.cons v hv))) := fun i j => by
        rw [← s₁ i j, ← mul_assoc, h1']
      have t : g ∈ suppGroup V (algebraMap (AF D.host.F) (AE D) (eps (S.cons v hv))) := hg
      have t₂ : g₂ ∈ suppGroup V (algebraMap (AF D.host.F) (AE D) (eps (S.cons v hv))) := by
        have := mul_mem (inv_mem t₁) t
        rwa [e, inv_mul_cancel_left] at this
      have u₂ : SuppPl (eps S) V g₂ := fun i j => by
        rw [← h2', mul_assoc, s₂ i j, t₂ i j]
      have m₁ : g₁ ∈ H := by
        by_cases hn : NonSplitAt D v (pairA D.host.F 0 (ind {v}))
        · exact hpl v _ hn g₁ k₁ s₁
        · exact h1 g₁ fun i j => (s₁ i j).symm.trans ((k₁ i j).1.2.2 v _ (isPlaceIdem v) hn)
      rw [e]
      exact mul_mem m₁ (ih g₂ k₂ u₂)
  intro g hg
  choose p hp using fun S : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    exists_piece V (alg_idem (eps_mul_self S)) (cA_algebraMap _) g
  choose q hq using fun S : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    exists_piece V (alg_idem (eps_mul_self S)) (cA_algebraMap _) g⁻¹
  have hpq : ∀ S, (p S)⁻¹ = q S := fun S => by
    refine inv_eq_of_mul_eq_one_right (mt_inj V ?_)
    rw [mt_mul, hp, hq, mix_mul (alg_idem (eps_mul_self S)), ← mt_mul, mul_inv_cancel, mt_one, one_mul, mix_self]
  have a1 : Tendsto (fun S => mt V (p S)) atTop (𝓝 (mt V g)) := (tendsto_mix _).congr fun S => (hp S).symm
  have a2 : Tendsto (fun S => mt V (p S)⁻¹) atTop (𝓝 (mt V g⁻¹)) := (tendsto_mix _).congr fun S => by rw [hpq, hq]
  have hlim : Tendsto p atTop (𝓝 g) := tendsto_HA _ _ _ a1 a2
  refine hH.mem_of_tendsto hlim (Eventually.of_forall fun S => hS S _ ?_ ?_)
  · exact piece_mem_congrGroup V _ (alg_idem (eps_mul_self S)) (cA_algebraMap _) (mul_mem_inertInt (ind_mem_intAf _ _)) hg (hp S)
  · exact (suppF_iff V _ (p S)).2 (smul_mix (alg_idem (eps_mul_self S)) (hp S))

theorem finQ_mem_iff (z : AE D) : finQ D z ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D ↔ finPart D z ∈ intAE D := by
  rw [mem_intAE_iff, ← GlobalTheory.BotClassDict.toAfE_int_iff, GlobalTheory.BotClassDict.toAfE_finQ]
  exact Iff.rfl

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 D.host.F)) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 D.host.F) ∈ v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := Ideal.absNorm_mem _
  generalize Ideal.absNorm v.asIdeal = n at h0 h1
  induction n using induction_on_primes with
  | zero => exact absurd rfl h0
  | one => exact absurd (Ideal.eq_top_of_isUnit_mem _ h1 (by simp)) v.isPrime.ne_top
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h1
    exact (v.isPrime.mem_or_mem h1).elim (fun h => ⟨p, hp, h⟩) (ih (right_ne_zero_of_mul h0))

theorem unramAt_of_hasFinPart {χ : (AE D)ˣ →* Circle} {N : ℕ} {c : HeckeU D N} {e : ℤ} (h : HasFinPart χ c e)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hv : NonSplitAt D v ε) : UnramAt ε χ := by
  intro x hx h1 h2
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hi : infPart D (x : AE D) = 1 := by
    have := congrArg (infPart D) hx
    rwa [RingHom.map_mul, (place_comp hΦ hv.1).1, zero_mul, RingHom.map_sub, RingHom.map_one, eq_comm, sub_eq_zero] at this
  have hy : c.f (Units.map (finQ D).toMonoidHom x) = 1 := by
    refine c.unr _ ⟨(finQ_mem_iff _).2 h1, (finQ_mem_iff _).2 h2⟩ fun q hq hn => ?_
    have e1 : ((Units.map (finQ D).toMonoidHom x : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 = finQ D ((x : AE D) - 1) := by
      rw [RingHom.map_sub, RingHom.map_one]; rfl
    rw [e1, GlobalTheory.T.finitePartRationalTensor_zeroAtPrime_iff_placeIdem D q hq]
    intro w η hη hw
    have hne : w ≠ v := by
      rintro rfl
      exact hn ((GlobalTheory.T.inertPrime_iff_nonSplitPlaceIdempotent D q hq w ε hv.1 hw).2 hv)
    rw [← hx, ← mul_assoc, place_orth hΦ hη hv.1 hne, zero_mul]
  have := h x (Units.map (finQ D).toMonoidHom x) ⟨hi, by
    rw [← GlobalTheory.BotClassDict.finAdEquiv_toAfE]
    exact congrArg _ (GlobalTheory.BotClassDict.toAfE_finQ _).symm⟩
  rw [hy, one_zpow] at this
  exact Circle.ext this

theorem finQ_mt_mem {V : HSp D} {g : GA D V} (hg : g ∈ congrGroup V (inertInt D)) (i j : Fin V.rank) :
    finQ D (mt V g i j) ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  have e : mt V g i j = (mt V g - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := by
    rw [Matrix.sub_apply, sub_add_cancel]
  rw [e, RingHom.map_add]
  refine add_mem ((finQ_mem_iff _).2 (hg i j).1.2.1) ?_
  rw [Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]; exact one_mem _
  · rw [RingHom.map_zero]; exact zero_mem _

theorem actO_mem_iff {S T : HSp D} (hS : S.gram = 1) {cc : Ideal (𝓞 D.host.K)} {r : D.host.E} (hc : cc ≠ ⊥)
    (hr : IsScale D cc r) {g : GA D S} {h : GA D T} (hg : g ∈ congrGroup S (inertInt D)) (hh : h ∈ congrGroup T (inertInt D))
    (u : WO S T) :
    u ∈ latO S T (lsB D cc r S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
    actO S T g h u ∈
      latO S T (lsB D cc r S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  have key : ∀ g ∈ congrGroup S (inertInt D), ∀ h ∈ congrGroup T (inertInt D), ∀ u ∈
      latO S T (lsB D cc r S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True),
      actO S T g h u ∈
      latO S T (lsB D cc r S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro g hg h hh u hu
    have h0 := GlobalTheory.VacUnique.latO_inf S T _ _ _ hu
    have h1 := (GlobalTheory.T.mem_latticeO_iff_scale_mul_finitePart_mem_idealLattice D S T hS cc r hc hr u h0).1 hu
    refine (GlobalTheory.T.mem_latticeO_iff_scale_mul_finitePart_mem_idealLattice D S T hS cc r hc hr _ ?_).2 fun i j => ?_
    · rw [actO, Matrix.map_mul, Matrix.map_mul, h0, Matrix.mul_zero, Matrix.zero_mul]
    · have e : finQ D (actO S T g h u i j) = ∑ l, (∑ k, finQ D (mt T h i k) * finQ D (u k l)) * finQ D (mt S g⁻¹ l j) := by
        have e1 : (actO S T g h u).map (finQ D) = (mt T h).map (finQ D) * u.map (finQ D) * (mt S g⁻¹).map (finQ D) := by
          rw [actO, Matrix.map_mul, Matrix.map_mul]
        exact congrFun (congrFun e1 i) j
      rw [e, Finset.mul_sum]
      refine sum_mem fun l _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine sum_mem fun k _ => ?_
      have := GlobalTheory.FinWeil.ihE_mul D cc (mul_mem (finQ_mt_mem hh i k) (finQ_mt_mem (inv_mem hg) l j)) (h1 k l)
      convert this using 1
      ring
  refine ⟨key g hg h hh u, fun hu => ?_⟩
  have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ u
  rw [inv_inv, inv_inv] at e
  rw [← e]
  exact key _ (inv_mem hg) _ (inv_mem hh) _ hu

theorem mem_congrGroup {V : HSp D} (hV : V.gram = 1) {g : GA D V} {x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank} (hg : IsFinPt V g x)
    (hs : Formalism.MainNotions.StandardLatticesGL3.SuppInert D (x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)))
    (hi : Formalism.MainNotions.StandardLatticesGL3.IntG D (x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : g ∈ congrGroup V (inertInt D) := by
  have e1 := GlobalTheory.LevelTr.finQ_mt_of_isFinPt V hV hg
  have e2 := GlobalTheory.LevelTr.finQ_mt_inv_of_isFinPt V hV hg
  have one : ∀ i j, finQ D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j := fun i j => by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact RingHom.map_one _
    · exact RingHom.map_zero _
  have oneI : ∀ i j, (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := fun i j => by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have inf : ∀ k ∈ GfC V, ∀ i j, infPart D ((mt V k - 1) i j) = 0 := fun k hk i j => by
    have h1 : (infPart D).mapMatrix (mt V k) = 1 := GlobalTheory.LevelTr.infPart_mt_of_mem_GfC V hk
    have h2 : (infPart D).mapMatrix (mt V k - 1) = 0 := by
      rw [RingHom.map_sub, h1, RingHom.map_one, sub_self]
    exact congrFun (congrFun h2 i) j
  have sp : ∀ v ε, IsPlaceIdem D v ε → ¬ NonSplitAt D v ε →
      g ∈ suppGroup V (1 - algebraMap (AF D.host.F) (AE D) ε) := fun v ε hε hn i j => by
    obtain ⟨q, hq, hqv⟩ := exists_prime_mem v
    have h1 := hs q hq (fun h => hn ((GlobalTheory.T.inertPrime_iff_nonSplitPlaceIdempotent D q hq v ε hε hqv).1 h)) i j
    rw [← e1, Matrix.map_apply, ← one, ← RingHom.map_sub, GlobalTheory.T.finitePartRationalTensor_zeroAtPrime_iff_placeIdem D q hq] at h1
    rw [sub_mul, one_mul, Matrix.sub_apply, h1 v ε hε hqv, sub_zero]
  have sp' : ∀ (k : GA D V) (a : AE D), k ∈ suppGroup V (1 - a) → ∀ i j, a * (mt V k - 1) i j = 0 := fun k a hk i j => by
    have := hk i j
    linear_combination -this
  intro i j
  refine ⟨⟨inf g hg.1 i j, ?_, fun v ε hε hn => sp' _ _ (sp v ε hε hn) i j⟩,
    ⟨inf _ (inv_mem hg.1) i j, ?_, fun v ε hε hn => sp' _ _ (inv_mem (sp v ε hε hn)) i j⟩⟩
  · rw [← finQ_mem_iff, Matrix.sub_apply, RingHom.map_sub, one]
    exact sub_mem (by have := (hi i j).1; rwa [← e1] at this) (oneI i j)
  · rw [← finQ_mem_iff, Matrix.sub_apply, RingHom.map_sub, one]
    exact sub_mem (by have := (hi i j).2; rwa [← e2] at this) (oneI i j)

theorem latVac_of_reads {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}
    {r : D.host.E} (hset : Setup ψ θ S T cc δ r) {e0 : VC D S.rank T.rank → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D S.rank) (stdL D T.rank)) {f₀ : WO S T → ℂ}
    (hf₀ : Reads ψ θ rfl rfl cc δ r e0 f₀) :
    IsSelfDualC S (lsB D cc r S.rank) ∧ IsSelfDualC T (stdL D T.rank) ∧ IsLatVac (heisO ψ S T)
      (latO S T (lsB D cc r S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True)
      f₀ := by
  obtain ⟨hψ, hθ, gS, gT, crv, sc⟩ := hset
  have hc : cc ≠ ⊥ := crv.1.1
  have hr : r ≠ 0 := IsScale.ne_zero hc sc
  have hδ : δ ≠ 0 := delta_ne_zero crv
  have hS1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin S.rank) D.host.E).1 * S.gram *
      (1 : GL (Fin S.rank) D.host.E).1 = 1 := by
    rw [gS]; simp [Formalism.UG.cT]
  have hT1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin T.rank) D.host.E).1 * T.gram *
      (1 : GL (Fin T.rank) D.host.E).1 = 1 := by
    rw [gT]; simp [Formalism.UG.cT]
  have hLs : Formalism.MainNotions.StandardLatticesGL3.SD D (lsB D cc r S.rank) := GlobalTheory.T.invDifferentLatticeProductHermitian_isSelfDual D cc r S.rank hc sc
  have hLt : Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D T.rank) := GlobalTheory.MovedVacuum.sd_stdL D T.rank
  obtain ⟨ΛS, hΛS, hSd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV S 1 hS1 _ hLs
  obtain ⟨ΛT, hΛT, hTd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV T 1 hT1 _ hLt
  have hone : ∀ {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), GlobalTheory.MovedDict.inV 1 L = (L : Set _) := fun L => by
    ext x
    simp [GlobalTheory.MovedDict.inV]
  obtain rfl : ΛS = lsB D cc r S.rank := SetLike.coe_injective (hΛS.trans (hone _))
  obtain rfl : ΛT = stdL D T.rank := SetLike.coe_injective (hΛT.trans (hone _))
  refine ⟨hSd, hTd, ?_⟩
  obtain ⟨f, hf0⟩ := GlobalTheory.VacRead.vac_exists_gram_one ψ θ hψ hθ S T gS gT _ _ hSd hTd
  have hf := hf0
  rw [hΛS, hΛT] at hf
  obtain ⟨Φ, hΦd, hΦ⟩ := GlobalTheory.FockPos.vacuum_real_entire ψ θ S T 1 1 _ _ hS1 hT1 f hf
  have hth := GlobalTheory.VacRead.theta_of_unit_vacuum ψ θ S T 1 1 hS1 hT1 δ hδ _ _ hLs hLt f hf Φ hΦd hΦ
  have hLa : ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) (stdL D S.rank) (stdL D T.rank),
      (fun τ i j => x τ i j / embT D τ r) ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) (lsB D cc r S.rank) (stdL D T.rank) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := GlobalTheory.ThetaLatImage.La_sub hx
    have h2 := GlobalTheory.ThetaLatImage.pt_mem_La (δ := δ) (GlobalTheory.T.inv_smul_mem_rationalHomLatticeScaled_of_normScale D cc r S.rank T.rank hc sc z hz) 1
    convert h2 using 1
    funext τ i j
    rw [one_smul, GlobalTheory.ThetaLatImage.pt_apply, GlobalTheory.ThetaLatImage.pt_apply]
    have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    field_simp
  have hG := GlobalTheory.VacRead.th_div_scale crv sc hLa hth
  have hback : ∀ Z : VC D S.rank T.rank,
      (δ⁻¹ • fun τ i j => (δ * embT D τ r * Z τ i j) / embT D τ r : VC D S.rank T.rank) = Z := by
    intro Z
    funext τ i j
    have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  obtain ⟨c, hc'⟩ := (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ crv _ _ _ (GlobalTheory.NormSum.VacMove.klat (tor0 D cc δ)
    (GlobalTheory.NormSum.VacMove.moves_one D S.rank) (GlobalTheory.NormSum.VacMove.moves_one D T.rank))).1 _ he _ hG (by
      intro h0
      apply GlobalTheory.StepMove.vacO_ne_zero hf
      refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hf.2.theta fun w hw => ?_
      rw [hΦ w hw]
      have e := congrFun h0 (fun τ i j => δ * embT D τ r * GlobalTheory.FockPos.zCo θ 1 1 w τ i j)
      simp only [Pi.zero_apply, hback] at e
      rw [e, mul_zero])
  have hR : Reads ψ θ rfl rfl cc δ r
      (fun Y => (fun Y' : VC D S.rank T.rank => Φ (δ⁻¹ • Y')) (fun τ i j => Y τ i j / embT D τ r)) f :=
    (reads_iff crv sc _ f).2 ⟨hf.2.theta, fun w hw => by
      rw [hΦ w hw]
      simp only [hback]⟩
  have e : f₀ = c • f := hf₀.unique (hc' ▸ hR.smul c)
  have hsm : ∀ u, heisO ψ S T u f = f → heisO ψ S T u f₀ = f₀ := fun u hu => by
    funext w
    have := congrFun hu w
    rw [e]
    simp only [heisO, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [mul_left_comm, this]
  exact ⟨fun u hu => hsm _ (hf0.2.lat.1 u hu), fun a ha u hu hh => hsm _ (hf0.2.lat.2 a ha u hu hh)⟩

def stab {G X : Type} [Group G] (om : G →* Module.End ℂ (X → ℂ)) (f : X → ℂ) : Subgroup G where
  carrier := {p | om p f = f}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    change om _ f = f at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := fun {a} ha => by
    change om _ f = f at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem isClosed_stab {G X : Type} [Group G] [TopologicalSpace G] (om : G →* Module.End ℂ (X → ℂ)) (f : X → ℂ)
    (h : ∀ w, Continuous fun p => om p f w) : IsClosed (stab om f : Set G) :=
  isClosed_eq (continuous_pi h) continuous_const

theorem inert_vacuum_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppInert D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Formalism.MainNotions.StandardLatticesGL3.IntG D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.IntG D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hset e0 W χS χT om hom _ t0 _ _ he hχS hχT f₀ hf₀ x y g h hg hh sx sy ix iy
  subst hS hT
  obtain ⟨sdS, sdT, hvac⟩ := latVac_of_reads hset he.1 hf₀
  have s1 : ∀ (V : HSp D) (ε : AF D.host.F), SuppPl ε V 1 := fun V ε i j => by
    rw [mt_one, sub_self, Matrix.zero_apply, mul_zero]
  have loc : ∀ v ε, NonSplitAt D v ε → ∀ g ∈ congrGroup S (inertInt D), ∀ h ∈ congrGroup T (inertInt D),
      SuppPl ε S g → SuppPl ε T h → om (g, h) f₀ = f₀ := fun v ε hv g hg h hh sg sh =>
    GlobalTheory.VecInvInert.om_fixes_vacuum D ψ S T _ _ χS χT om hom sdS sdT (exists_isEtaTilde_unramified D) v ε hv
      (unramAt_of_hasFinPart hχS hv) (unramAt_of_hasFinPart hχT hv) g h sg sh
      (actO_mem_iff hset.gS hset.crv.1.1 hset.scale hg hh) f₀ hf₀.1 hvac
  have hc := hom.om_cont f₀ hf₀.1
  have h1 : om (g, 1) f₀ = f₀ := congrGroup_le S (stab (om.comp (MonoidHom.inl _ _)) f₀)
    (isClosed_stab _ _ fun w => (hc w).comp (Continuous.prodMk_left 1))
    (fun v ε hv k hk sk => loc v ε hv k hk 1 (one_mem _) sk (s1 T ε)) (mem_congrGroup hset.gS hg sx ix)
  have h2 : om (1, h) f₀ = f₀ := congrGroup_le T (stab (om.comp (MonoidHom.inr _ _)) f₀)
    (isClosed_stab _ _ fun w => (hc w).comp (Continuous.prodMk_right 1))
    (fun v ε hv k hk sk => loc v ε hv 1 (one_mem _) k hk (s1 S ε) sk) (mem_congrGroup hset.gT hh sy iy)
  have hp : (g, h) = ((g, 1) : GA D S × GA D T) * (1, h) := Prod.ext (mul_one _).symm (one_mul _).symm
  rw [W.inert x y ix iy sx sy, hp, map_mul, Module.End.mul_apply, h2, h1]
  exact hf₀

end GlobalTheory.VacInertMove

end
end

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertIntegralPoints_fix_adelic_classical_vacuum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppInert D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Formalism.MainNotions.StandardLatticesGL3.IntG D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.IntG D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀) := by
  atlas_forward_decl GlobalTheory.VacInertMove.inert_vacuum_reads
end

section
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacMoveFin

theorem mulStep : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  ∀ (x₁ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₁ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₁ : GA D S) (h₁ : GA D T)
    (x₂ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₂ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₂ : GA D S) (h₂ : GA D T) (c₁ c₂ : ℂ),
    IsFinPt S g₁ x₁ → IsFinPt T h₁ y₁ → IsFinPt S g₂ x₂ → IsFinPt T h₂ y₂ →
    Reads ψ θ hS hT cc δ r (c₁ • W.Om x₁ y₁ e0) (om (g₁, h₁) f₀) → Reads ψ θ hS hT cc δ r (c₂ • W.Om x₂ y₂ e0) (om (g₂, h₂) f₀) →
    Reads ψ θ hS hT cc δ r ((c₁ * c₂) • W.Om (x₁ * x₂) (y₁ * y₂) e0) (om (g₁ * g₂, h₁ * h₂) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀ x₁ y₁ g₁ h₁ x₂ y₂ g₂ h₂ c₁ c₂ hg₁ hh₁ hg₂ hh₂ hr₁ hr₂
  have he := GlobalTheory.NormSum.Model.vac_mem_TT hSet.crv hodd.1
  have hG := GlobalTheory.NormSum.RatExtend.TT_smul c₂ (W.maps x₂ y₂ e0 he)
  have key := GlobalTheory.T.movedThetaFunctions_read_of_movedVacuum_reads ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hodd.1 x₁ y₁ g₁ h₁ hg₁ hh₁ c₁ f₀ hf₀ hr₁ _ hG _ hr₂
  have h1 : om (g₁ * g₂, h₁ * h₂) f₀ = om (g₁, h₁) (om (g₂, h₂) f₀) := by
    rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]
  have h2 : (c₁ * c₂) • W.Om (x₁ * x₂) (y₁ * y₂) e0 = c₁ • W.Om x₁ y₁ (c₂ • W.Om x₂ y₂ e0) := by
    rw [W.smul _ _ _ _ (W.maps x₂ y₂ e0 he), ← W.mul _ _ _ _ _ he, smul_smul]
  rw [h1, h2]; exact key

theorem vacuum_move_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ → Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT x y g h hg hh f₀ hf₀
  exact GlobalTheory.T.movedVacuum_constant_trivial_finite_pairs ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀
    (GlobalTheory.VacLine.moved_vacuum_reads ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀)
    (mulStep ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀)
    (GlobalTheory.SplitVacMove.reads_om_split ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀)
    (GlobalTheory.T.inertIntegralPoints_fix_adelic_classical_vacuum ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀) x y g h hg hh

end GlobalTheory.VacMoveFin
end

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_datum_finite_part_moves_vacuum_as_theta_model : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ → Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀) := by
  atlas_forward_decl GlobalTheory.VacMoveFin.vacuum_move_reads
end
