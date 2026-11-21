import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalFibPowExplicit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableProdPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleAffinePolynomialCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CokernelSubbundleIsVB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.C1FDetMetricEqChernOne
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GluedChartDensityMeasureAddOfCompatibleOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprEqZeroOfCardNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernTensorAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernRealClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsMapHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoGradedDeterminantIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernOneEqNegDdcLogDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteSymmetricMulDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensMulPullHeadL

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.LineForm GlobalTheory.CovTest GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.CxForm
open GlobalTheory.FlagFibre (Low)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.FibTriv

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {σ : k →+* ℂ}
  (π : Y ⟶ B) (w : π ≫ q = p) {E : B.Modules} (hE : IsVB E 2) (cE : Chart E 2)
  (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2)

abbrev cols {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Γ(Y, W)) : Fin 2 → Γ((Scheme.Modules.pullback π).obj E, W) :=
  pullCol π cE.e hW (uniR fun _ => n)

include w in

theorem crd_cols {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Γ(Y, W)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    (cE.pull hE π).crd p σ (cols π cE hW n 0) y = ![1, ev p σ W n y] ∧
      (cE.pull hE π).crd p σ (cols π cE hW n 1) y = ![0, 1] := by
  have hc : y ∈ ptsIn p σ (π ⁻¹ᵁ cE.U) := ptsIn_mono hW hy
  have hc' : PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U := hc
  have key (b : Fin 2) : (cE.pull hE π).crd p σ (cols π cE hW n b) y =
      fun a => ev p σ W (uniR (fun _ : Low 2 => n) a b) y := by
    funext a
    simp only [cols, pullCol, Chart.crd_sum, Chart.crd_smul, cE.crd_pull hE π w _ hW hy hc, cE.crd_frame hc',
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  constructor <;> rw [key] <;> funext a <;> fin_cases a <;> simp [uniR_apply, ev_eq hy]

include w in

theorem lineVec_of_spans {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Γ(Y, W)) (h : Spans fl W (cols π cE hW n))
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) : ∃ t : ℂ, t ≠ 0 ∧ lineVec π hE cE fl y = t • ![1, ev p σ W n y] := by
  obtain ⟨s, hs, es⟩ := h 1
  let cs : Chart (fl.F 1) 1 := ⟨W, s, hs⟩
  have ha := mem_frameAt fl y
  have hu := (isUnit_iff_isUnit_det _).1 (cs.isUnit_tr (frameAt fl y).sub hy ha)
  rw [det_unique] at hu
  refine ⟨_, hu.ne_zero, ?_⟩
  refine ((cE.pull hE π).crd_app cs (fl.ι 1) ((frameAt fl y).e 0) ha hy).trans ?_
  have e : (fl.ι 1).app W (cs.e 0) = cols π cE hW n 0 := es (0 : Fin 1)
  funext a
  simp only [mulVec, dotProduct, Fin.sum_univ_one, of_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_comm, ← (crd_cols π w hE cE hW n hy).1, ← e]
  rfl

theorem mem_finPart_of_spans {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Γ(Y, W)) (h : Spans fl W (cols π cE hW n))
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    y ∈ finPart π w hE cE fl σ ∧ slope π hE cE fl y = ev p σ W n y := by
  obtain ⟨t, ht, e⟩ := lineVec_of_spans π w hE cE fl hW n h hy
  refine ⟨⟨ptsIn_mono hW hy, by simpa [e] using ht⟩, ?_⟩
  simp [slope, e, ht]

theorem exists_spans {y : CxPts p σ} (hy : y ∈ finPart π w hE cE fl σ) :
    ∃ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Γ(Y, W)), y ∈ ptsIn p σ W ∧ Spans fl W (cols π cE hW n) := by
  let a := frameAt fl y
  let c := cE.pull hE π
  have h₀ : y ∈ ptsIn p σ (a.U ⊓ c.U) := mem_ptsIn_inf.2 ⟨mem_frameAt fl y, hy.1⟩
  let α : Fin 2 → Γ(Y, a.U ⊓ c.U) := (c.isFrame.basis inf_le_right).repr (resM _ inf_le_left (a.frame (.inl 0)))
  have hα : resM _ inf_le_left (a.frame (.inl 0)) = ∑ i, α i • resM _ inf_le_right (c.e i) := by
    conv_lhs => rw [← (c.isFrame.basis inf_le_right).sum_repr (resM _ inf_le_left (a.frame (.inl 0)))]
    simp only [IsFrame.basis_apply]
    rfl
  have hle := Y.basicOpen_le (α 0)
  obtain ⟨u, hu⟩ : IsUnit (resG Y hle (α 0)) := Y.toRingedSpace.isUnit_res_basicOpen (α 0)
  refine ⟨Y.basicOpen (α 0), hle.trans inf_le_right, resG Y hle (α 1) * u⁻¹.val,
    (mem_ptsIn_basicOpen h₀ _).2 hy.2, fun l => ?_⟩
  fin_cases l
  · refine ⟨Fin.elim0, fun W h => ?_, fun j => j.elim0⟩
    have z := isVB_zero_iff.1 (fl.isVB 0)
    refine ⟨fun _ _ _ => funext fun j => j.elim0, fun s => ⟨0, ?_⟩⟩
    have e := congrArg (fun φ => Scheme.Modules.Hom.app φ W s) (z.eq_of_src (𝟙 _) 0)
    exact (map_zero _).trans e.symm
  · refine ⟨_, UniColFrame.isFrame_cols (a.he.res (hle.trans inf_le_left)) (Matrix.of fun _ _ => u⁻¹.val) (by simp), fun j => ?_⟩
    obtain rfl : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    have e := congrArg (resM _ hle) hα
    have e' (i : Fin 2) : resM _ (hle.trans inf_le_right) (c.e i) =
        pullbackSections π E (hle.trans inf_le_right) (cE.e i) := QCoh.res_pullbackSections π E _ _ _
    simp only [resM_resM, map_add, resM_smul, Fin.sum_univ_two, ← hu, e'] at e
    refine (congrArg _ (Fin.sum_univ_one _)).trans ((Scheme.Modules.Hom.app_smul _ _ _).trans ?_)
    refine (congrArg (_ • ·) ((app_resM _ _ _).trans e)).trans ?_
    change _ = cols π cE _ _ 0
    rw [of_apply, smul_add, smul_smul, smul_smul, Units.inv_mul, mul_comm]
    unfold cols pullCol
    rw [Fin.sum_univ_two]
    rfl
  · have hf := UniColFrame.isFrame_pullCol_uniR _ _ π E 2 hE _ cE.e cE.isFrame _ (hle.trans inf_le_right)
      fun _ => resG Y hle (α 1) * u⁻¹.val
    refine ⟨_, hf.map_iso (inv (fl.ι (Fin.last 2))), fun j => ?_⟩
    exact congrArg (fun φ => Scheme.Modules.Hom.app φ _ _) (IsIso.inv_hom_id (fl.ι (Fin.last 2)))

theorem eq_of_slope_eq (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) fun _ => fl) {y y' : CxPts p σ}
    (hy : y ∈ finPart π w hE cE fl σ) (hy' : y' ∈ finPart π w hE cE fl σ)
    (e : PtsOver.map π w (spMap σ) y = PtsOver.map π w (spMap σ) y') (es : slope π hE cE fl y = slope π hE cE fl y') :
    y = y' := by
  obtain ⟨W, hW, n, hyW, hs⟩ := exists_spans π w hE cE fl hy
  obtain ⟨W', hW', n', hyW', hs'⟩ := exists_spans π w hE cE fl hy'
  rw [(mem_finPart_of_spans π w hE cE fl hW n hs hyW).2, (mem_finPart_of_spans π w hE cE fl hW' n' hs' hyW').2,
    ev_eq hyW, ev_eq hyW'] at es
  have e₁ : y'.1 ≫ π = y.1 ≫ π := (congrArg Subtype.val e).symm
  have k₁ := spans_pullCol_of_carries _ _ _ π Unit (fun _ => 2) (fun _ => E) (fun _ => fl) y.1 (y.1 ≫ π) rfl _
    (carries_carried π _ _ _ y.1 _ rfl) cE.U () cE.e W hW _ ⊤ hyW hy.1 hs
  have k₂ := spans_pullCol_of_carries _ _ _ π Unit (fun _ => 2) (fun _ => E) (fun _ => fl) y'.1 (y.1 ≫ π) e₁ _
    (carries_carried π _ _ _ y'.1 _ e₁) cE.U () cE.e W' hW' _ ⊤ hyW' hy.1 hs'
  rw [map_uniR] at k₁ k₂
  have e₂ : (y'.1.appLE W' ⊤ hyW').hom n' = (y.1.appLE W ⊤ hyW).hom n :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 es.symm
  rw [e₂] at k₂
  refine Subtype.ext ((hfl _ (y.1 ≫ π) (carried π _ _ (fun _ => fl) y.1 _ rfl)).unique
    ⟨rfl, carries_carried π _ _ _ y.1 _ rfl⟩ ⟨e₁, fun a i => ?_⟩)
  obtain ⟨e, he⟩ := steps_iso_of_spans_top _ _ _ _ _ _ k₂ k₁ i
  exact ⟨e, by simpa [carried, Vert.Flag.ofIso, Vert.Flag.pull] using he⟩

theorem exists_cell (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) fun _ => fl) {U : B.Opens} (hU : IsAffineOpen U)
    (h : U ≤ cE.U) : ∃ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U) (n : Γ(Y, W)), IsAffineOpen W ∧
      Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom fun _ : Unit => n) ∧
      Spans fl W (cols π cE (hW.trans (π.preimage_mono h)) n) ∧
      ptsIn p σ W = PtsOver.map π w (spMap σ) ⁻¹' ptsIn q σ U ∩ finPart π w hE cE fl σ := by
  obtain ⟨W, hW, hWa, n, hn, hs⟩ := GlobalTheory.T.flag_bundle_affine_polynomial_coords B Y π Unit (fun _ => 2) (fun _ => E) (fun _ => fl) hfl (fun _ => hE) U hU
    (fun _ i => resM E h (cE.e i)) fun _ => cE.isFrame.res h
  let s₀ : Σ _ : Unit, Low 2 := ⟨(), ⟨(1, 0), by decide⟩⟩
  have hs₀ (s : Σ _ : Unit, Low 2) : s = s₀ := by revert s; decide
  have hb : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom fun _ : Unit => n s₀) := by
    let ε : Unit ≃ Σ _ : Unit, Low 2 := ⟨fun _ => s₀, fun _ => (), fun _ => rfl, fun s => (hs₀ s).symm⟩
    have e : (MvPolynomial.eval₂Hom (π.appLE U W hW).hom fun _ : Unit => n s₀) =
        (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n).comp (MvPolynomial.renameEquiv Γ(B, U) ε).toRingEquiv.toRingHom :=
      MvPolynomial.ringHom_ext (fun a => by simp) fun a => by simp [ε]
    rw [e]
    exact hn.comp (MvPolynomial.renameEquiv Γ(B, U) ε).bijective
  have hS : Spans fl W (cols π cE (hW.trans (π.preimage_mono h)) (n s₀)) := by
    have := hs ()
    simp only [hs₀ ⟨(), _⟩] at this
    convert this using 1
    funext j
    exact Finset.sum_congr rfl fun l _ => congrArg _ (QCoh.pullbackSections_res π E hW h (cE.e l)).symm
  refine ⟨W, hW, n s₀, hWa, hb, hS, Set.ext fun y => ⟨fun hy => ⟨CellChart.map_mem π w hW hy,
    (mem_finPart_of_spans π w hE cE fl _ _ hS hy).1⟩, fun hy => ?_⟩⟩
  have hm := CellChart.cellPt_mem π w hW hWa _ hb hy.1 fun _ => slope π hE cE fl y
  have h₁ := mem_finPart_of_spans π w hE cE fl _ _ hS hm
  rwa [eq_of_slope_eq π w hE cE fl hfl h₁.1 hy.2 (CellChart.map_cellPt π w hW hWa _ hb hU _ _)
    (h₁.2.trans (CellChart.ev_n_cellPt π w hW hWa _ hb _ _ ()))] at hm

def swapChart : Chart E 2 := ⟨cE.U, cE.e ∘ Equiv.swap 0 1, cE.isFrame.comp_equiv _⟩

include w in

theorem lineVec_swap {y : CxPts p σ} (hy : PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U) :
    lineVec π hE (swapChart cE) fl y 0 = lineVec π hE cE fl y 1 ∧
      lineVec π hE (swapChart cE) fl y 1 = lineVec π hE cE fl y 0 := by
  have h := (cE.pull hE π).tr_mulVec ((swapChart cE).pull hE π) ((frameAt fl y).frame (.inl 0)) (mem_frameAt fl y) hy
  have e (b : Fin 2) : (cE.pull hE π).crd p σ (((swapChart cE).pull hE π).e b) y = Pi.single (Equiv.swap 0 1 b) 1 :=
    (cE.crd_pull hE π w _ le_rfl hy hy).trans (cE.crd_frame hy _)
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  simp [mulVec, dotProduct, Chart.tr, e] at h₀ h₁
  exact ⟨h₁, h₀⟩

include w in

theorem exists_adapted_of_spans {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Γ(Y, W)) (h : Spans fl W (cols π cE hW n)) :
    ∃ a : AdaptedChart (lineSC fl) 1 1, a.U = W ∧ ∀ y ∈ ptsIn p σ W,
      (cE.pull hE π).crd p σ (a.frame (.inl 0)) y = ![1, ev p σ W n y] ∧
      (cE.pull hE π).crd p σ (a.frame (.inr 0)) y = ![0, 1] := by
  obtain ⟨s, hs, es⟩ := h 1
  have hf := UniColFrame.isFrame_pullCol_uniR _ _ π E 2 hE _ cE.e cE.isFrame _ hW fun _ => n
  refine ⟨⟨W, s, fun j => cols π cE hW n (Fin.natAdd 1 j), hs,
    isFrame_cokernel_π (l := 1) (m := 1) (fl.ι 1) hf hs fun j => es j⟩, rfl, fun y hy => ⟨?_, ?_⟩⟩
  · exact (congrArg (fun t => (cE.pull hE π).crd p σ t y) (es (0 : Fin 1))).trans (crd_cols π w hE cE hW n hy).1
  · exact (crd_cols π w hE cE hW n hy).2

section

variable {d : ℕ}

theorem etale_snoc {k A R : Type} [CommRing k] [CommRing A] [CommRing R] (α : k →+* A) (t : Fin d → A) (f : A →+* R) (n : R)
    (hg : (MvPolynomial.eval₂Hom α t).Etale) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom f fun _ : Unit => n)) :
    (MvPolynomial.eval₂Hom (f.comp α) (Fin.snoc (α := fun _ => R) (fun a => f (t a)) n)).Etale := by
  let ι : MvPolynomial (Fin (d + 1)) k →+* MvPolynomial Unit (MvPolynomial (Fin d) k) :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
      (Fin.snoc (α := fun _ => _) (fun a => MvPolynomial.C (MvPolynomial.X a)) (MvPolynomial.X ()))
  let κ : MvPolynomial Unit (MvPolynomial (Fin d) k) →+* MvPolynomial (Fin (d + 1)) k :=
    MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom MvPolynomial.C fun a => MvPolynomial.X a.castSucc)
      fun _ => MvPolynomial.X (Fin.last d)
  have h1 : κ.comp ι = RingHom.id _ := MvPolynomial.ringHom_ext (fun r => by simp [ι, κ]) fun j => by
    induction j using Fin.lastCases <;> simp [ι, κ]
  have h2 : ι.comp κ = RingHom.id _ := MvPolynomial.ringHom_ext'
    (MvPolynomial.ringHom_ext (fun r => by simp [ι, κ]) fun j => by simp [ι, κ]) fun j => by simp [ι, κ]
  have hι : Function.Bijective ι :=
    Function.bijective_iff_has_inverse.2 ⟨κ, fun x => DFunLike.congr_fun h1 x, fun x => DFunLike.congr_fun h2 x⟩
  have key : MvPolynomial.eval₂Hom (f.comp α) (Fin.snoc (α := fun _ => R) (fun a => f (t a)) n) =
      (MvPolynomial.eval₂Hom f fun _ : Unit => n).comp ((MvPolynomial.map (MvPolynomial.eval₂Hom α t)).comp ι) :=
    MvPolynomial.ringHom_ext (fun r => by simp [ι]) fun j => by induction j using Fin.lastCases <;> simp [ι]
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hι) (etale_mvPolynomial_map_of_etale _ hg))
    (RingHom.Etale.of_bijective hΦ)

theorem exists_chart_le (c : AlgChart q σ d) {b : CxPts q σ} (hb : b ∈ c.e.source) {U : B.Opens} (hU : b ∈ ptsIn q σ U) :
    ∃ c₁ : AlgChart q σ d, b ∈ c₁.e.source ∧ c₁.U ≤ U ∧ c₁.e = c.e.restrOpen (ptsIn q σ c₁.U) (isOpen_ptsIn _) := by
  obtain ⟨f, hfU, hf⟩ := c.affine.exists_basicOpen_le (V := U) ⟨_, mem_ptsIn.1 hU⟩ (mem_ptsIn.1 (c.source_subset hb))
  have hle : B.basicOpen f ≤ c.U := B.basicOpen_le f
  refine ⟨⟨c.e.restrOpen (ptsIn q σ (B.basicOpen f)) (isOpen_ptsIn _), B.basicOpen f, c.affine.basicOpen f,
    fun a => resG B hle (c.x a), ?_, inter_subset_right, fun y hy a => (c.apply_eq y hy.1 a).trans (ev_res hle hy.2 _).symm,
    fun W g => (c.holo W g).mono fun v hv => ⟨hv.1.1, hv.2⟩⟩, ⟨hb, mem_ptsIn.2 hf⟩, hfU, rfl⟩
  have e : MvPolynomial.eval₂Hom (algX q (B.basicOpen f)) (fun a => resG B hle (c.x a)) =
      (resG B hle).comp (MvPolynomial.eval₂Hom (algX q c.U) c.x) := by
    rw [MvPolynomial.comp_eval₂Hom, GlobalTheory.TopForm.resG_comp_algX]
  rw [e]
  have hR : (resG B hle).Etale := by
    letI : Algebra Γ(B, c.U) Γ(B, B.basicOpen f) := (resG B hle).toAlgebra
    haveI : IsLocalization.Away f Γ(B, B.basicOpen f) := c.affine.isLocalization_basicOpen f
    exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway f)
  exact RingHom.Etale.stableUnderComposition _ _ c.etale hR

theorem exists_prodChart (c : AlgChart q σ d) {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ c.U) (hWa : IsAffineOpen W) (n : Γ(Y, W))
    (hΦ : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE c.U W hW).hom fun _ : Unit => n)) (y₀ : CxPts p σ) :
    ∃ c' : AlgChart p σ (d + 1), c'.e.source = PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ W ∧
      c'.e.target = basePt ⁻¹' c.e.target ∧
      ∀ y, c'.e y = prodPt (c.e (PtsOver.map π w (spMap σ) y)) (ev p σ W n y) := by
  classical
  let s (v : V (d + 1)) : CxPts p σ := if h : basePt v ∈ c.e.target then
    CellChart.cellPt π w hW hWa _ hΦ (c.source_subset (c.e.map_target h)) (fun _ => v (Fin.last d)) else y₀
  have hs {v : V (d + 1)} (h : basePt v ∈ c.e.target) : s v =
    CellChart.cellPt π w hW hWa _ hΦ (c.source_subset (c.e.map_target h)) (fun _ => v (Fin.last d)) := dif_pos h
  have s₁ (v : V (d + 1)) (h : basePt v ∈ c.e.target) : s v ∈ ptsIn p σ W := by
    rw [hs h]; exact CellChart.cellPt_mem ..
  have s₂ (v : V (d + 1)) (h : basePt v ∈ c.e.target) : PtsOver.map π w (spMap σ) (s v) = c.e.symm (basePt v) := by
    rw [hs h]; exact CellChart.map_cellPt _ _ _ _ _ _ c.affine _ _
  have s₃ (v : V (d + 1)) (h : basePt v ∈ c.e.target) : ev p σ W n (s v) = v (Fin.last d) := by
    rw [hs h]; exact CellChart.ev_n_cellPt π w hW hWa _ hΦ _ _ ()
  have hT : IsOpen (basePt ⁻¹' c.e.target : Set (V (d + 1))) := c.e.open_target.preimage differentiable_basePt.continuous
  have hol (g : Γ(Y, W)) : DifferentiableOn ℂ (fun v => ev p σ W g (s v)) (basePt ⁻¹' c.e.target) := by
    obtain ⟨P, rfl⟩ := hΦ.2 g
    induction P using MvPolynomial.induction_on with
    | C a =>
      have hd : DifferentiableOn ℂ (fun v : V (d + 1) => ev q σ c.U a (c.e.symm (basePt v))) (basePt ⁻¹' c.e.target) :=
        (c.holo c.U a).comp differentiable_basePt.differentiableOn fun v hv => ⟨hv, c.source_subset (c.e.map_target hv)⟩
      refine hd.congr fun v hv => ?_
      rw [MvPolynomial.eval₂Hom_C, CellChart.ev_appLE π w hW (s₁ v hv), s₂ v hv]
    | add P Q hP hQ =>
      simp only [map_add, ev_add]
      exact hP.add hQ
    | mul_X P i hP =>
      have hd : DifferentiableOn ℂ (fun v : V (d + 1) => v (Fin.last d)) (basePt ⁻¹' c.e.target) := by fun_prop
      simp only [map_mul, ev_mul, MvPolynomial.eval₂Hom_X']
      exact hP.mul (hd.congr s₃)
  obtain ⟨hc, hh⟩ := holo_of_affine hWa hT s₁ hol
  have hπ := PtsOver.continuous_map π w (spMap σ)
  let e : OpenPartialHomeomorph (CxPts p σ) (V (d + 1)) :=
    { toFun y := prodPt (c.e (PtsOver.map π w (spMap σ) y)) (ev p σ W n y)
      invFun := s
      source := PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ W
      target := basePt ⁻¹' c.e.target
      map_source' y hy := by simpa using c.e.map_source hy.1
      map_target' v hv := ⟨by rw [mem_preimage, s₂ v hv]; exact c.e.map_target hv, s₁ v hv⟩
      left_inv' y hy := by
        rw [hs (by simpa using c.e.map_source hy.1)]
        refine (CellChart.cellPt_congr π w hW hWa _ hΦ _ (CellChart.map_mem π w hW hy.2) ?_ ?_).trans
          (CellChart.cellPt_self π w hW hWa _ hΦ hy.2)
        · rw [basePt_prodPt, c.e.left_inv hy.1]
        · simp
      right_inv' v hv := by rw [s₂ v hv, s₃ v hv, c.e.right_inv hv, prodPt_basePt]
      open_source := (c.e.open_source.preimage hπ).inter (isOpen_ptsIn W)
      open_target := hT
      continuousOn_toFun := differentiable_prodPt.continuous.comp_continuousOn
        ((c.e.continuousOn.comp hπ.continuousOn fun y hy => hy.1).prodMk ((continuousOn_ev n).mono inter_subset_right))
      continuousOn_invFun := hc }
  refine ⟨⟨e, W, hWa, Fin.snoc (α := fun _ => _) (fun a => (π.appLE c.U W hW).hom (c.x a)) n, ?_, inter_subset_right,
    fun y hy a => ?_, hh⟩, rfl, rfl, fun _ => rfl⟩
  · have h := etale_snoc (algX q c.U) c.x (π.appLE c.U W hW).hom n c.etale hΦ
    rwa [CellChart.algX_eq π w hW] at h
  · change prodPt _ _ a = _
    induction a using Fin.lastCases with
    | last => rw [prodPt_last, Fin.snoc_last]
    | cast a => rw [prodPt_castSucc, Fin.snoc_castSucc, c.apply_eq _ hy.1, CellChart.ev_appLE π w hW hy.2]

end

variable {d : ℕ} (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) fun _ => fl)

include hfl in

theorem exists_slope_eq {b : CxPts q σ} (hb : b ∈ ptsIn q σ cE.U) (x : ℂ) :
    ∃ y ∈ finPart π w hE cE fl σ, PtsOver.map π w (spMap σ) y = b ∧ slope π hE cE fl y = x := by
  obtain ⟨U, hU, hbU, h⟩ := exists_isAffineOpen_le b.1 hb
  obtain ⟨W, hW, n, hWa, hΦ, hS, -⟩ := exists_cell (σ := σ) π w hE cE fl hfl hU h
  have h₁ := mem_finPart_of_spans π w hE cE fl _ _ hS (CellChart.cellPt_mem π w hW hWa _ hΦ (b := b) hbU fun _ => x)
  exact ⟨_, h₁.1, CellChart.map_cellPt π w hW hWa _ hΦ hU _ _, h₁.2.trans (CellChart.ev_n_cellPt π w hW hWa _ hΦ _ _ ())⟩

include hfl in

theorem exists_triv (b : CxPts q σ) (x : ℂ) : ∃ y : CxPts p σ, PtsOver.map π w (spMap σ) y = b ∧
    (b ∈ ptsIn q σ cE.U → y ∈ finPart π w hE cE fl σ ∧ slope π hE cE fl y = x) := by
  by_cases hb : b ∈ ptsIn q σ cE.U
  · obtain ⟨y, h₁, h₂, h₃⟩ := exists_slope_eq π w hE cE fl hfl hb x
    exact ⟨y, h₂, fun _ => ⟨h₁, h₃⟩⟩
  · obtain ⟨y, -, h₂, -⟩ := exists_slope_eq π w hE _ fl hfl (hE.mem_pick b) x
    exact ⟨y, h₂, fun h => (hb h).elim⟩

def triv (b : CxPts q σ) (x : ℂ) : CxPts p σ := (exists_triv π w hE cE fl hfl b x).choose

theorem map_triv (b : CxPts q σ) (x : ℂ) : PtsOver.map π w (spMap σ) (triv π w hE cE fl hfl b x) = b :=
  (exists_triv π w hE cE fl hfl b x).choose_spec.1

variable {cE}

theorem triv_mem {b : CxPts q σ} (hb : b ∈ ptsIn q σ cE.U) (x : ℂ) :
    triv π w hE cE fl hfl b x ∈ finPart π w hE cE fl σ :=
  ((exists_triv π w hE cE fl hfl b x).choose_spec.2 hb).1

theorem slope_triv {b : CxPts q σ} (hb : b ∈ ptsIn q σ cE.U) (x : ℂ) :
    slope π hE cE fl (triv π w hE cE fl hfl b x) = x :=
  ((exists_triv π w hE cE fl hfl b x).choose_spec.2 hb).2

theorem triv_slope {y : CxPts p σ} (hy : y ∈ finPart π w hE cE fl σ) :
    triv π w hE cE fl hfl (PtsOver.map π w (spMap σ) y) (slope π hE cE fl y) = y :=
  eq_of_slope_eq π w hE cE fl hfl (triv_mem π w hE fl hfl hy.1 _) hy (map_triv ..) (slope_triv π w hE fl hfl hy.1 _)

omit hfl in

theorem mem_infPart_iff {y : CxPts p σ} : y ∈ infPart π w hE cE fl σ ↔
    y ∈ finPart π w hE (swapChart cE) fl σ ∧ slope π hE (swapChart cE) fl y = 0 := by
  refine ⟨fun h => ?_, fun h => ⟨h.1.1, ?_⟩⟩
  · obtain ⟨e₀, e₁⟩ := lineVec_swap π w hE cE fl h.1
    refine ⟨⟨h.1, fun h₀ => lineVec_ne_zero π w hE cE fl h.1 (funext fun a => ?_)⟩, by rw [slope, e₁, h.2, zero_div]⟩
    fin_cases a
    exacts [h.2, e₀.symm.trans h₀]
  · exact (lineVec_swap π w hE cE fl h.1.1).2.symm.trans ((div_eq_zero_iff.1 h.2).resolve_right h.1.2)

theorem exists_trivChart (c : AlgChart q σ d) {b : CxPts q σ} (hc : b ∈ c.e.source) (hb : b ∈ ptsIn q σ cE.U) :
    ∃ (c₁ : AlgChart q σ d) (c' : AlgChart p σ (d + 1)) (a : AdaptedChart (lineSC fl) 1 1),
      b ∈ c₁.e.source ∧ c₁.U ≤ cE.U ∧ c₁.e = c.e.restrOpen (ptsIn q σ c₁.U) (isOpen_ptsIn _) ∧
      c'.e.source = PtsOver.map π w (spMap σ) ⁻¹' c₁.e.source ∩ finPart π w hE cE fl σ ∧
      c'.e.target = basePt ⁻¹' c₁.e.target ∧
      (∀ y ∈ c'.e.source, c'.e y = prodPt (c₁.e (PtsOver.map π w (spMap σ) y)) (slope π hE cE fl y)) ∧
      (∀ v ∈ c'.e.target, c'.e.symm v = triv π w hE cE fl hfl (c₁.e.symm (basePt v)) (v (Fin.last d))) ∧
      ∀ y ∈ c'.e.source, y ∈ ptsIn p σ a.U ∧
        (cE.pull hE π).crd p σ (a.frame (.inl 0)) y = ![1, slope π hE cE fl y] ∧
        (cE.pull hE π).crd p σ (a.frame (.inr 0)) y = ![0, 1] := by
  obtain ⟨c₁, h₁, h₂, h₃⟩ := exists_chart_le c hc hb
  obtain ⟨W, hW, n, hWa, hΦ, hS, hP⟩ := exists_cell (σ := σ) π w hE cE fl hfl c₁.affine h₂
  obtain ⟨c', e₁, e₂, e₃⟩ := exists_prodChart π w c₁ hW hWa n hΦ (triv π w hE cE fl hfl b 0)
  obtain ⟨a, ha, ha'⟩ := exists_adapted_of_spans (σ := σ) π w hE cE fl _ n hS
  have hm (y) (hy : y ∈ c'.e.source) : y ∈ ptsIn p σ W := (e₁ ▸ hy).2
  have hs (y) (hy : y ∈ c'.e.source) := mem_finPart_of_spans π w hE cE fl _ n hS (hm y hy)
  have e₄ (y) (hy : y ∈ c'.e.source) : c'.e y = prodPt (c₁.e (PtsOver.map π w (spMap σ) y)) (slope π hE cE fl y) := by
    rw [e₃, (hs y hy).2]
  refine ⟨c₁, c', a, h₁, h₂, h₃, ?_, e₂, e₄, fun v hv => ?_, fun y hy => ⟨ha ▸ hm y hy, ?_⟩⟩
  · rw [e₁, hP]
    exact Set.ext fun y => ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, c₁.source_subset h.1, h.2⟩⟩
  · have hy := c'.e.map_target hv
    have e := (c'.e.right_inv hv).symm.trans (e₄ _ hy)
    conv_rhs => rw [e]
    rw [basePt_prodPt, prodPt_last, c₁.e.left_inv (e₁ ▸ hy).1, triv_slope π w hE fl hfl (hs _ hy).1]
  · rw [(hs y hy).2]
    exact ha' y (hm y hy)

include hfl in

theorem exists_chart_infPart (c : AlgChart q σ d) {y : CxPts p σ} (hc : PtsOver.map π w (spMap σ) y ∈ c.e.source)
    (hy : y ∈ infPart π w hE cE fl σ) : ∃ c' : AlgChart p σ (d + 1), y ∈ c'.e.source ∧
      ∀ z ∈ c'.e.source, z ∈ infPart π w hE cE fl σ ↔ c'.e z (Fin.last d) = 0 := by
  obtain ⟨c₁, c', -, h₁, -, -, e₁, -, e₃, -⟩ := exists_trivChart (cE := swapChart cE) π w hE fl hfl c hc hy.1
  refine ⟨c', e₁ ▸ ⟨h₁, ((mem_infPart_iff π w hE fl).1 hy).1⟩, fun z hz => ?_⟩
  rw [e₃ z hz, prodPt_last, mem_infPart_iff, and_iff_right (e₁ ▸ hz).2]

end GlobalTheory.FibTriv
end
end

section
set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal ContDiff
open GlobalTheory.CxForm GlobalTheory.ChartGlue GlobalTheory.LineForm

namespace GlobalTheory.FormPartition

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem exists_bump [T2Space M] (x : M) {U : Set M} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ (i : A.ι) (ψ : M → ℝ), A.SmoothOn univ (fun y => (ψ y : ℂ)) ∧ (∀ y, 0 ≤ ψ y ∧ ψ y ≤ 1) ∧
      tsupport ψ ⊆ U ∩ (A.e i).source ∧ ∀ᶠ y in 𝓝 x, ψ y = 1 := by
  classical
  obtain ⟨i, hxe⟩ := A.cover x
  set e := A.e i with he
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_over e hU) (e x) (mem_over e hxe hx)
  let β : ContDiffBump (e x) := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  have hcb : Metric.closedBall (e x) (ε / 2) ⊆ e.target ∩ e.symm ⁻¹' U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  set C := e.symm '' Metric.closedBall (e x) (ε / 2) with hC
  have hCc : IsCompact C := (isCompact_closedBall (e x) (ε / 2)).image_of_continuousOn
    (e.continuousOn_symm.mono fun y hy => (hcb hy).1)
  have hCsub : C ⊆ U ∩ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(hcb hy).2, e.map_target (hcb hy).1⟩
  let ψ : M → ℝ := fun w => if w ∈ e.source then β (e w) else 0
  have hsupp : Function.support ψ ⊆ C := by
    intro w hw
    simp only [Function.mem_support, ψ] at hw
    split_ifs at hw with hws
    · have : e w ∈ Metric.ball (e x) (ε / 2) := by
        rw [← β.support_eq]; exact hw
      exact ⟨e w, Metric.ball_subset_closedBall this, e.left_inv hws⟩
    · exact absurd rfl hw
  have hts : tsupport ψ ⊆ C := closure_minimal hsupp hCc.isClosed
  refine ⟨i, ψ, ?_, fun y => ?_, hts.trans hCsub, ?_⟩
  · intro k
    rw [preimage_univ, inter_univ]
    apply contDiffOn_of_locally_contDiffOn
    intro y hy
    by_cases hys : (A.e k).symm y ∈ e.source
    · refine ⟨(A.e k).target ∩ (A.e k).symm ⁻¹' e.source,
        (A.e k).isOpen_inter_preimage_symm e.open_source, ⟨hy, hys⟩, ?_⟩
      have hβ : ContDiff ℝ ∞ (fun y : V n => ((β y : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp β.contDiff
      refine ((hβ.comp_contDiffOn (A.contDiffOn_real_transition k i)).mono inter_subset_right).congr
        fun v hv => ?_
      have hv1 : (A.e k).symm v ∈ e.source := hv.2.2
      simp only [Function.comp, ψ, if_pos hv1]
      rfl
    · refine ⟨(A.e k).target ∩ (A.e k).symm ⁻¹' Cᶜ,
        (A.e k).isOpen_inter_preimage_symm hCc.isClosed.isOpen_compl,
        ⟨hy, fun h => hys (hCsub h).2⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : ℂ))).congr fun v hv => ?_
      have : ψ ((A.e k).symm v) = 0 := by
        by_contra h
        exact hv.2.2 (hsupp h)
      simp [Function.comp, this]
  · simp only [ψ]
    split_ifs
    exacts [⟨β.nonneg, β.le_one⟩, ⟨le_rfl, zero_le_one⟩]
  · have ho : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e x) (ε / 4)) :=
      e.isOpen_inter_preimage Metric.isOpen_ball
    filter_upwards [ho.mem_nhds ⟨hxe, Metric.mem_ball_self (by linarith)⟩] with w hw
    simp only [ψ, if_pos hw.1]
    exact β.one_of_mem_closedBall (Metric.ball_subset_closedBall hw.2)

theorem exists_partition [CompactSpace M] [T2Space M] {κ : Type*} (U : κ → Set M) (hU : ∀ a, IsOpen (U a))
    (hc : ∀ y, ∃ a, y ∈ U a) :
    ∃ (N : ℕ) (a : Fin N → κ) (c : Fin N → A.ι) (χ : Fin N → M → ℝ), (∀ j, A.SmoothOn univ fun y => (χ j y : ℂ)) ∧
      (∀ j y, 0 ≤ χ j y) ∧ (∀ y, ∑ j, χ j y = 1) ∧
      ∀ j, IsCompact (tsupport (χ j)) ∧ tsupport (χ j) ⊆ U (a j) ∧ tsupport (χ j) ⊆ (A.e (c j)).source := by
  classical
  choose a ha using hc
  choose E Ψ hΨs hΨ0 hΨt hΨ1 using fun x => exists_bump A x (hU (a x)) (ha x)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : M => interior {y | Ψ x y = 1})
    (fun _ => isOpen_interior) (fun y _ => mem_iUnion.2 ⟨y, mem_interior_iff_mem_nhds.2 (hΨ1 y)⟩)
  let p : Fin t.card → M := fun i => (t.equivFin.symm i : M)
  let ψ : Fin t.card → M → ℝ := fun i => Ψ (p i)
  have hsum : ∀ x, ∑ i, ψ i x * ∏ j ∈ Finset.univ with j < i, (1 - ψ j x) =
      1 - ∏ i, (1 - ψ i x) := fun x => by
    rw [Finset.prod_one_sub_ordered]; ring
  refine ⟨t.card, fun i => a (p i), fun i => E (p i), fun i x => ψ i x * ∏ j ∈ Finset.univ with j < i, (1 - ψ j x),
    fun i k => ?_, fun i x => ?_, fun x => ?_, fun i => ⟨(isClosed_tsupport _).isCompact,
      (tsupport_mul_subset_left.trans (hΨt (p i))).trans inter_subset_left,
      (tsupport_mul_subset_left.trans (hΨt (p i))).trans inter_subset_right⟩⟩
  · refine ((hΨs (p i) k).mul (contDiffOn_prod (t := Finset.univ.filter (· < i))
      fun j _ => (contDiffOn_const (c := (1 : ℂ))).sub (hΨs (p j) k))).congr fun v _ => ?_
    simp [Function.comp, ψ]
  · exact mul_nonneg (hΨ0 _ _).1 (Finset.prod_nonneg fun j _ => sub_nonneg.2 (hΨ0 _ _).2)
  · rw [hsum]
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    have h1 : ψ (t.equivFin ⟨u, hu⟩) x = 1 := by
      have : p (t.equivFin ⟨u, hu⟩) = u := by simp [p]
      simp only [ψ, this]
      exact (interior_subset hxu : x ∈ {y | Ψ u y = 1})
    rw [Finset.prod_eq_zero (Finset.mem_univ (t.equivFin ⟨u, hu⟩)) (by rw [h1]; ring)]
    ring

theorem loc_sum {κ : Type*} (s : Finset κ) (α : κ → A.Fld) (i : A.ι) (v : V n) :
    A.loc (∑ j ∈ s, α j) i v = ∑ j ∈ s, A.loc (α j) i v := by
  unfold HolAtlas.loc
  split_ifs
  · exact Finset.sum_apply _ _ _
  · exact Finset.sum_const_zero.symm

theorem isForm_sum {κ : Type*} (s : Finset κ) {α : κ → A.Fld} (h : ∀ j ∈ s, A.IsForm (α j)) :
    A.IsForm (∑ j ∈ s, α j) := by
  refine ⟨fun i S => ?_, fun x x' e => ?_⟩
  · simp only [loc_sum, map_sum, Finsupp.finsetSum_apply]
    exact ContDiffOn.sum fun j hj => (h j hj).smooth i S
  · rw [Finset.sum_apply, Finset.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun j hj => (h j hj).compat x x' e

theorem isForm_fn_mul {χ : M → ℝ} (hχ : A.SmoothOn univ fun y => (χ y : ℂ)) {α : A.Fld} (hα : A.IsForm α) :
    A.IsForm (A.fn χ * α) :=
  FormMul.isForm_mul A _ _ (A.isForm_fn hχ) hα

theorem sum_fn_mul {κ : Type*} (s : Finset κ) {χ : κ → M → ℝ} (h : ∀ y, ∑ j ∈ s, χ j y = 1) (α : A.Fld) :
    ∑ j ∈ s, A.fn (χ j) * α = α := by
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.mul_apply, HolAtlas.fn]
  rw [← Finset.sum_mul, ← map_sum, ← Complex.ofReal_sum, h, Complex.ofReal_one, map_one, one_mul]

def rd (α : A.Fld) (i : A.ι) (v : V n) : ℝ := (dens (A.loc α i v)).re

theorem rd_add (α β : A.Fld) (i : A.ι) (v : V n) : rd A (α + β) i v = rd A α i v + rd A β i v := by
  have : A.loc (α + β) i v = A.loc α i v + A.loc β i v := by
    unfold HolAtlas.loc; split_ifs
    · rfl
    · exact (add_zero 0).symm
  simp only [rd, this, dens, map_add, Finsupp.add_apply, add_div, Complex.add_re]

theorem rd_zero (i : A.ι) (v : V n) : rd A 0 i v = 0 := by
  have : A.loc 0 i v = 0 := by
    unfold HolAtlas.loc; split_ifs <;> rfl
  simp [rd, this, dens]

def Good (r : A.ι → V n → ℝ) : Prop :=
  (∀ i, ContinuousOn (r i) (A.e i).target) ∧
  ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
    r i (A.e i y) = ‖transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y)

theorem good_rd {α : A.Fld} (hα : A.IsForm α) : Good A (rd A α) := by
  refine ⟨fun i => Complex.continuous_re.comp_continuousOn ((hα.smooth i Finset.univ).continuousOn.div_const _),
    fun i j y hi hj => ?_⟩
  have h1 := A.loc_crd α (⟨(i, y), hi⟩ : A.Pt)
  have h2 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
  have h3 := hα.compat (⟨(i, y), hi⟩ : A.Pt) ⟨(j, y), hj⟩ rfl
  simp only [rd]
  erw [h1, h2, h3, dens_pull]
  rw [Complex.re_ofReal_mul]
  rfl

theorem good_sign {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) : Good A fun i v => ((ε : ℤ) : ℝ) * rd A α i v :=
  ⟨fun i => continuousOn_const.mul ((good_rd A hα).1 i),
    fun i j y hi hj => by simp only [(good_rd A hα).2 i j y hi hj]; ring⟩

variable {A} in
theorem Good.compat {r : A.ι → V n → ℝ} (h : Good A r) (i j : A.ι) (y : M) (hi : y ∈ (A.e i).source)
    (hj : y ∈ (A.e j).source) : ENNReal.ofReal (r i (A.e i y)) =
      ENNReal.ofReal (‖transDet (A.e i) (A.e j) y‖ ^ 2) * ENNReal.ofReal (r j (A.e j y)) := by
  rw [h.2 i j y hi hj, ENNReal.ofReal_mul (by positivity)]

variable {A} in
theorem Good.aem {r : A.ι → V n → ℝ} (hr : Good A r) (i : A.ι) :
    AEMeasurable (fun v => ENNReal.ofReal (r i (A.e i ((A.e i).symm v)))) (volume.restrict (A.e i).target) := by
  have h := (ENNReal.continuous_ofReal.comp_continuousOn (hr.1 i)).aemeasurable (μ := volume)
    (A.e i).open_target.measurableSet
  refine h.congr ((ae_restrict_iff' (A.e i).open_target.measurableSet).2 (Eventually.of_forall fun v hv => ?_))
  simp [(A.e i).right_inv hv]

theorem ofReal_posNeg (x y : ℝ) :
    ENNReal.ofReal (x + y) + ENNReal.ofReal (-x) + ENNReal.ofReal (-y) =
      ENNReal.ofReal (-(x + y)) + ENNReal.ofReal x + ENNReal.ofReal y := by
  have m : ∀ t : ℝ, ENNReal.ofReal t = ENNReal.ofReal (max t 0) := fun t => by
    rcases le_total t 0 with h | h
    · simp [h, ENNReal.ofReal_of_nonpos h]
    · simp [h]
  have k : max (x + y) 0 + max (-x) 0 + max (-y) 0 = max (-(x + y)) 0 + max x 0 + max y 0 := by
    simp only [max_def]; split_ifs <;> linarith
  rw [m (x + y), m (-x), m (-y), m (-(x + y)), m x, m y,
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _), k]

variable [MeasurableSpace M] [BorelSpace M]

theorem part_eq (α : A.Fld) (ε : ℤˣ) :
    A.part α ε = glueMeas A.e fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * rd A α i (A.e i y)) := rfl

theorem part_zero (ε : ℤˣ) : A.part 0 ε = 0 := by
  rw [part_eq]
  refine le_antisymm (iSup_le fun i => Measure.le_iff.2 fun S hS => ?_) bot_le
  rw [chartMeas_apply _ _ hS]
  simp [rd_zero]

variable [SecondCountableTopology M]

theorem part_apply {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) (i : A.ι) {S : Set M} (hS : MeasurableSet S)
    (h : S ⊆ (A.e i).source) :
    A.part α ε S = ∫⁻ v in A.e i '' S, ENNReal.ofReal (((ε : ℤ) : ℝ) * rd A α i (A.e i ((A.e i).symm v))) := by
  rw [part_eq, glueMeas_apply _ _ A.holo (good_sign A hα ε).compat i hS h, chartMeas_apply_of_subset _ _ hS h]

theorem aem_part {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) (i : A.ι) {S : Set M} (h : S ⊆ (A.e i).source) :
    AEMeasurable (fun v => ENNReal.ofReal (((ε : ℤ) : ℝ) * rd A α i (A.e i ((A.e i).symm v))))
      (volume.restrict (A.e i '' S)) :=
  ((good_sign A hα ε).aem i).mono_measure (Measure.restrict_mono
    (by rintro _ ⟨y, hy, rfl⟩; exact (A.e i).map_source (h hy)) le_rfl)

theorem isForm_add {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) : A.IsForm (α + β) := by
  have := isForm_sum A Finset.univ (α := fun b : Bool => cond b α β) fun j _ => by cases j; exacts [hβ, hα]
  rwa [Fintype.sum_bool] at this

theorem isFiniteMeasure_part [CompactSpace M] {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) :
    IsFiniteMeasure (A.part α ε) :=
  ⟨by
    rw [part_eq]
    exact lt_top_iff_ne_top.2 (glueMeas_univ_ne_top_of_compact A.e A.cover A.holo
      (fun i v => ((ε : ℤ) : ℝ) * rd A α i v) (good_sign A hα ε).1 (good_sign A hα ε).2)⟩

theorem part_balance {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) (ε : ℤˣ) :
    A.part (α + β) ε + A.part α (-ε) + A.part β (-ε) = A.part (α + β) (-ε) + A.part α ε + A.part β ε := by
  have hs := isForm_add A hα hβ
  refine ext_of_cover (fun i => (A.e i).source) (fun i => (A.e i).open_source) A.cover fun i S hS h => ?_
  simp only [Measure.add_apply, part_apply A hα _ i hS h, part_apply A hβ _ i hS h, part_apply A hs _ i hS h]
  rw [← lintegral_add_left' (aem_part A hs _ i h), ← lintegral_add_left' (aem_part A hs _ i h),
    ← lintegral_add_right' _ (aem_part A hβ _ i h), ← lintegral_add_right' _ (aem_part A hβ _ i h)]
  refine lintegral_congr fun v => ?_
  simp only [rd_add, Units.val_neg, Int.cast_neg, neg_mul, mul_add]
  rw [← neg_add]
  exact ofReal_posNeg _ _

theorem part_add_le {α β : A.Fld} (ε : ℤˣ) (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.part (α + β) ε ≤ A.part α ε + A.part β ε := by
  have key : glueMeas A.e (fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * rd A α i (A.e i y)) +
      ENNReal.ofReal (((ε : ℤ) : ℝ) * rd A β i (A.e i y))) = A.part α ε + A.part β ε := by
    ext S hS
    exact glueMeas_add_of_compat_on A.e A.holo A.cover hS _ _
      (fun i j y _ hi hj => (good_sign A hα ε).compat i j y hi hj)
      (fun i j y _ hi hj => (good_sign A hβ ε).compat i j y hi hj)
      fun i => ((good_sign A hα ε).aem i).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  rw [← key, part_eq]
  exact iSup_mono fun i => Measure.le_iff.2 fun S hS => by
    rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
    exact lintegral_mono fun v => by beta_reduce; rw [rd_add, mul_add]; exact ENNReal.ofReal_add_le

theorem wInt_add {g : M → ℝ} {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β)
    (ga : ∀ ε : ℤˣ, Integrable g (A.part α ε)) (gb : ∀ ε : ℤˣ, Integrable g (A.part β ε)) :
    (∀ ε : ℤˣ, Integrable g (A.part (α + β) ε)) ∧ wInt A g (α + β) = wInt A g α + wInt A g β := by
  have gs : ∀ ε : ℤˣ, Integrable g (A.part (α + β) ε) := fun ε =>
    ((ga ε).add_measure (gb ε)).mono_measure (part_add_le A ε hα hβ)
  refine ⟨gs, ?_⟩
  have key := congrArg (fun μ : Measure M => ∫ y, g y ∂μ) (part_balance A hα hβ 1)
  beta_reduce at key
  rw [integral_add_measure (((gs 1).add_measure (ga (-1)))) (gb (-1)),
    integral_add_measure (gs 1) (ga (-1)),
    integral_add_measure (((gs (-1)).add_measure (ga 1))) (gb 1),
    integral_add_measure (gs (-1)) (ga 1)] at key
  simp only [wInt]
  linarith

theorem wInt_sum {κ : Type*} (s : Finset κ) {g : M → ℝ} {α : κ → A.Fld} (hα : ∀ j ∈ s, A.IsForm (α j))
    (hg : ∀ j ∈ s, ∀ ε : ℤˣ, Integrable g (A.part (α j) ε)) :
    (∀ ε : ℤˣ, Integrable g (A.part (∑ j ∈ s, α j) ε)) ∧ wInt A g (∑ j ∈ s, α j) = ∑ j ∈ s, wInt A g (α j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wInt, part_zero]
  | insert a s ha ih =>
    have h' : ∀ j ∈ s, A.IsForm (α j) := fun j hj => hα j (Finset.mem_insert_of_mem hj)
    obtain ⟨i₁, i₂⟩ := ih h' fun j hj => hg j (Finset.mem_insert_of_mem hj)
    obtain ⟨k₁, k₂⟩ := wInt_add A (hα a (Finset.mem_insert_self a s)) (isForm_sum A s h')
      (hg a (Finset.mem_insert_self a s)) i₁
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨k₁, by rw [k₂, i₂]⟩

theorem integral_sum [CompactSpace M] {κ : Type*} (s : Finset κ) {α : κ → A.Fld} (hα : ∀ j ∈ s, A.IsForm (α j)) :
    A.integral (∑ j ∈ s, α j) = ∑ j ∈ s, A.integral (α j) := by
  simp only [← wInt_one]
  exact (wInt_sum A s hα fun j hj ε => by
    have := isFiniteMeasure_part A (hα j hj) ε
    exact integrable_const _).2

section Variety

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (h : IsRegVar p D) (σ : k →+* ℂ)

theorem exists_partition_regVar {κ : Type*} (U : κ → Set (CxPts p σ)) (hU : ∀ a, IsOpen (U a))
    (hc : ∀ y, ∃ a, y ∈ U a) :
    ∃ (N : ℕ) (a : Fin N → κ) (c : Fin N → (h.atlas σ).ι) (χ : Fin N → CxPts p σ → ℝ),
      (∀ j, (h.atlas σ).SmoothOn univ fun y => (χ j y : ℂ)) ∧ (∀ j y, 0 ≤ χ j y) ∧ (∀ y, ∑ j, χ j y = 1) ∧
      ∀ j, IsCompact (tsupport (χ j)) ∧ tsupport (χ j) ⊆ U (a j) ∧
        tsupport (χ j) ⊆ ((h.atlas σ).e (c j)).source :=
  have := h.toIsArithVar.compactSpace σ
  have := CxPts.t2Space_cxPts_of_isProjOver σ h.isProjOver
  exists_partition _ U hU hc

theorem integral_sum_regVar {κ : Type*} (s : Finset κ) {α : κ → (h.atlas σ).Fld}
    (hα : ∀ j ∈ s, (h.atlas σ).IsForm (α j)) :
    (h.atlas σ).integral (∑ j ∈ s, α j) = ∑ j ∈ s, (h.atlas σ).integral (α j) :=
  have := h.toIsArithVar.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ h.isProjOver
  integral_sum _ s hα

end Variety

end GlobalTheory.FormPartition
end
end

section
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm GlobalTheory.LocFub

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocFub

def headLastIsom (n : ℕ) : V (n + 1) →ₗᵢ[ℂ] WithLp 2 (V n × ℂ) where
  toLinearMap := (WithLp.linearEquiv 2 ℂ (V n × ℂ)).symm.toLinearMap ∘ₗ
    LinearMap.prod (headL n).toLinearMap ((EuclideanSpace.proj (Fin.last n) : V (n + 1) →L[ℂ] ℂ).toLinearMap)
  norm_map' v := by
    have h : ‖(WithLp.toLp 2 (headL n v, v (Fin.last n)) : WithLp 2 (V n × ℂ))‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fin.sum_univ_castSucc]
      simp [headL_apply]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem headLastIsom_apply (n : ℕ) (v : V (n + 1)) :
    headLastIsom n v = WithLp.toLp 2 (headL n v, v (Fin.last n)) := rfl

theorem headLastIsom_surjective (n : ℕ) : Function.Surjective (headLastIsom n) := by
  intro p
  obtain ⟨q, rfl⟩ : ∃ q, p = WithLp.toLp 2 q := ⟨WithLp.ofLp p, (WithLp.toLp_ofLp (p := 2) p).symm⟩
  refine ⟨WithLp.toLp 2 (Fin.snoc (α := fun _ => ℂ) (WithLp.ofLp q.1) q.2), ?_⟩
  rw [headLastIsom_apply]
  congr 1
  ext
  · simp [headL_apply]
  · simp

def headLastMeas (n : ℕ) : V (n + 1) ≃ᵐ V n × ℂ :=
  ((LinearIsometryEquiv.ofSurjective (headLastIsom n) (headLastIsom_surjective n)).toHomeomorph.toMeasurableEquiv).trans
    (MeasurableEquiv.toLp 2 (V n × ℂ)).symm

theorem headLastMeas_apply (n : ℕ) (v : V (n + 1)) : headLastMeas n v = (headL n v, v (Fin.last n)) := rfl

theorem headLastMeas_measurePreserving (n : ℕ) : MeasurePreserving (headLastMeas n) := by
  let e := LinearIsometryEquiv.ofSurjective (headLastIsom n) (headLastIsom_surjective n)
  let eR : V (n + 1) ≃ₗᵢ[ℝ] WithLp 2 (V n × ℂ) :=
    { toLinearEquiv := e.toLinearEquiv.restrictScalars ℝ, norm_map' := e.norm_map }
  have h1 : MeasurePreserving eR := LinearIsometryEquiv.measurePreserving eR
  exact (WithLp.volume_preserving_ofLp (V n) ℂ).comp h1

theorem integral_headL_last {n : ℕ} (F : V n → ℂ → ℝ)
    (hF : Integrable (fun v : V (n + 1) => F (headL n v) (v (Fin.last n)))) :
    Integrable (fun w => ∫ x, F w x) ∧ ∫ v, F (headL n v) (v (Fin.last n)) = ∫ w, ∫ x, F w x := by
  have hmp := headLastMeas_measurePreserving n
  have hc : (fun v : V (n + 1) => F (headL n v) (v (Fin.last n))) = Function.uncurry F ∘ headLastMeas n := rfl
  have hI : Integrable (Function.uncurry F) ((volume : Measure (V n)).prod (volume : Measure ℂ)) := by
    rw [hc] at hF
    exact (hmp.integrable_comp_emb (headLastMeas n).measurableEmbedding).1 hF
  refine ⟨hI.integral_prod_left, ?_⟩
  calc ∫ v, F (headL n v) (v (Fin.last n)) = ∫ v, Function.uncurry F (headLastMeas n v) := rfl
    _ = ∫ z, Function.uncurry F z ∂((volume : Measure (V n)).prod (volume : Measure ℂ)) :=
        hmp.integral_comp' (Function.uncurry F)
    _ = ∫ w, ∫ x, F w x := integral_prod _ hI

end GlobalTheory.LocFub
end
end

section
section
set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.LocFub GlobalTheory.FibTriv GlobalTheory.FormPartition
open scoped ComplexOrder

namespace GlobalTheory.FibGlob

section Manifold

variable {M : Type} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ}
  (A : HolAtlas M n)

theorem part_eq_zero {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) (i : A.ι) {S : Set M} (hS : MeasurableSet S)
    (h : S ⊆ (A.e i).source) (h0 : volume (A.e i '' S) = 0 ∨ ∀ x : A.Pt, x.pt ∈ S → α x = 0) : A.part α ε S = 0 := by
  rw [part_apply A hα ε i hS h]
  rcases h0 with h0 | h0
  · exact setLIntegral_measure_zero _ _ h0
  · refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _ hS h) ?_
    rintro _ ⟨y, hy, rfl⟩
    have e := A.loc_crd α ⟨(i, y), h hy⟩
    rw [h0 ⟨(i, y), h hy⟩ hy] at e
    simp only [(A.e i).left_inv (h hy), rd, Pi.zero_apply]
    erw [e]
    simp [dens]

theorem integral_eq_chart [CompactSpace M] {α : A.Fld} (hα : A.IsForm α) (i : A.ι)
    (h0 : ∀ ε : ℤˣ, A.part α ε (A.e i).sourceᶜ = 0) :
    Integrable (rd A α i) ∧ A.integral α = ∫ v, rd A α i v := by
  have hs := (A.e i).open_source.measurableSet
  have ht := (A.e i).open_target.measurableSet
  have hz : ∀ v ∉ (A.e i).target, rd A α i v = 0 := fun v hv => by simp [rd, HolAtlas.loc, hv, dens]
  have hp : ∀ ε : ℤˣ, A.part α ε univ = ∫⁻ v, ENNReal.ofReal (((ε : ℤ) : ℝ) * rd A α i v) := by
    intro ε
    rw [← measure_add_measure_compl hs, h0, add_zero, part_apply A hα ε i hs subset_rfl, (A.e i).image_source_eq_target,
      ← lintegral_indicator ht]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ (A.e i).target
    · rw [indicator_of_mem hv, (A.e i).right_inv hv]
    · rw [indicator_of_notMem hv, hz v hv, mul_zero, ENNReal.ofReal_zero]
  have hcon : ContinuousOn (rd A α i) (A.e i).target :=
    Complex.continuous_re.comp_continuousOn ((hα.smooth i Finset.univ).continuousOn.div_const _)
  have hm : AEStronglyMeasurable (rd A α i) volume := by
    have e : rd A α i = (A.e i).target.indicator (rd A α i) := by
      funext v
      by_cases hv : v ∈ (A.e i).target
      · rw [indicator_of_mem hv]
      · rw [indicator_of_notMem hv, hz v hv]
    rw [e]
    exact (aestronglyMeasurable_indicator_iff ht).2 (hcon.aestronglyMeasurable ht)
  have e1 := hp 1
  have e2 := hp (-1)
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_one_mul] at e1 e2
  have f1 := isFiniteMeasure_part A hα 1
  have f2 := isFiniteMeasure_part A hα (-1)
  have hi : Integrable (rd A α i) := by
    refine ⟨hm, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    calc ∫⁻ v, ENNReal.ofReal ‖rd A α i v‖
        ≤ ∫⁻ v, (ENNReal.ofReal (rd A α i v) + ENNReal.ofReal (-rd A α i v)) := lintegral_mono fun v => by
          rcases le_total 0 (rd A α i v) with h | h
          · rw [Real.norm_of_nonneg h]; exact le_self_add
          · rw [Real.norm_of_nonpos h]; exact le_add_self
      _ = A.part α 1 univ + A.part α (-1) univ := by
          rw [lintegral_add_left' hm.aemeasurable.ennreal_ofReal, e1, e2]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨measure_lt_top _ _, measure_lt_top _ _⟩
  refine ⟨hi, ?_⟩
  simp only [HolAtlas.integral, Measure.real, e1, e2]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi).symm

theorem part_compl_eq_zero {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) {K S : Set M} (hK : IsClosed K)
    (h0 : ∀ x : A.Pt, x.pt ∉ K → α x = 0)
    (hS : ∀ y ∈ S, y ∈ K → ∃ (j : A.ι) (T : Set M), MeasurableSet T ∧ T ∈ 𝓝[S] y ∧ T ⊆ (A.e j).source ∧
      volume (A.e j '' T) = 0) : A.part α ε S = 0 := by
  refine measure_null_of_locally_null S fun y hy => ?_
  by_cases hk : y ∈ K
  · obtain ⟨j, T, hT, h₁, h₂, h₃⟩ := hS y hy hk
    exact ⟨T, h₁, part_eq_zero A hα ε j hT h₂ (.inl h₃)⟩
  · obtain ⟨j, hj⟩ := A.cover y
    have ho : IsOpen ((A.e j).source ∩ Kᶜ) := (A.e j).open_source.inter hK.isOpen_compl
    exact ⟨_, mem_nhdsWithin_of_mem_nhds (ho.mem_nhds ⟨hj, hk⟩),
      part_eq_zero A hα ε j ho.measurableSet inter_subset_left (.inr fun x hx => h0 x hx.2)⟩

theorem volume_last_eq_zero (n : ℕ) : volume {v : V (n + 1) | v (Fin.last n) = 0} = 0 := by
  let L : V (n + 1) →L[ℂ] ℂ := EuclideanSpace.proj (Fin.last n)
  refine Measure.addHaar_submodule volume (LinearMap.ker (L.toLinearMap.restrictScalars ℝ)) fun h => ?_
  have : EuclideanSpace.single (Fin.last n) (1 : ℂ) ∈ LinearMap.ker (L.toLinearMap.restrictScalars ℝ) := by
    rw [h]; trivial
  simp [L] at this

theorem integral_eq_of_fibre [CompactSpace M] {N : Type} [TopologicalSpace N] [SecondCountableTopology N] [MeasurableSpace N]
    [BorelSpace N] [CompactSpace N] (A' : HolAtlas N (n + 1)) {α : A'.Fld} (hα : A'.IsForm α) (j : A'.ι)
    (h0 : ∀ ε : ℤˣ, A'.part α ε (A'.e j).sourceᶜ = 0) {β : A.Fld} (hβ : A.IsForm β) (i : A.ι)
    (h1 : ∀ ε : ℤˣ, A.part β ε (A.e i).sourceᶜ = 0) (h : ∀ z, ∫ s : ℂ, rd A' α j (prodPt z s) = rd A β i z) :
    A'.integral α = A.integral β := by
  obtain ⟨hi, e⟩ := integral_eq_chart A' hα j h0
  have hF : rd A' α j = fun v => (fun z s => rd A' α j (prodPt z s)) (headL n v) (v (Fin.last n)) :=
    funext fun v => congrArg _ (prodPt_basePt v).symm
  rw [hF] at hi
  rw [e, (integral_eq_chart A hβ i h1).2, hF]
  exact (integral_headL_last (fun z s => rd A' α j (prodPt z s)) hi).2.trans (congrArg _ (funext h))

end Manifold

section Fibre

open GlobalTheory.FibLine MvPolynomial

theorem integral_affine (g : ℂ → ℂ) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    ∫ s : ℂ, (‖a‖ ^ 2 : ℝ) • g (a * s + b) = ∫ s, g s := by
  have hder : ∀ x ∈ (univ : Set ℂ), HasFDerivWithinAt (fun x : ℂ => a * x + b) (a • (1 : ℂ →L[ℝ] ℂ)) univ x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℂ => a * x + b) a x := by simpa using ((hasDerivAt_id x).const_mul a).add_const b
    exact h1.complexToReal_fderiv.hasFDerivWithinAt
  have hinj : InjOn (fun x : ℂ => a * x + b) univ := fun x _ y _ h => mul_left_cancel₀ ha (add_right_cancel h)
  have key := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ hder hinj g
  have him : (fun x : ℂ => a * x + b) '' univ = univ :=
    eq_univ_of_forall fun y => ⟨(y - b) / a, trivial, by simp only; field_simp; ring⟩
  rw [him, Measure.restrict_univ] at key
  rw [key]
  simp only [UnitaryInv.det_smul_one, Complex.normSq_eq_norm_sq, abs_pow, abs_norm]

def densL (n : ℕ) : Alt n →ₗ[ℂ] ℂ where
  toFun := dens
  map_add' _ _ := by simp [dens, add_div]
  map_smul' _ _ := by simp [dens, mul_div_assoc]

theorem integral_fsDens_qMat {n : ℕ} (H : Matrix (Fin 2) (Fin 2) (Ev n)) (m : ℕ) (Z : Alt n) :
    Integrable (fun s : ℂ => (fsDens s : ℂ) * dens (((qMat H s ^ m : Ev n) : Alt n) * Z)) ∧
    ∫ s : ℂ, (fsDens s : ℂ) * dens (((qMat H s ^ m : Ev n) : Alt n) * Z) =
      dens (((aeval (FibLine.entries H) (fibPow m) : Ev n) : Alt n) * Z) := by
  have e (s : ℂ) : (fsDens s : ℂ) * dens (((qMat H s ^ m : Ev n) : Alt n) * Z) =
      ∑ f : Fin m → Fin 2 × Fin 2, ((∏ i, qCoef s (f i)) * (fsDens s : ℂ)) *
        densL n (((∏ i, FibLine.entries H (f i) : Ev n) : Alt n) * Z) := by
    have e₁ : qMat H s ^ m = ∑ f : Fin m → Fin 2 × Fin 2, (∏ i, qCoef s (f i)) • ∏ i, FibLine.entries H (f i) := by
      rw [qMat, ← Fin.prod_const, Fintype.prod_sum]
      exact Finset.sum_congr rfl fun f _ => Finset.prod_smul _ _ _
    change _ * densL n _ = _
    rw [e₁, AddSubmonoidClass.coe_finsetSum, Finset.sum_mul, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Subalgebra.coe_smul, smul_mul_assoc, map_smul, smul_eq_mul]
    ring
  have hi (f : Fin m → Fin 2 × Fin 2) := (Intg.integrable_prod_qCoef_mul_fsDens m f).mul_const
    (densL n (((∏ i, FibLine.entries H (f i) : Ev n) : Alt n) * Z))
  simp only [e]
  refine ⟨integrable_finset_sum _ fun f _ => hi f, ?_⟩
  rw [integral_finset_sum _ fun f _ => hi f]
  change _ = densL n _
  rw [fibPow, map_sum, AddSubmonoidClass.coe_finsetSum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_mul_const, map_mul (aeval _), aeval_C, map_prod, ← Algebra.smul_def, Subalgebra.coe_smul, smul_mul_assoc, map_smul,
    smul_eq_mul]
  simp only [aeval_X]

theorem integral_fsDens_qMat_affine {n : ℕ} (H : Matrix (Fin 2) (Fin 2) (Ev n)) (m : ℕ) (Z : Alt n) {a : ℂ} (ha : a ≠ 0)
    (b : ℂ) : ∫ s : ℂ, (((fsDens (a * s + b) * ‖a‖ ^ 2 : ℝ) : ℂ) * dens (((qMat H (a * s + b) ^ m : Ev n) : Alt n) * Z)).re =
      (dens (((aeval (FibLine.entries H) (fibPow m) : Ev n) : Alt n) * Z)).re := by
  obtain ⟨hi, e⟩ := integral_fsDens_qMat H m Z
  have e₁ := integral_affine (fun s => (((fsDens s : ℂ) * dens (((qMat H s ^ m : Ev n) : Alt n) * Z)).re : ℂ)) ha b
  rw [← e, ← RCLike.re_to_complex, ← integral_re hi]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  refine Eq.trans (congrArg _ (funext fun s => ?_)) e₁
  simp only [Complex.re_ofReal_mul, Complex.real_smul]
  push_cast
  ring

theorem dens_mul_pow_pull {n : ℕ} {ω θ ζ : Alt (n + 1)} (hω : IsType 1 1 ω) {ρ : ℂ}
    (eω : pull (fibL n) ω = ρ • (vol 1 : Alt 1)) {β : Ev n} (eθ : θ = pull (headL n) β) {Z : Alt n}
    (eZ : ζ = pull (headL n) Z) (j : ℕ) : dens (ω * θ ^ j * ζ) = ρ * dens (((β ^ j : Ev n) : Alt n) * Z) := by
  rw [eθ, eZ, mul_assoc, ← map_pow, ← map_mul, TopDens.dens_mul_pull_headL _ _ hω, eω, SubmonoidClass.coe_pow]
  congr 1
  change densL 1 _ = _
  rw [map_smul]
  change _ * dens _ = _
  rw [dens_vol, mul_one]

theorem dens_pow_pull {n : ℕ} (L : V (n + 1) →L[ℂ] V n) {θ : Alt (n + 1)} {β : Alt n} (eθ : θ = pull L β) (Z : Alt n)
    (j : ℕ) : dens (θ ^ j * pull L Z) = dens (0 : Alt (n + 1)) := by
  rw [eθ, ← map_pow, ← map_mul]
  simp only [dens, PullTop.repr_pull_univ, map_zero, Finsupp.zero_apply]

theorem map_hs (m : ℕ) : (hs m).map (algebraMap ℝ ℂ) = hPoly m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [hs, hPoly_zero]
  | one => simp [hs, hPoly_one, Finset.sum_range_succ]
  | more k h0 h1 => rw [hs_add_two, hPoly_add_two, map_sub, map_mul, map_mul, map_X, map_X, h0, h1]

end Fibre

section Variety

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.FibTheta
open GlobalTheory.FibLine (fsDens qMat fibPow hPoly)

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d : ℕ}

theorem firstChern_flag_eq_sum_graded (h : IsRegVar q d) (σ : k →+* ℂ) {E : B.Modules} {m : VMetric q E 2} (H : m.IsCInf) (fl : Vert.Flag E 2) :
    c1EF h σ m fl = c1F h σ (VMetric.grLB fl 0 H) + c1F h σ (VMetric.grLB fl 1 H) := by
  have := h.isIntegral
  rw [← c1F_tens k B q d h σ, c1F_eq_of_isometric k B q d h σ _ _ (VMetric.isometric_grLB_tens_grLB_det k B q E m H fl)]
  funext x
  let b : Chart E 2 := pick ((VMetric.det H).φ σ).isLB x.pt
  have hb : x.pt ∈ ptsIn q σ b.U := mem_pick ((VMetric.det H).φ σ).isLB x.pt
  have e₁ : c1EF h σ m fl x = (h.atlas σ).chern ((m.met σ).G b) 1 x := by
    have hS := lineSC_shortExact fl
    have ha := mem_frameAt fl x.pt
    refine Eq.trans ?_ (SecondChernPull.chern_G_eq h (H σ) b ((frameAt fl x.pt).mid hS) x hb ha 1)
    refine SecondChernPull.chernAt_reindex (r := Fin 2) (finSumFinEquiv (m := 1) (n := 1)) ?_ 1
    filter_upwards [(ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds (ChartGlue.mem_over x.ch x.2 ha)] with v hv
    exact Met.gram_frame (S := lineSC fl) (r := 1) (s := 1) (m.met σ) hS _ hv.2
  rw [e₁, HolAtlas.chern, SecForm.chernAt_one_eq_ofValues]
  change _ = ofValues (ddc (fun v => -Real.log ((m.met σ).G b (x.ch.symm v)).det.re) x.crd)
  congr 1
  funext ξ η
  have hG : MContDiffAt 2 (fun v => (m.met σ).G b (x.ch.symm v)) x.crd :=
    ((H σ b _ hb).mContDiffAt x.1.1 x.2).of_le (by norm_cast)
  have hp : ∀ᶠ v in 𝓝 x.crd, ((m.met σ).G b (x.ch.symm v)).PosDef := by
    filter_upwards [(ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds (ChartGlue.mem_over x.ch x.2 hb)] with v hv
    exact (m.met σ).posDef b _ hv.2
  rw [chernOne_eq_neg_ddc_log_det hG (hp.mono fun v hv => hv.isHermitian)
    ((Matrix.isUnit_iff_isUnit_det _).1 hp.self_of_nhds.isUnit), ddc, ddc, leviForm_neg]
  simp

variable (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) {E : B.Modules} {m : VMetric q E 2}
  (H : m.IsCInf) (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2) (σ : k →+* ℂ)

theorem evalF_hs (A : HermLB q) (j : ℕ) (c : Chart E 2) {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsUnit P.det)
    (x : (hB.atlas σ).Pt) (hc : x.pt ∈ ptsIn q σ c.U) :
    ((1 / (j + 1 : ℝ) : ℝ) : ℂ) • evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3] (hs j)) x =
      (aeval (FibLine.entries (curvH hB σ m c P x)) (fibPow j) : Ev d) := by
  obtain ⟨e₁, e₂⟩ := trace_det_curvH hB σ H flB c hP x hc
  rw [FibLine.aeval_fibPow, e₁, e₂, firstChern_flag_eq_sum_graded hB σ H flB, Subalgebra.coe_smul, ← map_hs]
  congr 1
  · push_cast; rfl
  · change ((aeval _ _ : Ev d) : Alt d) = _
    congr 1
    generalize hs j = Q
    induction Q using MvPolynomial.induction_on with
    | C a => simp
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | mul_X P i hP =>
      simp only [map_mul, hP, aeval_X, map_X]
      congr 1
      fin_cases i <;> simp [fam4]

theorem dens_prodChart (cE : Chart E 2) (c₁ : AlgChart q σ d) (c' : AlgChart p σ (d + 1))
    (hU : c₁.e.source ⊆ ptsIn q σ cE.U)
    (hs : c'.e.source ⊆ PtsOver.map π w (spMap σ) ⁻¹' c₁.e.source ∩ finPart π w m.isVB cE fl σ)
    (ht : c'.e.target = basePt ⁻¹' c₁.e.target)
    (he : ∀ y ∈ c'.e.source, c'.e y = prodPt (c₁.e (PtsOver.map π w (spMap σ) y)) (FibTriv.slope π m.isVB cE fl y))
    {Z : (hB.atlas σ).Fld} (hZ : (hB.atlas σ).IsForm Z) (j : ℕ) (x' : (hB.atlas σ).Pt) (hx' : x'.1.1 = c₁) {a b : ℂ}
    (hab : ∀ s, ∃ t : ℂ, FibLine.lineVec s = t • (gsLow ((m.met σ).G cE x'.pt)).mulVec (FibLine.lineVec (a * s + b)))
    (s : ℂ) :
    dens ((hY.atlas σ).loc (fld _ (omF hY σ (m.pull π w) fl) * fld _ (thetaF hY σ (H.pull π w) fl) ^ j *
        pullF hB hY σ π w Z) c' (prodPt x'.crd s)) =
      ((fsDens (a * s + b) * ‖a‖ ^ 2 : ℝ) : ℂ) *
        dens (((qMat (curvH hB σ m cE (gsLow ((m.met σ).G cE x'.pt)) x') (a * s + b) ^ j : Ev d) : Alt d) * Z x') := by
  have := hB.isIntegral
  have := hY.isIntegral
  obtain ⟨⟨c, b₀⟩, hb⟩ := x'
  obtain rfl : c = c₁ := hx'
  change b₀ ∈ c.e.source at hb
  set f : CxPts p σ → CxPts q σ := PtsOver.map π w (spMap σ) with hf
  let Φ : ℂ → CxPts p σ := fun s => c'.e.symm (prodPt (c.e b₀) s)
  have h₁ (s : ℂ) : prodPt (c.e b₀) s ∈ c'.e.target := by
    rw [ht, mem_preimage, basePt_prodPt]; exact c.e.map_source hb
  have h₂ (s : ℂ) : Φ s ∈ c'.e.source := c'.e.map_target (h₁ s)
  have h₃ (s : ℂ) : c'.e (Φ s) = prodPt (c.e b₀) s := c'.e.right_inv (h₁ s)
  have h₄ (s : ℂ) : f (Φ s) = b₀ := by
    have := congrArg basePt ((he _ (h₂ s)).symm.trans (h₃ s))
    rw [basePt_prodPt, basePt_prodPt] at this
    exact c.e.injOn (hs (h₂ s)).1 hb this
  have h₅ (s : ℂ) : ∃ t : ℂ, lineCrd fl (cE.pull m.isVB π) (Φ s) =
      t • (gsLow ((m.met σ).G cE b₀)).mulVec (FibLine.lineVec (a * s + b)) := by
    have e := congrArg (fun v : V (d + 1) => v (Fin.last d)) ((he _ (h₂ s)).symm.trans (h₃ s))
    simp only [prodPt_last] at e
    obtain ⟨t, ht⟩ := hab s
    have h0 : FibTriv.lineVec π m.isVB cE fl (Φ s) 0 ≠ 0 := (hs (h₂ s)).2.2
    refine ⟨FibTriv.lineVec π m.isVB cE fl (Φ s) 0 * t, ?_⟩
    erw [mul_smul, ← ht]
    change FibTriv.lineVec π m.isVB cE fl (Φ s) = _
    funext i
    fin_cases i
    · simp [FibLine.lineVec]
    · have e' := mul_div_cancel₀ (FibTriv.lineVec π m.isVB cE fl (Φ s) 1) h0
      rw [show _ / _ = s from e] at e'
      simpa [FibLine.lineVec] using e'.symm
  have hG := (m.met σ).posDef cE b₀ (hU hb)
  let x : (hY.atlas σ).Pt := ⟨(c', Φ s), h₂ s⟩
  have hloc (α : (hY.atlas σ).Fld) : (hY.atlas σ).loc α c' (prodPt (c.e b₀) s) = α x := by
    rw [← (hY.atlas σ).loc_crd α x]; exact congrArg _ (h₃ s).symm
  have hD : fderiv ℂ (c.e ∘ f ∘ c'.e.symm) (c'.e (Φ s)) = headL d := by
    rw [← (headL d).fderiv (x := c'.e (Φ s))]
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source (h₂ s))] with v hv
    have := congrArg basePt ((he _ (c'.e.map_target hv)).symm.trans (c'.e.right_inv hv))
    rw [basePt_prodPt] at this
    exact this
  have eθ := thetaF_eq_pull_qMat hB hY π w H fl σ cE x ⟨(c, b₀), hb⟩ (h₄ s).symm (hU hb) (chg_gsLow hG) (h₅ s)
  have eZ : pullF hB hY σ π w Z x = pull (headL d) (Z ⟨(c, b₀), hb⟩) := by
    have hb' : f x.pt ∈ c.e.source := (h₄ s).symm ▸ hb
    refine (pullback_eq_chart _ _ _ _ _ _ f Z (isHolo_ptsOver_map k B q d hB σ Y p _ hY π w) hZ x c hb').trans ?_
    congr 1
    · exact congrArg pull hD
    · exact congrArg Z (Subtype.ext (Prod.ext rfl (h₄ s)))
  have hprod (t : ℂ) : prodPt (c.e b₀) t = prodPt (c.e b₀) 0 + fibL d (EuclideanSpace.single 0 t) := by
    ext i
    induction i using Fin.lastCases <;> simp [fibL_apply, EuclideanSpace.single_apply, Fin.castSucc_ne_last]
  have hdiff : Differentiable ℂ (prodPt (c.e b₀)) :=
    differentiable_prodPt.comp ((differentiable_const _).prodMk differentiable_id)
  have eω := pull_omF_affine hY π w H fl σ cE (hU hb) (chg_gsLow hG) x (Φ := Φ) a b (z := EuclideanSpace.single 0 s)
    (by simp [x]) ((c'.e.continuousAt_symm (h₁ _)).comp hdiff.continuous.continuousAt)
    ((hdiff.analyticAt _).congr (.of_forall fun t => (h₃ t).symm)) (.of_forall h₄) (.of_forall h₅)
  have hF : fderiv ℂ (fun v : V 1 => x.ch (Φ (v 0))) (EuclideanSpace.single 0 s) = fibL d := by
    have : (fun v : V 1 => x.ch (Φ (v 0))) = fun v => prodPt (c.e b₀) 0 + fibL d v := by
      funext v
      refine (h₃ _).trans ((hprod _).trans ?_)
      congr 2
      ext i
      simp [Subsingleton.elim i 0]
    rw [this, fderiv_const_add, ContinuousLinearMap.fderiv]
  have eω' := (congrArg (fun L => pull L (omF hY σ (m.pull π w) fl x : Alt (d + 1))) hF).symm.trans eω
  have eθ' := eθ.trans (congrArg (fun L => pull L _) hD)
  refine (congrArg dens (hloc _)).trans ((dens_mul_pow_pull
    ((isRealForm_omF k Y p _ hY σ _ _ (H.pull π w) fl).2 x).1 eω' eθ' eZ j).trans ?_)
  simp only [PiLp.single_eq_same]

theorem isForm_thetaF {D : ℕ} (h : IsRegVar p D) {E : Y.Modules} {m : VMetric p E 2} (H : m.IsCInf) (fl : Vert.Flag E 2) :
    (h.atlas σ).IsForm (fld _ (thetaF h σ H fl)) := by
  have := h.isIntegral
  have := CxPts.secondCountableTopology_of_isProjOver σ h.isProjOver
  exact isForm_add _ (FirstChern.c1F_isRealForm_closed k Y p D h σ (VMetric.grLB fl 0 H)).1.1
    (isRealForm_omF k Y p D h σ E m H fl).1

theorem isForm_up {Z : (hB.atlas σ).Fld} (hZ : (hB.atlas σ).IsForm Z) (j : ℕ) :
    (hY.atlas σ).IsForm (fld _ (omF hY σ (m.pull π w) fl) * fld _ (thetaF hY σ (H.pull π w) fl) ^ j *
      pullF hB hY σ π w Z) := by
  have := hB.isIntegral
  have := hY.isIntegral
  have hp : (hY.atlas σ).IsForm (fld _ (thetaF hY σ (H.pull π w) fl) ^ j) := by
    induction j with
    | zero => rw [pow_zero]; exact (formCalculus _ _ _).1
    | succ j ih => rw [pow_succ]; exact FormMul.isForm_mul _ _ _ ih (isForm_thetaF σ hY _ fl)
  exact FormMul.isForm_mul _ _ _ (FormMul.isForm_mul _ _ _ (isRealForm_omF k Y p _ hY σ _ _ (H.pull π w) fl).1 hp)
    (PullbackForm.isForm_pullback _ _ _ _ _ _ _ Z (isHolo_ptsOver_map k B q d hB σ Y p _ hY π w) hZ)

theorem isForm_down (A : HermLB q) (Q : MvPolynomial (Fin 4) ℝ) {Z : (hB.atlas σ).Fld} (hZ : (hB.atlas σ).IsForm Z) :
    (hB.atlas σ).IsForm (evalF (hB.atlas σ) (fam4 hB σ H flB A) Q * Z) := by
  have := hB.isIntegral
  refine FormMul.isForm_mul _ _ _ ((formCalculus _ _ _).2.2.2.1 _ _ Q fun i => ?_).1 hZ
  fin_cases i
  exacts [(FirstChern.c1F_isRealForm_closed k B q d hB σ _).1.1, (FirstChern.c1F_isRealForm_closed k B q d hB σ _).1.1,
    (FirstChern.c1F_isRealForm_closed k B q d hB σ _).1.1, (ChernReal.c2F_isRealForm_closed k B q d hB σ E m H flB).1.1]

theorem integral_local (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) fun _ => fl) (A : HermLB q) (j : ℕ)
    (b : CxPts q σ) : ∃ U : Set (CxPts q σ), IsOpen U ∧ b ∈ U ∧ ∀ Z : (hB.atlas σ).Fld, (hB.atlas σ).IsForm Z →
      ∀ K : Set (CxPts q σ), IsClosed K → K ⊆ U → (∀ x : (hB.atlas σ).Pt, x.pt ∉ K → Z x = 0) →
      (hY.atlas σ).integral (fld _ (omF hY σ (m.pull π w) fl) * fld _ (thetaF hY σ (H.pull π w) fl) ^ j *
        pullF hB hY σ π w Z) = 1 / (j + 1 : ℝ) *
        (hB.atlas σ).integral (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3] (hs j)) * Z) := by
  have := hB.toIsArithVar.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hB.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ hB.isProjOver
  have := hY.toIsArithVar.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  let cE : Chart E 2 := m.isVB.pick b
  obtain ⟨c, hc⟩ := (hB.atlas σ).cover b
  obtain ⟨c₁, c', -, hb, hle, e₁, hsrc, ht, he, -, -⟩ := exists_trivChart π w m.isVB fl hfl c hc (m.isVB.mem_pick b)
  have hU : c₁.e.source ⊆ ptsIn q σ cE.U := fun y hy => by
    rw [e₁, OpenPartialHomeomorph.restrOpen_source] at hy
    exact mem_ptsIn.2 (hle (mem_ptsIn.1 hy.2))
  refine ⟨c₁.e.source, c₁.e.open_source, hb, fun Z hZ K hK hKU hZK => ?_⟩
  have hβ := isForm_down hB H flB σ A (aeval ![X 1 + X 2, X 3] (hs j)) hZ
  have hβ' := ((formCalculus _ _ _).2.1 ((1 / (j + 1 : ℝ) : ℝ) : ℂ) _ _ hβ hβ).2.2.1
  have hα := isForm_up hB hY π w H fl σ hZ j
  have hcont : Continuous (PtsOver.map π w (spMap σ)) := CxPts.continuous_of_comp (f := π) (fun z => rfl)
  rw [← wInt_one (hB.atlas σ), ← (wInt_props _ _ _).2.2.1 _ _ _ hβ, wInt_one]
  refine integral_eq_of_fibre (hB.atlas σ) (hY.atlas σ) hα c' (fun ε => ?_) hβ' c₁ (fun ε => ?_) fun z => ?_
  · refine part_compl_eq_zero _ hα ε (hK.preimage hcont) (fun x hx => ?_) fun y hy hyK => ?_
    · change _ * pull _ (Z _) = 0
      erw [hZK ⟨(_, _), ((hB.atlas σ).cover (PtsOver.map π w (spMap σ) x.pt)).choose_spec⟩ hx, map_zero, mul_zero]
    · have key (y' : CxPts p σ) (h₁ : y' ∉ c'.e.source) (h₂ : PtsOver.map π w (spMap σ) y' ∈ c₁.e.source) :
          y' ∈ infPart π w m.isVB cE fl σ := by
        rw [infPart_eq]
        exact ⟨hU h₂, fun h => h₁ (hsrc ▸ ⟨h₂, h⟩)⟩
      obtain ⟨c'', h₁, h₂⟩ := exists_chart_infPart π w m.isVB fl hfl c₁ (hKU hyK) (key y hy (hKU hyK))
      have ho : IsOpen (c''.e.source ∩ PtsOver.map π w (spMap σ) ⁻¹' c₁.e.source) :=
        c''.e.open_source.inter (c₁.e.open_source.preimage hcont)
      refine ⟨c'', c'.e.sourceᶜ ∩ (c''.e.source ∩ PtsOver.map π w (spMap σ) ⁻¹' c₁.e.source),
        c'.e.open_source.measurableSet.compl.inter ho.measurableSet,
        inter_mem_nhdsWithin _ (ho.mem_nhds ⟨h₁, hKU hyK⟩), fun z hz => hz.2.1,
        measure_mono_null ?_ (volume_last_eq_zero d)⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (h₂ z hz.2.1).1 (key z hz.1 hz.2.2)
  · refine part_compl_eq_zero _ hβ' ε hK (fun x hx => ?_) fun y hy hyK => absurd (hKU hyK) hy
    rw [Pi.smul_apply, Pi.mul_apply, hZK _ hx, mul_zero, smul_zero]
  · by_cases hz : z ∈ c₁.e.target
    · let x' : (hB.atlas σ).Pt := ⟨(c₁, c₁.e.symm z), c₁.e.map_target hz⟩
      have hx : x'.crd = z := c₁.e.right_inv hz
      have hG := (m.met σ).posDef cE _ (hU x'.2)
      have ha : (m.met σ).G cE x'.pt 1 1 / (√((m.met σ).G cE x'.pt).det.re : ℝ) ≠ 0 :=
        div_ne_zero (hG.diag_pos (i := 1)).ne' (sqrt_re_sq hG.det_pos).1
      rw [← hx]
      simp only [rd]
      refine (congrArg _ (funext fun s => congrArg Complex.re (dens_prodChart hB hY π w H fl σ cE c₁ c' hU hsrc.subset ht he
        hZ j x' rfl (lineVec_eq_gsLow hG) s))).trans ((integral_fsDens_qMat_affine _ _ _ ha _).trans ?_)
      rw [← evalF_hs hB H flB σ A j cE (isUnit_det_of_chg_eq_one (chg_gsLow hG)) x' (hU x'.2), smul_mul_assoc]
      erw [(hB.atlas σ).loc_crd _ x']
      rw [Pi.smul_apply, Pi.mul_apply]
    · have h₁ (s : ℂ) : prodPt z s ∉ ((hY.atlas σ).e c').target := fun h => by
        change _ ∈ c'.e.target at h
        rw [ht, mem_preimage, basePt_prodPt] at h
        exact hz h
      have h₂ : z ∉ ((hB.atlas σ).e c₁).target := hz
      simp [rd, HolAtlas.loc, h₁, h₂, dens]

end Variety

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine

theorem integral_fibre : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ m : ℕ,
      (hY.atlas σ).integral ((fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0)) + fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)) ^ m * pullF hB hY σ π w φ) = 0 ∧
      (hY.atlas σ).integral (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) * (fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0)) + fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)) ^ m * pullF hB hY σ π w φ) =
        1 / (m + 1 : ℝ) * (hB.atlas σ).integral (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3] (hs m)) * φ) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ φ hφ m
  have := hY.toIsArithVar.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  have eθ : fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0)) + fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) =
      fld (hY.atlas σ) (thetaF hY σ (H.pull π w) fl) := rfl
  rw [eθ]
  constructor
  · rw [← wInt_one, (wInt_props _ _ _).2.2.2 _ _ 0 fun x => ?_]
    · simp [wInt, part_zero]
    obtain ⟨β, hβ⟩ := FibTheta.thetaF_horizontal hB hY π w H fl σ x
    exact dens_pow_pull _ hβ _ m
  · choose U hU hb hloc using integral_local hB hY π w H flB fl σ hfl A m
    obtain ⟨N, a, c, χ, hχ, -, h1, hK⟩ := exists_partition_regVar hB σ U hU fun y => ⟨y, hb y⟩
    have hZ (i : Fin N) := isForm_fn_mul _ (hχ i) hφ
    have e := sum_fn_mul (hB.atlas σ) Finset.univ h1 φ
    have e' : pullF hB hY σ π w φ = ∑ i, pullF hB hY σ π w ((hB.atlas σ).fn (χ i) * φ) := by
      conv_lhs => rw [← e]
      funext x
      rw [Finset.sum_apply, pullF, HolAtlas.pullback]
      erw [Finset.sum_apply, map_sum]
      rfl
    rw [e', Finset.mul_sum, integral_sum_regVar hY σ _ fun i _ => isForm_up hB hY π w H fl σ (hZ i) m]
    conv_rhs => rw [← e]
    rw [Finset.mul_sum, integral_sum_regVar hB σ _ fun i _ => isForm_down hB H flB σ A _ (hZ i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => hloc (a i) _ (hZ i) (tsupport (χ i)) (isClosed_tsupport _) (hK i).2.1
      fun x hx => ?_
    change algebraMap ℂ _ (χ i x.pt : ℂ) * φ x = 0
    rw [image_eq_zero_of_notMem_tsupport hx]
    simp

end GlobalTheory.FibGlob
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_chern_integral_pull_third : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ m : ℕ,
      (hY.atlas σ).integral ((fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0)) + fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)) ^ m * pullF hB hY σ π w φ) = 0 ∧
      (hY.atlas σ).integral (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) * (fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0)) + fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)) ^ m * pullF hB hY σ π w φ) =
        1 / (m + 1 : ℝ) * (hB.atlas σ).integral (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3] (hs m)) * φ) := by
  atlas_forward_decl GlobalTheory.FibGlob.integral_fibre
end
