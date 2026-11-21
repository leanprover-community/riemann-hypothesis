import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.MeasureFailsForLargeConstant
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention

section
section
open NumberField

noncomputable section

namespace GlobalTheory.CovolCore

section Transport

variable {R V W E F : Type} [Ring R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem rk_deg_transport (ρ : V →+ E) (σ : W →+ F) (T : V →+ W) {A : Submodule R V} {B : Submodule R W}
    (hA : Formalism.HN.IsLat ρ A) (hB : Formalism.HN.IsLat σ B)
    (hAB : ∀ y, y ∈ B ↔ ∃ x ∈ A, T x = y) (hn : ∀ x ∈ A, ‖σ (T x)‖ = ‖ρ x‖) :
    Formalism.HN.rk σ B = Formalism.HN.rk ρ A ∧ Formalism.HN.deg σ B = Formalism.HN.deg ρ A := by
  let f : A.toAddSubgroup →+ E := ρ.comp A.toAddSubgroup.subtype
  let g : A.toAddSubgroup →+ F := (σ.comp T).comp A.toAddSubgroup.subtype
  have h1 : ∀ y, y ∈ Formalism.HN.zl ρ A ↔ ∃ m, f m = y :=
    fun y => ⟨fun ⟨m, hm, e⟩ => ⟨⟨m, hm⟩, e⟩, fun ⟨m, e⟩ => ⟨m.1, m.2, e⟩⟩
  have h2 : ∀ y, y ∈ Formalism.HN.zl σ B ↔ ∃ m, g m = y := fun y =>
    ⟨fun ⟨m, hm, e⟩ => by
      obtain ⟨x, hx, rfl⟩ := (hAB m).1 hm
      exact ⟨⟨x, hx⟩, e⟩, fun ⟨m, e⟩ => ⟨T m.1, (hAB _).2 ⟨m.1, m.2, rfl⟩, e⟩⟩
  have hn' : ∀ m, ‖f m‖ = ‖g m‖ := fun m => (hn m.1 m.2).symm
  haveI := hA.2
  haveI := hB.2
  refine ⟨?_, ?_⟩
  · have hf : Function.Injective f := fun x y h => Subtype.ext (hA.1 x.2 y.2 h)
    have hg : Function.Injective g := fun x y h =>
      hf (Formalism.HN.QuotientRealization.eq_of_norm_eq g f (fun m => (hn' m).symm) h)
    have e1 : Formalism.HN.zl ρ A = LinearMap.range f.toIntLinearMap := Submodule.ext h1
    have e2 : Formalism.HN.zl σ B = LinearMap.range g.toIntLinearMap := Submodule.ext h2
    unfold Formalism.HN.rk Formalism.F.rk
    rw [e1, e2, ← (LinearEquiv.ofInjective f.toIntLinearMap hf).finrank_eq,
      ← (LinearEquiv.ofInjective g.toIntLinearMap hg).finrank_eq]
  · unfold Formalism.HN.deg Formalism.F.deg
    rw [Formalism.HN.QuotientRealization.covol_eq_of_norm_eq f g _ _ h1 h2 hn']

end Transport

theorem cnorm_smul {ι : Type} [Fintype ι] (s : ℝ) (hs : 0 ≤ s) (u : ι → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm ((s : ℂ) • u) = s * Formalism.HermitianLatticesTheory.cnorm u := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs, mul_pow,
    ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]

end GlobalTheory.CovolCore

namespace GlobalTheory.CovolCore

theorem lcv_div_le_neg_slope_sq : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ), GlobalTheory.AllWt.HasGram N →
    ∀ (L : Submodule (𝓞 K) V) (d : ℕ), 0 < d → ∀ (b : Fin d → V), LinearIndependent K b →
    (∀ x ∈ L, x ∈ Submodule.span K (Set.range b)) →
    ∀ (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (s : ℝ), 0 < s → s ≤ 1 → (∀ v, IsUnit (X v).det) →
    (∀ v (c : Fin d → K), Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X v c = s * N v.embedding (∑ k, c k • b k)) →
    Submodule.IsLattice K (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) →
    Formalism.DivisionValues.lcv X (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) / (d : ℝ) ≤
      -GlobalTheory.AllWt.slope_sq N L := by
  intro K V _ _ _ _ _ _ _ _ N hN L d hd b hb hLb X s hs0 hs1 hX hnorm hM
  set φ := Fintype.linearCombination K b with hφ
  set M := L.comap (φ.restrictScalars (𝓞 K)) with hMdef
  have hφa : ∀ c : Fin d → K, φ c = ∑ k, c k • b k := fun c => Fintype.linearCombination_apply K b c
  let X' : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ := fun v => (s : ℂ) • X v
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hX' : ∀ v, IsUnit (X' v).det := fun v => by
    show IsUnit ((s : ℂ) • X v).det
    rw [Matrix.det_smul]
    exact ((Ne.isUnit hs').pow _).mul (hX v)
  have hfc : ∀ v c, Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X v c =
      (s : ℂ) • Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X' v c := by
    intro v c
    have e : X' v = (Units.mk0 (s : ℂ) hs') • X v := rfl
    simp only [Formalism.HermitianLatticesTheory.fcoord]
    rw [e, Matrix.inv_smul' (X v) (Units.mk0 (s : ℂ) hs') (hX v), Units.smul_def, Matrix.smul_mulVec, smul_smul,
      Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel₀ hs', one_smul]
  have hOC : GlobalTheory.MeasureLeaf.OneConstant X X' (fun _ => s ^ 2) := fun v =>
    ⟨by positivity, fun x y => by
      simp only [Formalism.HermitianLatticesTheory.majAt, hfc, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [star_mul', Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring⟩
  have hn' : ∀ v c, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X' v c = N v.embedding (φ c) := by
    intro v c
    have h := hnorm v c
    simp only [Formalism.HermitianLatticesTheory.normAt, hfc, cnorm_smul s hs0.le] at h
    rw [hφa]
    exact mul_left_cancel₀ hs0.ne' h
  have h1 := GlobalTheory.MeasureLeaf.lcv_of_oneConstant hd X X' hX hX' (fun _ => s ^ 2) hOC M hM
  have h2 := Formalism.ExtensionFiltration.lcvMu K d hd X' hX' M hM
  have hlog : 2 / (Module.finrank ℚ K : ℝ) * ∑ v : InfinitePlace K, Real.log (s ^ 2) ≤ 0 := by
    refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun v _ => ?_)
    exact Real.log_nonpos (sq_nonneg _) (by nlinarith)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hMfg : M.FG := hM.fg
  have hML : ∀ y, y ∈ L ↔ ∃ x ∈ M, φ x = y := fun y =>
    ⟨fun hy => by
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hLb y hy)
      refine ⟨c, ?_, by rw [hφa, hc]⟩
      show φ c ∈ L
      rw [hφa, hc]; exact hy,
     fun ⟨x, hx, e⟩ => e ▸ hx⟩
  have hLM : L = M.map (φ.restrictScalars (𝓞 K)) := by
    ext y
    rw [hML y, Submodule.mem_map]
    rfl
  have hLfg : L.FG := by rw [hLM]; exact hMfg.map _
  obtain ⟨⟨n, ⟨b0, X0⟩, hG⟩⟩ := id hN
  change GlobalTheory.AllWt.IsGram b0 X0 N at hG
  rw [GlobalTheory.AllWt.slope_sq_eq hG hLfg]
  have hlatM := (Formalism.HN.plLat K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X' hX' M hMfg).1
  have hlatL := (Formalism.HN.plLat K V (Fin n) b0 X0 (fun v => (hG v).1) L hLfg).1
  have hnr : ∀ x ∈ M, ‖Formalism.HermitianLatticesTheory.realize b0 X0 (φ.toAddMonoidHom x)‖ =
      ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin d)) X' x‖ := fun x _ => by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), GlobalTheory.AllWt.norm_realize_sq, GlobalTheory.AllWt.norm_realize_sq]
    exact Finset.sum_congr rfl fun v _ => by rw [(hG v).2, hn' v x]; rfl
  obtain ⟨e1, e2⟩ := rk_deg_transport (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin d)) X')
    (Formalism.HermitianLatticesTheory.realize b0 X0) φ.toAddMonoidHom hlatM hlatL hML hnr
  have key : Formalism.HN.muDef (Pi.basisFun K (Fin d)) X' M = Formalism.HN.muDef b0 X0 L := by
    unfold Formalism.HN.rk at e1
    unfold Formalism.HN.deg at e2
    unfold Formalism.HN.muDef Formalism.HN.slope Formalism.F.slope
    rw [e1, e2]
  have h3 : Formalism.DivisionValues.lcv X' M / (d : ℝ) = -Formalism.HN.muDef (Pi.basisFun K (Fin d)) X' M := by
    rw [h2]; field_simp
  rw [h1, h3, key]
  linarith

end GlobalTheory.CovolCore
end
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolumePerRank_le_neg_slope_scaled : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ), GlobalTheory.AllWt.HasGram N →
    ∀ (L : Submodule (𝓞 K) V) (d : ℕ), 0 < d → ∀ (b : Fin d → V), LinearIndependent K b →
    (∀ x ∈ L, x ∈ Submodule.span K (Set.range b)) →
    ∀ (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (s : ℝ), 0 < s → s ≤ 1 → (∀ v, IsUnit (X v).det) →
    (∀ v (c : Fin d → K), Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X v c = s * N v.embedding (∑ k, c k • b k)) →
    Submodule.IsLattice K (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) →
    Formalism.DivisionValues.lcv X (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) / (d : ℝ) ≤ -GlobalTheory.AllWt.slope_sq N L := by
  atlas_forward_decl GlobalTheory.CovolCore.lcv_div_le_neg_slope_sq
end

section
section
open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.FrameRead

theorem normAt_eq_sqrt {K : Type} [Field K] [NumberField K] {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (v : InfinitePlace K) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v x = Real.sqrt (Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.cnorm
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show star (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) X v x i) = (starRingEnd ℂ) (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) X v x i) from rfl,
    Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem frames_read : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool)
    (i : Fin D.R.m), (R.toCx3 F).KForm b →
    (∀ v, IsUnit ((R.toCx3 F).XW b i v).det) ∧
      ∀ v (c : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b i)) → D.what₂.LL),
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL _) ((R.toCx3 F).XW b i) v c =
          (Real.sqrt (RealDat.nP F.lv2 b))⁻¹ * nrmR R.toRealDat i v.embedding (∑ k, c k • R.toRealDat.bL F.lv2 b i k) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F b i hK
  refine ⟨fun v => frame_gram_unit _ (hK i v).1, fun v c => ?_⟩
  have h1 := normAt_eq_sqrt (n := (R.toCx3 F).dW b i) ((R.toCx3 F).XW b i) v c
  have h2 := majAt_gram ((R.toCx3 F).XW b i) v ((R.toCx3 F).bW b i v) (hK i v).1 rfl c c
  refine h1.trans ?_
  have h3 : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (z : E), Real.sqrt (inner ℂ z z).re = ‖z‖ := by
    intro E _ _ z
    rw [show (inner ℂ z z).re = ‖z‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) z, Real.sqrt_sq (norm_nonneg _)]
  rw [h2, h3]
  set s := twAt D.what₂.embLL v
  set σ := sgAt D.what₂.embLL v
  have hl : lin ((R.toCx3 F).bW b i v) (cpt v.embedding c) =
      Tw.mk s (∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ)) := by
    rw [lin_apply]
    have e : ∀ x : ↥(R.toRealDat.WS F.lv2 b i σ), Tw.mk s x = Tw.mkL s ↥(R.toRealDat.WS F.lv2 b i σ) x := fun _ => rfl
    rw [e, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ]
    show v.embedding (c k) • _ = _
    rw [emb_eq D.what₂.embLL v (c k)]
    rfl
  rw [hl]
  have hc : (((∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ)) : R.toRealDat.WS F.lv2 b i σ) : (R.HW i σ).H) =
      (((Real.sqrt (RealDat.nP F.lv2 b))⁻¹ : ℝ) : ℂ) • (R.FW i).j σ (∑ k, c k • R.toRealDat.bL F.lv2 b i k) := by
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, RealDat.bC]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, smul_comm]
  calc ‖Tw.mk s (∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ))‖
      = ‖(((∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ)) : R.toRealDat.WS F.lv2 b i σ) : (R.HW i σ).H)‖ := rfl
    _ = _ := by
      rw [hc, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
      unfold nrmR
      rw [InfinitePlace.mk_embedding]

end GlobalTheory.FrameRead
end
end

open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftForms_frames_majorantNorm_eq_petersson : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool)
    (i : Fin D.R.m), (R.toCx3 F).KForm b →
    (∀ v, IsUnit ((R.toCx3 F).XW b i v).det) ∧
      ∀ v (c : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b i)) → D.what₂.LL),
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL _) ((R.toCx3 F).XW b i) v c =
          (Real.sqrt (RealDat.nP F.lv2 b))⁻¹ * nrmR R.toRealDat i v.embedding (∑ k, c k • R.toRealDat.bL F.lv2 b i k) := by
  atlas_forward_decl GlobalTheory.FrameRead.frames_read
end

section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.CovTop GlobalTheory.BigTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem recAt_of_gramAt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.Rows) (hg : GramAt p i) : RecAt p i := by
  have hR := complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  have hD : (p.S false).dW i = (p.S false).D :=
    (primRows3 hp.ok hp.sep p.R p.F p.charW hp.prim).dW_eq (hR.wf false) i
  have hpos : 0 < (p.S false).D := (primRows3 hp.ok hp.sep p.R p.F p.charW hp.prim).D_pos
  obtain ⟨hU, hN⟩ := GlobalTheory.T.liftForms_frames_majorantNorm_eq_petersson p.R p.F false i (RealDat3.kForm_of hp.prim.unif false)
  have hn1 : (1 : ℝ) ≤ RealDat.nP p.F.lv2 false := by
    unfold RealDat.nP
    exact_mod_cast Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have hs0 : 0 < (Real.sqrt (RealDat.nP p.F.lv2 false))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by linarith))
  have hs1 : (Real.sqrt (RealDat.nP p.F.lv2 false))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hn1)
  have hli : LinearIndependent D.what₂.LL (p.R.toRealDat.bL p.F.lv2 false i) :=
    (Module.finBasis D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)).linearIndependent.map'
      (p.R.toRealDat.WL p.F.lv2 false i).subtype (Submodule.ker_subtype _)
  have hsp : ∀ x ∈ latGood p.R.toRealDat p.F.lv2 i,
      x ∈ Submodule.span D.what₂.LL (Set.range (p.R.toRealDat.bL p.F.lv2 false i)) := by
    intro x hx
    have hxW : x ∈ p.R.toRealDat.WL p.F.lv2 false i := ⟨hx.1.2, hx.2⟩
    have e : Submodule.span D.what₂.LL (Set.range (p.R.toRealDat.bL p.F.lv2 false i)) = p.R.toRealDat.WL p.F.lv2 false i := by
      have := (Module.finBasis D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)).span_eq
      have h2 := congrArg (Submodule.map (p.R.toRealDat.WL p.F.lv2 false i).subtype) this
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top] at h2
      exact h2
    rw [e]; exact hxW
  have key := GlobalTheory.T.covolumePerRank_le_neg_slope_scaled D.what₂.LL _ (nrmR p.R.toRealDat i) hg.1 (latGood p.R.toRealDat p.F.lv2 i) _ (show 0 < (p.S false).dW i from hD.symm ▸ hpos)
    (p.R.toRealDat.bL p.F.lv2 false i) hli hsp ((p.S false).XW i) _ hs0 hs1 hU hN (hp.prim.mLat i)
  unfold RecAt
  rw [← hD]
  exact key

theorem rec_of_gram : Gram → Rec := fun h =>
  Closed.imp h fun _ _ _ ⟨C, hC, x0, h⟩ =>
    ⟨C, hC, x0, fun x hx hle ι p hp i => recAt_of_gramAt p i hp.1 (h x hx hle ι p hp i)⟩

end GlobalTheory.CovTop

end
end
