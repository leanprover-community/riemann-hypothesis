import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LevelVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CentralOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrFwd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrBwd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrCochain
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ExistsCurve
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbD
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHkSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ParamDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbNat
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrUniq

section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem one_kills {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))
    (hm : m ∈ Submodule.span ℂ {x | ∃ φ v, IsLevelFn U Ξ φ ∧ x = φ ⊗ₜ[ℂ] v}) : smLie Ξ (oneL E a) m = 0 := by
  obtain ⟨r, hr⟩ := oneReal E a Ξ
  have hr' : Ξ.dmat (oneL E a) = (r : ℂ) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := hr
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, v, hφ, rfl⟩ := hx
    change (lie E a (oneL E a)).rTensor _ (φ ⊗ₜ[ℂ] v) + (Matrix.toLin' (Ξ.dmat (oneL E a))).lTensor _ (φ ⊗ₜ[ℂ] v) = 0
    rw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hφ.2.2 _ hr', hr', map_smul, Matrix.toLin'_one,
      LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.smul_tmul, ← TensorProduct.tmul_add, neg_smul, neg_add_cancel,
      TensorProduct.tmul_zero]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

private theorem d_basic {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ} (α : Co Ξ q) (hα : IsLev U Ξ α)
    (X : Fin (q + 1) → Herm E a) (i : Fin (q + 1)) (hX : (X i).1 = 1) : dCo (smLie Ξ) α X = 0 := by
  rw [dCo_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : i = j
  · subst hj
    have h := one_kills U Ξ _ (hα.val (i.removeNth X))
    have e : oneL E a = toL (X i).1 := by rw [hX]
    rw [e] at h
    rw [h, smul_zero]
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
    have hz : α (j.removeNth X) = 0 := hα.basic _ k (by rw [← hX, ← hk]; rfl)
    rw [hz, map_zero, smul_zero]

theorem UpperTheory.V.Lit.Geo.levGood :
    LevGood := by
  intro E _ _ _ a ho U Ξ q
  refine ⟨fun α hα => ?_, fun w hw => ?_⟩
  · have hv : ∀ X, LeftInv (α X) ∧ RightInv U (α X) := fun X => (levelVal E a U Ξ _).1 (hα.val X)
    obtain ⟨w, hw, h0⟩ := corrFwd E a U Ξ q α hα.equiv fun X => (hv X).2
    let w' : (geo ho U Ξ).Om q := ⟨w, fun s => ⟨corrSmooth E a U Ξ q _ w hw s, h0 s⟩⟩
    have hw' : Corr U Ξ α w'.1 := hw
    exact ⟨w', hw', (corrInv E a ho U Ξ q _ _ hw').1 fun X => (hv X).1, (corrBasic E a U Ξ q _ _ hw').1 hα.basic,
      (corrBasic E a U Ξ (q + 1) _ _ (corrD E a ho U Ξ q _ _ hw')).1 (d_basic U Ξ α hα)⟩
  · obtain ⟨α, hα⟩ := corrBwd E a ho U Ξ q w
    have b := (corrBasic E a U Ξ q _ _ hα).2 hw.basic
    have b' := (corrBasic E a U Ξ (q + 1) _ _ (corrD E a ho U Ξ q _ _ hα)).2 hw.dbasic
    obtain ⟨c1, c2⟩ := corrCochain E a U Ξ q _ _ hα
    exact ⟨α, hα, c1, b, fun X => (levelVal E a U Ξ _).2 ((corrInv E a ho U Ξ q _ _ hα).2 hw.inv X) (c2 X)
      (centralOf E a _ (smLie Ξ) q α b b' X)⟩
end

section
noncomputable section

open ContinuousAlternatingMap

namespace UpperTheory.V.Lit.Geo

private theorem line_der {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q : ℕ} (p : V) (t : ℝ) (Ω : V × ℝ → (V × ℝ) [⋀^Fin q]→L[ℝ] F) (h : DifferentiableAt ℝ Ω (p, t)) :
    HasDerivAt (fun r => (Ω (p, r)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ))
      ((fderiv ℝ Ω (p, t) (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ)) t := by
  have h1 : HasDerivAt (fun r : ℝ => (p, r)) ((0 : V), (1 : ℝ)) t := (hasDerivAt_const t p).prodMk (hasDerivAt_id t)
  have h2 : HasDerivAt (fun r : ℝ => Ω (p, r)) (fderiv ℝ Ω (p, t) (0, 1)) t :=
    HasFDerivAt.comp_hasDerivAt t (l := Ω) h.hasFDerivAt h1
  exact (compContinuousLinearMapCLM (ι := Fin q) (F := F) (ContinuousLinearMap.inl ℝ V ℝ)).hasFDerivAt.comp_hasDerivAt t h2

private theorem hasFDerivAt_slice_of_differentiableAt {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {m : ℕ} (p : V) (t : ℝ) (Ω : V × ℝ → (V × ℝ) [⋀^Fin m]→L[ℝ] F)
    (h : DifferentiableAt ℝ Ω (p, t)) :
    HasFDerivAt (fun x : V => Ω (x, t))
      ((fderiv ℝ Ω (p, t)).comp ((ContinuousLinearMap.id ℝ V).prod 0)) p := by
  have hs : HasFDerivAt (fun x : V => ((x, t) : V × ℝ)) ((ContinuousLinearMap.id ℝ V).prod 0) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const t p)
  exact h.hasFDerivAt.comp p hs

private theorem fderiv_slice_apply_eq_fderiv_prod_inl {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {m : ℕ} (p : V) (t : ℝ) (Ω : V × ℝ → (V × ℝ) [⋀^Fin m]→L[ℝ] F)
    (h : DifferentiableAt ℝ Ω (p, t)) (c : Fin m → V × ℝ) (u : V) :
    fderiv ℝ (fun x : V => Ω (x, t) c) p u = fderiv ℝ Ω (p, t) (u, 0) c := by
  rw [((hasFDerivAt_slice_of_differentiableAt p t Ω h).continuousAlternatingMap_apply_const c).fderiv]
  simp

private theorem removeNth_succ_vecCons' {α : Type*} {n : ℕ} (a : α) (w : Fin (n + 1) → α) (i : Fin (n + 1)) :
    Fin.removeNth i.succ (Matrix.vecCons a w) = Matrix.vecCons a (Fin.removeNth i w) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Fin.removeNth, Fin.succ_succAbove_zero]
  · simp [Fin.removeNth, Fin.succ_succAbove_succ]

theorem prodDer : ProdDer := by
  intro V F _ _ _ _ p t
  refine ⟨fun Ω h => ?_, fun q Ω h => ?_⟩
  · convert line_der p t Ω h using 1
    ext v
    simp [curryLeft_apply_apply, extDeriv_apply h, fderiv_continuousAlternatingMap_apply_const h]
  · have hβ : DifferentiableAt ℝ
        (fun x => ((Ω (x, t)).curryLeft (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ)) p := by
      have hs := (hasFDerivAt_slice_of_differentiableAt p t Ω h).differentiableAt
      exact ((compContinuousLinearMapCLM (ContinuousLinearMap.inl ℝ V ℝ)).differentiableAt).comp p
        ((((curryLeftLI (𝕜 := ℝ) (E := V × ℝ) (F := F) (n := q)).toContinuousLinearMap.differentiableAt).comp p
          hs).clm_apply (differentiableAt_const _))
    convert line_der p t Ω h using 1
    ext v
    rw [ContinuousAlternatingMap.add_apply, compContinuousLinearMap_apply, curryLeft_apply_apply,
      extDeriv_apply h, Fin.sum_univ_succ, extDeriv_apply hβ]
    have hc : ∀ i : Fin (q + 1), (⇑(ContinuousLinearMap.inl ℝ V ℝ) ∘ Fin.removeNth i v) =
        Fin.removeNth i (⇑(ContinuousLinearMap.inl ℝ V ℝ) ∘ v) := fun i => rfl
    simp only [compContinuousLinearMap_apply, curryLeft_apply_apply, fderiv_slice_apply_eq_fderiv_prod_inl p t Ω h,
      fderiv_continuousAlternatingMap_apply_const h, removeNth_succ_vecCons', hc,
      ContinuousLinearMap.flipAlternating_apply_apply, Matrix.cons_val_succ, Matrix.cons_val_zero,
      Fin.removeNth_zero, Matrix.tail_cons, Fin.tail_cons, Fin.val_succ, Fin.val_zero, pow_zero, one_smul,
      pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib, Function.comp_apply,
      ContinuousLinearMap.inl_apply]
    abel

end UpperTheory.V.Lit.Geo
end
end

section
noncomputable section

open scoped ContDiff Topology

namespace UpperTheory.V.Lit.Geo

section

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

private def tot (W : V → V) (z : V × ℝ) : V := flow W z.2 z.1

private theorem tot_diff {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) :
    DifferentiableAt ℝ (tot W) (x, r) := by
  have h : DifferentiableAt ℝ (fun z : V × ℝ => W z.1) (x, r) :=
    DifferentiableAt.comp (x, r) (g := W) (f := Prod.fst) hW differentiableAt_fst
  exact differentiableAt_fst.add (differentiableAt_snd.smul h)

private theorem tot_smooth {W : V → V} {x : V} (hW : ContDiffAt ℝ ∞ W x) (r : ℝ) :
    ContDiffAt ℝ ∞ (tot W) (x, r) := by
  unfold tot flow
  exact contDiffAt_fst.add (contDiffAt_snd.smul (hW.comp (x, r) contDiffAt_fst))

private theorem tot_inl {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) (v : V) :
    fderiv ℝ (tot W) (x, r) (v, 0) = fderiv ℝ (flow W r) x v := by
  have h1 := (tot_diff hW r).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x r)
  have h2 : flow W r = tot W ∘ fun y => (y, r) := rfl
  rw [h2, h1.fderiv]
  rfl

private theorem tot_inr {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) :
    fderiv ℝ (tot W) (x, r) (0, 1) = W x := by
  have h1 := (tot_diff hW r).hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_const r x).prodMk (hasDerivAt_id r))
  have h2 : HasDerivAt (tot W ∘ fun s => (x, s)) ((1 : ℝ) • W x) r :=
    ((hasDerivAt_id r).smul_const (W x)).const_add x
  simpa using h1.unique h2

private theorem pb_tot {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) {q : ℕ}
    (w : V → V [⋀^Fin q]→L[ℝ] F) :
    (pb (tot W) w (x, r)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ) = pb (flow W r) w x := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, pb_apply, Function.comp_apply,
    ContinuousLinearMap.inl_apply, tot_inl hW]
  rfl

private theorem hk_tot {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) {q : ℕ}
    (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) :
    ((pb (tot W) w (x, r)).curryLeft (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ) = hk W r w x := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    pb_apply, hk_apply]
  congr 1
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [tot_inr hW]
  · simp [tot_inl hW]

end

theorem homPt : HomPt := by
  intro V F _ _ _ _ _ _ W p t hW
  have hd : DifferentiableAt ℝ W p := hW.differentiableAt (by simp)
  have hfl : ∀ (q : ℕ) (w : V → V [⋀^Fin q]→L[ℝ] F), (fun r => pb (flow W r) w p) =
      fun r => (pb (tot W) w (p, r)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ) :=
    fun q w => funext fun r => (pb_tot hd r w).symm
  have key : ∀ (q : ℕ) (w : V → V [⋀^Fin q]→L[ℝ] F), ContDiffAt ℝ ∞ w (flow W t p) →
      DifferentiableAt ℝ (pb (tot W) w) (p, t) ∧
        extDeriv (pb (tot W) w) (p, t) = pb (tot W) (extDeriv w) (p, t) := by
    intro q w hw
    obtain ⟨h1, h2⟩ := pbD (V × ℝ) V F q (tot W) w (p, t) (tot_smooth hW t) hw
    exact ⟨h1.differentiableAt (by simp), h2⟩
  refine ⟨fun w hw => ?_, fun q w hw => ?_⟩
  · obtain ⟨hD, hE⟩ := key 0 w hw
    rw [hfl, ← hk_tot hd t (extDeriv w), ← hE]
    exact (prodDer V F p t).1 _ hD
  · obtain ⟨hD, hE⟩ := key (q + 1) w hw
    have hev : (fun y => ((pb (tot W) w (y, t)).curryLeft (0, 1)).compContinuousLinearMap
        (ContinuousLinearMap.inl ℝ V ℝ)) =ᶠ[𝓝 p] hk W t w := by
      have h1 : ∀ᶠ y in 𝓝 p, ContDiffAt ℝ 1 W y := (hW.of_le (by simp)).eventually (by simp)
      filter_upwards [h1] with y hy
      exact hk_tot (hy.differentiableAt (by simp)) t w
    rw [hfl, ← hk_tot hd t (extDeriv w), ← hE, ← hev.extDeriv_eq]
    exact (prodDer V F p t).2 q _ hD

end UpperTheory.V.Lit.Geo
end
end

section
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr
open Set ContinuousAlternatingMap
open scoped ContDiff

private theorem extDeriv_smooth {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Y : Set V} (hY : IsOpen Y) {q : ℕ} {w : V → V [⋀^Fin q]→L[ℝ] F}
    (hw : ContDiffOn ℝ ∞ w Y) : ContDiffOn ℝ ∞ (extDeriv w) Y :=
  (alternatizeUncurryFinCLM ℝ V F).contDiff.comp_contDiffOn
    (hw.fderiv_of_isOpen hY (by simp))

private theorem pb_flow_zero {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : V → V) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) :
    pb (flow W 0) w p = w p := by
  have h : flow W 0 = id := by
    funext x
    simp [flow]
  ext v
  simp [pb_apply, h]

private theorem homForm_of (hP : HomPt) (hS : HkSmooth) : HomForm := by
  intro V F _ _ _ _ _ _ Y hY W hW p hp
  have hWp : ContDiffAt ℝ ∞ W p := hW.1.contDiffAt (hY.mem_nhds hp)
  refine ⟨fun w hw => ?_, fun q w hw => ?_⟩
  · have hI := ((hS V F Y hY W hW 0 _ (extDeriv_smooth hY hw)).2.2.1 p hp).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) zero_le_one
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r => pb (flow W r) w p) (hk W t (extDeriv w) p) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      exact (hP V F W p t hWp).1 w (hw.contDiffAt (hY.mem_nhds (hW.2 p hp t ht)))
    have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hI
    rw [pb_flow_zero] at h3
    exact h3.symm
  · have hI := ((hS V F Y hY W hW (q + 1) _ (extDeriv_smooth hY hw)).2.2.1 p hp).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) zero_le_one
    obtain ⟨hU, hΦ, -, -⟩ := hS V F Y hY W hW q w hw
    obtain ⟨hc, hD⟩ := paramDeriv V _ p _ _ hU (fun t ht => ⟨hp, hW.2 p hp t ht⟩) hΦ
    dsimp only at hc hD
    have hJ := hc.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) zero_le_one
    have hJ' : IntervalIntegrable (fun t => alternatizeUncurryFinCLM ℝ V F (fderiv ℝ (fun x => hk W t w x) p))
        MeasureTheory.volume 0 1 :=
      ((alternatizeUncurryFinCLM ℝ V F).continuous.comp_continuousOn hc).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) zero_le_one
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r => pb (flow W r) w p)
        (alternatizeUncurryFinCLM ℝ V F (fderiv ℝ (fun x => hk W t w x) p) + hk W t (extDeriv w) p) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      exact (hP V F W p t hWp).2 q w (hw.contDiffAt (hY.mem_nhds (hW.2 p hp t ht)))
    have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hJ'.add hI)
    rw [pb_flow_zero, intervalIntegral.integral_add hJ' hI,
      (alternatizeUncurryFinCLM ℝ V F).intervalIntegral_comp_comm hJ, ← hD.fderiv] at h3
    exact h3.symm

theorem UpperTheory.V.Lit.Geo.homForm :
    HomForm :=
  homForm_of homPt hkSmooth
end

section
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit
open scoped ContDiff

private theorem hom_congr_on {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Y : Set V} {W : V → V} (hW : IsField Y W) {q : ℕ} {w w' : V → V [⋀^Fin (q + 1)]→L[ℝ] F}
    (h : ∀ x ∈ Y, w x = w' x) {p : V} (hp : p ∈ Y) : hom W w p = hom W w' p := by
  unfold hom
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp only [hk]
  rw [h _ (hW.2 p hp t ht)]

private theorem om_ext {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    {G : Dr.Geo Γ V S d} {q : ℕ} {w w' : G.Om q} (h : ∀ s, ∀ p ∈ G.Y, w.1 s p = w'.1 s p) : w = w' := by
  refine Subtype.ext (funext fun s => funext fun p => ?_)
  by_cases hp : p ∈ G.Y
  · exact h s p hp
  · rw [(w.2 s).2 p hp, (w'.2 s).2 p hp]

private theorem extDeriv_congr_on {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Y : Set V} (hY : IsOpen Y) {q : ℕ} {w w' : V → V [⋀^Fin q]→L[ℝ] F}
    (h : ∀ x ∈ Y, w x = w' x) {p : V} (hp : p ∈ Y) : extDeriv w p = extDeriv w' p := by
  have hev : w =ᶠ[nhds p] w' := by
    filter_upwards [hY.mem_nhds hp] with y hy using h y hy
  exact hev.extDeriv_eq

theorem UpperTheory.V.Lit.Geo.omHom :
    OmHom := by
  intro Γ V S _ _ _ _ d G W hW
  have hA := omApply Γ V S d G W hW
  have h1 : ∀ s, ∀ p ∈ G.Y, flow (W s) 1 p ∈ G.Y := fun s p hp =>
    (hW.field s).2 p hp 1 ⟨zero_le_one, le_rfl⟩
  refine ⟨fun q w => om_ext fun s p hp => ?_, fun q w => om_ext fun s p hp => ?_,
    fun w => om_ext fun s p hp => ?_, fun q w => om_ext fun s p hp => ?_⟩
  · have hH : ContDiffAt ℝ ∞ (flow (W s) 1) p :=
      contDiffAt_id.add (((hW.field s).1.contDiffAt (G.isOpen.mem_nhds hp)).const_smul (1 : ℝ))
    rw [G.dOm_apply _ s hp, (hA (q + 1)).1 _ s p hp,
      extDeriv_congr_on G.isOpen ((hA q).1 w s) hp,
      (pbD V V (Fin d → ℂ) q (flow (W s) 1) (w.1 s) p hH (Dr.Geo.contDiffAt_Om w s (h1 s p hp))).2]
    unfold pb
    rw [G.dOm_apply w s (h1 s p hp)]
  · rw [G.dOm_apply _ s hp, extDeriv_congr_on G.isOpen (fun x hx => G.dOm_apply w s hx) hp]
    exact extDeriv_extDeriv_apply (Dr.Geo.contDiffAt_Om w s hp) (by
      rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  · change (pbOm G W w).1 s p - w.1 s p = _
    rw [(hA 0).1 w s p hp, (hA 0).2 _ s p hp,
      hom_congr_on (hW.field s) (fun x hx => G.dOm_apply w s hx) hp]
    exact (homForm V (Fin d → ℂ) G.Y G.isOpen (W s) (hW.field s) p hp).1 _ (w.2 s).1
  · change (pbOm G W w).1 s p - w.1 s p =
      (G.dOm q (homOm G W w)).1 s p + (homOm G W (G.dOm (q + 1) w)).1 s p
    rw [(hA (q + 1)).1 w s p hp, (hA (q + 1)).2 _ s p hp, G.dOm_apply _ s hp,
      extDeriv_congr_on G.isOpen ((hA q).2 w s) hp,
      hom_congr_on (hW.field s) (fun x hx => G.dOm_apply w s hx) hp]
    exact (homForm V (Fin d → ℂ) G.Y G.isOpen (W s) (hW.field s) p hp).2 q _ (w.2 s).1
end

section
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Geo.omEquiv :
    OmEquiv := by
  intro Γ V S _ _ _ _ d G W hW q γ
  have hρρ : ∀ x, G.ρ γ (G.ρ γ⁻¹ x) = x := fun x => by simpa using G.ρ_inv_apply γ⁻¹ x
  have hσ : ∀ s, G.σ γ (G.σ γ⁻¹ s) = s := fun s => by simp
  have hout : ∀ p, p ∉ G.Y → G.ρ γ⁻¹ p ∉ G.Y := fun p hp h => hp (by simpa [hρρ] using G.maps γ _ h)
  have heq : ∀ s, ∀ p ∈ G.Y, W s (G.ρ γ p) = G.ρ γ (W (G.σ γ⁻¹ s) p) := fun s p hp => by
    have := hW.equiv γ (G.σ γ⁻¹ s) p hp
    rwa [hσ] at this
  have hnat := fun s => pbNat V (Fin d → ℂ) G.Y G.isOpen (G.ρ γ) (mulVecL (G.ξ γ)) (W (G.σ γ⁻¹ s)) (W s)
    (hW.field _) (hW.field s) (G.maps γ) (heq s) q
  have hrel : ∀ (k : ℕ) (w : G.Om k) (s : S), ∀ p ∈ G.Y, ∀ v : Fin k → V,
      ((G.act k γ w).1 s (G.ρ γ p)) (fun i => G.ρ γ (v i)) = mulVecL (G.ξ γ) (w.1 (G.σ γ⁻¹ s) p v) := by
    intro k w s p hp v
    simp only [Geo.act_apply, mulVecL_apply, Geo.ρ_inv_apply]
  have hz : ∀ (k : ℕ) (w : G.Om k) (s : S) (p : V), p ∉ G.Y → w.1 s p = 0 :=
    fun k w s p hp => (w.2 s).2 p hp
  have hsm := fun (k : ℕ) (w : G.Om k) (s : S) => (w.2 s).1
  obtain ⟨hA, hB⟩ := omApply Γ V S d G W hW q
  refine ⟨fun w => ?_, fun w => ?_⟩
  · apply Subtype.ext
    funext s p
    ext v
    by_cases hp : p ∈ G.Y
    · have hp' := G.maps γ⁻¹ p hp
      rw [Geo.act_apply, hA w _ _ hp', hA (G.act q γ w) s p hp]
      have := (hnat s).1 (w.1 (G.σ γ⁻¹ s)) ((G.act q γ w).1 s) (hrel q w s) 1 ⟨zero_le_one, le_rfl⟩
        (G.ρ γ⁻¹ p) hp' (fun i => G.ρ γ⁻¹ (v i))
      simp only [hρρ] at this
      rw [← mulVecL_apply]
      exact congrFun this.symm _
    · rw [Geo.act_apply, hz q _ _ _ (hout p hp), hz q _ s p hp]
      simp
  · apply Subtype.ext
    funext s p
    ext v
    by_cases hp : p ∈ G.Y
    · have hp' := G.maps γ⁻¹ p hp
      rw [Geo.act_apply, hB w _ _ hp', hB (G.act (q + 1) γ w) s p hp]
      have := ((hnat s).2 (w.1 (G.σ γ⁻¹ s)) ((G.act (q + 1) γ w).1 s) (hrel (q + 1) w s)).2
        (hsm _ w _) (hsm _ _ s) (G.ρ γ⁻¹ p) hp' (fun i => G.ρ γ⁻¹ (v i))
      simp only [hρρ] at this
      rw [← mulVecL_apply]
      exact congrFun this.symm _
    · rw [Geo.act_apply, hz q _ _ _ (hout p hp), hz q _ s p hp]
      simp
end

section
open UpperTheory.V.Lit.Geo

private theorem UpperTheory.V.Lit.Geo.euler_flow {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : V → V} {p : V}
    (hd : DifferentiableAt ℝ W p) (hh : ∀ t : ℝ, 0 < t → W (t • p) = t • W p) (t : ℝ) :
    fderiv ℝ (flow W t) p p = flow W t p := by
  have hp1 : HasFDerivAt W (fderiv ℝ W p) ((1 : ℝ) • p) := by
    rw [one_smul]
    exact hd.hasFDerivAt
  have hr : HasDerivAt (fun s : ℝ => s • p) ((1 : ℝ) • p) 1 := (hasDerivAt_id (1 : ℝ)).smul_const p
  have h1 : HasDerivAt (fun s : ℝ => W (s • p)) (fderiv ℝ W p ((1 : ℝ) • p)) 1 :=
    hp1.comp_hasDerivAt (1 : ℝ) hr
  have h2 : HasDerivAt (fun s : ℝ => W (s • p)) (W p) 1 := by
    have hl : HasDerivAt (fun s : ℝ => s • W p) ((1 : ℝ) • W p) 1 := (hasDerivAt_id (1 : ℝ)).smul_const (W p)
    rw [one_smul] at hl
    refine hl.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (zero_lt_one' ℝ)] with s hs
    exact hh s hs
  have heul : fderiv ℝ W p p = W p := by
    have := h1.unique h2
    rwa [one_smul] at this
  have hf : HasFDerivAt (flow W t) (ContinuousLinearMap.id ℝ V + t • fderiv ℝ W p) p :=
    (hasFDerivAt_id p).add (hd.hasFDerivAt.const_smul t)
  rw [hf.fderiv]
  simp [flow, heul]

theorem UpperTheory.V.Lit.Geo.pbBasic :
    PbBasic := by
  intro V F _ _ _ _ _ _ Y hY W hW hh q
  have hdiff : ∀ p ∈ Y, DifferentiableAt ℝ W p := fun p hp =>
    (hW.1.contDiffAt (hY.mem_nhds hp)).differentiableAt (by simp)
  have he : ∀ p ∈ Y, ∀ t : ℝ, fderiv ℝ (flow W t) p p = flow W t p := fun p hp t =>
    euler_flow (hdiff p hp) (fun s hs => hh s hs p hp) t
  refine ⟨fun w hw => ?_, fun w _ hw => ?_⟩
  · intro p hp v i hi
    rw [pb_apply]
    apply hw (flow W 1 p) (hW.2 p hp 1 ⟨zero_le_one, le_rfl⟩) _ i
    simp [hi, he p hp]
  · intro p hp v i hi
    have hz : ∀ t ∈ Set.Icc (0 : ℝ) 1, hk W t w p v = 0 := by
      intro t ht
      rw [hk_apply]
      apply hw (flow W t p) (hW.2 p hp t ht) _ i.succ
      simp [hi, he p hp]
    show (∫ t in (0 : ℝ)..1, hk W t w p) v = 0
    by_cases hint : IntervalIntegrable (fun t => hk W t w p) MeasureTheory.volume 0 1
    · have hc := (ContinuousAlternatingMap.apply ℝ V F v).intervalIntegral_comp_comm hint
      simp only [ContinuousAlternatingMap.apply_apply] at hc
      rw [← hc, intervalIntegral.integral_congr (g := fun _ => (0 : F))]
      · simp
      · intro t ht
        rw [Set.uIcc_of_le zero_le_one] at ht
        exact hz t ht
    · rw [intervalIntegral.integral_undef hint]
      rfl
end

section
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Geo.omGood :
    OmGood := by
  intro Γ V S _ _ _ _ d G W hW q
  have hsub : ∀ (q : ℕ) (w w' : G.Om q), (∀ s, RadBasic G.Y (w.1 s)) → (∀ s, RadBasic G.Y (w'.1 s)) →
      ∀ s, RadBasic G.Y ((w - w').1 s) := by
    intro q w w' h h' s p hp v i hi
    have e : (w - w').1 s p v = w.1 s p v - w'.1 s p v := rfl
    rw [e, h s p hp v i hi, h' s p hp v i hi, sub_self]
  have hpb : ∀ (q : ℕ) (w : G.Om q), (∀ s, RadBasic G.Y (w.1 s)) → ∀ s, RadBasic G.Y ((pbOm G W w).1 s) := by
    intro q w h s p hp v i hi
    rw [(omApply Γ V S d G W hW q).1 w s p hp]
    exact (pbBasic V _ G.Y G.isOpen (W s) (hW.field s) (hW.homog s) q).1 _ (h s) p hp v i hi
  have hhom : ∀ (q : ℕ) (w : G.Om (q + 1)), (∀ s, RadBasic G.Y (w.1 s)) →
      ∀ s, RadBasic G.Y ((homOm G W w).1 s) := by
    intro q w h s p hp v i hi
    rw [(omApply Γ V S d G W hW q).2 w s p hp]
    exact (pbBasic V _ G.Y G.isOpen (W s) (hW.field s) (hW.homog s) q).2 _ (w.2 s).1 (h s) p hp v i hi
  obtain ⟨h1, h2, -, h4⟩ := omHom Γ V S d G W hW
  refine ⟨fun w hw => ⟨⟨fun γ => ?_, hpb q w hw.basic, ?_⟩, ⟨fun γ => ?_, hw.dbasic, ?_⟩⟩,
    fun w w' hw hw' => ⟨fun γ => ?_, hsub q w w' hw.basic hw'.basic, ?_⟩,
    fun w hw => ⟨fun γ => ?_, hhom q w hw.basic, ?_⟩⟩
  · rw [(omEquiv Γ V S d G W hW q γ).1 w, hw.inv γ]
  · rw [h1]
    exact hpb _ _ hw.dbasic
  · rw [← dEquiv Γ V S d G q γ w, hw.inv γ]
  · rw [h2]
    intro s p _ v i _
    rfl
  · rw [map_sub, hw.inv γ, hw'.inv γ]
  · rw [map_sub]
    exact hsub _ _ _ hw.dbasic hw'.dbasic
  · rw [(omEquiv Γ V S d G W hW q γ).2 w, hw.inv γ]
  · rw [eq_sub_of_add_eq (h4 q w).symm]
    exact hsub _ _ _ (hsub _ _ _ (hpb _ _ hw.basic) hw.basic) (hhom _ _ hw.dbasic)
end

section
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr Matrix

theorem UpperTheory.V.Lit.Geo.levD :
    LevD := by
  intro E _ _ _ a U Ξ q α hα
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, h⟩ := locSec E a p hp
    exact h.mono fun x hx => ⟨τ x, hx⟩
  obtain ⟨w, hc, hg⟩ := (levGood E a ho U Ξ q).1 α hα
  have hom := omGood _ _ _ _ (geo ho U Ξ) 0 (isFlow_zero _) q
  refine ⟨?_, fun β hβ => ?_⟩
  · obtain ⟨α', hc', hl⟩ := (levGood E a ho U Ξ (q + 1)).2 _ (hom.1 w hg).2
    rw [(corrUniq E a ho U Ξ (q + 1)).1 _ _ _ (corrD E a ho U Ξ q α w hc) hc']
    exact hl
  · obtain ⟨w', hc', hg'⟩ := (levGood E a ho U Ξ q).1 β hβ
    obtain ⟨γ, hc'', hl⟩ := (levGood E a ho U Ξ q).2 _ (hom.2.1 w w' hg hg')
    have hs : Corr U Ξ (α - β) (w - w').1 := fun g x X => by
      rw [AlternatingMap.sub_apply, map_sub, Pi.sub_apply, Matrix.mulVec_sub, ← hc g x X, ← hc' g x X]
      rfl
    rw [(corrUniq E a ho U Ξ q).1 _ _ _ hs hc'']
    exact hl
end
