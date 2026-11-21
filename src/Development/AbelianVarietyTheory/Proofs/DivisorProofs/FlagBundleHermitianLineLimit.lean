import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcEqOfLocalEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormSqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleCurvatureAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDensityBoundNearPoint
import BuildAid.ForwardExisting

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open scoped ComplexOrder

open GlobalTheory.HermFrame Filter Topology ComplexConjugate

namespace GlobalTheory.HermFrame

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem ddbar_mul_conj_mul_of_zero {s U : E → ℂ} {z : E} (hs : ContDiffAt ℂ 2 s z) (h0 : s z = 0)
    (hU : ContDiffAt ℝ 2 U z) (ξ η : E) :
    ddbar (fun x => s x * (conj (s x) * U x)) z ξ η = del s z ξ * (conj (del s z η) * U z) := by
  have hR : ContDiffAt ℝ 2 s z := hs.restrict_scalars ℝ
  have hc : ContDiffAt ℝ 2 (fun x => conj (s x)) z := Complex.conjCLE.contDiff.contDiffAt.comp z hR
  have hW : ContDiffAt ℝ 2 (fun x => conj (s x) * U x) z := hc.mul hU
  have he : (fun x => dbar (fun y => s y * (conj (s y) * U y)) x η) =ᶠ[𝓝 z]
      fun x => s x * dbar (fun y => conj (s y) * U y) x η := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt_two hs,
      eventually_differentiableAt_of_contDiffAt_two hW] with x h1 h2
    rw [dbar_mul (h1.restrictScalars ℝ) h2, dbar_eq_zero h1]
    simp
  rw [ddbar_eq_del_dbar (hR.mul hW), del_congr he,
    del_mul (hR.differentiableAt two_ne_zero) (differentiableAt_dbar_apply hW η),
    dbar_mul (hc.differentiableAt two_ne_zero) (hU.differentiableAt two_ne_zero), dbar_conj, h0]
  simp

open Matrix in

theorem extTrace_chg_of_block_eq_zero {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    {K A : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E} (h : MContDiffAt 1 K z)
    (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (hA : MContDiffAt 1 A z) (hu : IsUnit (A z).det)
    (hA0 : ∀ η, mdbar A z η = 0) (ht : (A z).toBlocks₂₁ = 0) (ξ η : E) :
    extTrace (fun x => chg (A x) (K x)) z ξ η = kappa *
      ((secondForm K z ξ + (mdel A z ξ).toBlocks₂₁ * (A z).toBlocks₁₁⁻¹) *
        adj (subGram (K z)) (quotGram (K z))
          (secondForm K z η + (mdel A z η).toBlocks₂₁ * (A z).toBlocks₁₁⁻¹)).trace := by
  have eA : A z = fromBlocks (A z).toBlocks₁₁ (A z).toBlocks₁₂ 0 (A z).toBlocks₂₂ := by
    rw [← ht, fromBlocks_toBlocks]
  have hd := hu
  rw [eA, det_fromBlocks_zero₂₁, IsUnit.mul_iff] at hd
  have hK := hp.self_of_nhds
  have hb (ξ : E) : secondForm (fun x => chg (A x) (K x)) z ξ =
      (A z).toBlocks₂₂⁻¹ * (secondForm K z ξ + (mdel A z ξ).toBlocks₂₁ * (A z).toBlocks₁₁⁻¹) *
        (A z).toBlocks₁₁ := by
    have e := congrArg (A z * ·) (conn_changeFrame h hK.det_pos.ne'.isUnit hA hu hA0 ξ)
    simp only [mul_nonsing_inv_cancel_left _ _ hu] at e
    have e₁ := congrArg toBlocks₂₁ e
    rw [← fromBlocks_toBlocks (conn _ z ξ), ← fromBlocks_toBlocks (conn K z ξ),
      ← fromBlocks_toBlocks (mdel A z ξ), eA] at e₁
    simp only [fromBlocks_multiply, fromBlocks_add, toBlocks_fromBlocks₂₁, Matrix.zero_mul,
      Matrix.mul_zero, zero_add, add_zero] at e₁
    rw [secondForm_eq, secondForm_eq, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_assoc,
      nonsing_inv_mul _ hd.1, Matrix.mul_one]
    first
      | (rw [← e₁, nonsing_inv_mul_cancel_left _ _ hd.2]; rfl)
      | (rw [add_comm, ← e₁, nonsing_inv_mul_cancel_left _ _ hd.2]; rfl)
  have hp' : ∀ᶠ x in 𝓝 z, (chg (A x) (K x)).PosDef := by
    filter_upwards [hp, hA.eventually_isUnit hu] with x h₁ h₂
    exact posDef_chg ((isUnit_iff_isUnit_det _).2 h₂) h₁
  rw [extTrace_eq (K := fun x => chg (A x) (K x))
    ((hA.transpose.mul h).mul hA.conjTranspose.transpose) hp',
    secondFormAdj, hb, hb, ← trace_mul_adj_chg hd.1 hd.2 (subGram (K z)),
    ← subGram_chg _ (A z).toBlocks₁₂ (A z).toBlocks₂₂,
    ← quotGram_chg (A z).toBlocks₁₂ _ hd.1 (posDef_subGram hK).det_pos.ne'.isUnit, ← eA]

end

theorem chg_mul_sub_form {K A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ} (hK : K.IsHermitian) :
    chg A K (.inl 0) (.inl 0) * K (.inl 0) (.inl 0) -
      ((‖form K (Pi.single (Sum.inl 0) 1) (fun i => A i (Sum.inl 0))‖ ^ 2 : ℝ) : ℂ) =
    A (.inr 0) (.inl 0) * (conj (A (.inr 0) (.inl 0)) *
      (K (.inl 0) (.inl 0) * K (.inr 0) (.inr 0) - K (.inl 0) (.inr 0) * K (.inr 0) (.inl 0))) := by
  have h1 : conj (K (.inl 0) (.inl 0)) = K (.inl 0) (.inl 0) := hK.apply _ _
  have h2 : conj (K (.inl 0) (.inr 0)) = K (.inr 0) (.inl 0) := hK.apply _ _
  rw [Complex.ofReal_pow, ← Complex.mul_conj', chg_apply, form_eq_sum, form_eq_sum]
  simp [Fintype.sum_sum_type, h1, h2]
  ring

end GlobalTheory.HermFrame

namespace GlobalTheory.LineForm

theorem ofValues_mul_ofValues_eq_zero {n : ℕ} (u u' w w' : ReciprocityTheory.L2DbarEstimates.V n → ℂ) (c : ℂ) :
    ((ofValues (fun ξ η => c * (u ξ * u' η)) : Ev n) : Alt n) *
      (((ofValues (fun ξ η => u ξ * w' η) : Ev n) : Alt n) +
        ((ofValues (fun ξ η => w ξ * u' η) : Ev n) : Alt n)) = 0 := by
  have e : ((ofValues (fun ξ η => c * (u ξ * u' η)) : Ev n) : Alt n) =
      c • ((ofValues (fun ξ η => u ξ * u' η) : Ev n) : Alt n) := by
    simp only [ofValues, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, Finset.smul_sum, smul_smul]
  rw [e, coe_ofValues_mul, coe_ofValues_mul, coe_ofValues_mul]
  generalize (∑ a, u (GlobalTheory.GoodMetric.coordVec a) • Pi.single (Sum.inl a) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = x
  generalize (∑ a, w (GlobalTheory.GoodMetric.coordVec a) • Pi.single (Sum.inl a) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = x'
  generalize (∑ b, u' (GlobalTheory.GoodMetric.coordVec b) • Pi.single (Sum.inr b) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = y
  generalize (∑ b, w' (GlobalTheory.GoodMetric.coordVec b) • Pi.single (Sum.inr b) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = y'
  have h := Subalgebra.mem_center_iff.1 (ι_mul_ι_mem_center x y) (ExteriorAlgebra.ι ℂ x)
  have h' := Subalgebra.mem_center_iff.1 (ι_mul_ι_mem_center x' y) (ExteriorAlgebra.ι ℂ y)
  rw [smul_mul_assoc, mul_add, ← mul_assoc _ (ExteriorAlgebra.ι ℂ x), ← h, ← mul_assoc (ExteriorAlgebra.ι ℂ x),
    ExteriorAlgebra.ι_sq_zero, mul_assoc (ExteriorAlgebra.ι ℂ x), h', mul_assoc (ExteriorAlgebra.ι ℂ x'),
    ExteriorAlgebra.ι_sq_zero]
  simp

theorem coe_ofValues_sub_eq {n : ℕ} {α β γ δ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n → ℂ}
    (h : ∀ ξ η, α ξ η = β ξ η + (γ ξ η + δ ξ η)) :
    ((ofValues α : Ev n) : Alt n) - ((ofValues β : Ev n) : Alt n) =
      ((ofValues γ : Ev n) : Alt n) + ((ofValues δ : Ev n) : Alt n) := by
  simp only [ofValues, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, Subalgebra.coe_add, h, add_smul,
    Finset.sum_add_distrib, add_sub_cancel_left]

theorem ddc_sinSq_mul_extTrace_sub : ∀ (n : ℕ) (K A : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n → ℝ) (z : ReciprocityTheory.L2DbarEstimates.V n),
    GlobalTheory.HermFrame.MContDiffAt 2 K z → (∀ᶠ x in nhds z, (K x).PosDef) → (∀ a b, AnalyticAt ℂ (fun x => A x a b) z) → IsUnit (A z).det → v z = 1 →
    (∀ᶠ x in nhds z, ‖GlobalTheory.HermFrame.form (K x) (Pi.single (Sum.inl 0) 1) (fun i => A x i (Sum.inl 0))‖ ^ 2 =
      v x * (GlobalTheory.HermFrame.chg (A x) (K x) (Sum.inl 0) (Sum.inl 0)).re * (K x (Sum.inl 0) (Sum.inl 0)).re) →
    ((ofValues (GlobalTheory.HermFrame.ddc (fun x => 1 - v x) z) : Ev n) : Alt n) *
      (((ofValues (GlobalTheory.HermFrame.extTrace (fun x => GlobalTheory.HermFrame.chg (A x) (K x)) z) : Ev n) : Alt n) -
        ((ofValues (GlobalTheory.HermFrame.extTrace K z) : Ev n) : Alt n)) = 0 := by
  intro n K A v z hK hp hA hu hv he
  have hA2 : MContDiffAt 2 A z := fun a b => ((hA a b).contDiffAt (n := 2)).restrict_scalars ℝ
  have hA1 : MContDiffAt 1 A z := fun a b => (hA2 a b).of_le (by norm_num)
  have hK1 : MContDiffAt 1 K z := fun a b => (hK a b).of_le (by norm_num)
  have hC : MContDiffAt 2 (fun x => chg (A x) (K x)) z :=
    (hA2.transpose.mul hK).mul hA2.conjTranspose.transpose
  have hp' : ∀ᶠ x in 𝓝 z, (chg (A x) (K x)).PosDef := by
    filter_upwards [hp, hA1.eventually_isUnit hu] with x h₁ h₂
    exact posDef_chg ((Matrix.isUnit_iff_isUnit_det _).2 h₂) h₁
  set s : ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun x => A x (.inr 0) (.inl 0) with hs
  set U : ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun x =>
    (K x (.inl 0) (.inl 0) * K x (.inr 0) (.inr 0) - K x (.inl 0) (.inr 0) * K x (.inr 0) (.inl 0)) *
      (chg (A x) (K x) (.inl 0) (.inl 0) * K x (.inl 0) (.inl 0))⁻¹ with hU
  have hne : chg (A z) (K z) (.inl 0) (.inl 0) * K z (.inl 0) (.inl 0) ≠ 0 :=
    mul_ne_zero (hp'.self_of_nhds.diag_pos).ne' (hp.self_of_nhds.diag_pos).ne'
  have hU2 : ContDiffAt ℝ 2 U z :=
    (((hK _ _).mul (hK _ _)).sub ((hK _ _).mul (hK _ _))).mul (((hC _ _).mul (hK _ _)).inv hne)
  have hev : (fun x => ((1 - v x : ℝ) : ℂ)) =ᶠ[𝓝 z] fun x => s x * (conj (s x) * U x) := by
    filter_upwards [hp, hp', he] with x h₁ h₂ h₃
    have e := chg_mul_sub_form (A := A x) h₁.isHermitian
    have n₁ := (h₁.diag_pos (i := .inl 0))
    have n₂ := (h₂.diag_pos (i := .inl 0))
    have r₁ : ((K x (.inl 0) (.inl 0)).re : ℂ) = K x (.inl 0) (.inl 0) :=
      Complex.ext rfl (by simpa using (Complex.lt_def.1 n₁).2)
    have r₂ : ((chg (A x) (K x) (.inl 0) (.inl 0)).re : ℂ) = chg (A x) (K x) (.inl 0) (.inl 0) :=
      Complex.ext rfl (by simpa using (Complex.lt_def.1 n₂).2)
    rw [h₃, Complex.ofReal_mul, Complex.ofReal_mul, r₁, r₂] at e
    have n₁' := n₁.ne'
    have n₂' := n₂.ne'
    simp only [hs, hU]
    rw [← mul_assoc (conj _), ← mul_assoc, ← e]
    push_cast
    field_simp
  have hUz : U z ≠ 0 := by
    refine mul_ne_zero ?_ (inv_ne_zero hne)
    have := hp.self_of_nhds.det_pos.ne'
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv.symm, Matrix.det_fin_two] at this
    exact this
  have hs0 : s z = 0 := by
    have := hev.self_of_nhds
    simp only [hv, sub_self, Complex.ofReal_zero] at this
    simpa [hUz] using this.symm
  have e1 : ddc (fun x => 1 - v x) z = fun ξ η => (kappa * U z) * (del s z ξ * conj (del s z η)) := by
    funext ξ η
    rw [ddc, leviForm, ddbar_congr hev, ddbar_mul_conj_mul_of_zero (hA _ _).contDiffAt hs0 hU2]
    ring
  have hA0 : ∀ η, mdbar A z η = 0 := fun η => Matrix.ext fun i j =>
    congr($(dbar_eq_zero (hA i j).differentiableAt) η)
  have ht : (A z).toBlocks₂₁ = 0 := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact hs0
  set c : ℂ := kappa * ((subGram (K z)).transpose⁻¹ 0 0 * quotGram (K z) 0 0) with hc
  set d : ℂ := (A z).toBlocks₁₁⁻¹ 0 0 with hd
  rw [e1, coe_ofValues_sub_eq (γ := fun ξ η => del s z ξ *
      (c * d * conj (secondForm K z η 0 0 + del s z η * d)))
    (δ := fun ξ η => (c * conj d * secondForm K z ξ 0 0) * conj (del s z η)) fun ξ η => ?_]
  · exact ofValues_mul_ofValues_eq_zero _ (fun η => conj (del s z η)) _ _ _
  · have m (ξ) : (mdel A z ξ).toBlocks₂₁ 0 0 = del s z ξ := rfl
    rw [extTrace_chg_of_block_eq_zero hK1 hp hA1 hu hA0 ht, extTrace_eq hK1 hp, secondFormAdj]
    simp only [adj, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_one, Matrix.add_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, m, ← hd, hc, Complex.star_def, map_add, map_mul]
    ring

end GlobalTheory.LineForm
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_frame_form_norm_sq_eq : ∀ (n : ℕ) (K A : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n → ℝ) (z : ReciprocityTheory.L2DbarEstimates.V n),
    GlobalTheory.HermFrame.MContDiffAt 2 K z → (∀ᶠ x in nhds z, (K x).PosDef) → (∀ a b, AnalyticAt ℂ (fun x => A x a b) z) → IsUnit (A z).det → v z = 1 →
    (∀ᶠ x in nhds z, ‖GlobalTheory.HermFrame.form (K x) (Pi.single (Sum.inl 0) 1) (fun i => A x i (Sum.inl 0))‖ ^ 2 =
      v x * (GlobalTheory.HermFrame.chg (A x) (K x) (Sum.inl 0) (Sum.inl 0)).re * (K x (Sum.inl 0) (Sum.inl 0)).re) →
    ((ofValues (GlobalTheory.HermFrame.ddc (fun x => 1 - v x) z) : Ev n) : Alt n) *
      (((ofValues (GlobalTheory.HermFrame.extTrace (fun x => GlobalTheory.HermFrame.chg (A x) (K x)) z) : Ev n) : Alt n) -
        ((ofValues (GlobalTheory.HermFrame.extTrace K z) : Ev n) : Alt n)) = 0 := by
  atlas_forward_decl GlobalTheory.LineForm.ddc_sinSq_mul_extTrace_sub
end

section
section
open MeasureTheory

namespace GlobalTheory

theorem lintegral_concKernel_le_one {t : ℝ} (ht : 0 < t) :
    ∫⁻ s in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (t / (1 - s + t) ^ 2) ≤ 1 := by
  have hpos : ∀ s ∈ Set.uIcc (0 : ℝ) 1, 1 - s + t ≠ 0 := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    have := hs.2
    linarith
  have hc : ContinuousOn (fun s : ℝ => t / (1 - s + t) ^ 2) (Set.uIcc (0 : ℝ) 1) :=
    ContinuousOn.div continuousOn_const (by fun_prop) (fun s hs => pow_ne_zero 2 (hpos s hs))
  have hint : ∫ s in (0 : ℝ)..1, t / (1 - s + t) ^ 2 = t / (1 - 1 + t) - t / (1 - 0 + t) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => t / (1 - s + t)) ?_
      hc.intervalIntegrable
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => 1 - s + t) (-1) s := by
      simpa using ((hasDerivAt_id s).const_sub 1).add_const t
    have h2 := (hasDerivAt_const s t).fun_div h1 (hpos s hs)
    have h3 : (0 * (1 - s + t) - t * -1) / (1 - s + t) ^ 2 = t / (1 - s + t) ^ 2 := by ring
    exact h3 ▸ h2
  rw [Set.uIcc_of_le zero_le_one] at hc
  rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall fun s => by positivity), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, hint]
  apply ENNReal.ofReal_le_one.2
  have : 0 ≤ t / (1 - 0 + t) := by positivity
  have h3 : t / (1 - 1 + t) = 1 := by
    rw [sub_self, zero_add, div_self ht.ne']
  linarith

theorem tendsto_lintegral_concKernel_mul_zero :
    ∀ (M : Type) [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M] (ν : Measure M) (K : Set M) (v D : M → ℝ) (C : ENNReal),
    IsCompact K → ContinuousOn v K → ContinuousOn D K → (∀ z ∈ K, v z = 1 → D z = 0) → C ≠ ⊤ →
    Measure.map v (ν.restrict K) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) →
    Filter.Tendsto (fun t : ℝ => ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro M _ _ _ _ ν K v D C hK hv hD h0 hC hle
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hvm : AEMeasurable v (ν.restrict K) := hv.aemeasurable hKm
  have hmap : ∀ f : ℝ → ENNReal, Measurable f →
      ∫⁻ z in K, f (v z) ∂ν ≤ C * ∫⁻ s in Set.Icc (0 : ℝ) 1, f s := by
    intro f hf
    rw [← lintegral_map' hf.aemeasurable hvm]
    refine (lintegral_mono' hle le_rfl).trans ?_
    rw [lintegral_smul_measure, smul_eq_mul]
  have hone : ∫⁻ _z in K, (1 : ENNReal) ∂ν ≤ C := by
    have := hmap (fun _ => 1) measurable_const
    simpa using this
  have hae : ∀ᵐ z ∂(ν.restrict K), v z ∈ Set.Icc (0 : ℝ) 1 := by
    apply ae_of_ae_map hvm (p := fun s => s ∈ Set.Icc (0 : ℝ) 1)
    apply Measure.AbsolutelyContinuous.ae_le (Measure.absolutelyContinuous_of_le_smul hle)
    exact ae_restrict_mem measurableSet_Icc
  obtain ⟨Mx, hMx⟩ := hK.exists_bound_of_continuousOn hD
  have key : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ t : ℝ, 0 < t →
      ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν ≤
        ENNReal.ofReal (δ + B * t) * C := by
    intro δ hδ
    have hS : IsCompact (K ∩ D ⁻¹' Set.Ici δ) :=
      hK.of_isClosed_subset (hD.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici)
        Set.inter_subset_left
    obtain ⟨η, hη, hηS⟩ : ∃ η : ℝ, 0 < η ∧ ∀ z ∈ K ∩ D ⁻¹' Set.Ici δ, η ≤ |1 - v z| := by
      apply hS.exists_forall_le' (f := fun z => |1 - v z|)
      · exact (continuousOn_const.sub (hv.mono Set.inter_subset_left)).abs
      · rintro z ⟨hz, hz'⟩
        refine abs_pos.2 fun h => ?_
        have := h0 z hz (by linarith)
        simp only [Set.mem_preimage, Set.mem_Ici] at hz'
        linarith
    refine ⟨|Mx| / η ^ 2, fun t ht => ?_⟩
    have hB : 0 ≤ |Mx| / η ^ 2 * t := by positivity
    have hf : Measurable fun s : ℝ => ENNReal.ofReal (t / (1 - s + t) ^ 2) := by fun_prop
    calc ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν
        ≤ ∫⁻ z in K, (ENNReal.ofReal (|Mx| / η ^ 2 * t) * 1 +
            ENNReal.ofReal δ * ENNReal.ofReal (t / (1 - v z + t) ^ 2)) ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae, ae_restrict_mem hKm] with z hz hzK
          have hk : 0 ≤ t / (1 - v z + t) ^ 2 := by positivity
          rw [mul_one, ← ENNReal.ofReal_mul hδ.le, ← ENNReal.ofReal_add hB (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          by_cases hd : δ ≤ D z
          · have h1 := hηS z ⟨hzK, hd⟩
            rw [abs_of_nonneg (by linarith [hz.2])] at h1
            have h2 : t / (1 - v z + t) ^ 2 ≤ t / η ^ 2 := by
              gcongr
              linarith
            have h3 : D z ≤ |Mx| := (le_abs_self _).trans ((hMx z hzK).trans (le_abs_self _))
            have h4 : t / (1 - v z + t) ^ 2 * D z ≤ t / η ^ 2 * |Mx| :=
              mul_le_mul h2 h3 (by linarith) (by positivity)
            have h5 : t / η ^ 2 * |Mx| = |Mx| / η ^ 2 * t := by ring
            have h6 : 0 ≤ δ * (t / (1 - v z + t) ^ 2) := by positivity
            linarith
          · push_neg at hd
            nlinarith
      _ = ENNReal.ofReal (|Mx| / η ^ 2 * t) * ∫⁻ _z in K, (1 : ENNReal) ∂ν +
            ENNReal.ofReal δ * ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2) ∂ν := by
          rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (|Mx| / η ^ 2 * t) * C + ENNReal.ofReal δ * C := by
          gcongr
          refine (hmap _ hf).trans ?_
          calc _ ≤ C * 1 := by gcongr; exact lintegral_concKernel_le_one ht
            _ = C := mul_one C
      _ = _ := by
          rw [ENNReal.ofReal_add hδ.le hB]; ring
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hT : Filter.Tendsto (fun x : ℝ => ENNReal.ofReal x * C) (nhds 0) (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => ENNReal.ofReal x) (nhds 0) (nhds 0) := by
      simpa using ENNReal.continuous_ofReal.tendsto 0
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hC)
  have hev := hT.eventually (gt_mem_nhds hε)
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨B, hB⟩ := key (r / 2) (by positivity)
  have hT2 : Filter.Tendsto (fun t : ℝ => r / 2 + B * t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (r / 2)) := by
    apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
    have : Continuous (fun t : ℝ => r / 2 + B * t) := by fun_prop
    simpa using this.tendsto 0
  have hmem : Metric.ball (0 : ℝ) r ∈ nhds (r / 2) := by
    apply Metric.isOpen_ball.mem_nhds
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  filter_upwards [hT2.eventually hmem, self_mem_nhdsWithin] with t h1 h2
  exact (hB t h2).trans (hrb h1).le

end GlobalTheory
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_lintegral_poisson_kernel_boundary : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M] (ν : Measure M) (K : Set M) (v D : M → ℝ) (C : ENNReal),
    IsCompact K → ContinuousOn v K → ContinuousOn D K → (∀ z ∈ K, v z = 1 → D z = 0) → C ≠ ⊤ →
    Measure.map v (ν.restrict K) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) →
    Filter.Tendsto (fun t : ℝ => ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  atlas_forward_decl GlobalTheory.tendsto_lintegral_concKernel_mul_zero
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineCos

section General

open ReciprocityTheory.L2DbarEstimates (V)

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem reDens_fn_mul (g : M → ℝ) (Φ : A.Fld) (i : A.ι) {z : V n} (hz : z ∈ (A.e i).target) :
    A.reDens (A.fn g * Φ) i z = g ((A.e i).symm z) * A.reDens Φ i z := by
  have h : (A.fn g * Φ) ⟨(i, (A.e i).symm z), (A.e i).map_target hz⟩ =
      ((g ((A.e i).symm z) : ℝ) : ℂ) • Φ ⟨(i, (A.e i).symm z), (A.e i).map_target hz⟩ := by
    rw [Algebra.smul_def]
    rfl
  simp only [HolAtlas.reDens, HolAtlas.loc, dif_pos hz]
  rw [h, dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc, Complex.re_ofReal_mul]
  rfl

theorem part_fn_mul_chart [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] (g : M → ℝ) {Φ : A.Fld}
    (hΦ : A.IsForm Φ) (ε : ℤˣ) (i : A.ι) {U : Set (V n)} (hU : IsOpen U) (hUt : U ⊆ (A.e i).target) :
    A.part (A.fn g * Φ) ε ((A.e i).source ∩ A.e i ⁻¹' U) =
      ∫⁻ z in U, ENNReal.ofReal (g ((A.e i).symm z) * (((ε : ℤ) : ℝ) * A.reDens Φ i z)) := by
  have hWm : MeasurableSet ((A.e i).source ∩ A.e i ⁻¹' U) := ((A.e i).isOpen_inter_preimage hU).measurableSet
  have hcompat := A.ofReal_compat (fun i v => ((ε : ℤ) : ℝ) * A.reDens (A.fn g * Φ) i v)
    (fun i j y hi hj => by
      rw [reDens_fn_mul A g Φ i ((A.e i).map_source hi), reDens_fn_mul A g Φ j ((A.e j).map_source hj),
        (A.e i).left_inv hi, (A.e j).left_inv hj, A.reDens_compat hΦ i j y hi hj]
      ring)
  have hp : A.part (A.fn g * Φ) ε = ChartGlue.glueMeas A.e
      (fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * A.reDens (A.fn g * Φ) i (A.e i y))) := rfl
  have himg : A.e i '' ((A.e i).source ∩ A.e i ⁻¹' U) = U := by
    ext z
    constructor
    · rintro ⟨y, ⟨-, hy⟩, rfl⟩
      exact hy
    · intro hz
      exact ⟨(A.e i).symm z, ⟨(A.e i).map_target (hUt hz), by simpa [(A.e i).right_inv (hUt hz)] using hz⟩,
        (A.e i).right_inv (hUt hz)⟩
  rw [hp, ChartGlue.glueMeas_apply _ _ A.holo hcompat i hWm Set.inter_subset_left,
    ChartGlue.chartMeas_apply_of_subset (A.e i) _ hWm Set.inter_subset_left, himg]
  refine setLIntegral_congr_fun hU.measurableSet fun z hz => ?_
  simp only [(A.e i).right_inv (hUt hz), reDens_fn_mul A g Φ i (hUt hz)]
  congr 1
  ring

end General

theorem tendsto_integral_kernel_mul : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ Φ : (hY.atlas σ).Fld, (hY.atlas σ).IsForm Φ → (∀ x : (hY.atlas σ).Pt, v x.pt = 1 → dens (Φ x) = 0) →
      Filter.Tendsto (fun t : ℝ => (hY.atlas σ).integral ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) * Φ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv Φ hΦ h0
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  have main : ∀ ε : ℤˣ, Filter.Tendsto (fun t : ℝ => (hY.atlas σ).part
      ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) * Φ) ε Set.univ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro ε
    have loc : ∀ y : CxPts p σ, ∃ W : Set (CxPts p σ), IsOpen W ∧ y ∈ W ∧ Filter.Tendsto (fun t : ℝ => (hY.atlas σ).part
        ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) * Φ) ε W) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      intro y
      obtain ⟨c, G, s, O, hy, hO, hcy, hOt, hG, hGp⟩ := GlobalTheory.T.flag_bundle_curvature_at_point k B Y q p d hB hY π w E h H flB fl hfl σ v hv y
      obtain ⟨N, hN, hzN, hNO, C, hC, hle⟩ :=
        GlobalTheory.T.local_density_bound_near_point d O (fun _ => 1) G s (c.e y) hO hcy continuousOn_const hG fun z hz => (hGp z hz).1
      obtain ⟨K, hK, hyK, hKN⟩ := exists_compact_subset hN hzN
      have hF := GlobalTheory.LineCos.continuousOn_cosSq s hG fun z hz => (hGp z hz).1
      have hKO : K ⊆ O := hKN.trans hNO
      have hKt : K ⊆ c.e.target := hKO.trans hOt
      have hle' : Measure.map (fun z => GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base z)) (GlobalTheory.LineCos.fib z))
          (volume.restrict K) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
        refine le_trans ?_ hle
        simp only [ENNReal.ofReal_one]
        rw [show (fun _ : ReciprocityTheory.L2DbarEstimates.V (d + 1) => (1 : ENNReal)) = 1 from rfl, withDensity_one]
        exact Measure.map_mono_of_aemeasurable (Measure.restrict_mono hKN le_rfl)
          ((hF.mono hNO).aemeasurable hN.measurableSet)
      have hD : ContinuousOn (fun z => ((ε : ℤ) : ℝ) * (hY.atlas σ).reDens Φ c z) K :=
        (continuousOn_const.mul ((hY.atlas σ).continuousOn_reDens hΦ c)).mono hKt
      have hz0 : ∀ z ∈ K, GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base z)) (GlobalTheory.LineCos.fib z) = 1 →
          ((ε : ℤ) : ℝ) * (hY.atlas σ).reDens Φ c z = 0 := by
        intro z hz h1
        have hzt : z ∈ ((hY.atlas σ).e c).target := hKt hz
        have := h0 ⟨(c, ((hY.atlas σ).e c).symm z), ((hY.atlas σ).e c).map_target hzt⟩
          (((hGp z (hKO hz)).2).trans h1)
        simp only [HolAtlas.reDens, HolAtlas.loc, dif_pos hzt, this, Complex.zero_re, mul_zero]
      have hlim := GlobalTheory.T.tendsto_lintegral_poisson_kernel_boundary _ volume K _ _ C hK (hF.mono hKO) hD hz0 hC hle'
      refine ⟨((hY.atlas σ).e c).source ∩ (hY.atlas σ).e c ⁻¹' interior K,
        ((hY.atlas σ).e c).isOpen_inter_preimage isOpen_interior, ⟨hy, hyK⟩, ?_⟩
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun t => zero_le) fun t => ?_
      beta_reduce
      rw [part_fn_mul_chart (hY.atlas σ) _ hΦ ε c isOpen_interior (interior_subset.trans hKt)]
      refine le_trans (le_of_eq ?_) (lintegral_mono_set interior_subset)
      refine setLIntegral_congr_fun isOpen_interior.measurableSet fun z hz => ?_
      have := (hGp z (hKO (interior_subset hz))).2
      beta_reduce
      rw [← this]
      rfl
    choose W hWo hyW hW using loc
    obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover W hWo fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩
    have hs := tendsto_finset_sum T fun y _ => hW y
    rw [Finset.sum_const_zero] at hs
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun t => zero_le)
      fun t => (measure_mono hT).trans (measure_biUnion_finset_le T _)
  have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (main 1)
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (main (-1))
  have := h1.sub h2
  rw [ENNReal.toReal_zero, sub_zero] at this
  exact this

end GlobalTheory.LineCos
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_chern_integral_rank_two : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ Φ : (hY.atlas σ).Fld, (hY.atlas σ).IsForm Φ → (∀ x : (hY.atlas σ).Pt, v x.pt = 1 → dens (Φ x) = 0) →
      Filter.Tendsto (fun t : ℝ => (hY.atlas σ).integral ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) * Φ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  atlas_forward_decl GlobalTheory.LineCos.tendsto_integral_kernel_mul
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineMeet

open Filter Topology Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.Points
open scoped ContDiff ComplexOrder

theorem pull_ofValues {n m : ℕ} (L : V n →L[ℂ] V m) {α : V m → V m → ℂ} (hα : IsSesq α) :
    pull L (ofValues α : Alt m) = ofValues (fun ξ η => α (L ξ) (L η)) := by
  simp only [ofValues, GlobalTheory.LineForm.OmReal.sesq_expand hα (L _), AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul,
    sym, map_sum, map_smul, map_mul, (pull_dz L _).1, (pull_dz L _).2, Finset.sum_mul, Finset.mul_sum, Finset.sum_smul,
    Finset.smul_sum, smul_mul_smul_comm, smul_smul]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, c, 2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]

theorem form_submatrix {r r' : Type} [Fintype r] [Fintype r'] (e : r' ≃ r) (M : Matrix r r ℂ) (u u' : r → ℂ) :
    form (M.submatrix e e) (u ∘ e) (u' ∘ e) = form M u u' := by
  simp only [form_eq_sum, submatrix_apply, Function.comp_apply]
  rw [← e.sum_comp]
  exact Finset.sum_congr rfl fun a _ => by rw [← e.sum_comp]

theorem ddc_fn_apply {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {f : M → ℝ}
    (hf : A.SmoothOn Set.univ fun y => (f y : ℂ)) (x : A.Pt) :
    A.ddc (A.fn f) x = ofValues (ddc (fun v => f (x.ch.symm v)) x.crd) := by
  have hn : x.ch.target ∈ 𝓝 x.crd := x.ch.open_target.mem_nhds (x.ch.map_source x.2)
  have h1 := Complex.reCLM.contDiff.comp_contDiffOn (hf x.1.1)
  have h2 : ContDiffOn ℝ ∞ (fun v => f (x.ch.symm v)) x.ch.target :=
    (h1.mono fun v hv => ⟨hv, trivial⟩).congr fun v _ => by simp
  rw [← delAt_dbarAt_fun ((h2.contDiffAt hn).of_le (by norm_cast))]
  refine GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq A _ x _ ?_
  filter_upwards [hn] with v hv
  rw [HolAtlas.loc, dif_pos hv]
  rfl

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {D D' : ℕ}

theorem gram_and_cos {π : Y ⟶ B} {w : π ≫ q = p} {E : B.Modules} (h : VMetric q E 2) {flB : Vert.Flag E 2}
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2} {σ : k →+* ℂ} {v : CxPts p σ → ℝ}
    (hv : GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v)
    (a : VBExt.AdaptedChart (lineSC fl) 1 1) (b : VBExt.AdaptedChart (lineSC flB) 1 1) {y : CxPts p σ}
    (ha : y ∈ ptsIn p σ a.U) (hb : PtsOver.map π w _ y ∈ ptsIn q σ b.U)
    {A K : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ}
    (hA : A = ((((b.mid (lineSC_shortExact flB)).pull (h.met σ).isVB π).tr p σ (a.mid (lineSC_shortExact fl)) y).submatrix
      finSumFinEquiv finSumFinEquiv))
    (hK : K = (h.met σ).gram b.frame (PtsOver.map π w _ y)) :
    ((h.pull π w).met σ).gram a.frame y = chg A K ∧
      ‖form K (Pi.single (Sum.inl 0) 1) (fun i => A i (Sum.inl 0))‖ ^ 2 =
        v y * (chg A K (Sum.inl 0) (Sum.inl 0)).re * (K (Sum.inl 0) (Sum.inl 0)).re := by
  have hS := lineSC_shortExact flB
  have hS' := lineSC_shortExact fl
  set m := (h.pull π w).met σ with hm
  let c : Chart E 2 := b.mid hS
  let c' : Chart ((Scheme.Modules.pullback π).obj E) 2 := c.pull (h.met σ).isVB π
  have hc' : y ∈ ptsIn p σ c'.U := hb
  have hG : m.G c' y = (h.met σ).G c (PtsOver.map π w _ y) := (h.met σ).pull_G π w c hb
  have hK' : K = (m.G c' y).submatrix (finSumFinEquiv (m := 1) (n := 1)) (finSumFinEquiv (m := 1) (n := 1)) := by
    rw [hG, hK]
    exact Met.gram_frame (S := lineSC flB) (r := 1) (s := 1) (h.met σ) hS b hb
  have e₁ : m.gram a.frame y = chg A K := by
    rw [hK', hA, chg_submatrix]
    refine (Met.gram_frame (S := lineSC fl) (r := 1) (s := 1) m hS' a ha).trans ?_
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M.submatrix (finSumFinEquiv (m := 1) (n := 1))
      (finSumFinEquiv (m := 1) (n := 1))) (m.trans c' (a.mid hS') y hc')
  refine ⟨e₁, ?_⟩
  have hy : y ∈ ptsIn p σ (a.U ⊓ π ⁻¹ᵁ b.U) := mem_ptsIn_inf.2 ⟨ha, hb⟩
  have key := hv (a.U ⊓ π ⁻¹ᵁ b.U) (Twist.resM _ inf_le_left (a.e 0))
    (QCoh.pullbackSections π _ inf_le_right (b.e 0)) y hy
  rw [QCoh.pullback_map_app_pullbackSections, Twist.app_resM, m.form_resM _ _ _ hy] at key
  have e₂ : m.form (QCoh.pullbackSections π E (inf_le_right : a.U ⊓ π ⁻¹ᵁ b.U ≤ _) ((flB.ι 1).app b.U (b.e 0)))
      (QCoh.pullbackSections π E (inf_le_right : a.U ⊓ π ⁻¹ᵁ b.U ≤ _) ((flB.ι 1).app b.U (b.e 0))) y =
      K (Sum.inl 0) (Sum.inl 0) := by
    rw [hK]
    exact (h.met σ).form_pull π w _ _ _ hy
  have e₃ : m.form ((fl.ι 1).app a.U (a.e 0)) ((fl.ι 1).app a.U (a.e 0)) y = chg A K (Sum.inl 0) (Sum.inl 0) := by
    rw [← e₁]; rfl
  have e₄ : m.form (QCoh.pullbackSections π E (inf_le_right : a.U ⊓ π ⁻¹ᵁ b.U ≤ _) ((flB.ι 1).app b.U (b.e 0)))
      (Twist.resM _ (inf_le_left : a.U ⊓ π ⁻¹ᵁ b.U ≤ _) ((fl.ι 1).app a.U (a.e 0))) y =
      form K (Pi.single (Sum.inl 0) 1) (fun i => A i (Sum.inl 0)) := by
    rw [m.form_eq c' hc' _ _ hy, Chart.crd_pull c _ π w _ _ hy hb, Chart.crd_resM _ _ _ hy, hK',
      ← form_submatrix (finSumFinEquiv (m := 1) (n := 1))]
    congr 1
    · funext i
      refine (b.crd_frame hS hb i (.inl 0)).trans ?_
      simp [Pi.single_apply, one_apply]
    · funext i
      rw [hA]
      simp [Chart.tr, VBExt.AdaptedChart.mid, VBExt.AdaptedChart.frame, c', c, -finSumFinEquiv_apply_left]
  rw [e₂, e₃, e₄] at key
  exact key

theorem ddc_mul_omF_sub (hB : IsRegVar q D) (hY : IsRegVar p D') {π : Y ⟶ B} {w : π ≫ q = p} {E : B.Modules}
    {h : VMetric q E 2} (H : h.IsCInf) {flB : Vert.Flag E 2}
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2} {σ : k →+* ℂ} {v : CxPts p σ → ℝ}
    (hv : GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v)
    (hs : (hY.atlas σ).SmoothOn Set.univ fun y => ((1 - v y : ℝ) : ℂ)) (x : (hY.atlas σ).Pt) (hx1 : v x.pt = 1) :
    (hY.atlas σ).ddc ((hY.atlas σ).fn fun y => 1 - v y) x *
      ((omF hY σ (h.pull π w) fl x : Alt D') - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) x) = 0 := by
  have hS := lineSC_shortExact flB
  have hS' := lineSC_shortExact fl
  set f : CxPts p σ → CxPts q σ := PtsOver.map π w _ with hf
  have hm : ∀ z, (f z).1 = z.1 ≫ π := fun _ => rfl
  let x' : (hB.atlas σ).Pt := ⟨(_, f x.pt), ((hB.atlas σ).cover (f x.pt)).choose_spec⟩
  let a := frameAt fl x.pt
  let b := frameAt flB (f x.pt)
  have ha : x.pt ∈ ptsIn p σ a.U := mem_frameAt fl x.pt
  have hb : f x.pt ∈ ptsIn q σ b.U := mem_frameAt flB (f x.pt)
  let c' : Chart ((Scheme.Modules.pullback π).obj E) 2 := (b.mid hS).pull (h.met σ).isVB π
  have hc' : x.pt ∈ ptsIn p σ c'.U := hb
  let φ := x'.ch ∘ f ∘ x.ch.symm
  let G : V D → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := fun u => (h.met σ).gram b.frame (x'.ch.symm u)
  let A : V D' → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := fun u =>
    (c'.tr p σ (a.mid hS') (x.ch.symm u)).submatrix (finSumFinEquiv (m := 1) (n := 1)) (finSumFinEquiv (m := 1) (n := 1))
  have e : x.ch.symm x.crd = x.pt := x.ch.left_inv x.2
  have ho := ChartGlue.isOpen_over x.ch (x'.ch.open_source.preimage (continuous_of_comp hm))
  have hx := ho.mem_nhds (ChartGlue.mem_over x.ch x.2 (show x.pt ∈ f ⁻¹' x'.ch.source from x'.2))
  have hφ : AnalyticAt ℂ φ x.crd :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (AlgChart.holo_map hm x.1.1 x'.1.1) hx
  have hφx : φ x.crd = x'.crd := congrArg (fun z => x'.ch (f z)) e
  have hG : MContDiffAt ∞ G (φ x.crd) := by
    rw [hφx]; exact ((H σ).gram b.frame hb).mContDiffAt x'.1.1 x'.2
  have hGp : ∀ᶠ u in 𝓝 (φ x.crd), (G u).PosDef := by
    rw [hφx]; exact Met.eventually_posDef (S := lineSC flB) (r := 1) (s := 1) (h.met σ) hS b x'.1.1 x'.2 hb
  have hG1 : MContDiffAt 1 G (φ x.crd) := hG.of_le (by norm_cast)
  have e₁ : pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) x = ofValues (extTrace (fun u => G (φ u)) x.crd) := by
    change pull (fderiv ℂ φ x.crd) (ofValues (extTrace G x'.crd) : Alt D) = _
    rw [← hφx, pull_ofValues _ (OmReal.isSesq_extTrace hG1 hGp)]
    refine congrArg (fun α : V D' → V D' → ℂ => (ofValues α : Alt D')) (funext fun ξ => funext fun η => ?_)
    rw [extTrace_comp_holo hG1 hGp hφ.contDiffAt]
  have hloc : ∀ᶠ u in 𝓝 x.crd, ((h.pull π w).met σ).gram a.frame (x.ch.symm u) = chg (A u) (G (φ u)) ∧
      ‖form (G (φ u)) (Pi.single (Sum.inl 0) 1) (fun i => A u i (Sum.inl 0))‖ ^ 2 =
        v (x.ch.symm u) * (chg (A u) (G (φ u)) (Sum.inl 0) (Sum.inl 0)).re * (G (φ u) (Sum.inl 0) (Sum.inl 0)).re := by
    filter_upwards [hx, (ChartGlue.isOpen_over x.ch (isOpen_ptsIn a.U)).mem_nhds (ChartGlue.mem_over x.ch x.2 ha),
      (ChartGlue.isOpen_over x.ch (isOpen_ptsIn c'.U)).mem_nhds (ChartGlue.mem_over x.ch x.2 hc')] with u h₁ h₂ h₃
    exact gram_and_cos h hv a b h₂.2 h₃.2 rfl (congrArg ((h.met σ).gram b.frame) (x'.ch.left_inv h₁.2))
  have e₂ : (omF hY σ (h.pull π w) fl x : Alt D') = ofValues (extTrace (fun u => chg (A u) (G (φ u))) x.crd) := by
    rw [← extTrace_congr (hloc.mono fun u hu => hu.1)]
    rfl
  rw [e₁, e₂, ddc_fn_apply _ hs]
  refine GlobalTheory.T.hermitian_frame_form_norm_sq_eq D' (fun u => G (φ u)) A (fun u => v (x.ch.symm u)) x.crd
    (fun i j => ((hG i j).of_le (by norm_cast)).comp x.crd (hφ.contDiffAt.restrict_scalars ℝ))
    (hφ.continuousAt.eventually hGp) (fun i j => ?_) ?_ (by rw [e, hx1]) (hloc.mono fun u hu => hu.2)
  · exact GlobalTheory.SCV.analyticAt_of_differentiableOn (AlgChart.holo x.1.1 _ _)
      ((ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds
        (ChartGlue.mem_over x.ch x.2 (mem_ptsIn_inf.2 ⟨ha, hc'⟩)))
  · simp only [A, det_submatrix_equiv_self, e]
    exact (isUnit_iff_isUnit_det _).1 (c'.isUnit_tr (a.mid hS') hc' ha)

theorem tendsto_integral_conc : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ K : MvPolynomial (Fin 5) ℝ, Filter.Tendsto (fun t : ℝ => (hY.atlas σ).integral ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) *
      ((hY.atlas σ).ddc ((hY.atlas σ).fn (fun y => 1 - v y)) + ((hY.atlas σ).fn (fun y => 1 - v y)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 4 - X 0)) * (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (K) * (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)))))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv K
  obtain ⟨-, -, hsm⟩ := GlobalTheory.CosSqSmooth.cosSq_smooth k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hs : (hY.atlas σ).SmoothOn Set.univ fun y => ((1 - v y : ℝ) : ℂ) := fun i =>
    ((contDiffOn_const (c := (1 : ℂ))).sub (hsm i)).congr fun u _ => by simp
  obtain ⟨-, halg, -, hev, -⟩ := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hY.atlas σ)
  obtain ⟨hc1, hom, -⟩ := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  obtain ⟨-, homB, hpl⟩ := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  have hf := (hY.atlas σ).isForm_fn hs
  have hP (P : MvPolynomial (Fin 5) ℝ) := (hev _ (fun i => c1F hY σ (fam5 π w H flB fl A i)) P
    fun i => (hc1 _ (fam5 π w H flB fl A i)).1.1).1
  have hdb := (halg 0 _ _ hf hf).2.2.2.2.1
  have hdd := (halg 0 _ _ hdb hdb).2.2.2.1
  have hddc : (hY.atlas σ).IsForm ((hY.atlas σ).ddc ((hY.atlas σ).fn fun y => 1 - v y)) :=
    (halg kappa _ _ hdd hdd).2.2.1
  have h₁ := (hom _ (h.pull π w) (H.pull π w) fl fl).1.1
  have h₂ : (hY.atlas σ).IsForm (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) :=
    ((((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _ (hpl Y p _ hY π w).1).2 0 _ 0).2.2.2
      (homB E h H flB flB).1.1).1
  have h₃ : (hY.atlas σ).IsForm (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) -
      pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (pullF hB hY σ π w _)]
    exact (halg 0 _ _ h₁ (halg (-1) _ _ h₂ h₂).2.2.1).1
  simp only [mul_assoc ((hY.atlas σ).fn fun y => _ / (1 - v y + _) ^ 2)]
  refine GlobalTheory.T.flag_bundle_chern_integral_rank_two k B Y q p d hB hY π w E h H flB fl hfl A σ v hv _
    (halg 0 _ _ (halg 0 _ _ hddc (halg 0 _ _ hf (hP _)).2.1).1 (halg 0 _ _ (hP K) h₃).2.1).2.1 fun x hx => ?_
  have key := ddc_mul_omF_sub hB hY H hv hs x hx
  have hz : (hY.atlas σ).fn (fun y => 1 - v y) x = 0 := by simp [HolAtlas.fn, hx]
  have hc : ∀ β : Alt (d + 1), β * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) K x =
      evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) K x * β := fun β =>
    Subalgebra.mem_center_iff.1 (Subtype.property _) β
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, hz, zero_mul, add_zero]
  rw [← mul_assoc, hc, mul_assoc]
  erw [key]
  simp [dens]

end GlobalTheory.LineMeet
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_limit : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ K : MvPolynomial (Fin 5) ℝ, Filter.Tendsto (fun t : ℝ => (hY.atlas σ).integral ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) *
      ((hY.atlas σ).ddc ((hY.atlas σ).fn (fun y => 1 - v y)) + ((hY.atlas σ).fn (fun y => 1 - v y)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 4 - X 0)) * (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (K) * (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)))))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  atlas_forward_decl GlobalTheory.LineMeet.tendsto_integral_conc
end
