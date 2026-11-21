import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.PhiIndep
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.UnipBEqUnipotent
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.LeviTransposeDistributions.BoundOneTwo
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.DetUpdateRowOneLast

section
noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory PositivityTheory.PfBern.Unit

namespace PositivityTheory.RgUd.AB.Pf

section Faith

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
  {B₀ : Sesq V} (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re)

theorem formD_faithful [ρ.IsIrreducible] (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w)
    (Pr : (G → ℂ) →ₗ[ℂ] testFn G) (hPr : ∀ f : testFn G, Pr f = f) (C : Sesq V)
    (h : ∀ f ∈ testFn G, formD μ hρ hpos hinv Pr C f = 0) : C = 0 := by
  refine LinearMap.ext fun v => LinearMap.ext fun u => ?_
  rw [LinearMap.zero_apply, LinearMap.zero_apply]
  by_cases hv0 : v = 0
  · rw [hv0, map_zero, LinearMap.zero_apply]
  by_cases hu0 : u = 0
  · rw [hu0, map_zero]
  have hU : (stabilizerOf ρ v : Set G) ∩ (stabilizerOf ρ u : Set G) ∈ nhds (1 : G) :=
    Filter.inter_mem ((hρ.1 v).mem_nhds (one_mem _)) ((hρ.1 u).mem_nhds (one_mem _))
  obtain ⟨K, hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hU
  have hKo : IsOpen ((K : Subgroup G) : Set G) := K.isOpen
  have := hρ.2 (K : Subgroup G) hKc hKo
  have hvW : v ∈ fixedVectors ρ (K : Subgroup G) := by
    rw [mem_fixedVectors]; intro x hx; exact (hKU hx).1
  have huW : u ∈ fixedVectors ρ (K : Subgroup G) := by
    rw [mem_fixedVectors]; intro x hx; exact (hKU hx).2
  have hW : fixedVectors ρ (K : Subgroup G) ≠ ⊥ := fun hb => hv0 (by
    have := hvW; rw [hb] at this; exact (Submodule.mem_bot ℂ).1 this)
  set W := fixedVectors ρ (K : Subgroup G)
  let vW : W := ⟨v, hvW⟩
  let uW : W := ⟨u, huW⟩
  let φ : W →ₗ[ℂ] ℂ := (B₀.flip u : V →ₗ[ℂ] ℂ) ∘ₗ W.subtype
  let A : Module.End ℂ W := φ.smulRight vW
  obtain ⟨r, hr⟩ := level_density (μ := μ) hKc hKo hρ.1 hW A
  let rf : locallyConstantCompactSupport G ℂ ℂ := (r : HeckeAlgebra μ)
  have hbi : BiInv (K : Subgroup G) (rf : G → ℂ) := fun κ hκ x => (HeckeAlgebraLevel.val_mem hKc hKo r) κ hκ x
  have hf := h rf rf.2
  rw [formD_apply, hPr rf] at hf
  change DF μ hρ hpos C rf = 0 at hf
  rw [DF_eq μ hρ hpos hinv C _ hKc hKo hbi] at hf
  have hres : ∀ x : W, resA μ hρ (K : Subgroup G) rf x = B₀ x u • v := by
    intro x
    have e := congrArg (fun T : Module.End ℂ W => (T x : V)) hr
    rw [← show ((levelLin hKc hKo ρ r x : W) : V) = resA μ hρ (K : Subgroup G) rf x from rfl, e]
    rfl
  have huu : (B₀ u u) ≠ 0 := fun e => by
    have := hpos u hu0
    rw [e] at this
    simp at this
  set N := rN μ hρ hpos hKc hKo C rf with hN
  have sN := rN_spec μ hρ hpos hKc hKo C rf
  let m : W := (B₀ u u)⁻¹ • N uW
  have hm : ∀ y : W, B₀ (m : V) y = C v y := by
    intro y
    have := sN uW y
    rw [hres] at this
    show B₀ ((B₀ u u)⁻¹ • (N uW : V)) y = C v y
    rw [map_smul, LinearMap.smul_apply, this, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ huu, one_mul]
  have hNe : N = φ.smulRight m := by
    refine riesz_unique hpos sN fun x y => ?_
    show B₀ ((φ x) • (m : V)) y = C (resA μ hρ (K : Subgroup G) rf x) y
    rw [hres, map_smul, LinearMap.smul_apply, hm, map_smul, LinearMap.smul_apply]
    rfl
  unfold DK at hf
  rw [← hN, hNe, LinearMap.trace_smulRight] at hf
  have : φ m = C v u := hm uW
  rw [← this]
  exact hf

end Faith

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem formTraceDistrGL : FormTraceDistrGL k := by
  intro n V _ _ π hadm hirr ⟨B₀, _, h2, h3⟩
  borelize (GL (Fin (n + 1)) k)
  have := hirr
  have := GroundTheory.Automorphic.Measures.isMulRightInvariant_GL k (n + 1) (Measure.haar : Measure (GL (Fin (n + 1)) k))
  obtain ⟨Pr, hPr⟩ := exists_testProj (G := GL (Fin (n + 1)) k)
  exact ⟨formD Measure.haar hadm h2 h3 Pr, fun g B f hf => formD_equiv Measure.haar hadm h2 h3 Pr hPr g B f hf,
    fun B hB => formD_faithful Measure.haar hadm h2 h3 Pr hPr B hB⟩

theorem theoremA_of_thmA (hA : PositivityTheory.RgUd.ThmA k) : TheoremA k := by
  intro n D hD g f hf
  have hf' : f ∈ supportedIn (Set.univ : Set (GL (Fin (n + 1)) k)) := ⟨hf, Set.subset_univ _⟩
  have hP : ∀ p ∈ GlobalTheory.BZMir.Mir k n, ∀ f ∈ supportedIn (Set.univ : Set (GL (Fin (n + 1)) k)),
      D (fun x => f (p * x * p⁻¹)) = D f := by
    intro p hp f hf
    have := hD p⁻¹ ((GlobalTheory.BZMir.Mir k n).inv_mem hp) f hf.1
    have e : conjFn p⁻¹ f = fun x => f (p * x * p⁻¹) := by
      funext x; unfold conjFn; rw [inv_inv]
    rw [← e]; exact this
  have := hA n D hP g⁻¹ f hf'
  have e : conjFn g f = fun x => f (g⁻¹ * x * g⁻¹⁻¹) := by
    funext x; unfold conjFn; rw [inv_inv]
  rw [e]; exact this

theorem thmB_of_kirillov (hK : KirillovForm k) : PositivityTheory.RgUd.ThmB k := by
  intro n V _ _ π hs hirr B hB β hβ
  have hadm : GroundTheory.Automorphic.IsAdmissible π :=
    (PositivityTheory.rg.gu.whit.isAdmissible_iff π).1 (PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k (n + 1) V π hs hirr)
  obtain ⟨c, hc⟩ := hK n V π B hadm hirr hB.1 hB.2.1 hB.2.2 β hβ
  exact ⟨c, fun v w => by rw [hc]; rfl⟩

theorem thmB (hA : PositivityTheory.RgUd.ThmA k) : PositivityTheory.RgUd.ThmB k :=
  thmB_of_kirillov k (kirillovForm_of_theoremA' k (theoremA_of_thmA k hA) (formTraceDistrGL k))

end PositivityTheory.RgUd.AB.Pf
end
end

section
noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def pfTrGL {n : ℕ} (h : GL (Fin (n + 1)) k) : GL (Fin (n + 1)) k :=
  ⟨(h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ, ((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one],
    by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_pfTrGL {n : ℕ} (h : GL (Fin (n + 1)) k) :
    GeneralLinearGroup.det (pfTrGL h) = GeneralLinearGroup.det h := by
  apply Units.ext
  simp [pfTrGL, GeneralLinearGroup.val_det_apply, det_transpose]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem transpose_mulVec_dotProduct_inv_mulVec {n : ℕ} (h : GL (Fin (n + 1)) k) (x z : Vc k n) :
    ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ x) ⬝ᵥ
        (((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ z) = x ⬝ᵥ z := by
  rw [mulVec_transpose, dotProduct_mulVec, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    vecMul_one]

variable (k) in
theorem pfAct : PfAct k := by
  intro mk bs ν hν ψ c hc n F hF h
  funext z
  have key := integral_comp_mulVec_eq_smul ν (pfTrGL h)
    (fun u => F (cj h⁻¹ z.1, u) * ((ψ (u ⬝ᵥ (((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ z.2)) : Circle) : ℂ))
  have hv : ((pfTrGL h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ := rfl
  simp only [hv, transpose_mulVec_dotProduct_inv_mulVec, det_pfTrGL] at key
  simp only [GlobalTheory.SplitDict.pf]
  rw [key, Complex.real_smul, Complex.ofReal_inv]

end PositivityTheory.RgUd.AB.Pf
end
end

section
noncomputable section

open Matrix GlobalTheory.SplitWeil GlobalTheory.BZMir GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in

def cutL {n : ℕ} (U : Set k) : (Mx k n → ℂ) →ₗ[ℂ] (GL (Fin (n + 1)) k → ℂ) where
  toFun ψ x := if (x.val).det ∈ U then ψ x.val else 0
  map_add' ψ₁ ψ₂ := funext fun x => by
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c ψ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
open Classical in
theorem cutL_apply {n : ℕ} (U : Set k) (ψ : Mx k n → ℂ) (x : GL (Fin (n + 1)) k) :
    cutL U ψ x = if (x.val).det ∈ U then ψ x.val else 0 := by
  classical
  rfl

theorem mem_SB_iff_supportedIn {X : Type} [TopologicalSpace X] (f : X → ℂ) :
    f ∈ SB X ↔ f ∈ supportedIn (Set.univ : Set X) := by
  constructor
  · intro h
    exact ⟨h, Set.subset_univ _⟩
  · intro h
    exact h.1

theorem cutL_mem {n : ℕ} (U : Set k) (hU : IsClopen U) (h0 : (0 : k) ∉ U) {ψ : Mx k n → ℂ}
    (hψ : ψ ∈ SB (Mx k n)) : cutL U ψ ∈ SB (GL (Fin (n + 1)) k) := by
  have h := PositivityTheory.PfBern.cocyclesToWachVectorsExponent.cutFun_mem U hU h0 ⟨ψ, hψ⟩
  convert h using 1
  funext x
  rw [cutL_apply]
  simp only [PositivityTheory.PfBern.cocyclesToWachVectorsExponent.cutFun]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_cj {n : ℕ} (p x : GL (Fin (n + 1)) k) :
    ((p * x * p⁻¹ : GL (Fin (n + 1)) k).val).det = (x.val).det := by
  simp only [Units.val_mul, Matrix.det_mul]
  rw [mul_right_comm, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.det_one, one_mul]

theorem cutL_cj {n : ℕ} (U : Set k) (p : GL (Fin (n + 1)) k) (ψ : Mx k n → ℂ) :
    cutL U (ψ ∘ cj p) = fun x => cutL U ψ (p * x * p⁻¹) := by
  funext x
  rw [cutL_apply, cutL_apply, det_cj]
  rfl

end PositivityTheory.RgUd.AB.Pf

namespace PositivityTheory.RgUd.AB.Pf

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thmA_of_core : CoreX k → ThmT k → ThmA k := by
  intro hC hT n Λ hP p f hf
  classical
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf.1
  let φ : SB (GL (Fin (n + 1)) k) := ⟨f, hf'⟩
  let ψ : SB (Mx k n) := ⟨PositivityTheory.PfBern.cocyclesToWachVectorsExponent.extZ φ, PositivityTheory.PfBern.cocyclesToWachVectorsExponent.extZ_mem φ⟩
  have hdet : Continuous fun x : GL (Fin (n + 1)) k => (x.val).det :=
    (continuous_id.matrix_det).comp Units.continuous_val
  obtain ⟨U, hU, hCU, h0⟩ := PositivityTheory.PfBern.cocyclesToWachVectorsExponent.exists_clopen_local
    ((fun x : GL (Fin (n + 1)) k => (x.val).det) '' tsupport f)
    (hf'.2.isCompact.image hdet)
    (by
      rintro ⟨x, -, hx⟩
      exact ((Matrix.isUnit_iff_isUnit_det _).mp x.isUnit).ne_zero hx)
  have hfeq : cutL U ψ.1 = f := by
    funext x
    rw [cutL_apply]
    split_ifs with h
    · exact PositivityTheory.PfBern.cocyclesToWachVectorsExponent.extZ_val φ x
    · symm
      by_contra hne
      exact h (hCU ⟨x, subset_tsupport _ hne, rfl⟩)
  let Λ' : (Mx k n → ℂ) →ₗ[ℂ] ℂ := Λ ∘ₗ cutL U
  have hPX : PInvX Λ' := by
    intro q hq g hg
    show Λ (cutL U (g ∘ cj q)) = Λ (cutL U g)
    rw [cutL_cj]
    exact hP q hq _ ((mem_SB_iff_supportedIn _).mp (cutL_mem U hU h0 hg))
  have hGX := hC hT n Λ' hPX p ψ.1 ψ.2
  have e1 : (fun g => f (p * g * p⁻¹)) = cutL U (ψ.1 ∘ cj p) := by
    rw [cutL_cj, hfeq]
  have e2 : Λ (cutL U (ψ.1 ∘ cj p)) = Λ (cutL U ψ.1) := hGX
  rw [e1, e2, hfeq]

end PositivityTheory.RgUd.AB.Pf
end
end

section
noncomputable section

open Matrix Topology Filter GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.BZMir

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

namespace Near

theorem cj_mul (g h : GL (Fin (n + 1)) k) (x : Mx k n) : cj (g * h) x = cj g (cj h x) := by
  simp only [cj, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem inv_cj (g : GL (Fin (n + 1)) k) (x : Mx k n) :
    ((g⁻¹ : GL (Fin (n + 1)) k) : Mx k n) * cj g x * (g : Mx k n) = x := by
  simp only [cj, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ _ (g : Mx k n)]
  simp [← Units.val_mul, Matrix.mul_assoc]

theorem eventually_conj {f : Mx k n → ℂ} (hf : f ∈ SB (Mx k n)) :
    ∀ᶠ AB : Mx k n × Mx k n in 𝓝 (1, 1), ∀ y ∈ tsupport f, f (AB.1 * y * AB.2) = f y := by
  obtain ⟨hlc, hcs⟩ := hf
  apply hcs.eventually_forall_of_forall_eventually
  intro y _
  have hc : Continuous fun z : (Mx k n × Mx k n) × Mx k n => z.1.1 * z.2 * z.1.2 :=
    ((continuous_fst.fst).matrix_mul continuous_snd).matrix_mul continuous_fst.snd
  have h1 := (hlc.comp_continuous hc).eventually_eq (((1 : Mx k n), (1 : Mx k n)), y)
  have h2 := (hlc.comp_continuous continuous_snd).eventually_eq (((1 : Mx k n), (1 : Mx k n)), y)
  filter_upwards [h1, h2] with z hz1 hz2
  simp only [Function.comp_apply] at hz1 hz2
  rw [hz1, hz2]
  simp

def rE (w : Vc k n) : Mx k n := vecMulVec (eN k n) (w - eN k n)

theorem rE_mul (w : Vc k n) : rE w * rE w = (w (Fin.last n) - 1) • rE w := by
  unfold rE
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have hd : (w - eN k n) ⬝ᵥ eN k n = w (Fin.last n) - 1 := by
    simp [eN, dotProduct_single]
  rw [hd]
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

def sw (w : Vc k n) (hw : w (Fin.last n) ≠ 0) : GL (Fin (n + 1)) k :=
  ⟨1 + rE w, 1 - (w (Fin.last n))⁻¹ • rE w, by
    have hc : (w (Fin.last n))⁻¹ * (w (Fin.last n) - 1) = 1 - (w (Fin.last n))⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hw, mul_one]
    rw [add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, rE_mul,
      smul_smul, hc, sub_smul, one_smul]
    abel, by
    have hc : (w (Fin.last n))⁻¹ * (w (Fin.last n) - 1) = 1 - (w (Fin.last n))⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hw, mul_one]
    rw [sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_one, rE_mul, smul_add, smul_smul, hc,
      sub_smul, one_smul]
    abel⟩

theorem sw_val (w : Vc k n) (hw : w (Fin.last n) ≠ 0) : ((sw w hw : GL (Fin (n + 1)) k) : Mx k n) = 1 + rE w := rfl

theorem sw_last (w : Vc k n) (hw : w (Fin.last n) ≠ 0) (j : Fin (n + 1)) :
    ((sw w hw : GL (Fin (n + 1)) k) : Mx k n) (Fin.last n) j = w j := by
  rw [sw_val]
  by_cases h : j = Fin.last n
  · subst h
    simp [rE, eN, vecMulVec]
  · have h' : Fin.last n ≠ j := fun e => h e.symm
    simp [rE, eN, vecMulVec, Matrix.one_apply, h, h']

end Near

private theorem conj_of_pair_lemma {f : Mx k n → ℂ} (g : GL (Fin (n + 1)) k)
    (h1 : ∀ y ∈ tsupport f, f ((g : Mx k n) * y * ((g⁻¹ : GL (Fin (n + 1)) k) : Mx k n)) = f y)
    (h2 : ∀ y ∈ tsupport f, f (((g⁻¹ : GL (Fin (n + 1)) k) : Mx k n) * y * (g : Mx k n)) = f y) :
    ∀ x, f (cj g x) = f x := by
  intro x
  by_cases hx : x ∈ tsupport f
  · exact h1 x hx
  · have hx0 : f x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hx0]
    by_contra hne
    have hy : cj g x ∈ tsupport f := subset_tsupport f hne
    have := h2 _ hy
    rw [Near.inv_cj] at this
    exact hne (this.symm.trans hx0)

private theorem near_lemma_2 {f : Mx k n → ℂ} (hf : f ∈ SB (Mx k n)) :
    ∀ᶠ w : Vc k n in 𝓝 (eN k n), ∀ hw : w (Fin.last n) ≠ 0,
      ∀ x, f (cj (Near.sw w hw)⁻¹ x) = f x := by
  have hr : Continuous (fun w : Vc k n => Near.rE w) := by
    refine continuous_matrix fun i j => ?_
    simp only [Near.rE, vecMulVec_apply]
    exact continuous_const.mul (((continuous_apply j).sub continuous_const))
  have h0 : Near.rE (eN k n) = 0 := by simp [Near.rE]
  have hi : Tendsto (fun w : Vc k n => (w (Fin.last n))⁻¹) (𝓝 (eN k n))
      (𝓝 ((eN k n (Fin.last n))⁻¹)) :=
    ((continuous_apply (Fin.last n)).tendsto _).inv₀ (by simp [eN])
  have hA : Tendsto (fun w : Vc k n => (1 : Mx k n) - (w (Fin.last n))⁻¹ • Near.rE w) (𝓝 (eN k n)) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : Mx k n))).sub (hi.smul (hr.tendsto (eN k n)))
    simpa [h0] using this
  have hB : Tendsto (fun w : Vc k n => (1 : Mx k n) + Near.rE w) (𝓝 (eN k n)) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : Mx k n))).add (hr.tendsto (eN k n))
    simpa [h0] using this
  have hS := Near.eventually_conj hf
  filter_upwards [(hA.prodMk_nhds hB).eventually hS, (hB.prodMk_nhds hA).eventually hS] with w h1 h2 hw
  have eA : (((Near.sw w hw)⁻¹ : GL (Fin (n + 1)) k) : Mx k n) = 1 - (w (Fin.last n))⁻¹ • Near.rE w := rfl
  have eB : (((Near.sw w hw)⁻¹⁻¹ : GL (Fin (n + 1)) k) : Mx k n) = 1 + Near.rE w := by
    rw [inv_inv]; exact Near.sw_val w hw
  apply conj_of_pair_lemma
  · intro y hy
    rw [eA, eB]
    exact h1 y hy
  · intro y hy
    rw [eA, eB]
    exact h2 y hy

open Near in
theorem phiNear : PhiNear k := by
  intro n Λ hΛ f₀ hf₀
  have hne : ∀ᶠ w : Vc k n in 𝓝 (eN k n), w (Fin.last n) ≠ 0 :=
    ((continuous_apply (Fin.last n)).tendsto (eN k n)).eventually_ne (by simp [eN])
  have hev := hne.and (near_lemma_2 hf₀)
  have ht : Tendsto (fun v : Vc k n => eN k n + v) (𝓝 0) (𝓝 (eN k n)) := by
    simpa using (continuous_add_left (eN k n)).tendsto (0 : Vc k n)
  have hU := ht.eventually hev
  obtain ⟨t, htU⟩ := exists_box_subset hU
  refine ⟨t, fun s hst => ?_⟩
  funext w
  by_cases hw : w - eN k n ∈ box (Fin (n + 1)) s
  · have hP := htU (hst hw)
    simp only [Set.mem_setOf_eq, add_sub_cancel] at hP
    obtain ⟨hl, hc⟩ := hP
    have hw0 : w ≠ 0 := by
      intro h
      apply hl
      simp [h]
    have hmem : w ∈ {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s} := hw
    rw [Set.indicator_of_mem hmem]
    simp only [phi, if_neg hw0, Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
    have hex : ∃ s : GL (Fin (n + 1)) k, ∀ j, (s : Mx k n) (Fin.last n) j = w j :=
      ⟨sw w hl, sw_last w hl⟩
    have hsec : ∀ j, ((sec w : GL (Fin (n + 1)) k) : Mx k n) (Fin.last n) j = w j := by
      simp only [sec, dif_pos hex]
      exact hex.choose_spec
    have hrow : ∀ M : Mx k n, eLast k n ᵥ* M = M (Fin.last n) := by
      intro M
      ext j
      simp [eLast, vecMul, dotProduct, Pi.single_apply]
    set p := sec w * (sw w hl)⁻¹ with hpdef
    have hp : p ∈ Mir k n := by
      show eLast k n ᵥ* ((p : GL (Fin (n + 1)) k) : Mx k n) = eLast k n
      have e1 : eLast k n ᵥ* ((sec w : GL (Fin (n + 1)) k) : Mx k n)
          = eLast k n ᵥ* ((sw w hl : GL (Fin (n + 1)) k) : Mx k n) := by
        rw [hrow, hrow]
        funext j
        rw [hsec j, sw_last w hl j]
      rw [hpdef, Units.val_mul, ← Matrix.vecMul_vecMul, e1, Matrix.vecMul_vecMul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
    have hsecp : sec w = p * sw w hl := by simp [hpdef]
    have hfun : (fun x : Mx k n => f₀ (cj (sec w)⁻¹ x)) = f₀ ∘ cj p⁻¹ := by
      funext x
      rw [hsecp, _root_.mul_inv_rev, cj_mul, Function.comp_apply]
      exact hc hl _
    rw [hfun]
    exact hΛ p⁻¹ (inv_mem hp) f₀ hf₀
  · have hmem : w ∉ {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s} := hw
    rw [Set.indicator_of_notMem hmem]
    simp only [phi, Set.indicator_of_notMem hmem, mul_zero]
    split_ifs
    · rfl
    · exact map_zero Λ

end PositivityTheory.RgUd.AB.Pf
end
end

section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.BZMir GroundTheory.Automorphic.Whittaker
  GlobalTheory.SplitDict

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_supportedIn_iff {X : Type*} [TopologicalSpace X] {U : Set X} {f : X → ℂ} :
    f ∈ supportedIn U ↔ f ∈ SB X ∧ Function.support f ⊆ U := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

theorem mem_supportedIn_univ_iff {X : Type*} [TopologicalSpace X] {f : X → ℂ} :
    f ∈ supportedIn (Set.univ : Set X) ↔ f ∈ SB X := by
  rw [mem_supportedIn_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, Set.subset_univ _⟩⟩

def recCjHomeo {n : ℕ} (g : GL (Fin (n + 1)) k) : Mx k n ≃ₜ Mx k n where
  toFun := cj g
  invFun := cj g⁻¹
  left_inv x := by
    simp only [cj, inv_inv]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul,
      Matrix.mul_one]
  right_inv x := by
    simp only [cj, inv_inv]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  continuous_toFun := by
    unfold cj
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := by
    unfold cj
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def mvHomeo {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hAB : A * B = 1) (hBA : B * A = 1) :
    Vc k n ≃ₜ Vc k n where
  toFun w := A *ᵥ w
  invFun w := B *ᵥ w
  left_inv w := by simp only [mulVec_mulVec, hBA, one_mulVec]
  right_inv w := by simp only [mulVec_mulVec, hAB, one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem comp_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {f : Y → ℂ}
    (hf : f ∈ SB Y) : f ∘ e ∈ SB X :=
  (bijOn_comp e).mapsTo hf

theorem cj_comp_mem {n : ℕ} (g : GL (Fin (n + 1)) k) {f : Mx k n → ℂ} (hf : f ∈ SB (Mx k n)) : f ∘ cj g ∈ SB (Mx k n) :=
  comp_mem_SB (recCjHomeo g) hf

theorem act_mem {n : ℕ} (g : GL (Fin (n + 1)) k) {F : Mx k n × Vc k n → ℂ} (hF : F ∈ SB (Mx k n × Vc k n)) :
    (fun p : Mx k n × Vc k n => F ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * p.1 *
      ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ p.2)) ∈ SB (Mx k n × Vc k n) :=
  comp_mem_SB ((recCjHomeo g).prodCongr (mvHomeo (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Units.mul_inv g) (Units.inv_mul g))) hF

theorem tw_mem {n : ℕ} (h : GL (Fin (n + 1)) k) {F : Mx k n × Vc k n → ℂ} (hF : F ∈ SB (Mx k n × Vc k n)) :
    (fun q : Mx k n × Vc k n => F (cj h⁻¹ q.1, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) ∈
      SB (Mx k n × Vc k n) :=
  comp_mem_SB ((recCjHomeo h⁻¹).prodCongr (mvHomeo (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ
    ((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ
    (by rw [← transpose_mul, Units.inv_mul, transpose_one]) (by rw [← transpose_mul, Units.mul_inv, transpose_one]))) hF

theorem isLocallyConstant_indicator_one {Y : Type*} [TopologicalSpace Y] {E : Set Y} (hE : IsClopen E) :
    IsLocallyConstant (E.indicator (1 : Y → ℂ)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun y => ?_
  by_cases hy : y ∈ E
  · filter_upwards [hE.isOpen.mem_nhds hy] with z hz
    rw [Set.indicator_of_mem hz, Set.indicator_of_mem hy]
    rfl
  · filter_upwards [hE.isClosed.isOpen_compl.mem_nhds hy] with z hz
    rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hy]

theorem tens_mem {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y] {f : X → ℂ}
    (hf : f ∈ SB X) {E : Set Y} (hEo : IsOpen E) (hEc : IsCompact E) :
    (fun q : X × Y => f q.1 * E.indicator 1 q.2) ∈ SB (X × Y) := by
  refine ⟨(hf.1.comp_continuous continuous_fst).mul
    ((isLocallyConstant_indicator_one ⟨hEc.isClosed, hEo⟩).comp_continuous continuous_snd),
    HasCompactSupport.intro (hf.2.isCompact.prod hEc) fun q hq => ?_⟩
  by_cases h1 : q.1 ∈ tsupport f
  · have h2 : q.2 ∉ E := fun h2 => hq ⟨h1, h2⟩
    simp [Set.indicator_of_notMem h2]
  · simp [image_eq_zero_of_notMem_tsupport h1]

theorem slice_fst_mem {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] {g : X × Y → ℂ}
    (hg : g ∈ SB (X × Y)) (y : Y) : (fun x => g (x, y)) ∈ SB X :=
  ⟨hg.1.comp_continuous (by fun_prop), HasCompactSupport.intro (hg.2.isCompact.image continuous_fst) fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩⟩

theorem zero_mem_box {m : Type*} (s : kˣ) : (0 : m → k) ∈ box m s := by
  intro i _
  simp [cball]

section Meas

variable [MeasurableSpace k] [BorelSpace k]

theorem integrable_slice (ν : Measure k) [ν.IsAddHaarMeasure] {T : Type} [TopologicalSpace T] {n : Type} [Fintype n]
    {ψ : AddChar k Circle} {c : kˣ} (hψ : HasConductor ψ c) {F : T × (n → k) → ℂ} (hF : F ∈ SB (T × (n → k)))
    (z : T × (n → k)) : Integrable (fun x => F (z.1, x) * (ψ (x ⬝ᵥ z.2) : ℂ)) (Measure.pi fun _ => ν) := by
  haveI := secondCountable k
  haveI := t2Space k
  have hs := slice_mem_SB hF z.1
  have h2 : IsLocallyConstant fun x : n → k => ((ψ (x ⬝ᵥ z.2) : Circle) : ℂ) :=
    (hψ.isLocallyConstant.comp_continuous (continuous_id.dotProduct continuous_const)).comp _
  exact (hs.1.mul h2).continuous.integrable_of_hasCompactSupport hs.2.mul_right

theorem pf_lin (ν : Measure k) [ν.IsAddHaarMeasure] {T : Type} [TopologicalSpace T] {n : Type} [Fintype n]
    {ψ : AddChar k Circle} {c : kˣ} (hψ : HasConductor ψ c) {F G : T × (n → k) → ℂ} (hF : F ∈ SB (T × (n → k)))
    (hG : G ∈ SB (T × (n → k))) (a b : ℂ) :
    pf ψ (Measure.pi fun _ => ν) (a • F + b • G) = a • pf ψ (Measure.pi fun _ => ν) F + b • pf ψ (Measure.pi fun _ => ν) G := by
  funext z
  simp only [pf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((integrable_slice ν hψ hF z).const_mul a)
    ((integrable_slice ν hψ hG z).const_mul b)]
  congr 1
  funext x
  ring

end Meas

theorem recover (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PhiIndep k → PhiLin k → PhiInt k → PhiNear k → PfAct k → LtEquiv k → Recover k := by
  intro _ hLin hInt hNear hPf hLt hT n Λ hP
  borelize k
  have := secondCountable k
  have := t2Space k
  obtain ⟨-, ⟨ψ, -, -, hψ⟩, ν, hν⟩ := conductor_exists k
  have := hν.1
  set μ : Measure (Vc k n) := Measure.pi fun _ => ν with hμ
  have hb := pf_bijOn (T := Mx k n) (n := Fin (n + 1)) ν hψ
  set Fi := Function.invFunOn (pf ψ μ) {f | f ∈ SB (Mx k n × Vc k n)} with hFi
  have Fi_mem : ∀ f ∈ SB (Mx k n × Vc k n), Fi f ∈ SB (Mx k n × Vc k n) := fun f hf => hb.surjOn.mapsTo_invFunOn hf
  have pf_Fi : ∀ f ∈ SB (Mx k n × Vc k n), pf ψ μ (Fi f) = f := fun f hf => hb.surjOn.rightInvOn_invFunOn hf
  have Fi_pf : ∀ F ∈ SB (Mx k n × Vc k n), Fi (pf ψ μ F) = F := fun F hF => hb.injOn.leftInvOn_invFunOn hF
  have pfL := fun {F G : Mx k n × Vc k n → ℂ} (hF : F ∈ SB _) (hG : G ∈ SB _) (a b : ℂ) => pf_lin ν hψ hF hG a b
  have pfS : ∀ F ∈ SB (Mx k n × Vc k n), ∀ a : ℂ, pf ψ μ (a • F) = a • pf ψ μ F := fun F hF a => by
    have := pfL hF hF a 0
    simpa using this
  have FiL : ∀ f ∈ SB (Mx k n × Vc k n), ∀ g ∈ SB (Mx k n × Vc k n), ∀ a b : ℂ,
      Fi (a • f + b • g) = a • Fi f + b • Fi g := by
    intro f hf g hg a b
    have h1 : a • Fi f + b • Fi g ∈ SB (Mx k n × Vc k n) :=
      add_mem (Submodule.smul_mem _ _ (Fi_mem f hf)) (Submodule.smul_mem _ _ (Fi_mem g hg))
    have := Fi_pf _ h1
    rw [pfL (Fi_mem f hf) (Fi_mem g hg), pf_Fi f hf, pf_Fi g hg] at this
    exact this
  have ltL : ∀ F ∈ SB (Mx k n × Vc k n), ∀ G ∈ SB (Mx k n × Vc k n), ∀ a b : ℂ,
      lt ν Λ (a • F + b • G) = a * lt ν Λ F + b * lt ν Λ G := by
    intro F hF G hG a b
    unfold lt
    rw [hLin n Λ F hF G hG a b]
    simp only [Pi.add_apply]
    rw [integral_add ((hInt ν n Λ hP F hF).smul a) ((hInt ν n Λ hP G hG).smul b)]
    simp only [Pi.smul_apply]
    rw [integral_smul, integral_smul, smul_eq_mul, smul_eq_mul]
  have ltS : ∀ F ∈ SB (Mx k n × Vc k n), ∀ a : ℂ, lt ν Λ (a • F) = a * lt ν Λ F := fun F hF a => by
    have := ltL F hF F hF a 0
    simpa using this
  let Ξ₀ : SB (Mx k n × Vc k n) →ₗ[ℂ] ℂ :=
    { toFun := fun f => lt ν Λ (Fi f)
      map_add' := fun f g => by
        have e := FiL f f.2 g g.2 1 1
        simp only [one_smul] at e
        have e2 := ltL _ (Fi_mem f f.2) _ (Fi_mem g g.2) 1 1
        simp only [one_smul, one_mul] at e2
        simp only [Submodule.coe_add, e, e2]
      map_smul' := fun c f => by
        have e := FiL f f.2 f f.2 c 0
        simp only [zero_smul, add_zero] at e
        simp only [SetLike.val_smul, RingHom.id_apply, smul_eq_mul, e, ltS _ (Fi_mem f f.2)] }
  obtain ⟨ξ, hξ⟩ := LinearMap.exists_extend Ξ₀
  have hξf : ∀ f ∈ SB (Mx k n × Vc k n), ξ f = lt ν Λ (Fi f) := fun f hf => LinearMap.congr_fun hξ ⟨f, hf⟩
  have hinv : ∀ (g : GL (Fin (n + 1)) k), ∀ f ∈ SB (Mx k n × Vc k n),
      ξ (fun p : Mx k n × Vc k n => f ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * p.1 *
        ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ p.2)) = ξ f := by
    intro g f hf
    have hF := Fi_mem f hf
    have hF' := tw_mem g⁻¹ hF
    have e1 := hPf ν ψ 1 hψ n (Fi f) hF g⁻¹
    set c : ℂ := (((nabs k (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ : ℝ) : ℂ) with hc
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact Complex.ofReal_ne_zero.2 (inv_ne_zero (nabs_pos k _).ne')
    have e2 : (fun p : Mx k n × Vc k n => f ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * p.1 *
        ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ p.2)) =
        pf ψ μ (c⁻¹ • fun q : Mx k n × Vc k n => Fi f (cj g⁻¹⁻¹ q.1,
          ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) := by
      rw [pfS _ hF', e1, pf_Fi f hf]
      funext p
      simp only [Pi.smul_apply, smul_eq_mul, cj, inv_inv]
      rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    rw [e2, hξf _ (pf_mem_SB μ hψ (Submodule.smul_mem _ _ hF')), Fi_pf _ (Submodule.smul_mem _ _ hF'),
      ltS _ hF', hLt ν n Λ hP (Fi f) hF g⁻¹, hξf f hf, ← hc, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hzero : ∀ f ∈ SB (Mx k n × Vc k n), (∀ x : Mx k n, f (x, 0) = 0) → ξ f = 0 := by
    intro f hf h0
    have hsupp : Function.support f ⊆ {p : Mx k n × Vc k n | p.2 ≠ 0} := by
      intro p hp h2
      apply hp
      obtain ⟨x, w⟩ := p
      simp only at h2
      subst h2
      exact h0 x
    refine hT (n + 1) ⊥ ?_ ?_ ξ ?_ ?_ f (mem_supportedIn_iff.2 ⟨hf, hsupp⟩)
    · intro a ha b _
      obtain ⟨r, rfl⟩ := Algebra.mem_bot.1 ha
      exact Algebra.commutes r b
    · refine ⟨fun x hx => ?_⟩
      obtain ⟨m, hm⟩ := hx
      obtain ⟨r, hr⟩ := Algebra.mem_bot.1 x.2
      have h1 : ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) ^ m = 0 := by
        simpa using congrArg Subtype.val hm
      have h2 : (algebraMap k (Matrix (Fin (n + 1)) (Fin (n + 1)) k)) (r ^ m) = 0 := by
        rw [map_pow, hr, h1]
      have h3 : r ^ m = 0 := (algebraMap k (Matrix (Fin (n + 1)) (Fin (n + 1)) k)).injective (h2.trans (map_zero _).symm)
      have h4 : r = 0 := by
        by_contra hr0
        exact pow_ne_zero m hr0 h3
      exact Subtype.ext (by rw [← hr, h4, map_zero]; rfl)
    · intro f' _ hz
      have : f' = 0 := funext fun p => hz p fun a ha => by
        obtain ⟨r, rfl⟩ := Algebra.mem_bot.1 ha
        exact Algebra.commutes r p.1
      rw [this, map_zero]
    · intro g _ f' hf'
      exact hinv g f' (mem_supportedIn_univ_iff.1 hf')
  set B : Set (Vc k n) := box (Fin (n + 1)) (1 : kˣ) with hB
  have hBo : IsOpen B := isOpen_box _
  have hBc : IsCompact B := isCompact_box _
  have hB0 : (0 : Vc k n) ∈ B := zero_mem_box _
  let T : (Mx k n → ℂ) →ₗ[ℂ] (Mx k n × Vc k n → ℂ) :=
    { toFun := fun f q => f q.1 * B.indicator 1 q.2
      map_add' := fun f g => by
        funext q
        simp only [Pi.add_apply]
        ring
      map_smul' := fun c f => by
        funext q
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hT_apply : ∀ f q, T f q = f q.1 * B.indicator 1 q.2 := fun _ _ => rfl
  refine ⟨ξ ∘ₗ T, ?_, ?_⟩
  · intro g f hf
    have h1 : T (f ∘ cj g) ∈ SB (Mx k n × Vc k n) := tens_mem (cj_comp_mem g hf) hBo hBc
    have h2 : T f ∈ SB (Mx k n × Vc k n) := tens_mem hf hBo hBc
    have h3 := act_mem g h2
    have hd := hzero _ (sub_mem h1 h3) fun x => by
      simp only [Pi.sub_apply, hT_apply, Function.comp_apply, mulVec_zero, Set.indicator_of_mem hB0, cj]
      ring
    rw [map_sub, sub_eq_zero] at hd
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hd, hinv g _ h2]
  · intro f₀ hf₀
    obtain ⟨t, ht⟩ := hNear n Λ hP f₀ hf₀
    have hφ := ht t subset_rfl
    set E : Set (Vc k n) := {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) t} with hE
    set F : Mx k n × Vc k n → ℂ := fun q => f₀ q.1 * E.indicator 1 q.2 with hFdef
    have hEo : IsOpen E := (isOpen_box t).preimage (continuous_id.sub continuous_const)
    have hEc : IsCompact E := by
      have : E = (fun w => w + eN k n) '' box (Fin (n + 1)) t := by
        ext w
        simp only [hE, Set.mem_ofPred_eq, Set.mem_image]
        exact ⟨fun h => ⟨w - eN k n, h, by abel⟩, fun ⟨u, hu, e⟩ => by rw [← e]; simpa using hu⟩
      rw [this]
      exact (isCompact_box t).image (continuous_id.add continuous_const)
    have hE0 : eN k n ∈ E := by
      simp only [hE, Set.mem_ofPred_eq, sub_self]
      exact zero_mem_box _
    have hF : F ∈ SB (Mx k n × Vc k n) := tens_mem hf₀ hEo hEc
    have hlt : lt ν Λ F = μ.real E * Λ f₀ := by
      unfold lt
      rw [hφ, integral_indicator_const _ hEo.measurableSet, Complex.real_smul]
    have hg := pf_mem_SB μ hψ hF
    have hg0 : ∀ x, pf ψ μ F (x, 0) = μ.real E * f₀ x := by
      intro x
      simp only [pf, hFdef, dotProduct_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
      rw [integral_const_mul, show (E.indicator (1 : Vc k n → ℂ)) = E.indicator (fun _ => (1 : ℂ)) from rfl,
        integral_indicator_const _ hEo.measurableSet, Complex.real_smul, mul_one, mul_comm]
    have h1 : ξ (pf ψ μ F) = lt ν Λ F := by rw [hξf _ hg, Fi_pf F hF]
    have h2 : (fun q : Mx k n × Vc k n => pf ψ μ F (q.1, 0) * B.indicator 1 q.2) = (μ.real E : ℂ) • T f₀ := by
      funext q
      simp only [hg0, Pi.smul_apply, smul_eq_mul, hT_apply]
      ring
    have h3 := hzero _ (sub_mem hg (tens_mem (slice_fst_mem hg 0) hBo hBc)) fun x => by
      simp only [Pi.sub_apply, Set.indicator_of_mem hB0, Pi.one_apply, mul_one, sub_self]
    rw [map_sub, sub_eq_zero, h2, map_smul, h1, hlt, smul_eq_mul] at h3
    have hpos : μ.real E ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨(hEo.measure_pos μ ⟨_, hE0⟩).ne', hEc.measure_lt_top.ne⟩
    have hpos' : (μ.real E : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos
    simp only [LinearMap.coe_comp, Function.comp_apply]
    exact mul_left_cancel₀ hpos' h3

theorem coreX (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Recover k → CoreX k := by
  intro hR hT n Λ hP g f hf
  obtain ⟨L, hL, hΛ⟩ := hR hT n Λ hP
  rw [hΛ _ (cj_comp_mem g hf), hΛ f hf, hL g f hf]

end PositivityTheory.RgUd.AB.Pf
end
end

section
noncomputable section

open Matrix MeasureTheory Topology Filter ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.BZMir

set_option linter.unusedSectionVars false

namespace PositivityTheory.RgUd.AB.BoxIntegration

open PositivityTheory.RgUd.AB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Act

variable {n : ℕ}

def actP (g : GL (Fin (n + 1)) k) (p : Mx k n × Vc k n) : Mx k n × Vc k n :=
  (cj g⁻¹ p.1, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ p.2)

theorem cj_apply (g : GL (Fin (n + 1)) k) (x : Mx k n) :
    cj g x = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * x * ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := rfl

theorem cj_one (x : Mx k n) : cj (1 : GL (Fin (n + 1)) k) x = x := by
  simp [cj_apply]

theorem cj_mul (g h : GL (Fin (n + 1)) k) (x : Mx k n) : cj (g * h) x = cj g (cj h x) := by
  simp only [cj_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem polyAction_one₂ (p : Mx k n × Vc k n) : actP (1 : GL (Fin (n + 1)) k) p = p := by
  simp [actP, cj_one]

theorem polyAction_mul (g h : GL (Fin (n + 1)) k) (p : Mx k n × Vc k n) : actP (g * h) p = actP h (actP g p) := by
  simp only [actP, _root_.mul_inv_rev, cj_mul, Units.val_mul, transpose_mul, mulVec_mulVec]

theorem actP_inv_actP (g : GL (Fin (n + 1)) k) (p : Mx k n × Vc k n) : actP g⁻¹ (actP g p) = p := by
  rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]

theorem continuous_actP : Continuous fun q : GL (Fin (n + 1)) k × (Mx k n × Vc k n) => actP q.1 q.2 := by
  unfold actP cj
  refine Continuous.prodMk ?_ ?_
  · simp only [inv_inv]
    exact ((Units.continuous_coe_inv.comp continuous_fst).matrix_mul
      (continuous_fst.comp continuous_snd)).matrix_mul (Units.continuous_val.comp continuous_fst)
  · exact (Units.continuous_val.comp continuous_fst).matrix_transpose.matrix_mulVec (continuous_snd.comp continuous_snd)

theorem eventually_actP_eq {F : Mx k n × Vc k n → ℂ} (hF : F ∈ SB (Mx k n × Vc k n)) :
    ∀ᶠ g in 𝓝 (1 : GL (Fin (n + 1)) k), ∀ p, F (actP g p) = F p := by
  have h1 : ∀ᶠ g in 𝓝 (1 : GL (Fin (n + 1)) k), ∀ p ∈ tsupport F, F (actP g p) = F p := by
    refine IsCompact.eventually_forall_of_forall_eventually hF.2 fun p _ => ?_
    have h2 : IsLocallyConstant fun q : GL (Fin (n + 1)) k × (Mx k n × Vc k n) => (F (actP q.1 q.2), F q.2) :=
      (hF.1.comp_continuous continuous_actP).prodMk (hF.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq ((1 : GL (Fin (n + 1)) k), p)] with q hq
    simp only [Prod.mk.injEq, polyAction_one₂] at hq
    rw [hq.1, hq.2]
  have h3 : ∀ᶠ g in 𝓝 (1 : GL (Fin (n + 1)) k), ∀ p ∈ tsupport F, F (actP g⁻¹ p) = F p := by
    have ht : Tendsto (fun g : GL (Fin (n + 1)) k => g⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : GL (Fin (n + 1)) k))
    exact ht.eventually h1
  filter_upwards [h1, h3] with g hg hg' p
  by_cases hp : p ∈ tsupport F
  · exact hg p hp
  by_cases hq : actP g p ∈ tsupport F
  · have := hg' _ hq
    rw [actP_inv_actP] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hp, image_eq_zero_of_notMem_tsupport hq]

end Act

section Phi

variable {n : ℕ}

theorem vecMul_eLast (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : vecMul (eLast k n) M = fun j => M (Fin.last n) j := by
  funext j
  simp [vecMul, dotProduct, eLast, Pi.single_apply]

def cjHomeo (g : GL (Fin (n + 1)) k) : Mx k n ≃ₜ Mx k n where
  toFun := cj g
  invFun := cj g⁻¹
  left_inv x := by rw [← cj_mul, inv_mul_cancel, cj_one]
  right_inv x := by rw [← cj_mul, mul_inv_cancel, cj_one]
  continuous_toFun := by
    unfold cj
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := by
    unfold cj
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem slice_snd_mem {F : Mx k n × Vc k n → ℂ} (hF : F ∈ SB (Mx k n × Vc k n)) (w : Vc k n) :
    (fun y => F (y, w)) ∈ SB (Mx k n) := by
  haveI := t2Space k
  refine ⟨hF.1.comp_continuous (f := fun y => (y, w)) (by fun_prop),
    HasCompactSupport.intro (IsCompact.image hF.2 continuous_fst) fun y hy => ?_⟩
  exact image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, h, rfl⟩

theorem comp_cj_mem {f : Mx k n → ℂ} (hf : f ∈ SB (Mx k n)) (g : GL (Fin (n + 1)) k) : f ∘ cj g ∈ SB (Mx k n) :=
  ⟨hf.1.comp_continuous (cjHomeo g).continuous, hf.2.comp_homeomorph (cjHomeo g)⟩

theorem sec_row {w : Vc k n} {s : GL (Fin (n + 1)) k} (hs : ∀ j, (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j) :
    ∀ j, ((sec w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j := by
  have hex : ∃ s' : GL (Fin (n + 1)) k, ∀ j, (s' : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j := ⟨s, hs⟩
  unfold sec
  rw [dif_pos hex]
  exact hex.choose_spec

theorem phi_eq_of_row {Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ} (hP : PInvX Λ) {F : Mx k n × Vc k n → ℂ} (hF : F ∈ SB (Mx k n × Vc k n))
    (s : GL (Fin (n + 1)) k) {w : Vc k n} (hs : ∀ j, (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j)
    (hw : w ≠ 0) : phi Λ F w = Λ (fun x => F (cj s⁻¹ x, w)) := by
  unfold phi
  rw [if_neg hw]
  set t := (sec w : GL (Fin (n + 1)) k) with ht
  have htr := sec_row hs
  have hp : s * t⁻¹ ∈ Mir k n := by
    show vecMul (eLast k n) ((s * t⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = eLast k n
    have e1 : vecMul (eLast k n) (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        vecMul (eLast k n) (t : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
      rw [vecMul_eLast, vecMul_eLast]
      funext j
      rw [hs j, ht, htr j]
    rw [Units.val_mul, ← vecMul_vecMul, e1, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
  have hpi : (s * t⁻¹)⁻¹ ∈ Mir k n := (Mir k n).inv_mem hp
  have hH := comp_cj_mem (slice_snd_mem hF w) t⁻¹
  have key := hP _ hpi _ hH
  have e : ((fun y => F (y, w)) ∘ cj t⁻¹) ∘ cj (s * t⁻¹)⁻¹ = fun x => F (cj s⁻¹ x, w) := by
    funext x
    simp only [Function.comp_apply]
    rw [← cj_mul]
    congr 2
    group
  rw [e] at key
  rw [key]
  rfl

theorem phi_eventually_eq {Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ} (hP : PInvX Λ) {F : Mx k n × Vc k n → ℂ}
    (hF : F ∈ SB (Mx k n × Vc k n)) {w₀ : Vc k n} (hw₀ : w₀ ≠ 0) : ∀ᶠ w in 𝓝 w₀, phi Λ F w = phi Λ F w₀ := by
  obtain ⟨s₀, hs₀⟩ := PositivityTheory.RgUd.AB.Pf.exists_last_row w₀ hw₀
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw₀
  let Mf : Vc k n → Matrix (Fin (n + 1)) (Fin (n + 1)) k := fun w =>
    1 + vecMulVec (Pi.single i (w₀ i)⁻¹) (w - w₀)
  have hMc : Continuous Mf := continuous_const.add (Continuous.matrix_vecMulVec continuous_const (continuous_id.sub continuous_const))
  have hM0 : Mf w₀ = 1 := by simp [Mf]
  obtain ⟨W, hW1, hW⟩ := (eventually_actP_eq hF).exists_mem
  have hE := PositivityTheory.PfBern.cocyclesToWachVectorsExponent.isOpenEmbedding_valGL (k := k) (m := n + 1)
  have hO : Units.val '' W ∈ 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    have := hE.isOpenMap.image_mem_nhds hW1
    simpa using this
  have h1 : ∀ᶠ w in 𝓝 w₀, Mf w ∈ Units.val '' W := by
    have := hMc.continuousAt (x := w₀)
    rw [ContinuousAt, hM0] at this
    exact this hO
  filter_upwards [h1, eventually_ne_nhds hw₀ |>.mono fun _ h => h, isOpen_ne.mem_nhds hw₀] with w hw _ hw0
  obtain ⟨g, hgW, hg⟩ := hw
  have hrow : ∀ j, ((s₀ * g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j := by
    have e1 : vecMul (eLast k n) ((s₀ * g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = w := by
      rw [Units.val_mul, ← vecMul_vecMul, vecMul_eLast, hg]
      have e2 : (fun j => (s₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j) = w₀ := funext hs₀
      rw [e2]
      simp only [Mf, vecMul_add, vecMul_one, vecMul_vecMulVec]
      have e3 : w₀ ⬝ᵥ Pi.single i (w₀ i)⁻¹ = 1 := by
        rw [dotProduct_single, mul_inv_cancel₀ hi]
      rw [e3, one_smul]
      abel
    intro j
    have := congrFun e1 j
    rw [vecMul_eLast] at this
    exact this
  have hw0' : w ≠ 0 := hw0
  rw [phi_eq_of_row hP hF (s₀ * g) hrow hw0', phi_eq_of_row hP hF s₀ hs₀ hw₀]
  congr 1
  funext x
  have hwg : w = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w₀ := by
    rw [mulVec_transpose]
    have e2 : (fun j => (s₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j) = w₀ := funext hs₀
    rw [← e2, ← vecMul_eLast, vecMul_vecMul, ← Units.val_mul, vecMul_eLast]
    funext j
    exact (hrow j).symm
  have := hW g hgW (cj s₀⁻¹ x, w₀)
  simp only [actP] at this
  rw [_root_.mul_inv_rev, cj_mul, hwg]
  exact this

theorem phi_eq_zero_of_notMem {Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ} {F : Mx k n × Vc k n → ℂ} {w : Vc k n}
    (hw : w ∉ Prod.snd '' tsupport F) : phi Λ F w = 0 := by
  unfold phi
  split_ifs
  · rfl
  · have : (fun x => F (cj (sec w)⁻¹ x, w)) = 0 := by
      funext x
      exact image_eq_zero_of_notMem_tsupport fun h => hw ⟨_, h, rfl⟩
    rw [this, map_zero]

theorem phi_zero {Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ} {F : Mx k n × Vc k n → ℂ} : phi Λ F 0 = 0 := by
  simp [phi]

theorem exists_box_phi_smul {Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ} (hP : PInvX Λ) {F : Mx k n × Vc k n → ℂ}
    (hF : F ∈ SB (Mx k n × Vc k n)) : ∃ s : kˣ, ∀ w ∈ box (Fin (n + 1)) s, ∀ c : kˣ, c • w ∈ box (Fin (n + 1)) s →
      phi Λ F (c • w) = phi Λ F w := by
  obtain ⟨s, hs⟩ := GlobalTheory.SplitDict.exists_box_invariant_snd hF
  have h0 : ∀ u ∈ box (Fin (n + 1)) s, ∀ y, F (y, u) = F (y, 0) := fun u hu y => by
    have := hs u hu (y, 0)
    simpa using this
  refine ⟨s, fun w hw c hc => ?_⟩
  by_cases hw0 : w = 0
  · subst hw0
    simp
  have hcw : c • w ≠ 0 := fun h => hw0 (by simpa using congrArg (fun v => c⁻¹ • v) h)
  obtain ⟨t, ht⟩ := PositivityTheory.RgUd.AB.Pf.exists_last_row w hw0
  let sc : GL (Fin (n + 1)) k := Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c
  have hrow : ∀ j, ((sc * t : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = (c • w) j := by
    intro j
    simp [sc, ht j, Units.smul_def]
  rw [phi_eq_of_row hP hF (sc * t) hrow hcw, phi_eq_of_row hP hF t ht hw0]
  congr 1
  funext x
  have hcj : cj (sc * t)⁻¹ x = cj t⁻¹ x := by
    rw [_root_.mul_inv_rev, cj_mul]
    congr 1
    ext a b
    simp [sc, cj_apply, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_mul, Matrix.mul_diagonal]
    field_simp
  rw [hcj, h0 _ hc, h0 _ hw]

end Phi

section Fin

variable {X Y : Type*} [TopologicalSpace X]

theorem finite_image_of_eventually {f : X → Y} {K : Set X} (hK : IsCompact K)
    (h : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, f y = f x) : (f '' K).Finite := by
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => {y | f y = f x}) (fun x hx => h x hx)
  refine (t.finite_toSet.image f).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hcov hy)
  exact ⟨x, hx, hyx.symm⟩

end Fin

section Range

variable {n : ℕ}

theorem zero_mem_box (s : kˣ) : (0 : Vc k n) ∈ box (Fin (n + 1)) s := by
  intro i _
  simp [cball]

theorem exists_smul_shell {s : kˣ} {r : k} (hr0 : r ≠ 0) (hr1 : valuation k r < 1) {w : Vc k n}
    (hw0 : w ≠ 0) : ∃ c : kˣ, c • w ∈ box (Fin (n + 1)) s ∧ c • w ∉ box (Fin (n + 1)) (s * Units.mk0 r hr0) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => valuation k (w j)) Finset.univ_nonempty
  have hwi : w i ≠ 0 := by
    intro h
    apply hw0
    funext j
    have := hi j (Finset.mem_univ j)
    rw [h, map_zero] at this
    simpa using le_antisymm this zero_le'
  refine ⟨s * (Units.mk0 (w i) hwi)⁻¹, ?_, ?_⟩
  · intro j _
    show valuation k (((s * (Units.mk0 (w i) hwi)⁻¹ : kˣ) : k) * w j) ≤ valuation k (s : k)
    have hv : valuation k (w i) ≠ 0 := by simpa using hwi
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, map_mul, map_inv₀]
    rw [mul_assoc]
    calc valuation k (s : k) * ((valuation k (w i))⁻¹ * valuation k (w j))
        ≤ valuation k (s : k) * ((valuation k (w i))⁻¹ * valuation k (w i)) :=
          by gcongr; exact hi j (Finset.mem_univ j)
      _ = valuation k (s : k) := by rw [inv_mul_cancel₀ hv, mul_one]
  · intro h
    have := h i (Set.mem_univ i)
    change valuation k (((s * (Units.mk0 (w i) hwi)⁻¹ : kˣ) : k) * w i) ≤ valuation k (((s * Units.mk0 r hr0 : kˣ)) : k) at this
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0] at this
    rw [mul_assoc, inv_mul_cancel₀ hwi, mul_one, map_mul] at this
    have hs : 0 < valuation k (s : k) := by simp [zero_lt_iff]
    have := lt_of_le_of_lt this (by rw [mul_comm]; exact mul_lt_of_lt_one_left hs hr1)
    exact lt_irrefl _ this

theorem finite_range_phi {Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ} (hP : PInvX Λ) {F : Mx k n × Vc k n → ℂ}
    (hF : F ∈ SB (Mx k n × Vc k n)) : (Set.range (phi Λ F)).Finite := by
  haveI := GlobalTheory.SplitWeil.t2Space (k := k)
  obtain ⟨s, hs⟩ := exists_box_phi_smul hP hF
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  set Q := Prod.snd '' tsupport F with hQdef
  have hQ : IsCompact Q := hF.2.image continuous_snd
  set B := box (Fin (n + 1)) s with hBdef
  set B' := box (Fin (n + 1)) (s * Units.mk0 r hr0) with hB'def
  have hBo : IsOpen B := isOpen_box s
  have hB'o : IsOpen B' := isOpen_box _
  have hK1 : IsCompact (Q ∩ Bᶜ) := hQ.inter_right hBo.isClosed_compl
  have hK2 : IsCompact (B ∩ B'ᶜ) := (isCompact_box s).inter_right hB'o.isClosed_compl
  have hf1 : (phi Λ F '' (Q ∩ Bᶜ)).Finite := finite_image_of_eventually hK1 fun x hx =>
    phi_eventually_eq hP hF fun h => hx.2 (h ▸ zero_mem_box s)
  have hf2 : (phi Λ F '' (B ∩ B'ᶜ)).Finite := finite_image_of_eventually hK2 fun x hx =>
    phi_eventually_eq hP hF fun h => hx.2 (h ▸ zero_mem_box _)
  refine ((Set.finite_singleton (0 : ℂ)).union (hf1.union hf2)).subset ?_
  rintro _ ⟨w, rfl⟩
  by_cases hw0 : w = 0
  · left; rw [hw0]; exact phi_zero
  by_cases hwB : w ∈ B
  · obtain ⟨c, hc1, hc2⟩ := exists_smul_shell (s := s) hr0 hr1 hw0
    right; right
    exact ⟨c • w, ⟨hc1, hc2⟩, hs w hwB c hc1⟩
  by_cases hwQ : w ∈ Q
  · right; left; exact ⟨w, ⟨hwQ, hwB⟩, rfl⟩
  · left; exact phi_eq_zero_of_notMem hwQ

end Range

section Meas

variable {n : ℕ} [MeasurableSpace k] [BorelSpace k]

theorem measurable_phi {Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ} (hP : PInvX Λ) {F : Mx k n × Vc k n → ℂ}
    (hF : F ∈ SB (Mx k n × Vc k n)) : Measurable (phi Λ F) := by
  haveI := GlobalTheory.SplitWeil.t2Space (k := k)
  haveI := GlobalTheory.SplitWeil.secondCountable (k := k)
  intro S _
  have hU : IsOpen (phi Λ F ⁻¹' S ∩ {w | w ≠ 0}) := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨hwS, hw0⟩
    filter_upwards [phi_eventually_eq hP hF hw0, isOpen_ne.mem_nhds hw0] with y hy hy0
    exact ⟨by show phi Λ F y ∈ S; rw [hy]; exact hwS, hy0⟩
  have e : phi Λ F ⁻¹' S = (phi Λ F ⁻¹' S ∩ {w | w ≠ 0}) ∪ (phi Λ F ⁻¹' S ∩ {0}) := by
    ext w
    by_cases hw : w = 0 <;> simp [hw]
  rw [e]
  refine hU.measurableSet.union ?_
  by_cases h0 : (0 : Vc k n) ∈ phi Λ F ⁻¹' S
  · rw [Set.inter_eq_right.2 (Set.singleton_subset_iff.2 h0)]
    exact isClosed_singleton.measurableSet
  · rw [Set.inter_singleton_eq_empty.2 h0]
    exact MeasurableSet.empty

end Meas

end PositivityTheory.RgUd.AB.BoxIntegration

namespace PositivityTheory.RgUd.AB.Pf

open PositivityTheory.RgUd.AB PositivityTheory.RgUd.AB.BoxIntegration

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem phiInt : PhiInt k := by
  intro _ _ ν _ n Λ hP F hF
  haveI := GlobalTheory.SplitWeil.t2Space (k := k)
  haveI := GlobalTheory.SplitWeil.secondCountable (k := k)
  obtain ⟨M, hM⟩ := ((finite_range_phi hP hF).image norm).bddAbove
  have hM' : ∀ w, ‖phi Λ F w‖ ≤ M := fun w => hM ⟨_, ⟨w, rfl⟩, rfl⟩
  set Q := Prod.snd '' tsupport F with hQdef
  have hQ : IsCompact Q := hF.2.image continuous_snd
  have hQm : MeasurableSet Q := hQ.isClosed.measurableSet
  have hQfin : (Measure.pi fun _ : Fin (n + 1) => ν) Q < ⊤ := hQ.measure_lt_top
  refine Integrable.mono' (g := Q.indicator fun _ => M) ?_ (measurable_phi hP hF).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  · exact (integrableOn_const hQfin.ne).integrable_indicator hQm
  · by_cases hw : w ∈ Q
    · rw [Set.indicator_of_mem hw]
      exact hM' w
    · rw [Set.indicator_of_notMem hw, phi_eq_zero_of_notMem hw, norm_zero]

end PositivityTheory.RgUd.AB.Pf
end
end

section
namespace PositivityTheory.RgUd.AB.Final

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thmA : ThmT k → ThmA k :=
  Pf.thmA_of_core k (Pf.coreX k (Pf.recover k (Pf.phiIndep (k := k)) (Pf.phiLin (k := k)) (Pf.phiInt (k := k)) (Pf.phiNear (k := k)) (Pf.pfAct (k := k))
    (Pf.ltEquiv (k := k) (Pf.phiEquiv (k := k)))))

theorem thmB : ThmA k → ThmB k := Pf.thmB k

end PositivityTheory.RgUd.AB.Final
end
