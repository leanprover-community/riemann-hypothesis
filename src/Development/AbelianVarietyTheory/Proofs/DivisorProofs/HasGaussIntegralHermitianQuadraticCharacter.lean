import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompAddEquivRescale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenSubgroupExhaustion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenNormClosedBallQuadratic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemRangeNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLinearEquivAddHaarLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualBicharacterPairingOfSymmBilinForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicProperties

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem exists_gl_diagonal_hermitian : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (b : Matrix ν ν E), (b.map c)ᵀ = b → b.det ≠ 0 → ∃ (a : GL ν E) (D : ν → Fˣ), b = (a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ := by
  intro F _ _ E _ _ c δ hE ν _ _ b hb hdet
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have h2 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have hG : ∀ x y, (c : E →+* E) (b x y) = b y x := by
    intro x y
    have := congrFun (congrFun hb y) x
    simpa using this
  obtain ⟨P, d, hP, hPd, hfix, hne⟩ :=
    GlobalTheory.HermDiag.exists_congr_diagonal (c := (c : E →+* E)) h2 (fun t => hE.invol t) (G := b) hG
  have hd0 := hne hdet
  have hPd' : Pᵀ * b * P.map c = diagonal d := hPd
  choose f hf using fun i => hE.exists_of_fixed (hfix i)
  have hf0 : ∀ i, f i ≠ 0 := by
    intro i h; apply hd0 i; rw [hf i, h, map_zero]
  have hQ : (Pᵀ).det ≠ 0 := by rwa [det_transpose]
  set A : Matrix ν ν E := (Pᵀ)⁻¹ with hA
  have hAQ : A * Pᵀ = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hQ)
  have hQA : Pᵀ * A = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hQ)
  have hAs : (A.map c)ᵀ * P.map c = 1 := by
    have h1 : (Pᵀ * A).map c = 1 := by rw [hQA]; exact Matrix.map_one _ (map_zero c) (map_one c)
    rw [show (Pᵀ * A).map c = (Pᵀ).map c * A.map c from Matrix.map_mul (f := c.toRingHom)] at h1
    have h3 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h3
    simpa [Matrix.transpose_map] using h3
  have hAs' : P.map c * (A.map c)ᵀ = 1 := mul_eq_one_comm.mp hAs
  have hAdet : A.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hAQ
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet, fun j => Units.mk0 (f j) (hf0 j), ?_⟩
  have hD : diagonal (fun j => algebraMap F E ((Units.mk0 (f j) (hf0 j) : Fˣ) : F)) = diagonal d := by
    congr 1; funext j; simp [hf j]
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  rw [hD, ← hPd']
  calc b = (A * Pᵀ) * b * (P.map c * (A.map c)ᵀ) := by rw [hAQ, hAs', Matrix.one_mul, Matrix.mul_one]
    _ = A * (Pᵀ * b * P.map c) * (A.map c)ᵀ := by simp only [Matrix.mul_assoc]

end GlobalTheory.KSp
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_diagonal_congruent_hermitian : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (b : Matrix ν ν E), (b.map c)ᵀ = b → b.det ≠ 0 → ∃ (a : GL ν E) (D : ν → Fˣ), b = (a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ := by
  atlas_forward_decl GlobalTheory.KSp.exists_gl_diagonal_hermitian
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem hasGauss_pi : ∀ (Y : Type) [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (_ : Good Y) (μ : Measure Y) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι] (f : ι → Y → ℂ) (γ : ι → ℂ), (∀ i, HasGauss μ (f i) (γ i)) → HasGauss (Measure.pi fun _ : ι => μ) (fun x => ∏ i, f i (x i)) (∏ i, γ i) := by
  intro Y _ _ _ _ hY μ _ ι _ f γ hf K hK
  haveI := hY.sc
  haveI := hY.lc
  haveI := hY.t2
  haveI : SigmaFinite μ := sigmaFinite_of_locallyFinite
  have hL : ∀ i, ∃ L : AddSubgroup Y, IsCompact (L : Set Y) ∧ IsOpen (L : Set Y) ∧
      (Function.eval i '' K) ⊆ L ∧ ∫ x in (L : Set Y), f i x ∂μ = γ i :=
    fun i => hf i _ (hK.image (continuous_apply i))
  choose L hLc hLo hLK hLi using hL
  refine ⟨AddSubgroup.pi Set.univ L, ?_, ?_, ?_, ?_⟩
  · rw [AddSubgroup.coe_pi]; exact isCompact_univ_pi hLc
  · rw [AddSubgroup.coe_pi]; exact isOpen_set_pi Set.finite_univ fun i _ => hLo i
  · intro x hx
    rw [SetLike.mem_coe, AddSubgroup.mem_pi]
    intro i _
    exact hLK i ⟨x, hx, rfl⟩
  · rw [AddSubgroup.coe_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
    exact Finset.prod_congr rfl fun i _ => hLi i

end GlobalTheory.KSp
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGaussIntegralCompactOpen_pi : ∀ (Y : Type) [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (_ : Good Y) (μ : Measure Y) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι] (f : ι → Y → ℂ) (γ : ι → ℂ), (∀ i, HasGauss μ (f i) (γ i)) → HasGauss (Measure.pi fun _ : ι => μ) (fun x => ∏ i, f i (x i)) (∏ i, γ i) := by
  atlas_forward_decl GlobalTheory.KSp.hasGauss_pi
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem exists_integral_cball_char_eq_zero :
    ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (lam : Measure F) [lam.IsAddHaarMeasure] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1), ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂lam = 0 := by
  intro F _ _ _ _ _ _ _ lam _ ψ _ _ hne
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (by ext x; simpa using h x)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (by simp)
  refine ⟨Units.mk0 t ht0, fun s hs => ?_⟩
  have hs' : t ∈ GlobalTheory.SplitWeil.cball s := hs
  have hm : MeasurableSet (GlobalTheory.SplitWeil.cball s) := (GlobalTheory.SplitWeil.isOpen_cball s).measurableSet
  have hadd : ∀ x y : F, x ∈ GlobalTheory.SplitWeil.cball s → y ∈ GlobalTheory.SplitWeil.cball s →
      x + y ∈ GlobalTheory.SplitWeil.cball s := fun x y hx hy => by
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at hx hy ⊢
    exact Valuation.map_add_le _ hx hy
  have hneg : -t ∈ GlobalTheory.SplitWeil.cball s := by
    simpa [GlobalTheory.SplitWeil.cball] using hs'
  have hiff : ∀ x : F, t + x ∈ GlobalTheory.SplitWeil.cball s ↔ x ∈ GlobalTheory.SplitWeil.cball s := fun x =>
    ⟨fun h => by simpa using hadd _ _ hneg h, fun h => hadd _ _ hs' h⟩
  rw [← integral_indicator hm]
  have h1 := integral_add_left_eq_self (μ := lam)
    ((GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x)) t
  have h2 : (fun x => (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) (t + x))
      = fun x => ψ t * (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) x := by
    funext x
    by_cases hx : x ∈ GlobalTheory.SplitWeil.cball s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hiff x).2 hx), AddChar.map_add_eq_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hiff x).1 h)), mul_zero]
  rw [h2, integral_const_mul] at h1
  have h3 : (ψ t - 1) * ∫ x, (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) x ∂lam = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 ht)

end GlobalTheory.KSp
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_closedBall_addChar_eq_zero : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (lam : Measure F) [lam.IsAddHaarMeasure] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1), ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂lam = 0 := by
  atlas_forward_decl GlobalTheory.KSp.exists_integral_cball_char_eq_zero
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel Topology
open scoped ENNReal NNReal Pointwise

noncomputable section
namespace GlobalTheory.KSp.Homog

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem nhdsNE_neBot : (𝓝[≠] (0 : F)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
  intro t ht
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset ht
  exact ⟨s, hs (show valuation F (s : F) ≤ valuation F (s : F) from le_refl _), s.ne_zero⟩

theorem isOpen_sphere {γ : ValueGroupWithZero F} (hγ : γ ≠ 0) :
    IsOpen {y : F | valuation F y = γ} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun z hz ↦ ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hz hy ⊢
  have : z = y + (z - y) := by ring
  rw [this, (valuation F).map_add_eq_of_lt_left (by rw [hy]; exact hz), hy]

open Classical in

def absE (x : F) : ℝ≥0∞ := if h : x = 0 then 0 else (distribHaarChar F (Units.mk0 x h) : ℝ≥0∞)

theorem absE_ne_zero {x : F} (hx : x ≠ 0) : absE x ≠ 0 := by
  simp only [absE, dif_neg hx, ne_eq, ENNReal.coe_eq_zero]
  exact (distribHaarChar_pos (A := F) (g := Units.mk0 x hx)).ne'

theorem absE_ne_top (x : F) : absE x ≠ ∞ := by
  unfold absE; split_ifs <;> simp

theorem absE_inv {x : F} (hx : x ≠ 0) : absE x⁻¹ = (absE x)⁻¹ := by
  simp only [absE, dif_neg hx, dif_neg (inv_ne_zero hx)]
  rw [← ENNReal.coe_inv (distribHaarChar_pos (A := F) (g := Units.mk0 x hx)).ne', ← map_inv]
  congr 3
  ext; simp

theorem absE_eq_one {x : F} (hx : valuation F x = 1) : absE x = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have h := GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (x := Units.mk0 x hx0) (by simpa using hx)
  simp only [GlobalTheory.SplitWeil.nabs, NNReal.coe_eq_one] at h
  simp [absE, hx0, h]

theorem absE_eq_of_val_eq {x y : F} (h : valuation F y = valuation F x) : absE y = absE x := by
  by_cases hx : x = 0
  · subst hx
    have : y = 0 := by simpa using h
    rw [this]
  have hy : y ≠ 0 := by rintro rfl; exact hx (by simpa using h.symm)
  have hu : valuation F (y / x) = 1 := by
    rw [map_div₀, h, div_self (by simpa using hx)]
  have e1 := absE_eq_one hu
  have hyx : Units.mk0 y hy = Units.mk0 x hx * Units.mk0 (y / x) (div_ne_zero hy hx) := by
    ext; simp [mul_div_cancel₀ _ hx]
  simp only [absE, dif_neg hy, dif_neg hx, dif_neg (div_ne_zero hy hx)] at e1 ⊢
  rw [hyx, map_mul, ENNReal.coe_mul, e1, mul_one]

section Meas
variable [MeasurableSpace F] [BorelSpace F]

theorem measurableSet_preimage_valuation (S : Set (ValueGroupWithZero F)) :
    MeasurableSet (valuation F ⁻¹' S) := by
  haveI := GlobalTheory.SplitWeil.t2Space F
  have e : valuation F ⁻¹' S = valuation F ⁻¹' (S \ {0}) ∪ valuation F ⁻¹' (S ∩ {0}) := by
    rw [← Set.preimage_union, Set.diff_union_inter]
  rw [e]
  refine MeasurableSet.union (IsOpen.measurableSet ?_) ?_
  · have : valuation F ⁻¹' (S \ {0}) = ⋃ γ ∈ S \ {0}, {y : F | valuation F y = γ} := by
      ext y; simp
    rw [this]
    exact isOpen_biUnion fun γ hγ ↦ isOpen_sphere hγ.2
  · by_cases h0 : (0 : ValueGroupWithZero F) ∈ S
    · have : valuation F ⁻¹' (S ∩ {0}) = {0} := by
        ext y; simp [h0]
      rw [this]; exact measurableSet_singleton 0
    · have : valuation F ⁻¹' (S ∩ {0}) = ∅ := by
        ext y; simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro hy h'; exact h0 (h' ▸ hy)
      rw [this]; exact MeasurableSet.empty

theorem measurable_absE : Measurable (absE : F → ℝ≥0∞) := by
  intro T _
  have : absE ⁻¹' T = valuation F ⁻¹' (valuation F '' (absE ⁻¹' T)) := by
    ext x; constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      simp only [Set.mem_preimage] at hy ⊢
      rwa [← absE_eq_of_val_eq hxy]
  rw [this]; exact measurableSet_preimage_valuation _

theorem lintegral_comp_mul_left (μ : Measure F)
    (hμ : ∀ x : F, x ≠ 0 → μ.map (fun y ↦ x * y) = (absE x)⁻¹ • μ) {f : F → ℝ≥0∞}
    (hf : Measurable f) {x : F} (hx : x ≠ 0) :
    ∫⁻ t, f (x * t) ∂μ = (absE x)⁻¹ * ∫⁻ t, f t ∂μ := by
  calc ∫⁻ t, f (x * t) ∂μ = ∫⁻ t, f t ∂(μ.map (fun y ↦ x * y)) :=
        (lintegral_map hf (measurable_const_mul x)).symm
    _ = _ := by rw [hμ x hx, lintegral_smul_measure]; rfl

theorem map_mul_haar (lam : Measure F) [lam.IsAddHaarMeasure] {x : F} (hx : x ≠ 0) :
    lam.map (fun y ↦ x * y) = (absE x)⁻¹ • lam := by
  haveI := GlobalTheory.SplitWeil.secondCountable F
  haveI := GlobalTheory.SplitWeil.t2Space F
  ext s hs
  rw [Measure.map_apply (measurable_const_mul x) hs, Measure.smul_apply, smul_eq_mul]
  have hset : (fun y ↦ x * y) ⁻¹' s = (Units.mk0 x hx)⁻¹ • s := by
    ext y
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def,
      Units.val_mk0, smul_eq_mul]
  rw [hset, ← distribHaarChar_mul, absE, dif_neg hx, map_inv,
    ENNReal.coe_inv (distribHaarChar_pos (A := F) (g := Units.mk0 x hx)).ne']

def U : Set F := {y | valuation F y = 1}

theorem measurableSet_U : MeasurableSet (U : Set F) := by
  haveI := GlobalTheory.SplitWeil.t2Space F
  exact (isOpen_sphere one_ne_zero).measurableSet

theorem inv_mem_U_iff (t : F) : t⁻¹ ∈ (U : Set F) ↔ t ∈ U := by
  simp [U, map_inv₀]

theorem measure_mul_measure_units_eq (lam : Measure F) [lam.IsAddHaarMeasure] (n : Measure F) [SFinite n]
    (hn0 : n {0} = 0) (hn : ∀ x : F, x ≠ 0 → n.map (fun y ↦ x * y) = (absE x)⁻¹ • n)
    {A : Set F} (hA : MeasurableSet A) :
    n A * lam U = n U * lam A := by
  haveI := GlobalTheory.SplitWeil.secondCountable F
  haveI := GlobalTheory.SplitWeil.t2Space F
  haveI := nhdsNE_neBot (F := F)
  have hU := measurableSet_U (F := F)
  have hl := fun x (hx : x ≠ 0) ↦ map_mul_haar lam (x := x) hx
  have hlam0 : lam {0} = 0 := measure_singleton 0
  let K : F → F → ℝ≥0∞ := fun x y ↦ A.indicator 1 x * (absE x)⁻¹ * U.indicator 1 (x⁻¹ * y)
  let G : F → F → ℝ≥0∞ := fun y t ↦ U.indicator 1 t * A.indicator 1 (y * t)
  have hIA : Measurable (A.indicator (1 : F → ℝ≥0∞)) := measurable_one.indicator hA
  have hIU : Measurable (U.indicator (1 : F → ℝ≥0∞)) := measurable_one.indicator hU
  have hK : Measurable (Function.uncurry K) := by
    refine ((hIA.comp measurable_fst).mul (measurable_absE.comp measurable_fst).inv).mul
      (hIU.comp (measurable_fst.inv.mul measurable_snd))
  have hG : Measurable (Function.uncurry G) :=
    (hIU.comp measurable_snd).mul (hIA.comp (measurable_fst.mul measurable_snd))

  have h1 : ∫⁻ x, ∫⁻ y, K x y ∂lam ∂n = n A * lam U := by
    have h0 : ∀ᵐ x ∂n, x ≠ 0 := by
      rw [ae_iff]; simpa using hn0
    have : ∀ᵐ x ∂n, ∫⁻ y, K x y ∂lam = A.indicator 1 x * lam U := by
      filter_upwards [h0] with x hx
      simp only [K]
      rw [lintegral_const_mul, lintegral_comp_mul_left lam hl hIU (inv_ne_zero hx), absE_inv hx,
        inv_inv, lintegral_indicator_one hU, mul_assoc, ← mul_assoc (absE x)⁻¹,
        ENNReal.inv_mul_cancel (absE_ne_zero hx) (absE_ne_top x), one_mul]
      exact hIU.comp (measurable_const_mul _)
    rw [lintegral_congr_ae this, lintegral_mul_const _ hIA, lintegral_indicator_one hA]

  have h2 : ∫⁻ y, ∫⁻ x, K x y ∂n ∂lam = ∫⁻ y, ∫⁻ t, G y t ∂n ∂lam := by
    have h0 : ∀ᵐ y ∂lam, y ≠ 0 := by
      rw [ae_iff]; simpa using hlam0
    apply lintegral_congr_ae
    filter_upwards [h0] with y hy
    have hf : Measurable fun x ↦ K x y := hK.comp (measurable_id.prodMk measurable_const)
    have hsub := lintegral_comp_mul_left n hn hf hy
    have hpt : ∀ t, K (y * t) y = (absE y)⁻¹ * G y t := by
      intro t
      simp only [K, G]
      have e : (y * t)⁻¹ * y = t⁻¹ := by rw [_root_.mul_inv_rev, inv_mul_cancel_right₀ hy]
      rw [e]
      by_cases ht : t ∈ (U : Set F)
      · have hv : valuation F (y * t) = valuation F y := by
          rw [map_mul, show valuation F t = 1 from ht, mul_one]
        rw [absE_eq_of_val_eq hv, Set.indicator_of_mem ((inv_mem_U_iff t).mpr ht),
          Set.indicator_of_mem ht]
        simp only [Pi.one_apply]; ring
      · rw [Set.indicator_of_notMem (fun h ↦ ht ((inv_mem_U_iff t).mp h)),
          Set.indicator_of_notMem ht]
        simp
    simp only [hpt] at hsub
    rw [lintegral_const_mul _ (show Measurable fun t ↦ G y t from
      hG.comp (measurable_const.prodMk measurable_id))] at hsub
    have hne := absE_ne_zero hy
    have hnt := absE_ne_top y

    have := congrArg (fun z ↦ absE y * z) hsub
    simp only [← mul_assoc, ENNReal.mul_inv_cancel hne hnt, one_mul] at this
    exact this.symm

  have h3 : ∫⁻ t, ∫⁻ y, G y t ∂lam ∂n = n U * lam A := by
    have : ∀ t, ∫⁻ y, G y t ∂lam = U.indicator 1 t * lam A := by
      intro t
      simp only [G]
      rw [lintegral_const_mul]
      swap; · exact hIA.comp (measurable_mul_const t)
      by_cases ht : t ∈ (U : Set F)
      · have ht0 : t ≠ 0 := by rintro rfl; simp [U] at ht
        simp_rw [mul_comm _ t]
        rw [lintegral_comp_mul_left lam hl hIA ht0, absE_eq_one ht, inv_one, one_mul,
          lintegral_indicator_one hA]
      · simp [Set.indicator_of_notMem ht]
    simp_rw [this]
    rw [lintegral_mul_const _ hIU, lintegral_indicator_one hU]
  rw [← h1, lintegral_lintegral_swap hK.aemeasurable, h2,
    lintegral_lintegral_swap hG.aemeasurable, h3]

end Meas

theorem eq_smul_haar_of_homog : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (lam : Measure F) [lam.IsAddHaarMeasure] (n : Measure F) [IsFiniteMeasureOnCompacts n],
    n {0} = 0 → (∀ u : Fˣ, n.map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • n) →
    ∃ r : NNReal, n = r • lam := by
  intro F _ _ _ _ _ _ _ lam _ n _ hn0 hn
  haveI := GlobalTheory.SplitWeil.secondCountable F
  haveI := GlobalTheory.SplitWeil.t2Space F
  have hn' : ∀ x : F, x ≠ 0 → n.map (fun y ↦ x * y) = (absE x)⁻¹ • n := by
    intro x hx
    have h := hn (Units.mk0 x hx)
    simp only [Units.val_mk0] at h
    rw [h, absE, dif_neg hx, ← ENNReal.coe_inv (distribHaarChar_pos (A := F) (g := Units.mk0 x hx)).ne']
    ext s; rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def]
  have hUO : (U : Set F) ⊆ (𝒪[F] : Set F) := fun y hy ↦
    (Valuation.mem_integer_iff _ _).mpr (le_of_eq hy)
  have hnU : n U ≠ ∞ :=
    ((measure_mono hUO).trans_lt (GlobalTheory.SplitWeil.isCompact_int F).measure_lt_top).ne
  have hlU : lam U ≠ ∞ :=
    ((measure_mono hUO).trans_lt (GlobalTheory.SplitWeil.isCompact_int F).measure_lt_top).ne
  have hlU0 : lam U ≠ 0 :=
    ((isOpen_sphere (F := F) one_ne_zero).measure_pos lam ⟨1, by simp⟩).ne'
  refine ⟨(n U / lam U).toNNReal, ?_⟩
  ext s hs
  rw [Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_toNNReal (ENNReal.div_ne_top hnU hlU0),
    smul_eq_mul]
  have hk := measure_mul_measure_units_eq lam n hn0 hn' hs
  rw [div_eq_mul_inv, mul_right_comm, ← hk, mul_assoc, ENNReal.mul_inv_cancel hlU0 hlU, mul_one]
end GlobalTheory.KSp.Homog
end
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousMeasure_eq_smul_addHaar_localField : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (lam : Measure F) [lam.IsAddHaarMeasure] (n : Measure F) [IsFiniteMeasureOnCompacts n], n {0} = 0 → (∀ u : Fˣ, n.map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • n) → ∃ r : NNReal, n = r • lam := by
  atlas_forward_decl GlobalTheory.KSp.Homog.eq_smul_haar_of_homog
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem map_mul_left_eq_norm_smul (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (z : Eˣ) :
    μ.map (fun x => (z : E) * x) =
      (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) z))⁻¹ • μ := by
  obtain ⟨b, -, -⟩ := hE.basis
  have : FiniteDimensional F E := Module.Finite.of_basis b
  let T : E ≃ₗ[F] E :=
    { LinearMap.mulLeft F (z : E) with
      invFun := fun x => ((z⁻¹ : Eˣ) : E) * x
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  have hT : LinearEquiv.det T = Units.map (Algebra.norm F : E →* F) z := by
    ext
    rw [LinearEquiv.coe_det, Units.coe_map, Algebra.norm_apply]
    rfl
  rw [← hT]
  exact GlobalTheory.T.map_linearEquiv_addHaar_localField F E μ T

end GlobalTheory.KSp
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_mul_left_eq_inv_norm_haarChar_smul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (z : Eˣ), μ.map (fun x => (z : E) * x) = (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) z))⁻¹ • μ := by
  atlas_forward_decl GlobalTheory.KSp.map_mul_left_eq_norm_smul
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp.Cancel

open ValuativeRel
open scoped Topology NNReal

theorem compact_subset_cball {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {K : Set F} (hK : IsCompact K) :
    ∃ s : Fˣ, K ⊆ GlobalTheory.SplitWeil.cball s := by
  refine hK.elim_directed_cover (fun s : Fˣ => GlobalTheory.SplitWeil.cball s) GlobalTheory.SplitWeil.isOpen_cball ?_ ?_
  · intro x _
    by_cases hx : x = 0
    · exact Set.mem_iUnion.mpr ⟨1, by simp [GlobalTheory.SplitWeil.cball, hx]⟩
    · exact Set.mem_iUnion.mpr ⟨Units.mk0 x hx, by simp [GlobalTheory.SplitWeil.cball]⟩
  · intro a b
    rcases le_total (valuation F (a : F)) (valuation F (b : F)) with h | h
    · exact ⟨b, fun x hx => le_trans (show valuation F x ≤ _ from hx) h, fun x hx => hx⟩
    · exact ⟨a, fun x hx => hx, fun x hx => le_trans (show valuation F x ≤ _ from hx) h⟩

theorem punctured_neBot (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : (𝓝[≠] (0 : F)).NeBot := by
  by_contra h
  rw [Filter.not_neBot, ← isOpen_singleton_iff_punctured_nhds] at h
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset (h.mem_nhds rfl)
  exact s.ne_zero (hs (by simp [GlobalTheory.SplitWeil.cball]))

theorem mul_mem_cball_iff {F : Type} [Field F] [ValuativeRel F] (a s : Fˣ) (x : F) :
    valuation F ((a : F) * x) ≤ valuation F (s : F) ↔ valuation F x ≤ valuation F ((a⁻¹ * s : Fˣ) : F) := by
  rw [Units.val_mul, map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    le_inv_mul_iff₀ (by simp [zero_lt_iff])]

theorem gauss_cancel : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (t : Fˣ), t ∉ (Units.map (Algebra.norm F : E →* F)).range → ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → (∫ z in {z : E | Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ (Algebra.norm F z) ∂μ) + (nabs F t : ℂ) * ∫ z in {z : E | (t : F) * Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ ((t : F) * Algebra.norm F z) ∂μ = 0 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE ψ hψ hψ1 hψ0 _ _ μ _ t ht
  borelize F
  obtain ⟨hfd, hring, -, ht2, -, hN, -, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := GlobalTheory.SplitWeil.t2Space F
  haveI := punctured_neBot F
  haveI : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
  haveI : (𝓝[≠] (0 : E)).NeBot := Module.punctured_nhds_neBot F E 0
  haveI : LocallyCompactSpace E := by
    obtain ⟨L, -, h1, h2⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE 1
    exact h1.locallyCompactSpace_of_mem_nhds_of_addGroup (h2.mem_nhds L.zero_mem)
  have hμ0 : μ {0} = 0 := measure_singleton 0
  obtain ⟨lam, hlam, -⟩ := GlobalTheory.SplitWeil.exists_isUnitVol F
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.T.exists_integral_closedBall_addChar_eq_zero F lam ψ hψ hψ1 hψ0
  have hm : ∀ a : F, Measurable fun z : E => a * Algebra.norm F z := fun a =>
    (continuous_const.mul hN).measurable
  let m : Fˣ → Measure F := fun a => μ.map fun z : E => (a : F) * Algebra.norm F z
  let n : Fˣ → Measure F := fun a => distribHaarChar F a • m a
  have hmc : ∀ a, IsFiniteMeasureOnCompacts (m a) := fun a => ⟨fun K hK => by
    obtain ⟨s, hs⟩ := compact_subset_cball hK
    obtain ⟨L, hL, h1, -⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE (a⁻¹ * s)
    rw [Measure.map_apply (hm a) hK.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) (h1.measure_lt_top (μ := μ))
    intro z hz
    rw [hL]
    exact (mul_mem_cball_iff a s _).mp (hs hz)⟩
  have hnc : ∀ a, IsFiniteMeasureOnCompacts (n a) := fun a => by
    haveI := hmc a
    exact IsFiniteMeasureOnCompacts.smul_nnreal (m a) _
  have hn0 : ∀ a, n a {0} = 0 := fun a => by
    have : (fun z : E => (a : F) * Algebra.norm F z) ⁻¹' {0} = {0} := by
      ext z; simp [Algebra.norm_eq_zero_iff]
    simp only [n, m, Measure.smul_apply]
    rw [Measure.map_apply (hm a) (measurableSet_singleton 0), this, hμ0, smul_zero]
  have hn1 : ∀ (a : Fˣ) (b : Fˣ), b ∈ (Units.map (Algebra.norm F : E →* F)).range → n (b * a) = n a := by
    rintro a _ ⟨w, rfl⟩
    have h1 := GlobalTheory.T.map_mul_left_eq_inv_norm_haarChar_smul F E c δ hE μ w
    have h2 : m (Units.map (Algebra.norm F : E →* F) w * a) =
        (μ.map fun x => (w : E) * x).map fun z : E => (a : F) * Algebra.norm F z := by
      rw [Measure.map_map (hm a) (measurable_const_mul _)]
      simp only [m]
      congr 1
      funext z
      simp only [Units.val_mul, Units.coe_map, Function.comp, map_mul]
      ring
    simp only [n]
    rw [h2, h1, Measure.map_smul, smul_smul, map_mul, mul_right_comm,
      mul_inv_cancel₀ (distribHaarChar_pos).ne', one_mul]
  have hn2 : ∀ a u : Fˣ, (n a).map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • n (u * a) := by
    intro a u
    simp only [n, m]
    rw [Measure.map_smul, Measure.map_map (measurable_const_mul _) (hm a), smul_smul, map_mul,
      inv_mul_cancel_left₀ (distribHaarChar_pos).ne']
    congr 2
    funext z
    simp [mul_assoc]
  have hhom : ∀ u : Fˣ, (n 1 + n t).map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • (n 1 + n t) := by
    intro u
    rw [Measure.map_add _ _ (measurable_const_mul _), hn2, hn2, ← smul_add]
    congr 1
    by_cases hu : u ∈ (Units.map (Algebra.norm F : E →* F)).range
    · rw [hn1 _ _ hu, hn1 _ _ hu]
    · have h1 := GlobalTheory.T.mul_mem_range_norm_of_not_mem F E c δ hE u t hu ht
      have h2 := GlobalTheory.T.mul_mem_range_norm_of_not_mem F E c δ hE t t ht ht
      have h3 := hn1 1 _ h1
      have h4 := hn1 t _ (mul_mem h1 (inv_mem h2))
      rw [mul_one] at h3
      have h5 : u * t * (t * t)⁻¹ * t = u * 1 := by group
      rw [h5] at h4
      rw [h3, h4, add_comm]
  haveI := hnc 1
  haveI := hnc t
  haveI : IsFiniteMeasureOnCompacts (n 1 + n t) := ⟨fun K hK => by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  obtain ⟨r, hr⟩ := GlobalTheory.T.homogeneousMeasure_eq_smul_addHaar_localField F lam (n 1 + n t) (by rw [Measure.add_apply, hn0, hn0, add_zero]) hhom
  refine ⟨s₀, fun s hs => ?_⟩
  have hB := GlobalTheory.SplitWeil.isCompact_cball s
  have hint : ∀ a : Fˣ, ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂(n a) = (nabs F a : ℂ) *
      ∫ z in {z : E | (a : F) * Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ ((a : F) * Algebra.norm F z) ∂μ := by
    intro a
    simp only [n, m]
    rw [Measure.restrict_smul, integral_smul_nnreal_measure,
      setIntegral_map hB.measurableSet hψ.aestronglyMeasurable (hm a).aemeasurable]
    rfl
  have h1 : ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂(n 1 + n t) = 0 := by
    rw [hr, Measure.restrict_smul, integral_smul_nnreal_measure, hs₀ s hs, smul_zero]
  rw [Measure.restrict_add, integral_add_measure (hψ.continuousOn.integrableOn_compact hB)
    (hψ.continuousOn.integrableOn_compact hB), hint, hint] at h1
  simpa [GlobalTheory.SplitWeil.nabs_one] using h1

end GlobalTheory.KSp.Cancel
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussIntegral_normForm_nonNorm_cancel : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (t : Fˣ), t ∉ (Units.map (Algebra.norm F : E →* F)).range → ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → (∫ z in {z : E | Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ (Algebra.norm F z) ∂μ) + (nabs F t : ℂ) * ∫ z in {z : E | (t : F) * Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ ((t : F) * Algebra.norm F z) ∂μ = 0 := by
  atlas_forward_decl GlobalTheory.KSp.Cancel.gauss_cancel
end

section
section
noncomputable section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology Classical

namespace GlobalTheory.KSp

theorem setIntegral_addSubgroup_add {X : Type} [AddCommGroup X] [MeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddRightInvariant] (H : AddSubgroup X)
    (hH : MeasurableSet (H : Set X)) {h : X} (hh : h ∈ H) (g : X → ℂ) :
    ∫ x in (H : Set X), g (x + h) ∂μ = ∫ x in (H : Set X), g x ∂μ := by
  rw [← integral_indicator hH, ← integral_indicator hH]
  have key : (Set.indicator (H : Set X) fun x => g (x + h)) =
      fun x => Set.indicator (H : Set X) g (x + h) := by
    funext x
    by_cases hx : x ∈ H
    · have hx' : x + h ∈ H := H.add_mem hx hh
      simp [Set.indicator_apply, hx, hx']
    · have hx' : x + h ∉ H := fun h' => hx (by simpa using H.sub_mem h' hh)
      simp [Set.indicator_apply, hx, hx']
  rw [key, integral_add_right_eq_self (Set.indicator (H : Set X) g) h]

theorem setIntegral_pair_char {X : Type} [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddRightInvariant] {e : X → X → ℂ} (he : IsPair e)
    (M : AddSubgroup X) (hM : MeasurableSet (M : Set X)) (x : X) :
    ∫ m in (M : Set X), e x m ∂μ =
      if ∀ m ∈ (M : Set X), e m x = 1 then ((μ.real (M : Set X) : ℝ) : ℂ) else 0 := by
  split_ifs with hx
  · rw [setIntegral_congr_fun hM (g := fun _ => (1 : ℂ)) (fun m hm => by
      simp only; rw [he.symm]; exact hx m hm)]
    rw [setIntegral_const]
    simp
  · push_neg at hx
    obtain ⟨m₀, hm₀, hne⟩ := hx
    have h := setIntegral_addSubgroup_add μ M hM hm₀ (fun m => e x m)
    have hsplit : ∀ m, e x (m + m₀) = e x m * e x m₀ := fun m => by
      rw [he.symm x, he.add, he.symm m, he.symm m₀]
    simp only [hsplit] at h
    rw [integral_mul_const] at h
    have hne' : e x m₀ ≠ 1 := by rwa [he.symm]
    have h2 : (∫ m in (M : Set X), e x m ∂μ) * (e x m₀ - 1) = 0 := by
      rw [mul_sub, h]; ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.mp h3) hne'

theorem gauss_integral_eventually_const : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e →
    ∀ f : X → ℂ, IsLocallyConstant f → f 0 = 1 → (∀ x y, f (x + y) = f x * f y * e x y) →
    ∃ (γ : ℂ) (K : Set X), IsCompact K ∧ ∀ L : AddSubgroup X, IsCompact (L : Set X) → IsOpen (L : Set X) →
      K ⊆ L → ∫ x in (L : Set X), f x ∂μ = γ := by
  intro X _ _ _ _ hG μ _ e he f hf hf0 hfe
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  obtain ⟨M, hMc, hMo, hMf⟩ := hG.small {x | f x = 1} ((hf.isOpen_fiber 1).mem_nhds hf0)
  have hMn : (M : Set X) ∈ 𝓝 (0 : X) := hMo.mem_nhds M.zero_mem
  obtain ⟨K₀, hK₀c, hK₀⟩ := he.big _ hMn
  have hecont : ∀ m, Continuous (fun y => e m y) := fun m =>
    (he.lc.comp_continuous (continuous_const.prodMk continuous_id)).continuous
  set M' : Set X := {y | ∀ m ∈ (M : Set X), e m y = 1} with hM'
  have hM'cl : IsClosed M' := by
    have : M' = ⋂ m ∈ (M : Set X), {y | e m y = 1} := by ext; simp [M']
    rw [this]
    exact isClosed_biInter fun m _ => isClosed_eq (hecont m) continuous_const
  refine ⟨∫ x in M', f x ∂μ, (M : Set X) ∪ K₀, hMc.union hK₀c, ?_⟩
  intro L hLc hLo hKL
  have hML : (M : Set X) ⊆ L := Set.subset_union_left.trans hKL
  have hM'L : M' ⊆ L := fun y hy => hKL (Or.inr (hK₀ y hy))
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have hMm : MeasurableSet (M : Set X) := hMo.measurableSet
  have hM'm : MeasurableSet M' := hM'cl.measurableSet
  haveI : IsFiniteMeasure (μ.restrict (L : Set X)) := isFiniteMeasure_restrict.mpr hLc.measure_lt_top.ne
  haveI : IsFiniteMeasure (μ.restrict (M : Set X)) := isFiniteMeasure_restrict.mpr hMc.measure_lt_top.ne
  set A := ∫ x in (L : Set X), f x ∂μ with hA
  have h1 : ∀ m ∈ (M : Set X), ∫ x in (L : Set X), f x * e x m ∂μ = A := by
    intro m hm
    rw [hA, ← setIntegral_addSubgroup_add μ L hLm (hML hm) f]
    congr 1; funext x
    rw [hfe, show f m = 1 from hMf hm]; ring
  obtain ⟨C, hC⟩ := hLc.exists_bound_of_continuousOn hf.continuous.continuousOn
  have hint : Integrable (Function.uncurry fun m x => f x * e x m)
      ((μ.restrict (M : Set X)).prod (μ.restrict (L : Set X))) := by
    refine Integrable.mono' (integrable_const C) ?_ ?_
    · exact (Continuous.mul (hf.continuous.comp continuous_snd)
        (he.lc.continuous.comp (continuous_snd.prodMk continuous_fst))).aestronglyMeasurable
    · rw [Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (hMm.prod hLm) fun p hp => ?_
      show ‖f p.2 * e p.2 p.1‖ ≤ C
      rw [norm_mul, he.norm, mul_one]
      exact hC p.2 hp.2
  have h3 := integral_integral_swap hint
  rw [setIntegral_congr_fun hMm h1, setIntegral_const] at h3
  simp_rw [integral_const_mul, setIntegral_pair_char μ he M hMm] at h3
  have h4 : ∫ x in (L : Set X), f x * (if ∀ m ∈ (M : Set X), e m x = 1 then ((μ.real (M : Set X) : ℝ) : ℂ) else 0) ∂μ
      = ((μ.real (M : Set X) : ℝ) : ℂ) * ∫ x in M', f x ∂μ := by
    have : (fun x => f x * (if ∀ m ∈ (M : Set X), e m x = 1 then ((μ.real (M : Set X) : ℝ) : ℂ) else 0)) =
        Set.indicator M' (fun x => ((μ.real (M : Set X) : ℝ) : ℂ) * f x) := by
      funext x
      by_cases hx : x ∈ M'
      · rw [Set.indicator_of_mem hx, if_pos (show ∀ m ∈ (M : Set X), e m x = 1 from hx)]; ring
      · rw [Set.indicator_of_notMem hx, if_neg (show ¬ ∀ m ∈ (M : Set X), e m x = 1 from hx)]; ring
    rw [this, integral_indicator hM'm, Measure.restrict_restrict hM'm, Set.inter_eq_left.mpr hM'L,
      integral_const_mul]
  rw [h4, Complex.real_smul] at h3
  have hpos : ((μ.real (M : Set X) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, measureReal_def]
    exact ENNReal.toReal_ne_zero.mpr ⟨(hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne', hMc.measure_lt_top.ne⟩
  exact mul_left_cancel₀ hpos h3

end GlobalTheory.KSp
end
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussIntegral_quadraticChar_eventually_const : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ f : X → ℂ, IsLocallyConstant f → f 0 = 1 → (∀ x y, f (x + y) = f x * f y * e x y) → ∃ (γ : ℂ) (K : Set X), IsCompact K ∧ ∀ L : AddSubgroup X, IsCompact (L : Set X) → IsOpen (L : Set X) → K ⊆ L → ∫ x in (L : Set X), f x ∂μ = γ := by
  atlas_forward_decl GlobalTheory.KSp.gauss_integral_eventually_const
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.GaussNorm

open GlobalTheory.SplitWeil (cball)

section Ball

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_cball_sup (a b : Fˣ) : ∃ s : Fˣ, cball a ⊆ cball s ∧ cball b ⊆ cball s := by
  rcases le_total (ValuativeRel.valuation F (a : F)) (ValuativeRel.valuation F (b : F)) with h | h
  · exact ⟨b, fun x (hx : ValuativeRel.valuation F x ≤ _) => (le_trans hx h : ValuativeRel.valuation F x ≤ _),
      Set.Subset.rfl⟩
  · exact ⟨a, Set.Subset.rfl,
      fun x (hx : ValuativeRel.valuation F x ≤ _) => (le_trans hx h : ValuativeRel.valuation F x ≤ _)⟩

theorem exists_cball_of_isCompact {K : Set F} (hK : IsCompact K) : ∃ s : Fˣ, K ⊆ cball s := by
  have hcov : K ⊆ ⋃ s : Fˣ, cball s := by
    intro x _
    by_cases hx : x = 0
    · exact Set.mem_iUnion.mpr ⟨1, by simp [cball, hx]⟩
    · exact Set.mem_iUnion.mpr ⟨Units.mk0 x hx, by simp [cball]⟩
  have hd : Directed (· ⊆ ·) (fun s : Fˣ => cball s) := by
    intro a b
    obtain ⟨s, h1, h2⟩ := exists_cball_sup a b
    exact ⟨s, h1, h2⟩
  exact hK.elim_directed_cover _ (fun s => GlobalTheory.SplitWeil.isOpen_cball s) hcov hd

theorem mul_mem_cball_iff (t s : Fˣ) (x : F) : (t : F) * x ∈ cball s ↔ x ∈ cball (t⁻¹ * s) := by
  simp only [cball, Set.mem_setOf_eq, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  rw [le_inv_mul_iff₀ (by simp [zero_lt_iff])]

end Ball

section Polar

variable {F : Type} [Field F] [CharZero F] {E : Type} [Field E] [Algebra F E] {c : E →ₐ[F] E} {δ : E}

theorem algebraMap_norm_add (hE : IsQuad c δ) (x y : E) :
    algebraMap F E (Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y) = x * c y + y * c x := by
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  rw [map_sub, map_sub, hE.algebraMap_norm, hE.algebraMap_norm, hE.algebraMap_norm, map_add]
  ring

def polar (hE : IsQuad c δ) : E →ₗ[F] E →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y)
    (fun x x' y => hE.algebraMap_injective (by
      simp only [map_add, algebraMap_norm_add hE]; ring))
    (fun a x y => hE.algebraMap_injective (by
      show algebraMap F E (Algebra.norm F (a • x + y) - Algebra.norm F (a • x) - Algebra.norm F y) =
        algebraMap F E (a • (Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y))
      rw [algebraMap_norm_add hE, smul_eq_mul, map_mul, algebraMap_norm_add hE, Algebra.smul_def, map_mul,
        AlgHom.commutes]; ring))
    (fun x y y' => hE.algebraMap_injective (by
      simp only [map_add, algebraMap_norm_add hE]; ring))
    (fun a x y => hE.algebraMap_injective (by
      show algebraMap F E (Algebra.norm F (x + a • y) - Algebra.norm F x - Algebra.norm F (a • y)) =
        algebraMap F E (a • (Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y))
      rw [algebraMap_norm_add hE, smul_eq_mul, map_mul, algebraMap_norm_add hE, Algebra.smul_def, map_mul,
        AlgHom.commutes]; ring))

theorem polar_apply (hE : IsQuad c δ) (x y : E) :
    polar hE x y = Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y := rfl

theorem algebraMap_polar (hE : IsQuad c δ) (x y : E) : algebraMap F E (polar hE x y) = x * c y + y * c x :=
  algebraMap_norm_add hE x y

theorem polar_symm (hE : IsQuad c δ) (x y : E) : polar hE x y = polar hE y x := by
  rw [polar_apply, polar_apply, add_comm x y]; ring

theorem polar_nondeg (hE : IsQuad c δ) (y : E) (hy : ∀ x, polar hE x y = 0) : y = 0 := by
  have h1 := congrArg (algebraMap F E) (hy y)
  rw [algebraMap_polar, map_zero] at h1
  have h2 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]; exact (map_ne_zero _).mpr two_ne_zero
  have h3 : (2 : E) * (y * c y) = 0 := by rw [two_mul]; exact h1
  rcases mul_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left h2) with h | h
  · exact h
  · rw [← hE.invol y, h, map_zero]

theorem polar_half (hE : IsQuad c δ) (z : E) : polar hE ((2 : F)⁻¹ • z) z = Algebra.norm F z := by
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  apply hE.algebraMap_injective
  rw [algebraMap_polar, hE.algebraMap_norm, Algebra.smul_def, map_mul, AlgHom.commutes]
  have h2 : algebraMap F E (2 : F)⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  linear_combination (z * c z) * h2

theorem norm_add_eq (hE : IsQuad c δ) (x y : E) :
    Algebra.norm F (x + y) = Algebra.norm F x + Algebra.norm F y + polar hE x y := by
  rw [polar_apply]; ring

end Polar

end GlobalTheory.KSp.GaussNorm

namespace GlobalTheory.KSp

open GlobalTheory.KSp.GaussNorm GlobalTheory.SplitWeil

theorem hasGauss_norm_mul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], ∃ g : ℂ, ∀ t : Fˣ, HasGauss μ (fun z => ψ ((t : F) * Algebra.norm F z)) (g * (sgn E t * ((nabs F t)⁻¹ : ℝ))) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE ψ hψ hψ1 hψ0 _ _ μ _
  obtain ⟨hfin, htr, -, -, -, hNc, -, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := hfin
  haveI := htr
  have hgood : Good E := GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional F E
  have hpair : IsPair fun x y => ψ (polar hE x y) :=
    GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F E ψ hψ hψ1 hψ0 (polar hE) (polar_symm hE) (polar_nondeg hE)
  set f : E → ℂ := fun z => ψ (Algebra.norm F z) with hf
  have hlc : IsLocallyConstant f := by
    have h := hpair.lc.comp_continuous (show Continuous fun z : E => ((2 : F)⁻¹ • z, z) by fun_prop)
    have heq : ((fun p : E × E => ψ (polar hE p.1 p.2)) ∘ fun z : E => ((2 : F)⁻¹ • z, z)) = f := by
      funext z; simp only [Function.comp_apply, f, polar_half]
    rwa [heq] at h
  have hf0 : f 0 = 1 := by simp [f]
  have hfadd : ∀ x y, f (x + y) = f x * f y * ψ (polar hE x y) := by
    intro x y
    simp only [f]
    rw [norm_add_eq hE, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  obtain ⟨γ, K₁, hK₁, hγ⟩ := GlobalTheory.T.gaussIntegral_quadraticChar_eventually_const E hgood μ _ hpair f hlc hf0 hfadd
  have hG : HasGauss μ f γ := by
    intro K hK
    obtain ⟨L, hLc, hLo, hL⟩ := hgood.large (K ∪ K₁) (hK.union hK₁)
    exact ⟨L, hLc, hLo, Set.subset_union_left.trans hL, hγ L hLc hLo (Set.subset_union_right.trans hL)⟩
  refine ⟨γ, fun t => ?_⟩
  by_cases ht : t ∈ (Units.map (Algebra.norm F : E →* F)).range
  · obtain ⟨w, hw⟩ := ht
    let T : E ≃ₜ+ E :=
      { toFun := fun z => (w : E) * z
        invFun := fun z => ((w⁻¹ : Eˣ) : E) * z
        left_inv := fun z => by simp
        right_inv := fun z => by simp
        map_add' := fun x y => mul_add _ _ _
        continuous_toFun := continuous_const.mul continuous_id
        continuous_invFun := continuous_const.mul continuous_id }
    have hT : μ.map T = (distribHaarChar F t)⁻¹ • μ := by
      have h := GlobalTheory.T.map_mul_left_eq_inv_norm_haarChar_smul F E c δ hE μ w
      rw [hw] at h
      exact h
    have h := GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale E E μ μ T _ f γ hT hG
    have e1 : (fun z : E => ψ ((t : F) * Algebra.norm F z)) = fun x => f (T x) := by
      funext z
      show ψ ((t : F) * Algebra.norm F z) = ψ (Algebra.norm F ((w : E) * z))
      rw [MonoidHom.map_mul (Algebra.norm F) (w : E) z, ← hw, Units.coe_map]
    have hs : sgn E t = 1 := by rw [sgn, if_pos ⟨w, hw⟩]
    have e2 : γ * (sgn E t * (((nabs F t)⁻¹ : ℝ) : ℂ)) = (((((distribHaarChar F t)⁻¹ : NNReal) : ℝ)) : ℂ) * γ := by
      rw [hs, one_mul, mul_comm]
      simp [nabs]
    rw [e1, e2]
    exact h
  · obtain ⟨s₀, hcan⟩ := GlobalTheory.T.gaussIntegral_normForm_nonNorm_cancel F E c δ hE ψ hψ hψ1 hψ0 μ t ht
    have hs : sgn E t = -1 := by rw [sgn, if_neg ht]
    intro K hK
    obtain ⟨a₁, ha₁⟩ := exists_cball_of_isCompact (hK.image hNc)
    obtain ⟨a₂, ha₂⟩ := exists_cball_of_isCompact (hK₁.image hNc)
    obtain ⟨s', hs'1, hs'2⟩ := exists_cball_sup (t * a₁) a₂
    obtain ⟨s, hs1, hs2⟩ := exists_cball_sup s' s₀
    obtain ⟨L, hLeq, hLc, hLo⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE (t⁻¹ * s)
    obtain ⟨L₁, hL₁eq, hL₁c, hL₁o⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE s
    have hset : {z : E | (t : F) * Algebra.norm F z ∈ cball s} = (L : Set E) := by
      rw [hLeq]; ext z; exact mul_mem_cball_iff t s _
    have hK₁L₁ : K₁ ⊆ L₁ := by
      intro z hz
      rw [hL₁eq]
      exact hs1 (hs'2 (ha₂ ⟨z, hz, rfl⟩))
    have hKL : K ⊆ L := by
      intro z hz
      rw [← hset]
      have h1 : Algebra.norm F z ∈ cball a₁ := ha₁ ⟨z, hz, rfl⟩
      have h2 : (t : F) * Algebra.norm F z ∈ cball (t * a₁) := by
        rw [mul_mem_cball_iff, inv_mul_cancel_left]; exact h1
      exact hs1 (hs'1 h2)
    have hs₀ : (s₀ : F) ∈ cball s := hs2 (show ValuativeRel.valuation F (s₀ : F) ≤ ValuativeRel.valuation F (s₀ : F) from le_refl _)
    have h1 := hcan s hs₀
    rw [← hL₁eq, hγ L₁ hL₁c hL₁o hK₁L₁, hset] at h1
    refine ⟨L, hLc, hLo, hKL, ?_⟩
    have hn : (nabs F t : ℂ) ≠ 0 := by exact_mod_cast (nabs_pos F t).ne'
    rw [hs, Complex.ofReal_inv]
    field_simp
    linear_combination h1
end GlobalTheory.KSp
end
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussIntegral_normForm_scaled_eq_sign_abs_inv : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], ∃ g : ℂ, ∀ t : Fˣ, HasGauss μ (fun z => ψ ((t : F) * Algebra.norm F z)) (g * (sgn E t * ((nabs F t)⁻¹ : ℝ))) := by
  atlas_forward_decl GlobalTheory.KSp.hasGauss_norm_mul
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem hasGauss_diag_norm : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ g : ℂ, ∀ t : α → ν → Fˣ, HasGauss μ (fun x => ψ (∑ i, ∑ j, (t i j : F) * Algebra.norm F (x i j))) (g * ∏ i, ∏ j, (sgn E (t i j) * ((nabs F (t i j))⁻¹ : ℝ))) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ ψ hψ hn h1 _ _ μ _
  obtain ⟨hfd, -, -, -, -, -, -, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  haveI : FiniteDimensional F E := hfd
  have hGE : Good E := GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional F E
  haveI := hGE.grp; haveI := hGE.lc; haveI := hGE.sc; haveI := hGE.t2
  let μE : Measure E := Measure.addHaar
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.gaussIntegral_normForm_scaled_eq_sign_abs_inv F E c δ hE ψ hψ hn h1 μE
  have hGM : Good (Matrix α ν E) := (hmat α ν).2
  haveI := hGM.grp; haveI := hGM.lc; haveI := hGM.sc
  let T : Matrix α ν E ≃ₜ+ (α × ν → E) :=
    { toFun := fun x p => x p.1 p.2
      invFun := fun y i j => y (i, j)
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_add' := fun x y => rfl
      continuous_toFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
      continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j) }
  haveI : BorelSpace (α × ν → E) := Pi.borelSpace
  haveI : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  have hr : μ.map T = (μ.map T).addHaarScalarFactor (Measure.pi fun _ : α × ν => μE) •
      Measure.pi fun _ : α × ν => μE := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨(((μ.map T).addHaarScalarFactor (Measure.pi fun _ : α × ν => μE) : ℝ) : ℂ) *
    g₁ ^ Fintype.card (α × ν), fun t => ?_⟩
  have hpi := GlobalTheory.T.hasGaussIntegralCompactOpen_pi E hGE μE (α × ν) (fun p z => ψ ((t p.1 p.2 : F) * Algebra.norm F z))
    (fun p => g₁ * (sgn E (t p.1 p.2) * ((nabs F (t p.1 p.2))⁻¹ : ℝ))) (fun p => hg₁ _)
  have hm := GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale _ _ μ _ T _ _ _ hr hpi
  have hsum : ∀ (s : Finset (α × ν)) (f : α × ν → F), ψ (∑ p ∈ s, f p) = ∏ p ∈ s, ψ (f p) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  convert hm using 1
  · funext x
    rw [← Fintype.sum_prod_type', hsum]
    rfl
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.prod_prod_type, mul_assoc]

end GlobalTheory.KSp
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussIntegral_diagonal_hermitianForm_matrices : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ g : ℂ, ∀ t : α → ν → Fˣ, HasGauss μ (fun x => ψ (∑ i, ∑ j, (t i j : F) * Algebra.norm F (x i j))) (g * ∏ i, ∏ j, (sgn E (t i j) * ((nabs F (t i j))⁻¹ : ℝ))) := by
  atlas_forward_decl GlobalTheory.KSp.hasGauss_diag_norm
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem pr_eq_half_trace_mat (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α : Type} [Fintype α] [DecidableEq α] {ν : Type} [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (x y : Matrix α ν E) :
  pr c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  simp only [pr, form, GlobalTheory.WeilM.hTens, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr, stdJ, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Pi.zero_apply, Matrix.zero_apply, map_zero, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, one_apply, Matrix.trace, mul_apply, transpose_apply, map_apply, diag_apply]
  congr 2
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pr_diag_norm : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (u : Matrix α α E) (D' : α → F) (a : Matrix ν ν E) (D : ν → F), Q = u * diagonal (fun i => algebraMap F E (D' i)) * (u.map c)ᵀ → ∀ x : Matrix α ν E, 2⁻¹ * pr c Q x (x * (a * diagonal (fun j => algebraMap F E (D j)) * (a.map c)ᵀ)) = ∑ i, ∑ j, (2⁻¹ * D' i * D j) * Algebra.norm F ((uᵀ * x * a) i j) := by
  intro F _ _ E _ _ c δ hE α _ _ ν _ _ Q _ u D' a D hQu x
  have hc : ∀ z, c (c z) = z := hE.invol
  have hmm : ∀ {m n : Type} (M : Matrix m n E), (M.map c).map c = M := fun M => by ext i j; simp [hc]
  have hd : ∀ {m : Type} [Fintype m] [DecidableEq m] (d : m → F),
      (diagonal (fun i => algebraMap F E (d i))).map c = diagonal (fun i => algebraMap F E (d i)) := by
    intro m _ _ d; ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
  set dD' := diagonal (fun i => algebraMap F E (D' i))
  set dD := diagonal (fun j => algebraMap F E (D j))
  set Y := uᵀ * x * a with hY
  have hQT : Qᵀ = u.map c * dD' * uᵀ := by
    rw [hQu, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  have hbs : ((x * (a * dD * (a.map c)ᵀ)).map c)ᵀ = a * dD * (a.map c)ᵀ * (x.map c)ᵀ := by
    rw [Matrix.map_mul (f := c), Matrix.map_mul (f := c), Matrix.map_mul (f := c), transpose_mul, transpose_mul,
      transpose_mul, hd, diagonal_transpose, transpose_map, hmm, ← transpose_map, transpose_transpose]
    simp only [Matrix.mul_assoc]
    rfl
  have hYs : (Y.map c)ᵀ = (a.map c)ᵀ * (x.map c)ᵀ * u.map c := by
    rw [hY, Matrix.map_mul (f := c), Matrix.map_mul (f := c), transpose_mul, transpose_mul, transpose_map,
      transpose_transpose]
    simp only [Matrix.mul_assoc]
  have htr : Matrix.trace (Qᵀ * (x * ((x * (a * dD * (a.map c)ᵀ)).map c)ᵀ)) = Matrix.trace (dD' * Y * dD * (Y.map c)ᵀ) := by
    rw [hQT, hbs, hYs, hY]
    rw [show u.map c * dD' * uᵀ * (x * (a * dD * (a.map c)ᵀ * (x.map c)ᵀ)) =
      u.map c * (dD' * uᵀ * x * a * dD * (a.map c)ᵀ * (x.map c)ᵀ) by simp only [Matrix.mul_assoc], trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hsum : Matrix.trace (dD' * Y * dD * (Y.map c)ᵀ) =
      algebraMap F E (∑ i, ∑ j, D' i * D j * Algebra.norm F (Y i j)) := by
    simp only [Matrix.trace, diag_apply, mul_apply, dD', dD, diagonal_apply, ite_mul, mul_ite, zero_mul, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, transpose_apply, map_apply,
      map_sum, map_mul, hE.algebraMap_norm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨b, -, -⟩ := hE.basis
  haveI : Module.Free F E := Module.Free.of_basis b
  haveI : Module.Finite F E := Module.Finite.of_basis b
  have hfin : Module.finrank F E = 2 := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [pr_eq_half_trace_mat, htr, hsum, Algebra.trace_algebraMap, hfin, nsmul_eq_mul, Nat.cast_ofNat,
    inv_mul_cancel_left₀ (two_ne_zero : (2 : F) ≠ 0), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.KSp
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianMatrixColumnPairing_diagonal_norm : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (u : Matrix α α E) (D' : α → F) (a : Matrix ν ν E) (D : ν → F), Q = u * diagonal (fun i => algebraMap F E (D' i)) * (u.map c)ᵀ → ∀ x : Matrix α ν E, 2⁻¹ * pr c Q x (x * (a * diagonal (fun j => algebraMap F E (D j)) * (a.map c)ᵀ)) = ∑ i, ∑ j, (2⁻¹ * D' i * D j) * Algebra.norm F ((uᵀ * x * a) i j) := by
  atlas_forward_decl GlobalTheory.KSp.pr_diag_norm
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem KSp.sgn_mul_of_isQuad : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (s t : Fˣ), sgn E (s * t) = sgn E s * sgn E t := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE s t
  set H := (Units.map (Algebra.norm F : E →* F)).range with hH
  unfold sgn
  rw [← hH]
  by_cases hs : s ∈ H <;> by_cases ht : t ∈ H
  · simp [hs, ht, H.mul_mem hs ht]
  · have : s * t ∉ H := fun h => ht ((H.mul_mem_cancel_left hs).mp h)
    simp [hs, ht, this]
  · have : s * t ∉ H := fun h => hs ((H.mul_mem_cancel_right ht).mp h)
    simp [hs, ht, this]
  · have : s * t ∈ H := GlobalTheory.T.mul_mem_range_norm_of_not_mem F E c δ hE s t hs ht
    simp [hs, ht, this]

end GlobalTheory
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localNormResidueSign_mul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (s t : Fˣ), sgn E (s * t) = sgn E s * sgn E t := by
  atlas_forward_decl GlobalTheory.KSp.sgn_mul_of_isQuad
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.GaussMain

section Scalar

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
  (c : E →ₐ[F] E) {δ : E} (hE : IsQuad c δ)

def sgnHom : Fˣ →* ℂ where
  toFun := sgn E
  map_one' := by simp only [sgn]; exact if_pos (one_mem _)
  map_mul' s t := GlobalTheory.T.localNormResidueSign_mul F E c δ hE s t

theorem sgn_inv (t : Fˣ) : sgn E t⁻¹ = sgn E t := by
  have h := (Units.map (Algebra.norm F : E →* F)).range.inv_mem_iff (x := t)
  unfold sgn
  by_cases ht : t ∈ (Units.map (Algebra.norm F : E →* F)).range
  · rw [if_pos ht, if_pos (h.mpr ht)]
  · rw [if_neg ht, if_neg (mt h.mp ht)]

variable {ν : Type} [Fintype ν] [DecidableEq ν]

theorem det_herm (a : GL ν E) (D : ν → Fˣ) :
    ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ).det =
      (Matrix.GeneralLinearGroup.det a : E) * c (Matrix.GeneralLinearGroup.det a : E) *
        algebraMap F E ((∏ j, D j : Fˣ) : F) := by
  have hm : ((a : Matrix ν ν E).map c).det = c (a : Matrix ν ν E).det := (RingHom.map_det (c : E →+* E) _).symm
  rw [det_mul, det_mul, det_transpose, det_diagonal, hm]
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod, map_prod]
  ring

include hE in

theorem sc_det_inv (χ : Eˣ →* Circle) (m : ℕ) (hχ : ResEtaPow (R := F) ⊥ χ m) (a : GL ν E) (D : ν → Fˣ) :
    sc F χ m ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ).det⁻¹ =
      (((distribHaarChar F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det a)) : ℝ)⁻¹ ^ m : ℝ) : ℂ) *
        (∏ j, (sgn E (D j) * ((nabs F (D j))⁻¹ : ℝ))) ^ m := by
  obtain ⟨-, hmul, -, -, -, halg, hzc⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE m χ hχ
  set d : Eˣ := Matrix.GeneralLinearGroup.det a with hd
  have hdet : ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ).det⁻¹ =
      ((d⁻¹ : Eˣ) : E) * c ((d⁻¹ : Eˣ) : E) * algebraMap F E (((∏ j, D j)⁻¹ : Fˣ) : F) := by
    rw [det_herm c a D]
    simp only [hd, Units.val_inv_eq_inv_val, map_inv₀, mul_inv]
  have e1 : nabs F (Units.map (Algebra.norm F : E →* F) d⁻¹) =
      ((distribHaarChar F (Units.map (Algebra.norm F : E →* F) d)) : ℝ)⁻¹ := by
    simp [nabs, map_inv]
  have e2 : sgn E (∏ j, D j)⁻¹ = ∏ j, sgn E (D j) := by
    rw [sgn_inv]; exact map_prod (sgnHom c hE) D Finset.univ
  have e3 : nabs F (∏ j, D j)⁻¹ = ∏ j, (nabs F (D j))⁻¹ := by
    simp [nabs, map_prod, map_inv]
  rw [hdet, hmul, hzc, halg, e1, e2, e3, Finset.prod_mul_distrib]
  push_cast
  ring

end Scalar

section Equiv

variable {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

def glT (u : GL α E) : GL α E :=
  ⟨(u : Matrix α α E)ᵀ, ((u⁻¹ : GL α E) : Matrix α α E)ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one], by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

def sandwich (U : GL α E) (A : GL ν E) : Matrix α ν E ≃ₜ+ Matrix α ν E where
  toFun x := (U : Matrix α α E) * x * (A : Matrix ν ν E)
  invFun y := ((U⁻¹ : GL α E) : Matrix α α E) * y * ((A⁻¹ : GL ν E) : Matrix ν ν E)
  left_inv x := by
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv y := by
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  map_add' x y := by simp only [Matrix.mul_add, Matrix.add_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

end Equiv

theorem hasGauss_herm : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ γ₀ : ℂ, ∀ b : Matrix ν ν E, (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) (γ₀ * sc F χ (Fintype.card α) b.det⁻¹) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψ0 χ hχc hχ _ _ μ _
  haveI : IsTopologicalRing E := (GlobalTheory.T.quadExt_topological_properties F E c δ hE).2.1
  obtain ⟨u, D', hQd⟩ := GlobalTheory.T.exists_GL_diagonal_congruent_hermitian F E c δ hE α Q (Matrix.ext fun i j => hQ.1 i j) hQ.2.ne_zero
  obtain ⟨g0, hg0⟩ := GlobalTheory.T.gaussIntegral_diagonal_hermitianForm_matrices F E c δ hE α ν ψ hψ hψ1 hψ0 μ
  let s : α → Fˣ := fun i =>
    Units.mk0 (2⁻¹ * (D' i : F)) (mul_ne_zero (inv_ne_zero two_ne_zero) (D' i).ne_zero)
  let U : GL α E := glT u
  refine ⟨g0 * (((distribHaarChar F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det U)) : ℝ)⁻¹ ^
    Fintype.card ν : ℝ) : ℂ) * (∏ i, (sgn E (s i) * ((nabs F (s i))⁻¹ : ℝ))) ^ Fintype.card ν, ?_⟩
  intro b hb hdet
  obtain ⟨a, D, rfl⟩ := GlobalTheory.T.exists_GL_diagonal_congruent_hermitian F E c δ hE ν b hb hdet
  let t : α → ν → Fˣ := fun i j => s i * D j
  have hfun : (fun x : Matrix α ν E => ψ (2⁻¹ * pr c Q x (x * ((a : Matrix ν ν E) *
      diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ)))) =
      fun x => (fun y : Matrix α ν E => ψ (∑ i, ∑ j, (t i j : F) * Algebra.norm F (y i j))) (sandwich U a x) := by
    funext x
    rw [GlobalTheory.T.hermitianMatrixColumnPairing_diagonal_norm F E c δ hE α ν Q hQ (u : Matrix α α E) (fun i => (D' i : F)) (a : Matrix ν ν E)
      (fun j => (D j : F)) hQd x]
    congr 1
  have key := GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale (Matrix α ν E) (Matrix α ν E) μ μ (sandwich U a) _ _ _
    (GlobalTheory.T.map_twoSided_mul_haar_matrix_quadraticExt F E c δ hE α ν μ U a) (hg0 t)
  rw [hfun]
  convert key using 1
  rw [sc_det_inv c hE χ _ hχ a D]
  have ht : ∀ i j, sgn E (t i j) * (((nabs F (t i j))⁻¹ : ℝ) : ℂ) =
      (sgn E (s i) * (((nabs F (s i))⁻¹ : ℝ) : ℂ)) * (sgn E (D j) * (((nabs F (D j))⁻¹ : ℝ) : ℂ)) := by
    intro i j
    simp only [t]
    rw [GlobalTheory.T.localNormResidueSign_mul F E c δ hE, GlobalTheory.SplitWeil.nabs_mul F, mul_inv]
    push_cast
    ring
  rw [Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ht i j]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]
  push_cast
  ring

end GlobalTheory.KSp.GaussMain
end
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGaussIntegral_hermitian_quadratic_character : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ γ₀ : ℂ, ∀ b : Matrix ν ν E, (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) (γ₀ * sc F χ (Fintype.card α) b.det⁻¹) := by
  atlas_forward_decl GlobalTheory.KSp.GaussMain.hasGauss_herm
end
