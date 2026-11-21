import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveClosedPointChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PClosedPointChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PClosedPointUnitSection

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def segre (y : (Σ k, ι k) → Ω) : (Σ _ : Unit, ∀ k, ι k) → Ω :=
  fun q ↦ ∏ k, y ⟨k, q.2 k⟩

omit [∀ k, Fintype (ι k)] in
theorem segre_ne_zero_iff (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) :
    segre y ⟨(), f⟩ ≠ 0 ↔ ∀ k, y ⟨k, f k⟩ ≠ 0 := by
  simp [segre, Finset.prod_ne_zero_iff]

omit [∀ k, Fintype (ι k)] in

theorem segre_ratio (y : (Σ k, ι k) → Ω) (f g : ∀ k, ι k) :
    segre y ⟨(), g⟩ / segre y ⟨(), f⟩ = ∏ k, y ⟨k, g k⟩ / y ⟨k, f k⟩ := by
  simp [segre, Finset.prod_div_distrib]

omit [∀ k, Fintype (ι k)] in

theorem prod_ratio_update [DecidableEq K] (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0)
    (p : Σ k, ι k) :
    ∏ k, y ⟨k, Function.update f p.1 p.2 k⟩ / y ⟨k, f k⟩ = y p / y ⟨p.1, f p.1⟩ := by
  rw [Finset.prod_eq_single p.1]
  · simp
  · intro k _ hk
    rw [Function.update_of_ne hk, div_self (hf k)]
  · simp

omit [∀ k, Fintype (ι k)] in

theorem chartRingZ_segre (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) :
    chartRingZ (segre y) (fun _ ↦ f) = chartRingZ y f := by
  classical
  apply le_antisymm
  · rw [chartRingZ, Algebra.adjoin_le_iff]
    rintro _ ⟨⟨⟨⟩, g⟩, rfl⟩
    change segre y ⟨(), g⟩ / segre y ⟨(), f⟩ ∈ chartRingZ y f
    rw [segre_ratio]
    exact prod_mem fun k _ ↦ Algebra.subset_adjoin ⟨⟨k, g k⟩, rfl⟩
  · rw [chartRingZ, Algebra.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    change y p / y ⟨p.1, f p.1⟩ ∈ chartRingZ (segre y) (fun _ ↦ f)
    rw [← prod_ratio_update y f hf p, ← segre_ratio]
    exact Algebra.subset_adjoin ⟨⟨(), Function.update f p.1 p.2⟩, rfl⟩

theorem charZero_of_isArithVar {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn ↦ ?_
  have hmem : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_C]
    rw [eq_intCast, Int.cast_natCast, ← map_natCast (C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hP.2.2.1, Ideal.mem_bot] at hmem
  exact_mod_cast hmem

theorem exists_chart {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) :
    ∃ f : ∀ k, ι k, ∀ k, y ⟨k, f k⟩ ≠ 0 := by
  have h : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k ↦ by
    obtain ⟨i, hi⟩ := hP.2.1.2.2 k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]
  choose f hf using h
  exact ⟨f, hf⟩

theorem isAlgebraic_segre_ratio [CharZero Ω] {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1)
    (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) :
    IsAlgebraic ℚ (segre y ⟨(), g⟩ / segre y ⟨(), f⟩) := by
  rw [segre_ratio]
  refine (IsIntegral.prod _ fun k _ ↦ ?_).isAlgebraic
  exact (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_ratio hP f hf ⟨k, g k⟩).isIntegral

theorem isArithVar_segre [DecidableEq K] [CharZero Ω] {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1)
    (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) : IsArithVar (mCoordIdeal (segre y)) 1 := by
  refine CoordConeArithVar.full Unit (fun _ ↦ ∀ k, ι k) Ω (segre y) (fun _ ↦ f) 0 Fin.elim0 ⟨()⟩
    (fun _ ↦ (segre_ne_zero_iff y f).mpr hf) algebraicIndependent_empty_type (fun i ↦ i.elim0) ?_
  rintro _ ⟨⟨⟨⟩, g⟩, rfl⟩
  exact IsAlgebraic.extendScalars (RingHom.injective _) (isAlgebraic_segre_ratio hP f hf g)

end SegreChart

end

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

set_option linter.unusedSectionVars false

noncomputable section

namespace CurveClosedPointChartAlt

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω] (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k)

abbrev fld : IntermediateField ℚ Ω :=
  CoordinateConeArithVar.ratioField (SegreChart.segre y) (fun _ ↦ f)

def pt : (Σ _ : Unit, ∀ k, ι k) → fld y f :=
  CoordinateConeArithVar.ratioPtL (SegreChart.segre y) (fun _ ↦ f)

theorem coe_pt (q : Σ _ : Unit, ∀ k, ι k) :
    ((pt y f q : fld y f) : Ω) = SegreChart.segre y q / SegreChart.segre y ⟨(), f⟩ := rfl

variable {y f}

theorem numberField (hP : IsArithVar (mCoordIdeal y) 1) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) : NumberField (fld y f) := by
  have : Finite (coneRatios (SegreChart.segre y) fun _ ↦ f) := (Set.finite_range _).to_subtype
  have : FiniteDimensional ℚ (fld y f) := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨⟨⟨⟩, g⟩, rfl⟩
    exact (SegreChart.isAlgebraic_segre_ratio hP f hf g).isIntegral)
  exact {}

theorem isArithVar_pt (hP : IsArithVar (mCoordIdeal y) 1) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) :
    IsArithVar (mCoordIdeal (pt y f)) 1 := by
  rw [pt, CoordinateConeArithVar.mCoordIdeal_ratioPtL _ _ fun _ ↦ (SegreChart.segre_ne_zero_iff y f).mpr hf]
  exact SegreChart.isArithVar_segre hP f hf

theorem pt_ne_zero_iff (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) :
    pt y f ⟨(), g⟩ ≠ 0 ↔ ∀ k, y ⟨k, g k⟩ ≠ 0 := by
  rw [← SegreChart.segre_ne_zero_iff, ne_eq, ← ZeroMemClass.coe_eq_zero, coe_pt, div_eq_zero_iff, not_or,
    and_iff_left ((SegreChart.segre_ne_zero_iff y f).mpr hf)]

theorem coe_pt_ratio (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g h : ∀ k, ι k) :
    ((pt y f ⟨(), h⟩ / pt y f ⟨(), g⟩ : fld y f) : Ω) =
      SegreChart.segre y ⟨(), h⟩ / SegreChart.segre y ⟨(), g⟩ := by
  rw [IntermediateField.coe_div, coe_pt, coe_pt,
    div_div_div_cancel_right₀ ((SegreChart.segre_ne_zero_iff y f).mpr hf)]

theorem map_chartRingZ (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) (hg : ∀ k, y ⟨k, g k⟩ ≠ 0) :
    (chartRingZ (pt y f) (fun _ ↦ g)).map (algebraMap (fld y f) Ω).toIntAlgHom = chartRingZ y g := by
  rw [chartRingZ, ← Algebra.adjoin_image, ← Set.range_comp, ← SegreChart.chartRingZ_segre y g hg, chartRingZ]
  congr 2
  funext q
  obtain ⟨⟨⟩, h⟩ := q
  exact coe_pt_ratio hf g h

theorem mem_chartRingZ_iff (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) (hg : ∀ k, y ⟨k, g k⟩ ≠ 0)
    (x : fld y f) : x ∈ chartRingZ (pt y f) (fun _ ↦ g) ↔ (x : Ω) ∈ chartRingZ y g := by
  rw [← map_chartRingZ hf g hg, Subalgebra.mem_map]
  refine ⟨fun h ↦ ⟨x, h, rfl⟩, ?_⟩
  rintro ⟨x', hx', he⟩
  rwa [show x' = x from Subtype.ext he] at hx'

theorem mem_curveRing_iff (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (x : fld y f) :
    x ∈ curveRing (pt y f) ↔ (x : Ω) ∈ curveRing y := by
  rw [mem_curveRing, mem_curveRing]
  refine ⟨fun h g hg ↦ (mem_chartRingZ_iff hf g hg x).1 (h _ fun _ ↦ (pt_ne_zero_iff hf g).2 hg),
    fun h c hc ↦ ?_⟩
  have hc' := (pt_ne_zero_iff hf (c ())).1 (hc ())
  exact (mem_chartRingZ_iff hf (c ()) hc' x).2 (h _ hc')

theorem exists_of_mem_curveRing (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) {b : Ω} (hb : b ∈ curveRing y) :
    ∃ x : fld y f, (x : Ω) = b := by
  have h := mem_curveRing.mp hb f hf
  rw [← map_chartRingZ hf f hf, Subalgebra.mem_map] at h
  obtain ⟨x, -, hx⟩ := h
  exact ⟨x, hx⟩

end CurveClosedPointChartAlt

open CurveClosedPointChartAlt in

theorem CurveClosedPointChart.proof : CurveClosedPointChart.Statement := by
  classical
  intro K _ ι _ Ω _ y hP m hm
  have := SegreChart.charZero_of_isArithVar hP
  obtain ⟨f, hf⟩ := SegreChart.exists_chart hP
  have := numberField hP hf
  let φ : curveRing (pt y f) →+* curveRing y :=
    RingHom.codRestrict ((algebraMap (fld y f) Ω).comp (curveRing (pt y f)).subtype) (curveRing y)
      fun x ↦ (mem_curveRing_iff hf x).1 x.2
  have hφ : Function.Surjective φ := by
    rintro ⟨b, hb⟩
    obtain ⟨x, rfl⟩ := exists_of_mem_curveRing hf hb
    exact ⟨⟨x, (mem_curveRing_iff hf x).2 hb⟩, rfl⟩
  have hm' : (m.comap φ).IsMaximal := Ideal.comap_isMaximal_of_surjective φ hφ
  obtain ⟨t, ht, hrat⟩ := ClosedPointChart.proof ClosedPointUnitSection.proof (∀ k, ι k) (fld y f) (pt y f)
    (isArithVar_pt hP hf) (m.comap φ) hm'
  have hyt := (pt_ne_zero_iff hf t).1 ht
  refine ⟨t, hyt, fun p ↦ ?_⟩
  obtain ⟨a, b, hb, hab⟩ := hrat (Function.update t p.1 p.2)
  refine ⟨φ a, φ b, hb, ?_⟩
  have h1 := congrArg (fun x : fld y f ↦ (x : Ω)) hab
  simp only [IntermediateField.coe_mul] at h1
  rw [coe_pt_ratio hf, SegreChart.segre_ratio, SegreChart.prod_ratio_update y t hyt p] at h1
  exact h1

end

end GroundTheory.Heights₂.Heights.Targets
end
