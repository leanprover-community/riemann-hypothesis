import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MeasurePreservingSwapPi

section
namespace ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall

open MeasureTheory

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sqBall (r : ℕ) (E : Type*) [NormedAddCommGroup E] (R : ℝ) : Set (Fin r → E) :=
  {u | ∑ k, ‖u k‖ ^ 2 ≤ R ^ 2}

lemma norm_sq_convex_comb {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (z w : E) :
    ‖a • z + b • w‖ ^ 2 ≤ a * ‖z‖ ^ 2 + b * ‖w‖ ^ 2 := by
  have h1 : ‖a • z + b • w‖ ≤ a * ‖z‖ + b * ‖w‖ := by
    calc ‖a • z + b • w‖ ≤ ‖a • z‖ + ‖b • w‖ := norm_add_le _ _
      _ = a * ‖z‖ + b * ‖w‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have h2 : (a * ‖z‖ + b * ‖w‖) ^ 2 ≤ a * ‖z‖ ^ 2 + b * ‖w‖ ^ 2 := by
    obtain rfl : b = 1 - a := by linarith
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (‖z‖ - ‖w‖))]
  calc ‖a • z + b • w‖ ^ 2 ≤ (a * ‖z‖ + b * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

lemma sqBall_convex (r : ℕ) (R : ℝ) : Convex ℝ (sqBall r E R) := by
  intro u hu v hv a b ha hb hab
  simp only [sqBall, Set.mem_setOf_eq] at hu hv ⊢
  calc ∑ k, ‖(a • u + b • v) k‖ ^ 2 = ∑ k, ‖a • u k + b • v k‖ ^ 2 := rfl
    _ ≤ ∑ k, (a * ‖u k‖ ^ 2 + b * ‖v k‖ ^ 2) :=
        Finset.sum_le_sum fun k _ => norm_sq_convex_comb ha hb hab _ _
    _ = a * ∑ k, ‖u k‖ ^ 2 + b * ∑ k, ‖v k‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * R ^ 2 + b * R ^ 2 := by gcongr
    _ = R ^ 2 := by rw [← add_mul, hab, one_mul]

lemma sqBall_neg (r : ℕ) (R : ℝ) : ∀ u ∈ sqBall r E R, -u ∈ sqBall r E R := by
  intro u hu
  simpa [sqBall] using hu

lemma sqBall_subset (r : ℕ) (R : ℝ) : sqBall r E R ⊆ Metric.closedBall 0 |R| := by
  intro u hu
  simp only [sqBall, Set.mem_setOf_eq] at hu
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg R)).2 fun k => ?_
  have hk : ‖u k‖ ^ 2 ≤ R ^ 2 :=
    (Finset.single_le_sum (f := fun k => ‖u k‖ ^ 2) (fun k _ => by positivity)
      (Finset.mem_univ k)).trans hu
  have := sq_le_sq.mp hk
  rwa [abs_of_nonneg (norm_nonneg _)] at this

lemma sqBall_isBounded (r : ℕ) (R : ℝ) : Bornology.IsBounded (sqBall r E R) := Metric.isBounded_closedBall.subset (sqBall_subset r R)

lemma sqBall_isClosed (r : ℕ) (R : ℝ) : IsClosed (sqBall r E R) := by
  unfold sqBall
  exact isClosed_le (continuous_finset_sum _ fun k _ => (continuous_apply k).norm.pow 2)
    continuous_const


variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace V] [BorelSpace V]

end Generic

end ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
end

section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder
open ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall

noncomputable def qC {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℂ) : ℝ :=
  (∑ i, ∑ j, starRingEnd ℂ (y i) * G i j * y j).re

noncomputable def qR {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) (y : Fin r → ℝ) : ℝ :=
  ∑ i, ∑ j, y i * G i j * y j

private lemma exists_factor_C {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) :
    ∃ B : Matrix (Fin r) (Fin r) ℂ, G = Bᴴ * B := by
  first
  | exact Matrix.posSemidef_iff_eq_transpose_mul_self.1 hG.posSemidef
  | exact (Matrix.posSemidef_iff_eq_conjTranspose_mul_self).1 hG.posSemidef
  | exact hG.posSemidef.exists_eq_conjTranspose_mul_self
  | (refine ⟨hG.posSemidef.sqrt, ?_⟩
     rw [hG.posSemidef.posSemidef_sqrt.isHermitian.eq, hG.posSemidef.sqrt_mul_self])
  | (refine ⟨CFC.sqrt G, ?_⟩
     have h0 : 0 ≤ G := hG.posSemidef.nonneg
     have hs : (CFC.sqrt G)ᴴ = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint.star_eq
     rw [hs, CFC.sqrt_mul_sqrt_self G h0])

private lemma exists_factor_R {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) :
    ∃ B : Matrix (Fin r) (Fin r) ℝ, G = Bᵀ * B := by
  have hC : ∃ B : Matrix (Fin r) (Fin r) ℝ, G = Bᴴ * B := by
    first
    | exact Matrix.posSemidef_iff_eq_transpose_mul_self.1 hG.posSemidef
    | exact (Matrix.posSemidef_iff_eq_conjTranspose_mul_self).1 hG.posSemidef
    | exact hG.posSemidef.exists_eq_conjTranspose_mul_self
    | (refine ⟨hG.posSemidef.sqrt, ?_⟩
       rw [hG.posSemidef.posSemidef_sqrt.isHermitian.eq, hG.posSemidef.sqrt_mul_self])
    | (refine ⟨CFC.sqrt G, ?_⟩
       have h0 : 0 ≤ G := hG.posSemidef.nonneg
       have hs : (CFC.sqrt G)ᴴ = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint.star_eq
       rw [hs, CFC.sqrt_mul_sqrt_self G h0])
  obtain ⟨B, hB⟩ := hC
  exact ⟨B, by rw [hB, Matrix.conjTranspose_eq_transpose_of_trivial]⟩

private lemma qC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℂ) :
    qC (Bᴴ * B) y = ∑ k, ‖(B *ᵥ y) k‖ ^ 2 := by
  have h1 : (∑ i, ∑ j, starRingEnd ℂ (y i) * (Bᴴ * B) i j * y j) =
      dotProduct (star y) ((Bᴴ * B) *ᵥ y) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply, RCLike.star_def]
  unfold qC
  rw [h1, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.re_sum, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  refine Finset.sum_congr rfl (fun k _ => by ring)

private lemma qR_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (y : Fin r → ℝ) :
    qR (Bᵀ * B) y = ∑ k, ‖(B *ᵥ y) k‖ ^ 2 := by
  have h1 : qR (Bᵀ * B) y = dotProduct y ((Bᵀ * B) *ᵥ y) := by
    simp only [qR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [h1, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, Real.norm_eq_abs, sq_abs, sq, abs_mul_abs_self]

private lemma setC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    {y | qC (Bᴴ * B) y ≤ R ^ 2} = ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, qC_eq, LinearMap.restrictScalars_apply,
    Matrix.toLin'_apply, sqBall]

private lemma setR_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    {y | qR (Bᵀ * B) y ≤ R ^ 2} = (Matrix.toLin' B) ⁻¹' sqBall r ℝ R := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, qR_eq, Matrix.toLin'_apply, sqBall]
  skip

private lemma detC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) :
    (Bᴴ * B).det = (Complex.normSq B.det : ℂ) := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.normSq_eq_conj_mul_self]
  rfl

private theorem isBounded_preimage_sqBall_complex_of_det_ne_zero {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (hdet : B.det ≠ 0) (R : ℝ) :
    Bornology.IsBounded (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) := by
  have hS : IsCompact (sqBall r ℂ R) :=
    Metric.isCompact_of_isClosed_isBounded (sqBall_isClosed r R) (sqBall_isBounded r R)
  have hc' : Continuous ((Matrix.toLin' B⁻¹).restrictScalars ℝ) :=
    LinearMap.continuous_of_finiteDimensional _
  refine (hS.image hc').isBounded.subset ?_
  intro y hy
  refine ⟨(Matrix.toLin' B).restrictScalars ℝ y, hy, ?_⟩
  show Matrix.mulVec B⁻¹ (Matrix.mulVec B y) = y
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

private theorem convex_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    Convex ℝ (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) :=
  Convex.linear_preimage (sqBall_convex (E := ℂ) r R) ((Matrix.toLin' B).restrictScalars ℝ)

private theorem neg_mem_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    ∀ y ∈ ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R,
      -y ∈ ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R := by
  intro y hy
  rw [Set.mem_preimage, map_neg]
  exact sqBall_neg (E := ℂ) r R _ hy

private theorem measurableSet_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    MeasurableSet (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) := by
  have hc : Continuous ((Matrix.toLin' B).restrictScalars ℝ) :=
    LinearMap.continuous_of_finiteDimensional _
  exact ((sqBall_isClosed r R).preimage hc).measurableSet

private lemma hermitianEllipsoid_props_of_eq {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (B : Matrix (Fin r) (Fin r) ℂ)
    (hB : G = Bᴴ * B) (R : ℝ) :
    Convex ℝ {y | qC G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qC G y ≤ R ^ 2}, -y ∈ {y | qC G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qC G y ≤ R ^ 2} ∧ MeasurableSet {y | qC G y ≤ R ^ 2} := by
  subst hB
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [detC_eq, h0] at h1
    simp at h1
  rw [setC_eq]
  exact ⟨convex_preimage_sqBall_complex B R, neg_mem_preimage_sqBall_complex B R, isBounded_preimage_sqBall_complex_of_det_ne_zero B hdet R, measurableSet_preimage_sqBall_complex B R⟩

theorem ellipsoidC_props {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (R : ℝ) :
    Convex ℝ {y | qC G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qC G y ≤ R ^ 2}, -y ∈ {y | qC G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qC G y ≤ R ^ 2} ∧ MeasurableSet {y | qC G y ≤ R ^ 2} := by
  obtain ⟨B, hB⟩ := exists_factor_C hG
  exact hermitianEllipsoid_props_of_eq hG B hB R


private theorem isBounded_preimage_sqBall_real_of_det_ne_zero {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (hdet : B.det ≠ 0) (R : ℝ) :
    Bornology.IsBounded ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) := by
  have hS : IsCompact (sqBall r ℝ R) :=
    Metric.isCompact_of_isClosed_isBounded (sqBall_isClosed r R) (sqBall_isBounded r R)
  have hc' : Continuous (Matrix.toLin' B⁻¹) := LinearMap.continuous_of_finiteDimensional _
  refine (hS.image hc').isBounded.subset ?_
  intro y hy
  refine ⟨Matrix.toLin' B y, hy, ?_⟩
  show Matrix.mulVec B⁻¹ (Matrix.mulVec B y) = y
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

private theorem convex_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    Convex ℝ ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) :=
  Convex.linear_preimage (sqBall_convex (E := ℝ) r R) (Matrix.toLin' B)

private theorem neg_mem_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    ∀ y ∈ (Matrix.toLin' B) ⁻¹' sqBall r ℝ R, -y ∈ (Matrix.toLin' B) ⁻¹' sqBall r ℝ R := by
  intro y hy
  rw [Set.mem_preimage, map_neg]
  exact sqBall_neg (E := ℝ) r R _ hy

private theorem measurableSet_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    MeasurableSet ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) := by
  have hc : Continuous (Matrix.toLin' B) := LinearMap.continuous_of_finiteDimensional _
  exact ((sqBall_isClosed r R).preimage hc).measurableSet

private lemma realEllipsoid_props_of_eq {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) (B : Matrix (Fin r) (Fin r) ℝ)
    (hB : G = Bᵀ * B) (R : ℝ) :
    Convex ℝ {y | qR G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qR G y ≤ R ^ 2}, -y ∈ {y | qR G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qR G y ≤ R ^ 2} ∧ MeasurableSet {y | qR G y ≤ R ^ 2} := by
  subst hB
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero] at h1
    exact lt_irrefl _ h1
  rw [setR_eq]
  exact ⟨convex_preimage_sqBall_real B R, neg_mem_preimage_sqBall_real B R, isBounded_preimage_sqBall_real_of_det_ne_zero B hdet R, measurableSet_preimage_sqBall_real B R⟩

theorem ellipsoidR_props {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) (R : ℝ) :
    Convex ℝ {y | qR G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qR G y ≤ R ^ 2}, -y ∈ {y | qR G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qR G y ≤ R ^ 2} ∧ MeasurableSet {y | qR G y ≤ R ^ 2} := by
  obtain ⟨B, hB⟩ := exists_factor_R hG
  exact realEllipsoid_props_of_eq hG B hB R


end ReciprocityTheory.GeometryOfNumbersTheory
end

section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Module NumberField Set

set_option backward.isDefEq.respectTransparency.types false in
theorem covol_div_covol_eq_relIndex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ μ / ZLattice.covolume L₂ μ =
      L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  classical
  let b₂ := Module.Free.chooseBasis ℤ L₂
  let e : Module.Free.ChooseBasisIndex ℤ L₁ ≃ Module.Free.ChooseBasisIndex ℤ L₂ :=
    Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex,
        ZLattice.rank ℝ L₁, ZLattice.rank ℝ L₂])
  let b₁ := (Module.Free.chooseBasis ℤ L₁).reindex e
  let b₀ := b₂.ofZLatticeBasis ℝ L₂
  have h1 := ZLattice.covolume_eq_det_mul_measureReal L₁ μ b₁ b₀
  have h2 := ZLattice.covolume_eq_det_mul_measureReal L₂ μ b₂ b₀
  have hb : ((↑) ∘ b₂ : _ → E) = ⇑b₀ := by ext i; simp [b₀, Basis.ofZLatticeBasis_apply]
  rw [hb, Basis.det_self, abs_one, one_mul] at h2
  have hpos := ZLattice.covolume_pos L₂ μ
  rw [h2] at hpos
  rw [h1, h2, mul_div_assoc, div_self hpos.ne', mul_one,
    AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂,
    Nat.cast_natAbs, Int.cast_abs]
  congr 1
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  exact (b₂.ofZLatticeBasis_repr_apply ℝ L₂ ⟨b₁ j, h (Submodule.coe_mem _)⟩ i)

theorem measurePreserving_swapPi {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] :
    MeasurePreserving (fun (f : ι → κ → X) (k : κ) (i : ι) => f i k)
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => ν)
      (Measure.pi fun _ : κ => Measure.pi fun _ : ι => ν) := by
  first | exact UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi .. | (apply UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi <;> first | assumption | infer_instance)

end ReciprocityTheory.GeometryOfNumbersTheory

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder
open Matrix

section Form

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem HermFam.form_add_left (h : HermFam K V) (σ : K →+* ℂ) (x x' y : V) :
    h.form σ (x + x') y = h.form σ x y + h.form σ x' y := by
  rw [← h.conj_symm, h.add_right, map_add, h.conj_symm, h.conj_symm]

theorem HermFam.form_smul_left (h : HermFam K V) (σ : K →+* ℂ) (a : K) (x y : V) :
    h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by
  rw [← h.conj_symm, h.smul_right, map_mul, h.conj_symm]

theorem HermFam.form_sum_right (h : HermFam K V) (σ : K →+* ℂ) (x : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ x (∑ i ∈ s, f i) = ∑ i ∈ s, h.form σ x (f i) :=
  map_sum (AddMonoidHom.mk' (h.form σ x) (h.add_right σ x)) f s

theorem HermFam.form_sum_left (h : HermFam K V) (σ : K →+* ℂ) (y : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ (∑ i ∈ s, f i) y = ∑ i ∈ s, h.form σ (f i) y := by
  rw [← h.conj_symm, h.form_sum_right, map_sum]
  simp only [h.conj_symm]

theorem HermFam.form_expand (h : HermFam K V) (σ : K →+* ℂ) {n : ℕ} (c : Fin n → K)
    (v : Fin n → V) :
    h.form σ (∑ i, c i • v i) (∑ j, c j • v j) =
      ∑ i, ∑ j, starRingEnd ℂ (σ (c i)) * h.gram σ v i j * σ (c j) := by
  rw [h.form_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h.form_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h.form_smul_left, h.smul_right, HermFam.gram, Matrix.of_apply]
  ring

end Form

section Places

variable {K : Type*} [Field K] [NumberField K]

end Places

end ReciprocityTheory.GeometryOfNumbersTheory
end
