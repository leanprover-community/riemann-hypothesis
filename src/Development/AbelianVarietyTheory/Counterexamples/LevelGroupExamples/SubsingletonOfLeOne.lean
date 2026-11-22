module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BetaAtAddLeftAndDiagEqTwoOrder
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProperOfSubsingleton
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PeriodFormAdditiveBalancedPosDefBoundedRank

@[expose] public section

noncomputable section

namespace GlobalTheory.PointLawsEdge

open Filter Topology Matrix in
theorem real_pos_of_int_ge {ι : Type} [Fintype ι] (M : ι → ι → ℝ) (hs : ∀ i k, M i k = M k i) {c : ℝ} (hc : 0 < c)
    (hM : ∀ z : ι → ℤ, z ≠ 0 → c ≤ ∑ i, ∑ k, (z i : ℝ) * z k * M i k) (x : ι → ℝ) (hx : x ≠ 0) :
    0 < ∑ i, ∑ k, x i * x k * M i k := by
  classical
  set Q : (ι → ℝ) → ℝ := fun y => ∑ i, ∑ k, y i * y k * M i k with hQdef
  have hQc : Continuous Q := by simp only [hQdef]; fun_prop
  have hM0 : ∀ z : ι → ℤ, 0 ≤ Q fun i => z i := by
    intro z
    by_cases hz : z = 0
    · simp [hz, hQdef]
    · exact hc.le.trans (hM z hz)
  have hQ : ∀ q : ι → ℚ, 0 ≤ Q fun i => q i := by
    intro q
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
    choose z hz using hd
    have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero d.2
    have hz' : ∀ i, (z i : ℝ) = ((d : ℤ) : ℝ) * (q i : ℝ) := by
      intro i
      have h := hz i
      simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul] at h
      have := congrArg (fun t : ℚ => (t : ℝ)) h
      simpa using this
    have h1 := hM0 z
    have h2 : (Q fun i => z i) = ((d : ℤ) : ℝ) ^ 2 * Q fun i => q i := by
      simp only [hQdef, Finset.mul_sum, hz']
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    rw [h2] at h1
    exact (mul_nonneg_iff_of_pos_left (by positivity)).1 h1
  have hR : ∀ y, 0 ≤ Q y := by
    intro y
    have hdr : DenseRange (Pi.map (fun (_ : ι) (q : ℚ) => (q : ℝ))) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    exact hdr.induction_on y (isClosed_le continuous_const hQc) fun q => hQ q
  have hform : ∀ y : ι → ℝ, star y ⬝ᵥ (Matrix.of M) *ᵥ y = Q y := by
    intro y
    simp only [hQdef, dotProduct, mulVec, Finset.mul_sum, star_trivial, of_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hpsd : (Matrix.of M).PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun y => by rw [hform]; exact hR y⟩
    ext i k
    simp [hs i k]
  refine (hR x).lt_of_ne fun h0 => ?_
  have hker : (Matrix.of M) *ᵥ x = 0 := (hpsd.dotProduct_mulVec_zero_iff).1 ((hform x).trans h0.symm)
  have hker' : x ᵥ* (Matrix.of M) = 0 := by
    ext k
    have := congrFun hker k
    simp only [mulVec, vecMul, dotProduct, of_apply, Pi.zero_apply] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [hs i k, mul_comm]
  have hshift : ∀ (y : ι → ℝ) (t : ℝ), Q (y + t • x) = Q y := by
    intro y t
    rw [← hform, ← hform]
    simp only [star_trivial, mulVec_add, mulVec_smul, hker, smul_zero, add_zero, add_dotProduct, smul_dotProduct,
      dotProduct_mulVec x, hker', zero_dotProduct]
  let u : ℕ → ι → ℝ := fun n i => Int.fract ((n : ℝ) * x i)
  have hu : ∀ n, u n ∈ Set.Icc (0 : ι → ℝ) 1 := fun n =>
    ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hu
  have hd : Tendsto (fun k => u (φ (k + 1)) - u (φ k)) atTop (𝓝 0) := by
    have := (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
    simpa using this
  have h1 : ∀ᶠ k in atTop, Q (u (φ (k + 1)) - u (φ k)) < c := by
    have := (hQc.tendsto 0).comp hd
    refine this.eventually (gt_mem_nhds ?_)
    simpa [hQdef] using hc
  have h2 : ∀ᶠ k in atTop, ‖u (φ (k + 1)) - u (φ k)‖ < ‖x‖ :=
    hd.norm.eventually (gt_mem_nhds (by simpa using hx))
  obtain ⟨k, h1, h2⟩ := (h1.and h2).exists
  let z : ι → ℤ := fun i => ⌊(φ k : ℝ) * x i⌋ - ⌊(φ (k + 1) : ℝ) * x i⌋
  have e : u (φ (k + 1)) - u (φ k) = (fun i => (z i : ℝ)) + ((φ (k + 1) : ℝ) - φ k) • x := by
    ext i
    simp only [u, z, Int.fract, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [e] at h1 h2
  by_cases hz : z = 0
  · have h3 : (φ k : ℝ) + 1 ≤ φ (k + 1) := by exact_mod_cast hφ (Nat.lt_succ_self k)
    have e0 : (fun i => (z i : ℝ)) = 0 := by ext i; simp [hz]
    rw [e0, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h2
    nlinarith [norm_nonneg x]
  · rw [hshift] at h1
    exact absurd (hM z hz) (not_le.2 h1)

section Geometry

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre GlobalTheory.EigenSplit GlobalTheory.LieEigen Matrix
open Formalism.MainNotions.DIV.Cons GlobalTheory.ToricRank GlobalTheory.PeriodLaws
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)
open scoped CategoryTheory.Obj

end Geometry

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.PointLawsEdge
