module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Matrix ComplexOrder ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section HidaSetting

variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

end HidaSetting

attribute [instance] ProjectiveLineBundle.fieldΩ ProjectiveLineBundle.finι ProjectiveLineBundle.finν ProjectiveLineBundle.finκ ProjectiveLineBundle.acgE ProjectiveLineBundle.modE
  ProjectiveLineBundle.fieldΦ ProjectiveLineBundle.algΦ

namespace ProjectiveLineBundle

variable {D : ℕ} (S : ProjectiveLineBundle D)

end ProjectiveLineBundle

section Diag

variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

end Diag

section Powers

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def hermZpow (A : HermLine ι) (m : ℤ) : HermLine ι where
  a := m • A.a
  h z := A.h z ^ m
  pos z hz := zpow_pos (A.pos z hz) m
  smul c z hc := by
    rw [A.smul c z hc, mul_zpow, ← Finset.prod_zpow]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, ← _root_.zpow_mul, mul_comm]

end Powers

section Statements

open ReciprocityTheory.ChartRestriction.G.AI

end Statements

section Inhabit

section Homog

variable {K : Type*} [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem exHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

end Homog

section FS

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ofMetrics_fs_h (a : K → ℤ) (z : (Σ k, ι k) → ℂ) :
    (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) a).h z =
      ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ a k := by
  simp only [HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]

theorem isSmoothHerm_ofMetrics_fs (a : K → ℤ) :
    IsSmoothHerm (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) a) := by
  have hfun : (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) a).h =
      fun z => ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ a k := funext (ofMetrics_fs_h a)
  unfold IsSmoothHerm
  rw [hfun]
  refine contDiffOn_prod fun k _ => ?_
  have hpos : ∀ z ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
    intro z hz
    obtain ⟨i, hi⟩ := hz k
    exact Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2))
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    ContDiffOn.sqrt (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, ι k))).contDiffOn fun z hz => (hpos z hz).ne'
  have hf0 : ∀ z ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ≠ 0 :=
    fun z hz => (Real.sqrt_pos.2 (hpos z hz)).ne'
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg (a k)
  · simp only [hm, zpow_natCast]
    exact hf.pow m
  · simp only [hm, _root_.zpow_neg, zpow_natCast]
    exact (hf.pow m).inv fun z hz => pow_ne_zero _ (hf0 z hz)

end FS

end Inhabit

end

end GroundTheory.Heights₂.Heights.Inter
