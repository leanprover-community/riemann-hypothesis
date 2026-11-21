import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.AssemblyStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.UnipotentExpHaarSqrtBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiDecayCore
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HWExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.BasePointPsiExpFormula
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.NoncompactLoweringNormSmall
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.MatrixCoeffBoundsImplyBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.InvMulSelfOfMemIndefiniteUnitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.B3b
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.NormMatrixTripleProductLe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.SmInfUnitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Laplace
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.IsCompactUnitaryMat
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.PsiCoef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.ImportsAlt

section
noncomputable section

open Finset Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

namespace Asm

variable {k r : ℕ}

theorem cay_unit {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) :
    P * P⁻¹ = 1 ∧ P⁻¹ * P = 1 := by
  have h := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  exact ⟨Matrix.mul_nonsing_inv P h, Matrix.nonsing_inv_mul P h⟩

theorem cay_left {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) :
    Pᴴ * Jm ε = Formalism.QuantumDeterminants.Hpk k r * P⁻¹ := by
  have h1 := (cay_unit hP).1
  rw [← hP.2, Matrix.mul_assoc (Pᴴ * Formalism.REAL.Jm ε), h1, Matrix.mul_one]
  rfl

theorem cay_right {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) :
    Jm ε * P = (P⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r := by
  have h1 := (cay_unit hP).1
  have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  rw [← hP.2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rfl

theorem cay_mem {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {g : Mat k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : inUJ ε (P * g * P⁻¹) := by
  have h1 := (cay_unit hP).1
  have hR := cay_right hP
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have hPJP : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.2
  show (P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹) = Jm ε
  calc (P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Jm ε * P) * g) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by
        rw [hPJP, hg', ← hR, Matrix.mul_assoc, h1, Matrix.mul_one]

open scoped Matrix.Norms.Operator in

theorem cay_inG {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {Y : Mat k r} (hY : Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r)) : inG ε (P * Y * P⁻¹) := by
  have hL := cay_left hP
  have hR := cay_right hP
  set H := Formalism.QuantumDeterminants.Hpk k r with hH
  have hlie : Yᴴ * H + H * Y = 0 := by
    have hc : ∀ t : ℝ, NormedSpace.exp (t • Yᴴ) * H * NormedSpace.exp (t • Y) = H := by
      intro t
      have h : (NormedSpace.exp ((t : ℂ) • Y))ᴴ * H * NormedSpace.exp ((t : ℂ) • Y) = H :=
        (hY t).1
      have e1 : (NormedSpace.exp ((t : ℂ) • Y))ᴴ = NormedSpace.exp (t • Yᴴ) := by
        rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Complex.star_def,
          Complex.conj_ofReal, Complex.coe_smul]
      rw [← e1, ← Complex.coe_smul]
      exact h
    have hd1 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) Yᴴ (0 : ℝ)
    have hd2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y (0 : ℝ)
    have hf := (hd1.mul_const H).mul hd2
    have h0 := hf.unique ((hasDerivAt_const (0 : ℝ) H).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => hc t))
    simpa using h0
  show (P * Y * P⁻¹)ᴴ * Jm ε + Jm ε * (P * Y * P⁻¹) = 0
  calc (P * Y * P⁻¹)ᴴ * Jm ε + Jm ε * (P * Y * P⁻¹)
      = (P⁻¹)ᴴ * Yᴴ * (Pᴴ * Jm ε) + (Jm ε * P) * Y * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Yᴴ * H + H * Y) * P⁻¹ := by
        rw [hL, hR]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hlie, Matrix.mul_zero, Matrix.zero_mul]

theorem conj_sum_sub {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    starRingEnd ℂ (∑ i ∈ s, (a i - starRingEnd ℂ (a i))) = -∑ i ∈ s, (a i - starRingEnd ℂ (a i)) := by
  rw [map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, Complex.conj_conj, neg_sub]

theorem re_sum_sub {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    (∑ i ∈ s, (a i - starRingEnd ℂ (a i))).re = 0 := by
  rw [Complex.re_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Complex.sub_re, Complex.conj_re, sub_self]

theorem hs_nonneg {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ S7.hs X := by
  unfold S7.hs
  positivity

theorem hs_unreal {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    S7.hs (Formalism.MainNotions.S.unrealify x) = ‖x‖ ^ 2 := by
  unfold S7.hs
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [Formalism.MainNotions.S.unrealify, Complex.sq_norm, Complex.normSq_mk, Real.norm_eq_abs, sq_abs]
  ring

theorem eight_n_q0_lt_needed_gap {n : ℕ} (ε : Fin n → Bool) : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < hNeed ε := by
  have hq : ((S7.q0 ε : ℕ) : ℝ) = min (pOf ε : ℝ) (qOf ε : ℝ) := by
    simp [S7.q0]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : (0 : ℝ) ≤ min (pOf ε : ℝ) (qOf ε : ℝ) :=
    le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hs : 0 ≤ Real.sqrt (2 * min (pOf ε : ℝ) (qOf ε : ℝ)) := Real.sqrt_nonneg _
  have hnm := mul_nonneg hn hm
  rw [hq]
  unfold hNeed
  refine lt_max_of_lt_right (lt_max_of_lt_left ?_)
  nlinarith

theorem stdGap_of {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hG : GapLap ε lam h) :
    StdGap ε lam := by
  obtain ⟨h1, h2, h3⟩ := hG
  refine ⟨h1, h, h2, lt_trans ?_ h3⟩
  unfold hNeed
  refine lt_max_of_lt_left ?_
  have := le_max_right (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
  linarith

theorem norm_inner_w {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) (A : T.V →L[ℂ] T.V) :
    ‖⟪T.w, A T.w⟫_ℂ‖ ≤ ‖A‖ := by
  calc ‖⟪T.w, A T.w⟫_ℂ‖ ≤ ‖T.w‖ * ‖A T.w‖ := norm_inner_le_norm _ _
    _ ≤ ‖T.w‖ * (‖A‖ * ‖T.w‖) := by gcongr; exact A.le_opNorm _
    _ = ‖A‖ := by rw [T.w_norm]; ring

def chart (k r : ℕ) (x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r)) : Formalism.QuantumDeterminants.Mt k r :=
  fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j

theorem exp_mat_continuous : Continuous (NormedSpace.exp : Mat k r → Mat k r) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_continuous

theorem unreal_continuous :
    Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) =>
      (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _) : Mat k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have h1 : Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) =>
      (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) (i, j, false) :=
    (EuclideanSpace.proj (i, j, false)).continuous.comp continuous_subtype_val
  have h2 : Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) =>
      (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) (i, j, true) :=
    (EuclideanSpace.proj (i, j, true)).continuous.comp continuous_subtype_val
  have h3 : Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) =>
      ((x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) (i, j, false) : ℂ) +
        ((x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) (i, j, true) : ℂ) *
          Complex.I :=
    (Complex.continuous_ofReal.comp h1).add ((Complex.continuous_ofReal.comp h2).mul continuous_const)
  refine h3.congr fun x => ?_
  apply Complex.ext <;> simp [Formalism.MainNotions.S.unrealify]

theorem exp_unreal_continuous :
    Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) =>
      (NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) : Mat k r) :=
  exp_mat_continuous.comp unreal_continuous

theorem chart_embedding
    (hinj : ∀ Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r), ∀ Y' ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r),
      NormedSpace.exp Y = NormedSpace.exp Y' → Y = Y')
    (hunr : ∀ x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r),
      Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _) ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r)) :
    MeasurableEmbedding (chart k r) := by
  have hcont : Continuous (chart k r) :=
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply j).comp ((continuous_apply i).comp exp_unreal_continuous)
  refine hcont.measurableEmbedding ?_
  intro x y hxy
  have h1 : NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) =
      NormedSpace.exp (Formalism.MainNotions.S.unrealify (y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) := by
    ext i j
    exact congrFun (congrFun hxy i) j
  have h2 := hinj _ (hunr x) _ (hunr y) h1
  exact Subtype.ext ((unrealL (2 * r + k + 1)).injective h2)

def partNML {n : ℕ} (ε : Fin n → Bool) (d : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := partNM ε d
  map_add' X Y := by
    ext a b; simp only [partNM, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c X := by
    ext a b; simp only [partNM, Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

def bracketB {n : ℕ} (ε : Fin n → Bool) (d : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (fun X Y => -(1 / 2 : ℂ) * trace (dMat d * (X * partNML ε d Y - partNML ε d Y * X)))
    (fun X X' Y => by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]; ring)
    (fun c X Y => by
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_smul,
        Complex.real_smul]; ring)
    (fun X Y Y' => by
      simp only [map_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add,
        Matrix.trace_sub]; ring)
    (fun c X Y => by
      simp only [map_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_sub,
        Matrix.trace_smul, Complex.real_smul]; ring)

def conjL (P : Mat k r) : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) →ₗ[ℝ] Mat k r :=
  (LinearMap.mulRight ℝ P⁻¹).comp ((LinearMap.mulLeft ℝ P).comp
    ((unrealL (2 * r + k + 1)).toLinearMap.comp (Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r)).subtype))

theorem conjL_apply (P : Mat k r) (x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r)) :
    conjL P x = P * Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _) * P⁻¹ := rfl

theorem bracketB_apply {n : ℕ} (ε : Fin n → Bool) (d : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    bracketB ε d X X = qForm ε d X / 2 := by
  show -(1 / 2 : ℂ) * trace (dMat d * (X * partNM ε d X - partNM ε d X * X)) = qForm ε d X / 2
  unfold qForm
  ring

end Asm

open Asm in
theorem assembly : AssemblyStatement := by
  intro hB1 hB3 hB4 hB5 hB6 hB7a hB7b hLamT hPsi hLink
  intro k r u v b hk hHC hIl hH
  obtain ⟨huHC, hq0, hlin, hWwt, t₁, ht₁⟩ := hLamT k r u v b hk hHC hIl hH
  obtain ⟨P, hP, hPW, htr, hpsi⟩ := hB1 k r hk
  obtain ⟨hinj, -, hunr, hNhaar, -⟩ := hB4 k r
  obtain ⟨c5, hc5, hmaj⟩ := hB5 k r (parEps k r) P hP
  obtain ⟨μW, hμW, hμW1⟩ := hB7a k r
  obtain ⟨Hπ, iπ1, iπ2, π', hπ'⟩ := HW.highest_weight_exists k u huHC
  have hT : ∀ t : ℕ, t₁ ≤ t →
      Nonempty (S7.KType (parEps k r) (lowK (parEps k r) (lamT k r u b t))) :=
    fun t ht => HW.kType_exists _ _ (ht₁ t ht).1
  have hMu : ∀ t : ℕ, t₁ ≤ t → ∃ μ : Fin (2 * r + k + 1) → ℤ, S7.IsMu (lamT k r u b t) μ := by
    intro t ht
    choose m hm using (ht₁ t ht).1.2
    refine ⟨fun a => m a + (((2 * r + k + 1 : ℕ) : ℤ) - 1 - ((a : ℕ) : ℤ)), fun a => ?_⟩
    have h1 := hm a
    simp only [rho]
    push_cast at h1 ⊢
    linarith
  choose μ hμ using hMu

  have hGap : ∀ t (ht : t₁ ≤ t), GapAtLeast (parEps k r) (lamT k r u b t) ((t : ℝ) / 2) :=
    fun t ht => (ht₁ t ht).2.2.1
  have h8 : ∀ t (ht : t₁ ≤ t), 8 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 (parEps k r) : ℝ) < (t : ℝ) / 2 :=
    fun t ht => (eight_n_q0_lt_needed_gap _).trans (ht₁ t ht).2.2.2
  have hPF : ∀ t (ht : t₁ ≤ t), IsPsiFor (parEps k r) (lamT k r u b t) (Classical.choice (hT t ht))
      (S7.PsiM (Classical.choice (hT t ht)) (μ t ht)) ∧
      ContinuousOn (S7.PsiM (Classical.choice (hT t ht)) (μ t ht)) (UJset (parEps k r)) :=
    fun t ht => hPsi _ _ _ _ _ _ (ht₁ t ht).1 (hμ t ht) (hGap t ht) hq0 (h8 t ht)

  have hU : ∀ x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r),
      Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _) ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r) := hunr
  have hexpN : ∀ x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r),
      NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) ∈ Formalism.QuantumDeterminants.Nset k r := by
    intro x; simpa using hU x 1
  have hgU : ∀ x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r),
      P * NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) * P⁻¹ ∈ UJset (parEps k r) :=
    fun x => cay_mem hP (hexpN x).1
  have hτre : ∀ x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r),
      (trace (dMat (dNode k r) * conjL P x)).re = 0 := by
    intro x; rw [conjL_apply, htr _ (hU x)]; exact re_sum_sub _ _
  have hτconj : ∀ x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r),
      starRingEnd ℂ (trace (dMat (dNode k r) * conjL P x)) = -trace (dMat (dNode k r) * conjL P x) := by
    intro x; rw [conjL_apply, htr _ (hU x)]; exact conj_sum_sub _ _
  have hτc : Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) => trace (dMat (dNode k r) * conjL P x) :=
    (continuous_const.matrix_mul ((continuous_const.matrix_mul unreal_continuous).matrix_mul
      continuous_const)).matrix_trace

  let f : ℕ → Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) → ℂ := fun t x =>
    if ht : t₁ ≤ t then
      ⟪(Classical.choice (hT t ht)).w, S7.PsiM (Classical.choice (hT t ht)) (μ t ht)
          (P * NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) * P⁻¹)
          (Classical.choice (hT t ht)).w⟫_ℂ *
        Complex.exp (-((t : ℂ) * trace (dMat (dNode k r) * conjL P x)))
    else 0
  have hfe : ∀ t (ht : t₁ ≤ t) x, f t x =
      ⟪(Classical.choice (hT t ht)).w, S7.PsiM (Classical.choice (hT t ht)) (μ t ht)
          (P * NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) * P⁻¹)
          (Classical.choice (hT t ht)).w⟫_ℂ *
        Complex.exp (-((t : ℂ) * trace (dMat (dNode k r) * conjL P x))) :=
    fun t ht x => dif_pos ht
  have hgc : Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) =>
      P * NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) * P⁻¹ :=
    (continuous_const.matrix_mul exp_unreal_continuous).matrix_mul continuous_const
  have hPc : ∀ t (ht : t₁ ≤ t), Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) =>
      S7.PsiM (Classical.choice (hT t ht)) (μ t ht)
        (P * NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) * P⁻¹) :=
    fun t ht => (hPF t ht).2.comp_continuous hgc hgU
  have hfc : ∀ t (ht : t₁ ≤ t), Continuous (f t) := by
    intro t ht
    have : f t = fun x => _ := funext (hfe t ht)
    rw [this]
    exact (continuous_const.inner ((hPc t ht).clm_apply continuous_const)).mul
      (Complex.continuous_exp.comp (continuous_const.mul hτc).neg)

  have hbound : ∀ t (ht : t₁ ≤ t) (x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r)),
      ‖S7.PsiM (Classical.choice (hT t ht)) (μ t ht)
          (P * NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) * P⁻¹)‖ ≤
        (1 + ‖x‖ ^ 2) ^ (-(c5 / 16 * (t : ℝ))) := by
    intro t ht x
    obtain ⟨κ, X, hX, hkX⟩ := S7.polar_exists (hgU x)
    have hdec := S7.psiM_dec (Classical.choice (hT t ht)) (μ t ht) (hμ t ht) (ht₁ t ht).1 (hGap t ht)
      hq0 κ hX
    have hm := hmaj _ (hU x) κ X hX hkX
    rw [hs_unreal] at hm
    have hxn : ‖(x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ = ‖x‖ := rfl
    rw [hxn] at hm
    rw [hkX]
    refine hdec.trans ?_
    have h1p : 0 < 1 + ‖x‖ ^ 2 := by positivity
    rw [Real.rpow_def_of_pos h1p]
    apply Real.exp_le_exp.mpr
    have h2 := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ (t : ℝ) / 16 by positivity)
    nlinarith [h2]
  have hbd : ∀ᶠ t : ℕ in atTop, ∀ x, ‖f t x‖ ≤ (1 + 1 * ‖x‖ ^ 2) ^ (-(c5 / 16 * (t : ℝ))) := by
    filter_upwards [eventually_ge_atTop t₁] with t ht x
    rw [hfe t ht x, one_mul, norm_mul, Complex.norm_exp]
    have hre : (-((t : ℂ) * trace (dMat (dNode k r) * conjL P x))).re = 0 := by
      simp [Complex.mul_re, hτre x]
    rw [hre, Real.exp_zero, mul_one]
    exact (norm_inner_w _ _).trans (hbound t ht x)

  let B := (bracketB (parEps k r) (dNode k r)).compl₁₂ (conjL P) (conjL P)
  have hBx : ∀ x, B x x = qForm (parEps k r) (dNode k r) (conjL P x) / 2 :=
    fun x => bracketB_apply _ _ _
  have hlim : ∀ x, Tendsto (fun t : ℕ => f t ((Real.sqrt t)⁻¹ • x)) atTop
      (𝓝 (Complex.exp (-(B x x)))) := by
    intro x
    obtain ⟨C, hC⟩ := hB3 (2 * r + k + 1) (parEps k r) (dNode k r) (lowK (parEps k r) (lamT k r u b 0))
      (Real.sqrt (S7.hs (conjL P x)))
    have hlimC : Tendsto (fun t : ℕ => C / Real.sqrt t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlimC
    filter_upwards [eventually_ge_atTop t₁, eventually_ge_atTop 1] with t ht ht1
    have ht1' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    obtain ⟨H, i1, i2, σ, w, hsm, hcoef⟩ := hLink _ _ _ (Classical.choice (hT t ht))
      (S7.PsiM (Classical.choice (hT t ht)) (μ t ht)) (stdGap_of (ht₁ t ht).2) (hPF t ht).1
    have hY := cay_inG hP (hU x)
    have hB3' := hC t ht1' H σ _ w hsm (hlin t) (conjL P x) hY (Real.sq_sqrt (hs_nonneg _)).symm.le
    have hus : Formalism.MainNotions.S.unrealify
        ((((Real.sqrt t)⁻¹ • x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r))) : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) =
        ((((Real.sqrt t)⁻¹ : ℝ) : ℂ)) • Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) := by
      rw [Submodule.coe_smul, Complex.coe_smul]
      exact (unrealL (2 * r + k + 1)).map_smul _ _
    have hcj : P * NormedSpace.exp ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) *
        P⁻¹ = NormedSpace.exp ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • conjL P x) := by
      rw [← Matrix.exp_conj _ _ hP.1, conjL_apply, Matrix.mul_smul, Matrix.smul_mul]
    have hmem : NormedSpace.exp ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • conjL P x) ∈ UJset (parEps k r) := by
      rw [← hcj]; exact cay_mem hP (hU x _).1
    have hτs : trace (dMat (dNode k r) * conjL P ((Real.sqrt t)⁻¹ • x)) =
        (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * trace (dMat (dNode k r) * conjL P x) := by
      rw [map_smul, Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul]
    have hts : (t : ℂ) * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) = ((Real.sqrt t : ℝ) : ℂ) := by
      have h := Real.div_sqrt (x := (t : ℝ))
      rw [div_eq_mul_inv] at h
      exact_mod_cast h
    have hfx : f t ((Real.sqrt t)⁻¹ • x) =
        ⟪w, σ (NormedSpace.exp ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • conjL P x)) w⟫_ℂ *
          Complex.exp (-((Real.sqrt t : ℂ) * trace (dMat (dNode k r) * conjL P x))) := by
      rw [hfe t ht, hus, hcj, ← hcoef _ hmem, hτs, ← mul_assoc, hts]
    rw [hfx, hBx, show -(qForm (parEps k r) (dNode k r) (conjL P x) / 2) =
      -qForm (parEps k r) (dNode k r) (conjL P x) / 2 by ring]
    exact hB3'

  have hm : ∀ᶠ t : ℕ in atTop, AEStronglyMeasurable (f t) volume := by
    filter_upwards [eventually_ge_atTop t₁] with t ht
    exact (hfc t ht).aestronglyMeasurable
  have hγ : 0 < c5 / 16 := by positivity
  have hev := hB6 (Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r)) volume f hm B hlim one_pos hγ hbd
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt
    ((Module.finrank ℝ (Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r)) : ℝ) / (2 * (c5 / 16)))
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp (hev.and (eventually_ge_atTop (max (max t₁ N₂) 1)))
  refine ⟨t₀, fun t ht => ?_⟩
  obtain ⟨⟨-, hne⟩, htm⟩ := ht₀ t ht
  have htt : t₁ ≤ t := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) htm)
  have htN : N₂ ≤ t := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) htm)
  have ht1 : 1 ≤ t := le_trans (le_max_right _ _) htm

  haveI : Nontrivial Hπ := hπ'.1
  haveI hFD : FiniteDimensional ℂ Hπ := hπ'.2.1
  haveI hCS : CompleteSpace Hπ := FiniteDimensional.complete ℂ Hπ
  let πm : Mat k r → (Hπ →L[ℂ] Hπ) := fun g =>
    π' (Matrix.of fun i j : Fin k => g (Formalism.QuantumDeterminants.wI k r i.castSucc) (Formalism.QuantumDeterminants.wI k r j.castSucc))
  have hblk : ∀ h : Matrix (Fin k) (Fin k) ℂ, πm (Formalism.MainNotions.S.blockW k r h) = π' h := by
    intro h
    show π' _ = π' h
    congr 1
    ext i j
    simp [Formalism.MainNotions.S.blockW, Formalism.QuantumDeterminants.wI]
  have hπb : (fun h => πm (Formalism.MainNotions.S.blockW k r h)) = π' := funext hblk
  have hHCU : Formalism.MainNotions.S.IsHCTypeU k u (fun h => πm (Formalism.MainNotions.S.blockW k r h)) := by rw [hπb]; exact hπ'
  obtain ⟨v0, -, hv0, hwt⟩ := hπ'.2.2.2.2.2.2.1
  let ξ : Hπ := ((‖v0‖⁻¹ : ℝ) : ℂ) • v0
  have hξn : ‖ξ‖ = 1 := by
    simp only [ξ]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  have hξw : Formalism.MainNotions.S.IsWtOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) (fun h => πm (Formalism.MainNotions.S.blockW k r h))
      (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u) ξ := by
    rw [hπb]
    intro θ _
    have hθK : Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈
        Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k) := by
      refine ⟨?_, ?_⟩
      · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
          Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext a
        rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          Complex.norm_exp_ofReal_mul_I]
        simp
      · simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal]
        congr 1
        funext a
        ring
    simp only [ξ]
    rw [ContinuousLinearMap.map_smul, hwt θ hθK, smul_comm]

  have hinWb : Formalism.QuantumDeterminants.inWb k r (z0 k r) := by
    intro i hi
    show (Pi.single (Formalism.QuantumDeterminants.wI k r (Fin.last k)) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i = 0
    rw [Pi.single_apply, if_neg]
    intro hh
    subst hh
    simp only [Formalism.QuantumDeterminants.wI, Fin.val_last] at hi
    omega
  have key : ∀ (H : Mat k r) (i : Fin (2 * r + k + 1)),
      Formalism.QuantumDeterminants.herm H (Formalism.QuantumDeterminants.bvec i) (Formalism.QuantumDeterminants.bvec i) = H i i := by
    intro H i
    rw [show Formalism.QuantumDeterminants.herm H (Formalism.QuantumDeterminants.bvec i) (Formalism.QuantumDeterminants.bvec i) =
      ∑ j, star (Formalism.QuantumDeterminants.bvec i j) * (H *ᵥ Formalism.QuantumDeterminants.bvec i) j from rfl]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply, hj]) (by simp)]
    simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hTz1 : Formalism.QuantumDeterminants.Tz k r (z0 k r) = 1 := by
    rw [Formalism.QuantumDeterminants.Tz, z0, key]
    simp [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.wI]
  have hone : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    show (1 : Mat k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  have hframe : Formalism.MainNotions.S.IsFrameW k r (z0 k r) 1 := by
    refine ⟨hone, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, ?_⟩
    rw [Matrix.one_mulVec, hTz1, Real.sqrt_one]
    simp [z0]
  have hHCW : Formalism.MainNotions.S.IsHCTypeW k r (z0 k r) u πm := by
    refine ⟨1, hframe, ?_⟩
    have : (fun h => πm (1 * Formalism.MainNotions.S.blockW k r h * 1⁻¹)) = fun h => πm (Formalism.MainNotions.S.blockW k r h) := by
      funext h; rw [inv_one, Matrix.mul_one, Matrix.one_mul]
    rw [this]; exact hHCU
  have hcne : ∀ a, cBase r (t : ℝ) a ≠ 0 := by
    intro a
    have : (t : ℂ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
    simp [cBase, Complex.I_ne_zero, this]

  have hemb := chart_embedding hinj hU
  have hμN : Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) 1 = Measure.map (chart k r) volume := by
    rw [Formalism.MainNotions.S.haarLie, one_smul]; rfl
  have hI : ∫ m, psiCoef (Classical.choice (hT t htt)) (μ t htt) P (Classical.choice (hT t htt)).w
        (Classical.choice (hT t htt)).w (Matrix.of m) *
        starRingEnd ℂ (Formalism.MainNotions.S.psiGen k r (z0 k r) (cBase r t) (Matrix.of m))
        ∂(Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) 1) = ∫ x, f t x := by
    rw [hμN, hemb.integral_map]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    rw [hfe t htt x]
    show ⟪(Classical.choice (hT t htt)).w, S7.PsiM (Classical.choice (hT t htt)) (μ t htt)
        (P * NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) * P⁻¹)
        (Classical.choice (hT t htt)).w⟫_ℂ *
        starRingEnd ℂ (Formalism.MainNotions.S.psiGen k r (z0 k r) (cBase r t)
          (NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))))) = _
    congr 1
    rw [hpsi _ (hU x) (t : ℝ), ← Complex.exp_conj, map_mul, Complex.conj_ofReal, ← conjL_apply, hτconj x]
    congr 1
    push_cast
    ring
  have hint2 : Integrable (fun m : Formalism.QuantumDeterminants.Mt k r =>
      ‖S7.PsiM (Classical.choice (hT t htt)) (μ t htt) (P * Matrix.of m * P⁻¹)‖)
      (Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) 1) := by
    rw [hμN, hemb.integrable_map_iff]
    have hfr : (Module.finrank ℝ (Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r)) : ℝ) < 2 * (c5 / 16) * t := by
      have h1 := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (c5 / 16))).mp hN₂
      have h2 : (N₂ : ℝ) ≤ t := by exact_mod_cast htN
      nlinarith
    refine Integrable.mono' (integrable_rpow_neg_one_add_norm_sq (μ := volume) hfr)
      ((hPc t htt).norm.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [Function.comp_apply, norm_norm]
    exact (hbound t htt x).trans (le_of_eq (by congr 1; ring))
  have h7 := hB7b k r (parEps k r) (lowK (parEps k r) (lamT k r u b t)) (Classical.choice (hT t htt))
    (μ t htt) P u (cBase r t) Hπ πm ξ μW (Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) 1) hk hP hPW hHCU hξn
    hξw (hWwt t) hμW hμW1 hNhaar.1 (hPF t htt).2 hint2
  refine ⟨Classical.choice (hT t htt), μ t htt, P, z0 k r, cBase r t, Hπ, iπ1, iπ2, hCS, πm, μW,
    Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) 1, hμ t htt, hP,
    ⟨hinWb, by rw [hTz1]; norm_num, hcne, hHCW, hμW, hNhaar⟩,
    (Classical.choice (hT t htt)).w, (Classical.choice (hT t htt)).w, ξ, 1, 1, hone, hone, ?_⟩
  intro h0
  rw [h0, inner_zero_right, hI] at h7
  have hfr : (Module.finrank ℂ Hπ : ℂ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℂ) (M := Hπ)).ne'
  rcases mul_eq_zero.mp h7.symm with h | h
  · exact inv_ne_zero hfr h
  · exact hne h

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.LieExponentialMajorant

variable {n : ℕ}

theorem hs_eq_re_trace (A : Matrix (Fin n) (Fin n) ℂ) :
    S7.hs A = (trace (Aᴴ * A)).re := by
  simp only [S7.hs, trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

theorem sqrt_hs_mul (A B : Matrix (Fin n) (Fin n) ℂ) :
    Real.sqrt (S7.hs (A * B)) ≤ Real.sqrt (S7.hs A) * Real.sqrt (S7.hs B) := by
  let _ : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAddCommGroup
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ, Real.sqrt (S7.hs M) = ‖M‖ := by
    intro M
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow, S7.hs]
    norm_num
  rw [key, key, key]
  exact Matrix.frobenius_norm_mul A B

theorem trace_conj {V W A : Matrix (Fin n) (Fin n) ℂ} (h : W * V = 1) :
    trace (V * A * W) = trace A := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem phi_le (x : ℝ) :
    Real.exp (2 * x) + Real.exp (-(2 * x)) - 2 ≤ 4 * x ^ 2 * Real.exp (2 * |x|) := by
  have key : ∀ y : ℝ, 0 ≤ y →
      Real.exp (2 * y) + Real.exp (-(2 * y)) - 2 ≤ 4 * y ^ 2 * Real.exp (2 * y) := by
    intro y hy
    have e1 : Real.exp (2 * y) = Real.exp y * Real.exp y := by rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(2 * y)) = Real.exp (-y) * Real.exp (-y) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    have h1 := Real.add_one_le_exp (-(2 * y))
    have hpos := Real.exp_pos y
    have hu0 : 0 ≤ Real.exp y - Real.exp (-y) := by
      have := Real.exp_le_exp.mpr (show -y ≤ y by linarith); linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    rw [e2] at h2
    have h3 : Real.exp y * (Real.exp (-y) * Real.exp (-y)) = Real.exp (-y) := by
      rw [← mul_assoc, e3, one_mul]
    have hu : Real.exp y - Real.exp (-y) ≤ 2 * y * Real.exp y := by nlinarith
    calc Real.exp (2 * y) + Real.exp (-(2 * y)) - 2 = (Real.exp y - Real.exp (-y)) ^ 2 := by
          rw [e1, e2]; nlinarith [e3]
      _ ≤ (2 * y * Real.exp y) ^ 2 := pow_le_pow_left₀ hu0 hu 2
      _ = 4 * y ^ 2 * Real.exp (2 * y) := by rw [e1]; ring
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact key x hx
  · have := key (-x) (by linarith)
    rw [abs_of_nonpos hx]
    have e : -(2 * -x) = 2 * x := by ring
    rw [e] at this
    have e' : (-x) ^ 2 = x ^ 2 := by ring
    rw [e'] at this
    rw [show 2 * -x = -(2 * x) by ring] at this ⊢
    linarith

theorem exp_two_lt : Real.exp 2 < 7.5 := by
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_pos 1
  rw [h]; nlinarith

theorem log_bound (D : ℝ) (m : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ s a y : ℝ, 0 ≤ s → 0 ≤ a → 0 ≤ y →
    a ≤ 4 * s * Real.exp (2 * Real.sqrt s) → y ≤ D ^ 2 * a * (1 + Real.sqrt a) ^ (2 * m) →
    Real.log (1 + y) ≤ A * min s (Real.sqrt s) := by
  set A1 : ℝ := D ^ 2 * 49 ^ m * 30 with hA1d
  set B : ℝ := D ^ 2 * 9 ^ (m + 1) with hBd
  have hB : 0 ≤ B := by positivity
  set A2 : ℝ := Real.log (1 + B) + 4 * ((m : ℝ) + 1) with hA2d
  have hA1 : 0 ≤ A1 := by positivity
  have hlB : 0 ≤ Real.log (1 + B) := Real.log_nonneg (by linarith)
  have hA2 : 0 ≤ A2 := by positivity
  refine ⟨max A1 A2, le_max_of_le_left hA1, fun s a y hs ha hy haS hyA => ?_⟩
  have hσ0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hσs : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
  have hsa0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hlog : Real.log (1 + y) ≤ y := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + y by linarith); linarith
  have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
  rcases le_total s 1 with h1 | h1
  · have hσ1 : Real.sqrt s ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt h1
    have hmin : min s (Real.sqrt s) = s := min_eq_left (by nlinarith)
    have he : Real.exp (2 * Real.sqrt s) ≤ 7.5 :=
      (Real.exp_le_exp.mpr (by linarith)).trans exp_two_lt.le
    have ha30 : a ≤ 30 * s := by nlinarith
    have ha36 : a ≤ 36 := by linarith
    have hsq6 : Real.sqrt a ≤ 6 := by
      have := Real.sqrt_le_sqrt ha36
      rwa [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    have hp : (1 + Real.sqrt a) ^ (2 * m) ≤ 49 ^ m := by
      calc (1 + Real.sqrt a) ^ (2 * m) ≤ 7 ^ (2 * m) :=
            pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = 49 ^ m := by rw [pow_mul]; norm_num
    have hy2 : y ≤ A1 * s := by
      calc y ≤ D ^ 2 * a * (1 + Real.sqrt a) ^ (2 * m) := hyA
        _ ≤ D ^ 2 * (30 * s) * 49 ^ m := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left ha30 hD2) hp (by positivity) (by positivity)
        _ = A1 * s := by rw [hA1d]; ring
    rw [hmin]
    calc Real.log (1 + y) ≤ A1 * s := hlog.trans hy2
      _ ≤ max A1 A2 * s := mul_le_mul_of_nonneg_right (le_max_left _ _) hs
  · have hσ1 : 1 ≤ Real.sqrt s := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt h1
    have hmin : min s (Real.sqrt s) = Real.sqrt s := min_eq_right (by nlinarith)
    set σ := Real.sqrt s with hσ
    set E := Real.exp σ with hE
    have hE1 : 1 ≤ E := Real.one_le_exp hσ0
    have hσE : σ ≤ E := by have := Real.add_one_le_exp σ; linarith
    have he2 : Real.exp (2 * σ) = E * E := by rw [hE, ← Real.exp_add]; ring_nf
    have hsa1 : Real.sqrt a ≤ 2 * σ * E := by
      have h2 : a ≤ (2 * σ * E) ^ 2 := by rw [← hσs] at haS; rw [he2] at haS; nlinarith
      have := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq (by positivity)] at this
    have hsa2 : 1 + Real.sqrt a ≤ 3 * E ^ 2 := by nlinarith
    have hy2 : y ≤ B * Real.exp (4 * ((m : ℝ) + 1) * σ) := by
      have hexp : Real.exp (4 * ((m : ℝ) + 1) * σ) = E ^ (4 * (m + 1)) := by
        rw [hE, ← Real.exp_nat_mul]; push_cast; ring_nf
      calc y ≤ D ^ 2 * a * (1 + Real.sqrt a) ^ (2 * m) := hyA
        _ ≤ D ^ 2 * (1 + Real.sqrt a) ^ 2 * (1 + Real.sqrt a) ^ (2 * m) := by
            gcongr; nlinarith
        _ = D ^ 2 * (1 + Real.sqrt a) ^ (2 * (m + 1)) := by ring
        _ ≤ D ^ 2 * (3 * E ^ 2) ^ (2 * (m + 1)) := by gcongr
        _ = B * Real.exp (4 * ((m : ℝ) + 1) * σ) := by
            rw [hexp, hBd, mul_pow, ← pow_mul, pow_mul 3 2 (m + 1)]; ring_nf
    have hX1 : 1 ≤ Real.exp (4 * ((m : ℝ) + 1) * σ) := Real.one_le_exp (by positivity)
    have h3 : 1 + y ≤ (1 + B) * Real.exp (4 * ((m : ℝ) + 1) * σ) := by nlinarith
    have h4 : Real.log (1 + y) ≤ Real.log (1 + B) + 4 * ((m : ℝ) + 1) * σ := by
      calc Real.log (1 + y) ≤ Real.log ((1 + B) * Real.exp (4 * ((m : ℝ) + 1) * σ)) :=
            Real.log_le_log (by linarith) h3
        _ = _ := by rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp]
    rw [hmin]
    calc Real.log (1 + y) ≤ Real.log (1 + B) + 4 * ((m : ℝ) + 1) * σ := h4
      _ ≤ A2 * σ := by rw [hA2d]; nlinarith
      _ ≤ max A1 A2 * σ := mul_le_mul_of_nonneg_right (le_max_right _ _) hσ0

theorem herm_decomp {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) :
    ∃ (V : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℝ), star V * V = 1 ∧ V * star V = 1 ∧
      X = V * diagonal (fun i => (l i : ℂ)) * star V ∧
      NormedSpace.exp X = V * diagonal (fun i => (Real.exp (l i) : ℂ)) * star V := by
  have h1 := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  have h2 := Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
  refine ⟨hX.eigenvectorUnitary, hX.eigenvalues, h1, h2, ?_, ?_⟩
  · conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  · conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]
    have hinv : star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
        (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)⁻¹ :=
      (Matrix.inv_eq_left_inv h1).symm
    have hu : IsUnit (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) :=
      ⟨⟨_, _, h2, h1⟩, rfl⟩
    rw [hinv, Matrix.exp_conj _ _ hu, Matrix.exp_diagonal]
    congr 3
    funext i
    rw [Pi.coe_exp]
    simp [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

theorem hs_sub_one (g : Matrix (Fin n) (Fin n) ℂ) (ht : trace g = (n : ℂ)) :
    S7.hs (g - 1) = (trace (gᴴ * g)).re - n := by
  rw [hs_eq_re_trace]
  simp only [conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub, Matrix.mul_one,
    Matrix.one_mul, trace_sub, trace_one, trace_conjTranspose, ht, Complex.sub_re]
  simp

open ReciprocityTheory.ChartRestriction.DS.Lap.Base.N in
open scoped Matrix.Norms.Operator in
theorem trace_exp_lie {k r : ℕ} {Y : Mat k r} (hY : Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r)) :
    trace (NormedSpace.exp Y) = ((2 * r + k + 1 : ℕ) : ℂ) := by
  rw [lieOf_Nset_eq] at hY
  have h0 := (mem_lieN.mp hY).1
  have h1 : NormedSpace.exp Y - 1 ∈ levF (levB k r) 0 := (isFilB (k := k) (r := r)).exp_shear.1 Y h0
  have hnil : IsNilpotent (NormedSpace.exp Y - 1) := by
    refine ⟨2 * r + 1, ?_⟩
    have := (isFilB (k := k) (r := r)).pow_mem h1 (2 * r)
    rw [(isFilB (k := k) (r := r)).bot] at this
    exact (Submodule.mem_bot ℝ).mp this
  have ht := (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have e : NormedSpace.exp Y = 1 + (NormedSpace.exp Y - 1) := by abel
  rw [e, trace_add, ht, trace_one]
  simp

theorem herm_of_inP {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (h : ReciprocityTheory.ChartRestriction.DS.inP ε X) : X.IsHermitian := by
  obtain ⟨hG, hP⟩ := h
  have h1 : Xᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε = X * ReciprocityTheory.ChartRestriction.DS.Jm ε := by
    rw [hP]; exact eq_neg_of_add_eq_zero_left hG
  have hJ := S7.Jm_mul_self ε
  show Xᴴ = X
  calc Xᴴ = Xᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * ReciprocityTheory.ChartRestriction.DS.Jm ε := by
        rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = X * ReciprocityTheory.ChartRestriction.DS.Jm ε * ReciprocityTheory.ChartRestriction.DS.Jm ε := by rw [h1]
    _ = X := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]

theorem eq_zero_of_noncompactPart_of_noncompactRank_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (h : ReciprocityTheory.ChartRestriction.DS.inP ε X) (hq : S7.q0 ε = 0) : X = 0 := by
  have hP := h.2
  have hc : ∃ b : Bool, ∀ a, ε a = b := by
    rcases Nat.min_eq_zero_iff.mp hq with hp | hp
    · refine ⟨false, fun a => ?_⟩
      rw [ReciprocityTheory.ChartRestriction.DS.pOf, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hp
      simpa using hp (Finset.mem_univ a)
    · refine ⟨true, fun a => ?_⟩
      rw [ReciprocityTheory.ChartRestriction.DS.qOf, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hp
      simpa using hp (Finset.mem_univ a)
  obtain ⟨b, hb⟩ := hc
  ext i j
  have := congrFun (congrFun hP i) j
  simp only [ReciprocityTheory.ChartRestriction.DS.Jm, mul_diagonal, diagonal_mul, Matrix.neg_apply, hb] at this
  cases b <;> simp at this
  · show X i j = 0
    linear_combination -this / 2
  · show X i j = 0
    linear_combination this / 2

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.LieExponentialMajorant
end
end

section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.LieExponentialMajorant

variable {n : ℕ}

theorem re_trace_conj_diag {V : Matrix (Fin n) (Fin n) ℂ} (hV1 : star V * V = 1) (d : Fin n → ℝ) :
    (trace (V * diagonal (fun i => (d i : ℂ)) * star V)).re = ∑ i, d i := by
  rw [trace_conj hV1, trace_diagonal, Complex.re_sum]; simp

theorem diag_mul' (a b : Fin n → ℝ) :
    diagonal (fun i => (a i : ℂ)) * diagonal (fun i => (b i : ℂ)) =
      diagonal (fun i => ((a i * b i : ℝ) : ℂ)) := by
  rw [diagonal_mul_diagonal]; congr 1; funext i; push_cast; rfl

theorem diag_herm (a : Fin n → ℝ) :
    (diagonal (fun i => (a i : ℂ)))ᴴ = diagonal (fun i => (a i : ℂ)) := by
  rw [diagonal_conjTranspose]; congr 1; funext i; simp

theorem conj_herm (V : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℝ) :
    (V * diagonal (fun i => (a i : ℂ)) * star V)ᴴ = V * diagonal (fun i => (a i : ℂ)) * star V := by
  rw [conjTranspose_mul, conjTranspose_mul, diag_herm, star_eq_conjTranspose,
    conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

theorem sum_bound (l : Fin n → ℝ) :
    ∑ i, (Real.exp (2 * l i) + Real.exp (-(2 * l i)) - 2) ≤
      4 * (∑ i, l i ^ 2) * Real.exp (2 * Real.sqrt (∑ i, l i ^ 2)) := by
  have hab : ∀ i, |l i| ≤ Real.sqrt (∑ j, l j ^ 2) := by
    intro i
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (l j)) (Finset.mem_univ i))
  calc ∑ i, (Real.exp (2 * l i) + Real.exp (-(2 * l i)) - 2)
      ≤ ∑ i, 4 * l i ^ 2 * Real.exp (2 * Real.sqrt (∑ j, l j ^ 2)) := by
        refine Finset.sum_le_sum fun i _ => (phi_le (l i)).trans ?_
        have := Real.exp_le_exp.mpr (show 2 * |l i| ≤ 2 * Real.sqrt (∑ j, l j ^ 2) by
          linarith [hab i])
        have h0 : 0 ≤ 4 * l i ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left this h0
    _ = 4 * (∑ i, l i ^ 2) * Real.exp (2 * Real.sqrt (∑ i, l i ^ 2)) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem hs_polar {g h κ V : Matrix (Fin n) (Fin n) ℂ} {l : Fin n → ℝ}
    (hV1 : star V * V = 1) (hk : star κ * κ = 1)
    (hgE : g = κ * (V * diagonal (fun i => (Real.exp (l i) : ℂ)) * star V))
    (hhg : h * g = 1) (htg : trace g = (n : ℂ)) (hth : trace h = (n : ℂ)) :
    S7.hs (g - 1) ≤ ∑ i, (Real.exp (2 * l i) + Real.exp (-(2 * l i)) - 2) := by
  set E := diagonal (fun i => (Real.exp (l i) : ℂ)) with hE
  have hgg : gᴴ * g = V * diagonal (fun i => ((Real.exp (l i) * Real.exp (l i) : ℝ) : ℂ)) * star V := by
    have e1 : gᴴ = V * E * star V * κᴴ := by
      rw [hgE, conjTranspose_mul, conj_herm]
    have hk' : κᴴ * κ = 1 := hk
    calc gᴴ * g = V * E * star V * (κᴴ * κ) * (V * E * star V) := by
          rw [e1, hgE]; simp only [Matrix.mul_assoc]
      _ = V * E * (star V * V) * E * star V := by
          rw [hk', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = V * (E * E) * star V := by rw [hV1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hE, diag_mul']
  set M := V * diagonal (fun i => ((Real.exp (-l i) * Real.exp (-l i) : ℝ) : ℂ)) * star V with hM
  have hgM : gᴴ * g * M = 1 := by
    have hdd : diagonal (fun i => ((Real.exp (l i) * Real.exp (l i) : ℝ) : ℂ)) *
        diagonal (fun i => ((Real.exp (-l i) * Real.exp (-l i) : ℝ) : ℂ)) = 1 := by
      rw [diag_mul', ← diagonal_one]; congr 1; funext i
      have : Real.exp (l i) * Real.exp (l i) * (Real.exp (-l i) * Real.exp (-l i)) = 1 := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf; simp
      rw [this]; simp
    rw [hgg, hM]
    calc V * diagonal (fun i => ((Real.exp (l i) * Real.exp (l i) : ℝ) : ℂ)) * star V *
          (V * diagonal (fun i => ((Real.exp (-l i) * Real.exp (-l i) : ℝ) : ℂ)) * star V)
        = V * diagonal (fun i => ((Real.exp (l i) * Real.exp (l i) : ℝ) : ℂ)) * (star V * V) *
          diagonal (fun i => ((Real.exp (-l i) * Real.exp (-l i) : ℝ) : ℂ)) * star V := by
          simp only [Matrix.mul_assoc]
      _ = V * star V := by rw [hV1, Matrix.mul_one, Matrix.mul_assoc V, hdd, Matrix.mul_one]
      _ = 1 := mul_eq_one_comm.mp hV1
  have hgh : g * h = 1 := mul_eq_one_comm.mp hhg
  have hhh : h * hᴴ = M := by
    have h1 : gᴴ * g * (h * hᴴ) = 1 := by
      calc gᴴ * g * (h * hᴴ) = gᴴ * (g * h) * hᴴ := by simp only [Matrix.mul_assoc]
        _ = (h * g)ᴴ := by rw [hgh, Matrix.mul_one, conjTranspose_mul]
        _ = 1 := by rw [hhg, conjTranspose_one]
    have h2 : M * (gᴴ * g) = 1 := mul_eq_one_comm.mp hgM
    calc h * hᴴ = M * (gᴴ * g) * (h * hᴴ) := by rw [h2, Matrix.one_mul]
      _ = M := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have hA := hs_sub_one g htg
  have hB := hs_sub_one h hth
  rw [hgg, re_trace_conj_diag hV1] at hA
  rw [trace_mul_comm, hhh, hM, re_trace_conj_diag hV1] at hB
  have hB0 : 0 ≤ S7.hs (h - 1) := by
    unfold S7.hs; positivity
  have hn : (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
  have e2 : ∀ i, Real.exp (2 * l i) = Real.exp (l i) * Real.exp (l i) := fun i => by
    rw [← Real.exp_add]; ring_nf
  have e3 : ∀ i, Real.exp (-(2 * l i)) = Real.exp (-l i) * Real.exp (-l i) := fun i => by
    rw [← Real.exp_add]; ring_nf
  simp only [e2, e3]
  have : ∑ i, (Real.exp (l i) * Real.exp (l i) + Real.exp (-l i) * Real.exp (-l i) - 2) =
      (∑ i, Real.exp (l i) * Real.exp (l i) - n) + (∑ i, Real.exp (-l i) * Real.exp (-l i) - n) := by
    rw [hn, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this]
  linarith

open ReciprocityTheory.ChartRestriction.DS

theorem neg_mem_lie {k r : ℕ} {Y : Mat k r} (hY : Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r)) :
    -Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r) := by
  intro t
  have := hY (-t)
  rw [Complex.ofReal_neg, neg_smul] at this
  rwa [smul_neg]

theorem hs_X_eq {n : ℕ} {X V : Matrix (Fin n) (Fin n) ℂ} {l : Fin n → ℝ} (hXh : X.IsHermitian)
    (hV1 : star V * V = 1) (hXV : X = V * diagonal (fun i => (l i : ℂ)) * star V) :
    S7.hs X = ∑ i, l i ^ 2 := by
  rw [hs_eq_re_trace, hXh.eq, hXV]
  have : V * diagonal (fun i => (l i : ℂ)) * star V * (V * diagonal (fun i => (l i : ℂ)) * star V) =
      V * diagonal (fun i => ((l i * l i : ℝ) : ℂ)) * star V := by
    calc _ = V * diagonal (fun i => (l i : ℂ)) * (star V * V) * diagonal (fun i => (l i : ℂ)) *
          star V := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV1, Matrix.mul_one, Matrix.mul_assoc V, diag_mul']
  rw [this, re_trace_conj_diag hV1]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem polar_a {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hPP : P⁻¹ * P = 1)
    (hPP' : P * P⁻¹ = 1) {Y : Mat k r} (hY : Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r))
    (κ : S7.KG ε) {X : Mat k r} (hX : inP ε X)
    (heq : P * NormedSpace.exp Y * P⁻¹ = S7.toMK κ * NormedSpace.exp X) :
    S7.hs (P * NormedSpace.exp Y * P⁻¹ - 1) ≤
      4 * S7.hs X * Real.exp (2 * Real.sqrt (S7.hs X)) := by
  have htg : trace (P * NormedSpace.exp Y * P⁻¹) = ((2 * r + k + 1 : ℕ) : ℂ) := by
    rw [trace_conj hPP]; exact trace_exp_lie hY
  have hth : trace (P * NormedSpace.exp (-Y) * P⁻¹) = ((2 * r + k + 1 : ℕ) : ℂ) := by
    rw [trace_conj hPP]; exact trace_exp_lie (neg_mem_lie hY)
  have hhg : P * NormedSpace.exp (-Y) * P⁻¹ * (P * NormedSpace.exp Y * P⁻¹) = 1 := by
    have hx : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
      rw [Matrix.exp_neg]
      exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp Y))
    calc P * NormedSpace.exp (-Y) * P⁻¹ * (P * NormedSpace.exp Y * P⁻¹)
        = P * (NormedSpace.exp (-Y) * (P⁻¹ * P) * NormedSpace.exp Y) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPP, Matrix.mul_one, hx, Matrix.mul_one, hPP']
  have hk : star (S7.toMK κ) * S7.toMK κ = 1 :=
    Unitary.star_mul_self_of_mem (show S7.toMK κ ∈ Kset ε from κ.2).1
  have hXh := herm_of_inP hX
  obtain ⟨V, l, hV1, _, hXV, hEV⟩ := herm_decomp hXh
  have hgE : P * NormedSpace.exp Y * P⁻¹ =
      S7.toMK κ * (V * diagonal (fun i => (Real.exp (l i) : ℂ)) * star V) := by
    rw [heq, hEV]
  have ha := hs_polar hV1 hk hgE hhg htg hth
  rw [hs_X_eq hXh hV1 hXV]
  exact ha.trans (sum_bound l)

theorem growth_a {k r : ℕ} {P : Mat k r} (hPP : P⁻¹ * P = 1) {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    {Y : Mat k r}
    (hgr : Real.sqrt (S7.hs Y) ≤ C * Real.sqrt (S7.hs (NormedSpace.exp Y - 1)) *
      (1 + Real.sqrt (S7.hs (NormedSpace.exp Y - 1))) ^ m) :
    S7.hs Y ≤ (C * (max (Real.sqrt (S7.hs P⁻¹) * Real.sqrt (S7.hs P)) 1) ^ (m + 1)) ^ 2 *
      S7.hs (P * NormedSpace.exp Y * P⁻¹ - 1) *
      (1 + Real.sqrt (S7.hs (P * NormedSpace.exp Y * P⁻¹ - 1))) ^ (2 * m) := by
  obtain ⟨K1, hK1⟩ : ∃ K1, K1 = max (Real.sqrt (S7.hs P⁻¹) * Real.sqrt (S7.hs P)) 1 := ⟨_, rfl⟩
  obtain ⟨a, had⟩ : ∃ a, a = S7.hs (P * NormedSpace.exp Y * P⁻¹ - 1) := ⟨_, rfl⟩
  rw [← hK1, ← had]
  have hK11 : 1 ≤ K1 := hK1 ▸ le_max_right _ _
  have hKK : Real.sqrt (S7.hs P⁻¹) * Real.sqrt (S7.hs P) ≤ K1 := hK1 ▸ le_max_left _ _
  have ha0 : 0 ≤ a := by rw [had]; unfold S7.hs; positivity
  have hexp : NormedSpace.exp Y - 1 = P⁻¹ * (P * NormedSpace.exp Y * P⁻¹ - 1) * P := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPP]
    congr 1
    simp only [← Matrix.mul_assoc]
    rw [hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have hb : Real.sqrt (S7.hs (NormedSpace.exp Y - 1)) ≤ K1 * Real.sqrt a := by
    rw [hexp]
    calc Real.sqrt (S7.hs (P⁻¹ * (P * NormedSpace.exp Y * P⁻¹ - 1) * P))
        ≤ Real.sqrt (S7.hs (P⁻¹ * (P * NormedSpace.exp Y * P⁻¹ - 1))) * Real.sqrt (S7.hs P) :=
          sqrt_hs_mul _ _
      _ ≤ Real.sqrt (S7.hs P⁻¹) * Real.sqrt a * Real.sqrt (S7.hs P) := by
          rw [had]; exact mul_le_mul_of_nonneg_right (sqrt_hs_mul _ _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (S7.hs P⁻¹) * Real.sqrt (S7.hs P) * Real.sqrt a := by ring
      _ ≤ K1 * Real.sqrt a := mul_le_mul_of_nonneg_right hKK (Real.sqrt_nonneg _)
  have hsa0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hb0 : 0 ≤ Real.sqrt (S7.hs (NormedSpace.exp Y - 1)) := Real.sqrt_nonneg _
  have hYb : Real.sqrt (S7.hs Y) ≤ C * K1 ^ (m + 1) * Real.sqrt a * (1 + Real.sqrt a) ^ m := by
    calc Real.sqrt (S7.hs Y)
        ≤ C * Real.sqrt (S7.hs (NormedSpace.exp Y - 1)) *
          (1 + Real.sqrt (S7.hs (NormedSpace.exp Y - 1))) ^ m := hgr
      _ ≤ C * (K1 * Real.sqrt a) * (K1 * (1 + Real.sqrt a)) ^ m := by
          gcongr
          nlinarith
      _ = C * K1 ^ (m + 1) * Real.sqrt a * (1 + Real.sqrt a) ^ m := by rw [mul_pow, pow_succ]; ring
  have hY0 : 0 ≤ S7.hs Y := by unfold S7.hs; positivity
  rw [← Real.sq_sqrt hY0]
  calc Real.sqrt (S7.hs Y) ^ 2 ≤ (C * K1 ^ (m + 1) * Real.sqrt a * (1 + Real.sqrt a) ^ m) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hYb 2
    _ = (C * K1 ^ (m + 1)) ^ 2 * a * (1 + Real.sqrt a) ^ (2 * m) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt ha0, ← pow_mul, mul_comm m 2, mul_pow]

theorem final_ineq {A q s L : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q) (hs : 0 ≤ s) (hL : L ≤ A * min s (Real.sqrt s))
    (hq0 : q = 0 → s = 0) :
    1 / ((A + 1) * (1 + q)) * L ≤ min s (Real.sqrt s / q) := by
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = min s (Real.sqrt s) := ⟨_, rfl⟩
  rw [← hμ] at hL
  have hμ0 : 0 ≤ μ := by rw [hμ]; exact le_min hs (Real.sqrt_nonneg _)
  have hA1 : 0 < A + 1 := by linarith
  have h1q : 0 < 1 + q := by linarith
  have hc : 1 / ((A + 1) * (1 + q)) * L ≤ μ / (1 + q) := by
    have hc0 : 0 ≤ 1 / ((A + 1) * (1 + q)) := by positivity
    calc 1 / ((A + 1) * (1 + q)) * L
        ≤ 1 / ((A + 1) * (1 + q)) * (A * μ) := mul_le_mul_of_nonneg_left hL hc0
      _ = A / (A + 1) * (μ / (1 + q)) := by field_simp
      _ ≤ 1 * (μ / (1 + q)) :=
          mul_le_mul_of_nonneg_right ((div_le_one hA1).mpr (by linarith)) (div_nonneg hμ0 h1q.le)
      _ = μ / (1 + q) := one_mul _
  have hμs : μ / (1 + q) ≤ s := (div_le_self hμ0 (by linarith)).trans (hμ ▸ min_le_left _ _)
  refine le_min (hc.trans hμs) ?_
  rcases eq_or_lt_of_le hq with h0 | h0
  · have hs0 : s = 0 := hq0 h0.symm
    have : μ = 0 := by rw [hμ, hs0]; simp
    rw [this] at hc
    rw [hs0]
    simpa using hc
  · calc 1 / ((A + 1) * (1 + q)) * L ≤ μ / (1 + q) := hc
      _ ≤ Real.sqrt s / (1 + q) := div_le_div_of_nonneg_right (hμ ▸ min_le_right _ _) h1q.le
      _ ≤ Real.sqrt s / q := div_le_div_of_nonneg_left (Real.sqrt_nonneg _) h0 (by linarith)

theorem lieExponentialMajorant_holds : CayleyMajorantBound := by
  intro k r ε P hP
  obtain ⟨C, m, hC, hgr⟩ := (b4 k r).2.2.2.2
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPP' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  obtain ⟨A, hA, hlog⟩ :=
    log_bound (C * (max (Real.sqrt (S7.hs P⁻¹) * Real.sqrt (S7.hs P)) 1) ^ (m + 1)) m
  have hq : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  refine ⟨1 / ((A + 1) * (1 + Real.sqrt (2 * (S7.q0 ε : ℝ)))), by positivity,
    fun Y hY κ X hX heq => ?_⟩
  have hs0 : 0 ≤ S7.hs X := by unfold S7.hs; positivity
  have ha0 : 0 ≤ S7.hs (P * NormedSpace.exp Y * P⁻¹ - 1) := by unfold S7.hs; positivity
  have hY0 : 0 ≤ S7.hs Y := by unfold S7.hs; positivity
  have hL := hlog _ _ _ hs0 ha0 hY0 (polar_a hPP hPP' hY κ hX heq) (growth_a hPP hC (hgr Y hY))
  refine final_ineq hA hq hs0 hL fun h0 => ?_
  have hq0 : S7.q0 ε = 0 := by
    have h2 : (2 * (S7.q0 ε : ℝ)) = 0 := by
      have := Real.sqrt_eq_zero'.mp h0
      have h3 : (0 : ℝ) ≤ 2 * (S7.q0 ε : ℝ) := by positivity
      linarith
    exact_mod_cast (by linarith : (S7.q0 ε : ℝ) = 0)
  rw [eq_zero_of_noncompactPart_of_noncompactRank_zero hX hq0]
  simp [S7.hs]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.LieExponentialMajorant
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

theorem b5 : CayleyMajorantBound := LieExponentialMajorant.lieExponentialMajorant_holds

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

private theorem integrable_one_add_mul_norm_sq_rpow_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [μ.IsAddHaarMeasure] {a s : ℝ} (ha : 0 < a) (hs : (Module.finrank ℝ E : ℝ) < 2 * s) :
    MeasureTheory.Integrable (fun v : E => (1 + a * ‖v‖ ^ 2) ^ (-s)) μ := by
  open MeasureTheory Filter Topology in
  have h := (integrable_rpow_neg_one_add_norm_sq (μ := μ) hs).comp_smul (Real.sqrt_pos.2 ha).ne'
  refine h.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 ha), mul_pow,
    Real.sq_sqrt ha.le]
  congr 1
  ring

private theorem main_lemma_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [μ.IsAddHaarMeasure] (f : ℕ → E → ℂ)
    (hm : ∀ᶠ t : ℕ in Filter.atTop, MeasureTheory.AEStronglyMeasurable (f t) μ) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ)
    (hlim : ∀ v, Filter.Tendsto (fun t : ℕ => f t ((Real.sqrt t)⁻¹ • v)) Filter.atTop
      (nhds (Complex.exp (-(B v v)))))
    {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ)
    (hbd : ∀ᶠ t : ℕ in Filter.atTop, ∀ v, ‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))) :
    ∀ᶠ t : ℕ in Filter.atTop, MeasureTheory.Integrable (f t) μ ∧ ∫ v, f t v ∂μ ≠ 0 := by
  open MeasureTheory Filter Topology in
  have hbig : ∀ᶠ t : ℕ in atTop, (Module.finrank ℝ E : ℝ) < 2 * (γ * t) ∧ (1 : ℝ) ≤ t := by
    have h1 : Tendsto (fun t : ℕ => 2 * (γ * (t : ℝ))) atTop atTop :=
      Tendsto.const_mul_atTop two_pos (Tendsto.const_mul_atTop hγ tendsto_natCast_atTop_atTop)
    filter_upwards [h1.eventually_gt_atTop (Module.finrank ℝ E : ℝ), eventually_ge_atTop 1]
      with t ht ht1
    exact ⟨ht, by exact_mod_cast ht1⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hbd.and hm).and hbig)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos (hN N le_rfl).2.2

  have hmaj : ∀ t : ℕ, N ≤ t → ∀ w : E,
      ‖f t ((Real.sqrt t)⁻¹ • w)‖ ≤ (1 + c / N * ‖w‖ ^ 2) ^ (-(γ * N)) := by
    intro t ht w
    have ht' : (N : ℝ) ≤ t := by exact_mod_cast ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hNpos ht'
    have h1 := (hN t ht).1.1 ((Real.sqrt t)⁻¹ • w)
    have hn : ‖(Real.sqrt t)⁻¹ • w‖ ^ 2 = ‖w‖ ^ 2 / t := by
      rw [norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        inv_pow, Real.sq_sqrt htpos.le]
      ring
    rw [hn] at h1
    refine h1.trans ?_
    have hx : 0 ≤ c * ‖w‖ ^ 2 := by positivity
    have hmono := ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.mono_pow hx hNpos ht'
    have hA : 0 < 1 + c * ‖w‖ ^ 2 / N := by positivity
    have hB : 0 < 1 + c * ‖w‖ ^ 2 / t := by positivity
    have key : (1 + c * ‖w‖ ^ 2 / N) ^ (γ * N) ≤ (1 + c * ‖w‖ ^ 2 / t) ^ (γ * t) := by
      rw [mul_comm γ (N : ℝ), mul_comm γ (t : ℝ), Real.rpow_mul hA.le, Real.rpow_mul hB.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hA.le _) hmono hγ.le
    have e1 : c * (‖w‖ ^ 2 / t) = c * ‖w‖ ^ 2 / t := by ring
    have e2 : c / N * ‖w‖ ^ 2 = c * ‖w‖ ^ 2 / N := by ring
    rw [e1, e2, Real.rpow_neg hB.le, Real.rpow_neg hA.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hA _) key
  have hbint : Integrable (fun w : E => (1 + c / N * ‖w‖ ^ 2) ^ (-(γ * N))) μ :=
    integrable_one_add_mul_norm_sq_rpow_neg μ (div_pos hc hNpos) (hN N le_rfl).2.1
  have hgm : ∀ t : ℕ, N ≤ t → AEStronglyMeasurable (fun w => f t ((Real.sqrt t)⁻¹ • w)) μ := by
    intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hNpos (by exact_mod_cast ht)
    have hr : (Real.sqrt t)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 htpos).ne'
    exact (hN t ht).1.2.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_smul μ hr)
  have hT : Tendsto (fun t : ℕ => ∫ w, f t ((Real.sqrt t)⁻¹ • w) ∂μ) atTop
      (𝓝 (∫ w, Complex.exp (-(B w w)) ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence _
      ((eventually_ge_atTop N).mono hgm)
      ((eventually_ge_atTop N).mono fun t ht => Eventually.of_forall (hmaj t ht))
      hbint (Eventually.of_forall hlim)

  have hpos : ∀ v : E, v ≠ 0 → 0 < (B v v).re := by
    intro v hv
    have hle : ‖Complex.exp (-(B v v))‖ ≤ (1 + c / N * ‖v‖ ^ 2) ^ (-(γ * N)) :=
      le_of_tendsto (hlim v).norm (eventually_atTop.2 ⟨N, fun t ht => hmaj t ht v⟩)
    have hlt : (1 + c / N * ‖v‖ ^ 2) ^ (-(γ * N)) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · have hv' := norm_pos_iff.2 hv
        have : 0 < c / N * ‖v‖ ^ 2 := by positivity
        linarith
      · have := mul_pos hγ hNpos
        linarith
    rw [Complex.norm_exp] at hle
    have h3 : Real.exp (-(B v v)).re < 1 := hle.trans_lt hlt
    have h4 := Real.exp_lt_exp.1 (h3.trans_eq Real.exp_zero.symm)
    rw [Complex.neg_re] at h4
    linarith
  have hev : ∀ᶠ t : ℕ in atTop, ∫ w, f t ((Real.sqrt t)⁻¹ • w) ∂μ ≠ 0 :=
    hT.eventually_ne (ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.gauss_ne_zero μ B hpos)
  filter_upwards [eventually_ge_atTop N, hev] with t ht hgt
  refine ⟨?_, ?_⟩
  · exact Integrable.mono' (integrable_one_add_mul_norm_sq_rpow_neg μ hc (hN t ht).2.1) (hN t ht).1.2
      (Eventually.of_forall (hN t ht).1.1)
  · intro h0
    apply hgt
    rw [Measure.integral_comp_smul μ (f t) (Real.sqrt t)⁻¹, h0, smul_zero]

theorem b6 : GaussianLimitHaar := by
  intro E _ _ _ _ _ μ _ f hm B hlim c γ hc hγ hbd
  exact main_lemma_2 μ f hm B hlim hc hγ hbd

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

theorem b7a : ExistsUnitaryHaarProbability := fun k r => StandardBasisEmbedding.main k r

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

theorem parEps_eq_false_iff (k r : ℕ) (hk : 1 ≤ k) (b : Fin (2 * r + k + 1)) :
    parEps k r b = false ↔ k ≤ b.val ∧ (b.val - k) % 2 = 0 := by
  unfold parEps
  split_ifs with h
  · constructor
    · intro h'
      exact absurd h' (by decide)
    · intro h'
      omega
  · simp only [decide_eq_false_iff_not]
    omega

theorem parEps_true_of_lt (k r : ℕ) (hk : 1 ≤ k) (b : Fin (2 * r + k + 1)) (hb : b.val < k) :
    parEps k r b = true := by
  cases h : parEps k r b
  · exact absurd ((parEps_eq_false_iff k r hk b).1 h).1 (by omega)
  · rfl

theorem card_parEps_false (k r : ℕ) (hk : 1 ≤ k) :
    (univ.filter fun b : Fin (2 * r + k + 1) => parEps k r b = false).card = r + 1 := by
  have e : (univ.filter fun b : Fin (2 * r + k + 1) => parEps k r b = false) =
      (univ : Finset (Fin (r + 1))).image
        (fun i => (⟨k + 2 * i.val, by have := i.isLt; omega⟩ : Fin (2 * r + k + 1))) := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_image, parEps_eq_false_iff k r hk]
    constructor
    · rintro ⟨h1, h2⟩
      have := b.isLt
      refine ⟨⟨(b.val - k) / 2, by omega⟩, Fin.ext ?_⟩
      show k + 2 * ((b.val - k) / 2) = b.val
      omega
    · rintro ⟨i, rfl⟩
      show k ≤ k + 2 * i.val ∧ (k + 2 * i.val - k) % 2 = 0
      omega
  rw [e, card_image_of_injective]
  · simp
  · intro i j h
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)

theorem one_le_noncompactRank_parabolicSign (k r : ℕ) (hk : 1 ≤ k) : 1 ≤ S7.q0 (parEps k r) := by
  unfold S7.q0
  refine le_min ?_ ?_
  · unfold pOf
    refine Finset.card_pos.2 ⟨⟨0, by omega⟩, ?_⟩
    simp only [mem_filter, mem_univ, true_and]
    exact parEps_true_of_lt k r hk _ (by show 0 < k; omega)
  · unfold qOf
    rw [card_parEps_false k r hk]
    omega

theorem rhoN_parEps (k r : ℕ) (hk : 1 ≤ k) (a : Fin (2 * r + k + 1)) (ha : a.val < k) :
    rhoN (parEps k r) a = ((r : ℝ) + 1) / 2 := by
  have hea := parEps_true_of_lt k r hk a ha
  have e1 : (univ.filter fun b => a < b ∧ parEps k r b ≠ parEps k r a) =
      univ.filter fun b : Fin (2 * r + k + 1) => parEps k r b = false := by
    ext b
    simp only [mem_filter, mem_univ, true_and, hea, ne_eq, Bool.not_eq_true]
    constructor
    · exact And.right
    · intro hb
      have := ((parEps_eq_false_iff k r hk b).1 hb).1
      exact ⟨show a.val < b.val by omega, hb⟩
  have e2 : (univ.filter fun b => b < a ∧ parEps k r b ≠ parEps k r a) = ∅ := by
    refine filter_eq_empty_iff.2 ?_
    rintro b - ⟨hba, hne⟩
    have : b.val < a.val := hba
    exact hne (by rw [parEps_true_of_lt k r hk b (by omega), hea])
  unfold rhoN
  rw [e1, e2, card_parEps_false k r hk, card_empty]
  push_cast
  ring

theorem rhoC_parEps (k r : ℕ) (hk : 1 ≤ k) (a : Fin (2 * r + k + 1)) (ha : a.val < k) :
    rhoC (parEps k r) a = ((r : ℝ) + k - 1 - 2 * (a.val : ℝ)) / 2 := by
  have hea := parEps_true_of_lt k r hk a ha
  have e1 : (univ.filter fun b => a < b ∧ parEps k r b = parEps k r a) =
      (Ioi a).filter fun b => parEps k r b = true := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_Ioi, hea]
  have e3 : ((Ioi a).filter fun b => ¬ parEps k r b = true) =
      univ.filter fun b : Fin (2 * r + k + 1) => parEps k r b = false := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_Ioi, Bool.not_eq_true]
    constructor
    · exact And.right
    · intro hb
      have := ((parEps_eq_false_iff k r hk b).1 hb).1
      exact ⟨show a.val < b.val by omega, hb⟩
  have e2 : (univ.filter fun b => b < a ∧ parEps k r b = parEps k r a) = Iio a := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_Iio, hea]
    constructor
    · exact And.left
    · intro hb
      have : b.val < a.val := hb
      exact ⟨hb, parEps_true_of_lt k r hk b (by omega)⟩
  have hsum := card_filter_add_card_filter_not (s := Ioi a) (p := fun b => parEps k r b = true)
  rw [e3, card_parEps_false k r hk, Fin.card_Ioi] at hsum
  have hC : ((univ.filter fun b => a < b ∧ parEps k r b = parEps k r a).card : ℝ) =
      (r : ℝ) + k - 1 - (a.val : ℝ) := by
    rw [e1]
    have := a.isLt
    have h2 : ((Ioi a).filter fun b => parEps k r b = true).card + a.val + 1 = r + k := by omega
    have h3 := congrArg (fun m : ℕ => (m : ℝ)) h2
    push_cast at h3
    linarith
  unfold rhoC
  rw [hC, e2, Fin.card_Iio]
  ring

theorem u_strictAnti (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (hI : Interlaces k r u v b) : StrictAnti u := by
  have step : ∀ (i j : Fin k), j.val = i.val + 1 → u j < u i := by
    intro i j hij
    have hi : i.val < k - 1 := by have := j.isLt; omega
    obtain ⟨h1, h2⟩ := hI.1 ⟨i.val, hi⟩
    have : j = ⟨i.val + 1, by have := j.isLt; omega⟩ := Fin.ext hij
    rw [this]
    exact lt_trans h2 h1
  have gen : ∀ d : ℕ, ∀ (i j : Fin k), j.val = i.val + d + 1 → u j < u i := by
    intro d
    induction d with
    | zero => intro i j h; exact step i j (by omega)
    | succ d ih =>
      intro i j h
      have hm : i.val + d + 1 < k := by have := j.isLt; omega
      exact lt_trans (step ⟨i.val + d + 1, hm⟩ j (by show j.val = i.val + d + 1 + 1; omega))
        (ih i ⟨i.val + d + 1, hm⟩ rfl)
  intro i j hij
  have : i.val < j.val := hij
  exact gen (j.val - i.val - 1) i j (by omega)

theorem u_isHCParam (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (hP : IsHCPar (parLam k r v b)) (hI : Interlaces k r u v b)
    (hH : HalfInts k r u v b) : Formalism.QuantumDeterminants.IsHCParam u := by
  refine ⟨u_strictAnti k r u v b hI, fun i => ?_⟩
  let s : Fin (2 * r + k + 1) := ⟨0, by omega⟩
  obtain ⟨m1, hm1⟩ := hH i s
  obtain ⟨m2, hm2⟩ := hP.2 s
  refine ⟨m1 + m2 + r + 1, ?_⟩
  push_cast at hm2 ⊢
  linarith

theorem lamT_eq_sub (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t : ℕ)
    (a : Fin (2 * r + k + 1)) :
    lamT k r u b t a = lamT k r u b 0 a - ((a.val + 1 - k : ℕ) : ℝ) * (t : ℝ) := by
  unfold lamT
  split_ifs with h
  · have : a.val + 1 - k = 0 := by omega
    simp [this]
  · have : a.val - (k - 1) = a.val + 1 - k := by omega
    have e : ((a.val - (k - 1) : ℕ) : ℝ) = ((a.val + 1 - k : ℕ) : ℝ) := by rw [this]
    rw [e]
    simp

theorem lamT_eq_parLam (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (t : ℕ) (a : Fin (2 * r + k + 1)) (ha : k ≤ a.val) :
    lamT k r u b t a = parLam k r v b a - ((a.val + 1 - k : ℕ) : ℝ) * (t : ℝ) := by
  unfold lamT parLam
  rw [dif_neg (by omega), dif_neg (by omega)]
  have : a.val - (k - 1) = a.val + 1 - k := by omega
  have e : ((a.val - (k - 1) : ℕ) : ℝ) = ((a.val + 1 - k : ℕ) : ℝ) := by rw [this]
  rw [e]

theorem lowK_lamT_affine (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t : ℕ) :
    lowK (parEps k r) (lamT k r u b t) = (t : ℝ) • dNode k r + lowK (parEps k r) (lamT k r u b 0) := by
  funext a
  simp only [lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [lamT_eq_sub k r hk u b t a]
  have hd : dNode k r a = -((a.val + 1 - k : ℕ) : ℝ) := by
    unfold dNode
    split_ifs with h
    · have : a.val + 1 - k = 0 := by omega
      rw [this]
      simp
    · rfl
  rw [hd]
  ring

theorem lowK_lamT_first (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t : ℕ)
    (a : Fin k) :
    lowK (parEps k r) (lamT k r u b t) ⟨a.val, by omega⟩ = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u a := by
  have ha : (⟨a.val, by omega⟩ : Fin (2 * r + k + 1)).val < k := a.isLt
  have hN0 : Formalism.REAL.rhoN (Formalism.MainNotions.S.allPos k) a = 0 := by
    simp [Formalism.REAL.rhoN, Formalism.MainNotions.S.allPos]
  have e1 : (univ.filter fun b : Fin k => a < b ∧ Formalism.MainNotions.S.allPos k b = Formalism.MainNotions.S.allPos k a) =
      Ioi a := by
    ext b; simp [Formalism.MainNotions.S.allPos]
  have e2 : (univ.filter fun b : Fin k => b < a ∧ Formalism.MainNotions.S.allPos k b = Formalism.MainNotions.S.allPos k a) =
      Iio a := by
    ext b; simp [Formalism.MainNotions.S.allPos]
  have hC0 : Formalism.REAL.rhoC (Formalism.MainNotions.S.allPos k) a = (((k : ℝ) - 1) - 2 * (a.val : ℝ)) / 2 := by
    have hc : ((k - 1 - (a : ℕ) : ℕ) : ℝ) = (k : ℝ) - 1 - (a : ℕ) := by
      have := a.2
      rw [Nat.cast_sub (by omega), Nat.cast_sub hk]; simp
    unfold Formalism.REAL.rhoC
    rw [e1, e2, Fin.card_Ioi, Fin.card_Iio, hc]
    ring
  simp only [lowK, Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply]
  rw [rhoN_parEps k r hk _ ha, rhoC_parEps k r hk _ ha, hN0, hC0]
  simp only [lamT, a.isLt, ↓reduceDIte]
  ring

theorem lamT_facts : LamTStatement := by
  intro k r u v b hk hP hI hH
  refine ⟨u_isHCParam k r hk u v b hP hI hH, one_le_noncompactRank_parabolicSign k r hk,
    fun t => lowK_lamT_affine k r hk u b t, fun t a => lowK_lamT_first k r hk u b t a, ?_⟩
  set B : ℝ := ∑ a, |lamT k r u b 0 a| with hB
  have hBa : ∀ a, |lamT k r u b 0 a| ≤ B := fun a =>
    single_le_sum (f := fun a => |lamT k r u b 0 a|) (fun i _ => abs_nonneg _) (mem_univ a)
  have hB0 : 0 ≤ B := sum_nonneg (fun i _ => abs_nonneg _)
  obtain ⟨t₀, ht₀⟩ := exists_nat_gt (4 * B + 2 + 2 * |hNeed (parEps k r)|)
  refine ⟨t₀, fun t ht => ?_⟩
  have htR : 4 * B + 2 + 2 * |hNeed (parEps k r)| < (t : ℝ) :=
    lt_of_lt_of_le ht₀ (by exact_mod_cast ht)
  have hNa := le_abs_self (hNeed (parEps k r))
  have hNb := abs_nonneg (hNeed (parEps k r))
  have key : ∀ a c : Fin (2 * r + k + 1), a.val + 1 - k < c.val + 1 - k →
      (t : ℝ) / 2 ≤ lamT k r u b t a - lamT k r u b t c := by
    intro a c hac
    rw [lamT_eq_sub k r hk u b t a, lamT_eq_sub k r hk u b t c]
    have h1 : ((a.val + 1 - k : ℕ) : ℝ) + 1 ≤ ((c.val + 1 - k : ℕ) : ℝ) := by exact_mod_cast hac
    have h2 := abs_le.1 (hBa a)
    have h3 := abs_le.1 (hBa c)
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    nlinarith [mul_le_mul_of_nonneg_right h1 ht0]
  have hanti : StrictAnti (lamT k r u b t) := by
    intro a c hac
    have hac' : a.val < c.val := hac
    by_cases hc : c.val < k
    · have ha : a.val < k := by omega
      have hu := u_strictAnti k r u v b hI (show (⟨a.val, ha⟩ : Fin k) < ⟨c.val, hc⟩ from hac')
      simp only [lamT, ha, hc, ↓reduceDIte]
      linarith
    · have := key a c (by omega)
      linarith
  refine ⟨⟨hanti, fun a => ?_⟩, hanti, ?_, ?_⟩
  · by_cases ha : a.val < k
    · obtain ⟨m1, hm1⟩ := hH ⟨a.val, ha⟩ a
      obtain ⟨m2, hm2⟩ := hP.2 a
      refine ⟨m1 + m2, ?_⟩
      simp only [lamT, ha, ↓reduceDIte]
      push_cast at hm2 ⊢
      linarith
    · obtain ⟨m2, hm2⟩ := hP.2 a
      refine ⟨m2 - ((a.val + 1 - k : ℕ) : ℤ) * (t : ℤ), ?_⟩
      rw [lamT_eq_parLam k r hk u v b t a (by omega)]
      push_cast at hm2 ⊢
      linarith
  · intro a c hne
    have hj : a.val + 1 - k ≠ c.val + 1 - k := by
      intro h
      apply hne
      by_cases ha : a.val < k
      · have hc : c.val < k := by omega
        rw [parEps_true_of_lt k r hk a ha, parEps_true_of_lt k r hk c hc]
      · have : a = c := Fin.ext (by omega)
        rw [this]
    rcases lt_or_gt_of_ne hj with h | h
    · exact le_trans (key a c h) (le_abs_self _)
    · rw [abs_sub_comm]
      exact le_trans (key c a h) (le_abs_self _)
  · linarith

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

theorem stepIBase : StepIBaseStatement :=
  assembly b1 (matrixCoeffBounds_imply_bound b2 b3a b3b b3c smInfUnitary) b4 b5 b6 b7a b7b lamT_facts psiFor link

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end
