import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel

section
open NumberField IsDedekindDomain Topology Filter Set MeasureTheory
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

instance instModuleFiniteArchMatrix : Module.Finite ℝ (ArchMatrix K n) :=
  (inferInstance : FiniteDimensional ℝ (ArchMatrix K n))

instance instFreeArchMatrix : Module.Free ℝ (ArchMatrix K n) := Module.Free.of_divisionRing ℝ _

theorem exp_eq_one_add_of_mul_self_eq_zero {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] {Y : 𝔸} (h : Y * Y = 0) : NormedSpace.exp Y = 1 + Y := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  show ∑' k, _ = _
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ]
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add, pow_two, h, zero_mul, smul_zero]

def archExp (Y : ArchMatrix K n) : AdelicGLn.AdelicGL K n :=
  infEmb K n ((isExpLieAlgebra K n).expG ⟨Y, Submodule.mem_top⟩)

theorem coe_expG_top (Y : ArchMatrix K n) :
    ((((isExpLieAlgebra K n).expG ⟨Y, Submodule.mem_top⟩ : archGroup K n) : (ArchMatrix K n)ˣ) :
      ArchMatrix K n) = NormedSpace.exp Y := rfl

theorem expG_top_add {Y Z : ArchMatrix K n} (h : Commute Y Z) :
    (isExpLieAlgebra K n).expG ⟨Y + Z, Submodule.mem_top⟩ =
      (isExpLieAlgebra K n).expG ⟨Y, Submodule.mem_top⟩ *
        (isExpLieAlgebra K n).expG ⟨Z, Submodule.mem_top⟩ := by
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_expG_top]
  exact exp_add_of_commute' ℝ h

theorem archExp_zero : archExp (0 : ArchMatrix K n) = 1 := by
  have : (⟨0, Submodule.mem_top⟩ : archLie K n) = 0 := rfl
  rw [archExp, this, IsExpLieAlgebra.expG_zero, map_one]

theorem archExp_add {Y Z : ArchMatrix K n} (h : Commute Y Z) :
    archExp (Y + Z) = archExp Y * archExp Z := by
  rw [archExp, expG_top_add h, map_mul]
  rfl

theorem continuous_archExp : Continuous (archExp (K := K) (n := n)) :=
  continuous_infEmb.comp ((isExpLieAlgebra K n).continuous_expG.comp
    (continuous_id.subtype_mk _))

def lieOf : ArchMatrix K n →ₗ[ℝ] (isExpLieAlgebra K n).lieSubalgebra where
  toFun Y := ⟨Y, (isExpLieAlgebra K n).mem_lieSubalgebra.2 Submodule.mem_top⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem hasDerivAt_archExp (ψ : archSmooth K n) (g : AdelicGLn.AdelicGL K n) (Y : ArchMatrix K n)
    (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * archExp (s • Y)))
      ((uAction (UniversalEnvelopingAlgebra.ι ℝ (lieOf Y)) ψ : AdelicGLn.AdelicGL K n → ℂ)
        (g * archExp (s₀ • Y))) s₀ := by
  rw [uAction_ι_apply]
  have h := (isExpLieAlgebra K n).hasDerivAt_rightDeriv (ψ.2 (g * archExp (s₀ • Y)))
    ((isExpLieAlgebra K n).ofLie (lieOf Y)) 1
  rw [← sub_self s₀] at h
  refine (h.comp_sub_const s₀ s₀).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [archSlice_apply, one_mul]
  have e : infEmb K n ((isExpLieAlgebra K n).expG ((s - s₀) • (isExpLieAlgebra K n).ofLie (lieOf Y))) =
      archExp ((s - s₀) • Y) := rfl
  rw [e, mul_assoc, ← archExp_add ((Commute.refl Y).smul_left _ |>.smul_right _)]
  rw [show s₀ • Y + (s - s₀) • Y = s • Y by module]

def diffSum (ψ : AdelicGLn.AdelicGL K n → ℂ) (x : AdelicGLn.AdelicGL K n) {k : ℕ}
    (Y : Fin k → ArchMatrix K n) : ℂ :=
  ∑ ε : Fin k → Bool, (altSign ε : ℂ) * ψ (x * archExp (altPoint Y ε))

theorem diffSum_eq_altSum (ψ : AdelicGLn.AdelicGL K n → ℂ) (x : AdelicGLn.AdelicGL K n) {k : ℕ}
    (Y : Fin k → ArchMatrix K n) :
    diffSum ψ x Y = altSum k (fun Z => ψ (x * archExp Z)) Y 0 := by
  rw [altSum_eq_sum, diffSum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [zero_add, zsmul_eq_mul]

theorem commute_altPoint {Z : ArchMatrix K n} {k : ℕ} {Y : Fin k → ArchMatrix K n}
    (h : ∀ i, Commute Z (Y i)) (ε : Fin k → Bool) : Commute Z (altPoint Y ε) := by
  unfold altPoint
  refine Commute.sum_right _ _ _ fun i _ => ?_
  split_ifs
  · exact h i
  · exact Commute.zero_right Z

theorem diffSum_succ (ψ : AdelicGLn.AdelicGL K n → ℂ) (x : AdelicGLn.AdelicGL K n) {k : ℕ}
    (Y : Fin (k + 1) → ArchMatrix K n) (hY : ∀ i j, Commute (Y i) (Y j)) :
    diffSum ψ x Y = diffSum ψ (x * archExp (Y 0)) (Fin.tail Y) - diffSum ψ x (Fin.tail Y) := by
  rw [diffSum_eq_altSum, altSum_succ, altSum_eq_sum, diffSum, diffSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ε _ => ?_
  have hc : Commute (Y 0) (altPoint (Fin.tail Y) ε) :=
    commute_altPoint (fun i => hY 0 i.succ) ε
  rw [zero_add, zsmul_eq_mul, mul_sub, add_comm, archExp_add hc, mul_assoc]

theorem diffSum_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ψ : ι → AdelicGLn.AdelicGL K n → ℂ)
    (x : AdelicGLn.AdelicGL K n) {k : ℕ} (Y : Fin k → ArchMatrix K n) :
    diffSum (fun g => ∑ j ∈ s, c j * ψ j g) x Y = ∑ j ∈ s, c j * diffSum (ψ j) x Y := by
  simp only [diffSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ε _ => ?_
  ring

theorem hasDerivAt_diffSum (ψ : archSmooth K n) (x : AdelicGLn.AdelicGL K n) (Y₀ : ArchMatrix K n)
    {k : ℕ} (Y : Fin k → ArchMatrix K n) (hc : ∀ i, Commute Y₀ (Y i)) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => diffSum (ψ : AdelicGLn.AdelicGL K n → ℂ) (x * archExp (s • Y₀)) Y)
      (diffSum (uAction (UniversalEnvelopingAlgebra.ι ℝ (lieOf Y₀)) ψ : AdelicGLn.AdelicGL K n → ℂ)
        (x * archExp (s₀ • Y₀)) Y) s₀ := by
  have key : ∀ (P : ArchMatrix K n), Commute Y₀ P → ∀ s : ℝ,
      x * archExp (s • Y₀) * archExp P = x * archExp P * archExp (s • Y₀) := by
    intro P hP s
    rw [mul_assoc, mul_assoc, ← archExp_add (hP.smul_left s), ← archExp_add (hP.smul_left s).symm,
      add_comm]
  have := HasDerivAt.sum (u := Finset.univ) (x := s₀)
    (A := fun ε (s : ℝ) => (altSign ε : ℂ) * (ψ : AdelicGLn.AdelicGL K n → ℂ)
      (x * archExp (altPoint Y ε) * archExp (s • Y₀)))
    (A' := fun ε => (altSign ε : ℂ) *
      (uAction (UniversalEnvelopingAlgebra.ι ℝ (lieOf Y₀)) ψ : AdelicGLn.AdelicGL K n → ℂ)
        (x * archExp (altPoint Y ε) * archExp (s₀ • Y₀)))
    fun ε _ => (hasDerivAt_archExp ψ _ Y₀ s₀).const_mul _
  refine (this.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · rw [Finset.sum_apply]
    simp only [diffSum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [key _ (commute_altPoint hc ε)]
  · simp only [diffSum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [key _ (commute_altPoint hc ε)]

variable (K n) in

abbrev archBasis : Module.Basis (Fin (Module.finrank ℝ (ArchMatrix K n))) ℝ (ArchMatrix K n) :=
  Module.finBasis ℝ (ArchMatrix K n)

variable (K n) in

abbrev archDim : ℕ := Module.finrank ℝ (ArchMatrix K n)

def uJ : (k : ℕ) → (Fin k → Fin (archDim K n)) → UEnv K n
  | 0, _ => 1
  | k + 1, J => uJ k (Fin.tail J) * UniversalEnvelopingAlgebra.ι ℝ (lieOf (archBasis K n (J 0)))

theorem uAction_uJ_succ {k : ℕ} (J : Fin (k + 1) → Fin (archDim K n)) (ψ : archSmooth K n) :
    uAction (uJ (k + 1) J) ψ =
      uAction (uJ k (Fin.tail J)) (uAction (UniversalEnvelopingAlgebra.ι ℝ
        (lieOf (archBasis K n (J 0)))) ψ) := by
  rw [uJ, map_mul, Module.End.mul_apply]

theorem exists_abs_le_of_linear (f : ArchMatrix K n →ₗ[ℝ] ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C * ‖x‖ := by
  have hc : Continuous f := LinearMap.continuous_of_finiteDimensional f
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hc.continuousAt 1 one_pos
  refine ⟨2 / δ, by positivity, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  set c : ℝ := δ / (2 * ‖x‖)
  have hc0 : 0 < c := by positivity
  have h1 : dist (c • x) 0 < δ := by
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg hc0.le]
    have : c * ‖x‖ = δ / 2 := by simp only [c]; field_simp
    rw [this]; linarith
  have h2 := hδf h1
  rw [map_zero, dist_zero_right, map_smul, smul_eq_mul, Real.norm_eq_abs, abs_mul,
    abs_of_pos hc0] at h2
  have : |f x| < 1 / c := by rw [lt_div_iff₀ hc0]; linarith
  refine this.le.trans (le_of_eq ?_)
  simp only [c]; field_simp

theorem exists_abs_archBasis_repr_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (Y : ArchMatrix K n) (j : Fin (archDim K n)),
      |(archBasis K n).repr Y j| ≤ c * ‖Y‖ := by
  choose C hC0 hC using fun j => exists_abs_le_of_linear ((archBasis K n).coord j)
  refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ => hC0 j, fun Y j => ?_⟩
  refine (hC j Y).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_univ j)

theorem uAction_lieOf_apply (Y : ArchMatrix K n) (ψ : archSmooth K n) (g : AdelicGLn.AdelicGL K n) :
    (uAction (UniversalEnvelopingAlgebra.ι ℝ (lieOf Y)) ψ : AdelicGLn.AdelicGL K n → ℂ) g =
      ∑ j, ((archBasis K n).repr Y j : ℂ) *
        (uAction (UniversalEnvelopingAlgebra.ι ℝ (lieOf (archBasis K n j))) ψ :
          AdelicGLn.AdelicGL K n → ℂ) g := by
  conv_lhs => rw [← (archBasis K n).sum_repr Y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply,
    Complex.real_smul]

theorem norm_diffSum_le {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ (Y : ArchMatrix K n) (j : Fin (archDim K n)), |(archBasis K n).repr Y j| ≤ c * ‖Y‖) :
    ∀ (k : ℕ) (ψ : archSmooth K n) (x : AdelicGLn.AdelicGL K n) (Y : Fin k → ArchMatrix K n),
      (∀ i j, Commute (Y i) (Y j)) → ∀ B : ℝ, 0 ≤ B →
      (∀ (J : Fin k → Fin (archDim K n)) (t : Fin k → ℝ), (∀ i, t i ∈ Icc (0 : ℝ) 1) →
        ‖(uAction (uJ k J) ψ : AdelicGLn.AdelicGL K n → ℂ) (x * archExp (∑ i, t i • Y i))‖ ≤ B) →
      ‖diffSum (ψ : AdelicGLn.AdelicGL K n → ℂ) x Y‖ ≤ (archDim K n * c) ^ k * (∏ i, ‖Y i‖) * B
  | 0, ψ, x, Y, _, B, _, hB => by
    have h := hB Fin.elim0 Fin.elim0 fun i => i.elim0
    simp only [uJ, map_one, Module.End.one_apply, Finset.univ_eq_empty, Finset.sum_empty,
      archExp_zero, mul_one] at h
    simpa [diffSum, altSign, altPoint, archExp_zero] using h
  | k + 1, ψ, x, Y, hY, B, hB0, hB => by
    have hc' : ∀ i, Commute (Y 0) (Fin.tail Y i) := fun i => hY 0 i.succ
    have hY' : ∀ i j, Commute (Fin.tail Y i) (Fin.tail Y j) := fun i j => hY i.succ j.succ
    set d := archDim K n
    set G : ℝ → ℂ := fun s =>
      diffSum (ψ : AdelicGLn.AdelicGL K n → ℂ) (x * archExp (s • Y 0)) (Fin.tail Y) with hG
    set G' : ℝ → ℂ := fun s => diffSum (uAction (UniversalEnvelopingAlgebra.ι ℝ (lieOf (Y 0))) ψ :
      AdelicGLn.AdelicGL K n → ℂ) (x * archExp (s • Y 0)) (Fin.tail Y) with hG'
    set A := (d * c) ^ k * (∏ i, ‖Fin.tail Y i‖) * B with hA
    have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hc0) _)
      (Finset.prod_nonneg fun i _ => norm_nonneg _)) hB0
    have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt G (G' s) (Icc 0 1) s := fun s _ =>
      (hasDerivAt_diffSum ψ x (Y 0) (Fin.tail Y) hc' s).hasDerivWithinAt
    have hbound : ∀ s ∈ Ico (0 : ℝ) 1, ‖G' s‖ ≤ d * c * ‖Y 0‖ * A := by
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hs
      have e : G' s = ∑ j, ((archBasis K n).repr (Y 0) j : ℂ) *
          diffSum (uAction (UniversalEnvelopingAlgebra.ι ℝ (lieOf (archBasis K n j))) ψ :
            AdelicGLn.AdelicGL K n → ℂ) (x * archExp (s • Y 0)) (Fin.tail Y) := by
        rw [← diffSum_sum]
        simp only [hG']
        congr 1
        funext g
        exact uAction_lieOf_apply (Y 0) ψ g
      rw [e]
      have hIH : ∀ j, ‖diffSum (uAction (UniversalEnvelopingAlgebra.ι ℝ
          (lieOf (archBasis K n j))) ψ : AdelicGLn.AdelicGL K n → ℂ)
            (x * archExp (s • Y 0)) (Fin.tail Y)‖ ≤ A := by
        intro j
        refine norm_diffSum_le hc0 hc k _ _ (Fin.tail Y) hY' B hB0 fun J t ht => ?_
        have h := hB (Fin.cons j J) (Fin.cons s t) (fun i => Fin.cases hs' (fun i => ht i) i)
        rw [uAction_uJ_succ, Fin.tail_cons, Fin.cons_zero] at h
        have hsum : ∑ i, (Fin.cons s t : Fin (k + 1) → ℝ) i • Y i =
            s • Y 0 + ∑ i, t i • Fin.tail Y i := by
          rw [Fin.sum_univ_succ]; rfl
        have hcomm : Commute (s • Y 0) (∑ i, t i • Fin.tail Y i) :=
          Commute.sum_right _ _ _ fun i _ => ((hc' i).smul_left s).smul_right (t i)
        rw [hsum, archExp_add hcomm, ← mul_assoc] at h
        exact h
      calc ‖∑ j, ((archBasis K n).repr (Y 0) j : ℂ) *
            diffSum (uAction (UniversalEnvelopingAlgebra.ι ℝ (lieOf (archBasis K n j))) ψ :
              AdelicGLn.AdelicGL K n → ℂ) (x * archExp (s • Y 0)) (Fin.tail Y)‖
          ≤ ∑ j, |(archBasis K n).repr (Y 0) j| * A := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (hIH j) (abs_nonneg _)
        _ ≤ ∑ _j : Fin d, c * ‖Y 0‖ * A :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc (Y 0) j) hA0
        _ = d * c * ‖Y 0‖ * A := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1 ⟨zero_le_one, le_rfl⟩
    have hG1 : G 1 = diffSum (ψ : AdelicGLn.AdelicGL K n → ℂ) (x * archExp (Y 0)) (Fin.tail Y) := by
      simp only [hG, one_smul]
    have hG0 : G 0 = diffSum (ψ : AdelicGLn.AdelicGL K n → ℂ) x (Fin.tail Y) := by
      simp only [hG, zero_smul, archExp_zero, mul_one]
    rw [diffSum_succ _ x Y hY, ← hG1, ← hG0]
    refine hmv.trans (le_of_eq ?_)
    rw [hA, Fin.prod_univ_succ, pow_succ]
    simp only [Fin.tail]
    ring

def HasGrowth (φ : AdelicGLn.AdelicGL K n → ℂ) (N : ℕ) : Prop :=
  ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * height g ^ N

theorem HasGrowth.add {φ ψ : AdelicGLn.AdelicGL K n → ℂ} {N : ℕ} (hφ : HasGrowth φ N)
    (hψ : HasGrowth ψ N) : HasGrowth (φ + ψ) N := by
  obtain ⟨C₁, h₁⟩ := hφ
  obtain ⟨C₂, h₂⟩ := hψ
  exact ⟨C₁ + C₂, fun g => (norm_add_le _ _).trans (by rw [add_mul]; exact add_le_add (h₁ g) (h₂ g))⟩

theorem HasGrowth.of_eq_integral [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)]
    {φ ψ : AdelicGLn.AdelicGL K n → ℂ} {N : ℕ}
    (hφ : HasGrowth φ N) (μ : Measure (archGroup K n)) [μ.IsHaarMeasure]
    {D : archGroup K n → ℂ} (hD : Continuous D) (hDc : HasCompactSupport D)
    (hψ : ∀ g, ψ g = ∫ y, φ (g * infEmb K n y) * D y ∂μ) : HasGrowth ψ N := by
  obtain ⟨C, hC⟩ := hφ
  obtain ⟨M, hM⟩ := exists_height_infEmb_le (K := K) (n := n) hDc.isCompact
  set M' := max M 1
  have hc0 : 0 ≤ heightConst K n := le_trans zero_le_one one_le_heightConst
  refine ⟨|C| * (heightConst K n * M') ^ N * ∫ y, ‖D y‖ ∂μ, fun g => ?_⟩
  rw [hψ]
  have hb : ∀ y, ‖φ (g * infEmb K n y) * D y‖ ≤
      |C| * (heightConst K n * M') ^ N * height g ^ N * ‖D y‖ := by
    intro y
    by_cases hy : y ∈ tsupport D
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have hhg := height_pos g
      calc ‖φ (g * infEmb K n y)‖ ≤ C * height (g * infEmb K n y) ^ N := hC _
        _ ≤ |C| * height (g * infEmb K n y) ^ N :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (height_pos _).le _)
        _ ≤ |C| * (heightConst K n * height g * M') ^ N := by
            refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le ?_ _) (abs_nonneg _)
            calc height (g * infEmb K n y)
                ≤ heightConst K n * height g * height (infEmb K n y) := height_mul_le _ _
              _ ≤ heightConst K n * height g * M' :=
                  mul_le_mul_of_nonneg_left ((hM y hy).trans (le_max_left _ _))
                    (mul_nonneg hc0 hhg.le)
        _ = |C| * (heightConst K n * M') ^ N * height g ^ N := by ring
    · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, norm_zero, mul_zero]
  have hint : Integrable (fun y => ‖D y‖) μ := hD.norm.integrable_of_hasCompactSupport hDc.norm
  calc ‖∫ y, φ (g * infEmb K n y) * D y ∂μ‖
      ≤ ∫ y, |C| * (heightConst K n * M') ^ N * height g ^ N * ‖D y‖ ∂μ :=
        norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall hb)
    _ = |C| * (heightConst K n * M') ^ N * (∫ y, ‖D y‖ ∂μ) * height g ^ N := by
        rw [integral_const_mul]; ring

theorem hasGrowth_uAction {N : ℕ} (u : UEnv K n) :
    ∀ {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsSmoothKZ φ), HasGrowth φ N →
      HasGrowth (uAction u ⟨φ, hφ.isSmooth.1⟩ : AdelicGLn.AdelicGL K n → ℂ) N := by
  induction u using UEnv.induction with
  | halg r =>
    intro φ hφ hN
    rw [coe_uAction_algebraMap]
    obtain ⟨C, hC⟩ := hN
    refine ⟨|r| * C, fun g => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g) (abs_nonneg r)
  | hι X =>
    intro φ hφ hN
    let _ : MeasurableSpace (archGroup K n) := borel _
    have _ : BorelSpace (archGroup K n) := ⟨rfl⟩
    obtain ⟨D, hD, hDc, hrep⟩ := exists_integral_uAction_ι hφ Measure.haar X
    exact hN.of_eq_integral Measure.haar hD hDc hrep
  | hmul a b ha hb =>
    intro φ hφ hN
    rw [coe_uAction_mul]
    exact ha (hφ.uAction b) (hb hφ hN)
  | hadd a b ha hb =>
    intro φ hφ hN
    rw [map_add, LinearMap.add_apply, Submodule.coe_add]
    exact (ha hφ hN).add (hb hφ hN)

theorem exists_norm_diffSum_le {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsAutomorphicForm φ) :
    ∃ N : ℕ, ∀ (k : ℕ) (T : ℝ), ∃ C : ℝ, ∀ (x : AdelicGLn.AdelicGL K n)
      (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ T) →
      ‖diffSum φ x Y‖ ≤ C * (∏ i, ‖Y i‖) * height x ^ N := by
  obtain ⟨C₀, N, hC₀⟩ := hφ.hasModerateGrowth
  refine ⟨N, fun k T => ?_⟩
  obtain ⟨c, hc0, hc⟩ := exists_abs_archBasis_repr_le (K := K) (n := n)
  have hgrowth : ∀ J : Fin k → Fin (archDim K n),
      HasGrowth (uAction (uJ k J) ⟨φ, hφ.isSmooth.1⟩ : AdelicGLn.AdelicGL K n → ℂ) N :=
    fun J => hasGrowth_uAction (uJ k J) hφ.isSmoothKZ ⟨C₀, hC₀⟩
  choose CJ hCJ using hgrowth
  set T' := (k : ℝ) * max T 0
  set S : Set (archGroup K n) :=
    (fun Z : ArchMatrix K n => (isExpLieAlgebra K n).expG ⟨Z, Submodule.mem_top⟩) ''
      Metric.closedBall 0 T'
  have hS : IsCompact S := (isCompact_closedBall _ _).image
    ((isExpLieAlgebra K n).continuous_expG.comp (continuous_id.subtype_mk _))
  obtain ⟨Mh, hMh⟩ := exists_height_infEmb_le (K := K) (n := n) hS
  set Mh' := max Mh 1
  set Cs := ∑ J, |CJ J|
  have hCs : 0 ≤ Cs := Finset.sum_nonneg fun J _ => abs_nonneg _
  have hc0' : 0 ≤ heightConst K n := le_trans zero_le_one one_le_heightConst
  refine ⟨(archDim K n * c) ^ k * (Cs * (heightConst K n * Mh') ^ N), fun x Y hYY hYT => ?_⟩
  have hcomm : ∀ i j, Commute (Y i) (Y j) := fun i j => (hYY i j).trans (hYY j i).symm
  have hB0 : 0 ≤ Cs * (heightConst K n * Mh') ^ N * height x ^ N := by
    have := height_pos x
    have : 0 ≤ Mh' := le_trans zero_le_one (le_max_right _ _)
    positivity
  have h := norm_diffSum_le hc0 hc k ⟨φ, hφ.isSmooth.1⟩ x Y hcomm _ hB0 fun J t ht => by
    have hZ : ‖∑ i, t i • Y i‖ ≤ T' := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i, ‖t i • Y i‖ ≤ ∑ _i : Fin k, max T 0 := Finset.sum_le_sum fun i _ => by
            rw [norm_smul, Real.norm_of_nonneg (ht i).1]
            calc t i * ‖Y i‖ ≤ 1 * max T 0 :=
                  mul_le_mul (ht i).2 ((hYT i).trans (le_max_left _ _)) (norm_nonneg _) zero_le_one
              _ = max T 0 := one_mul _
        _ = T' := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hmem : (isExpLieAlgebra K n).expG ⟨∑ i, t i • Y i, Submodule.mem_top⟩ ∈ S :=
      ⟨_, mem_closedBall_zero_iff.2 hZ, rfl⟩
    have hh : height (x * archExp (∑ i, t i • Y i)) ≤ heightConst K n * height x * Mh' :=
      (height_mul_le _ _).trans (mul_le_mul_of_nonneg_left ((hMh _ hmem).trans (le_max_left _ _))
        (mul_nonneg hc0' (height_pos x).le))
    calc ‖(uAction (uJ k J) ⟨φ, hφ.isSmooth.1⟩ : AdelicGLn.AdelicGL K n → ℂ)
          (x * archExp (∑ i, t i • Y i))‖
        ≤ CJ J * height (x * archExp (∑ i, t i • Y i)) ^ N := hCJ J _
      _ ≤ |CJ J| * (heightConst K n * height x * Mh') ^ N :=
          mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (height_pos _).le hh _)
            (pow_nonneg (height_pos _).le _) (abs_nonneg _)
      _ ≤ Cs * (heightConst K n * height x * Mh') ^ N :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun J => |CJ J|)
            (fun J _ => abs_nonneg _) (Finset.mem_univ J)) (by
              have := height_pos x
              have : 0 ≤ Mh' := le_trans zero_le_one (le_max_right _ _)
              positivity)
      _ = Cs * (heightConst K n * Mh') ^ N * height x ^ N := by ring
  refine h.trans (le_of_eq ?_)
  ring

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end

section
open NumberField IsDedekindDomain Topology Filter Set MeasureTheory
open scoped NumberField.AdeleRing Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open AutomorphicForm

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem exists_height_le_of_isCompact {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω) :
    ∃ M : ℝ, ∀ b ∈ ω, height b ≤ M := by
  obtain ⟨C₀, hC₀c, hC₀⟩ := exists_compact_mem_nhds (1 : archGroup K n)
  obtain ⟨MA, hMA⟩ := exists_height_infEmb_le (K := K) (n := n) hC₀c
  set W : Set (AdelicGLn.AdelicGL K n) :=
    (fun g => archPart g) ⁻¹' C₀ ∩
      (fun g => finPart g) ⁻¹' (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n))
  have hcA : Continuous fun g : AdelicGLn.AdelicGL K n => archPart g :=
    (archEquiv K n).continuous.comp (continuous_fst.comp (AdelicGLn.prodEquiv K n).continuous)
  have hcF : Continuous fun g : AdelicGLn.AdelicGL K n => finPart g :=
    continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous
  have hW : W ∈ 𝓝 (1 : AdelicGLn.AdelicGL K n) := by
    refine inter_mem (hcA.continuousAt.preimage_mem_nhds ?_) (hcF.continuousAt.preimage_mem_nhds ?_)
    · rw [show archPart (1 : AdelicGLn.AdelicGL K n) = 1 by simp [archPart]]
      exact hC₀
    · have : finPart (1 : AdelicGLn.AdelicGL K n) = 1 := by simp [finPart]
      rw [this]
      exact (AdelicGLn.isOpen_integralFiniteGL K n).mem_nhds (one_mem _)
  set c := heightConst K n
  have hc0 : 0 ≤ c := le_trans zero_le_one one_le_heightConst
  have hWb : ∀ w ∈ W, height w ≤ c * max MA 1 := by
    intro w hw
    rw [← infEmb_archPart_mul_finEmb_finPart w]
    refine (height_mul_le _ _).trans ?_
    rw [height_eq_one_of_mem_maxCompact (finEmb_mem_maxCompact hw.2), mul_one]
    exact mul_le_mul_of_nonneg_left ((hMA _ hw.1).trans (le_max_left _ _)) hc0
  obtain ⟨s, -, hs⟩ := hω.elim_nhds_subcover (fun g => (fun y => g * y) '' W) fun g _ => by
    have := (Homeomorph.mulLeft g).isOpenMap.image_mem_nhds hW
    simpa using this
  refine ⟨∑ g ∈ s, c * height g * (c * max MA 1), fun b hb => ?_⟩
  obtain ⟨g, hg, hbg⟩ := mem_iUnion₂.1 (hs hb)
  obtain ⟨w, hw, rfl⟩ := hbg
  have hterm : height (g * w) ≤ c * height g * (c * max MA 1) :=
    (height_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hWb w hw)
      (mul_nonneg hc0 (height_pos g).le))
  refine hterm.trans (Finset.single_le_sum (f := fun g => c * height g * (c * max MA 1))
    (fun g _ => ?_) hg)
  have := height_pos g
  have : 0 ≤ max MA 1 := le_trans zero_le_one (le_max_right _ _)
  positivity

theorem mult_le_two (w : InfinitePlace K) : w.mult ≤ 2 := by
  unfold InfinitePlace.mult
  split_ifs <;> norm_num

theorem height_diagUnits_posIdele_le {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {L : ℝ} (hL1 : 1 ≤ L)
    (hL : ∀ i, ρ i ≤ L ∧ (ρ i)⁻¹ ≤ L) :
    height (Reduction.diagUnits n fun i => Reduction.posIdele (K := K) (ρ i) (hρ i)) ≤
      L ^ (2 * Fintype.card (InfinitePlace K)) := by
  set a := Reduction.diagUnits n fun i => Reduction.posIdele (K := K) (ρ i) (hρ i)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K), Reduction.finAt v a = 1 := by
    intro v
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [Reduction.finAt_apply, Reduction.coe_diagUnits, Matrix.diagonal_apply, Units.val_one, Matrix.one_apply]
    split_ifs with h
    · subst h
      exact Reduction.posIdele_finite (K := K) (ρ i) (hρ i) v
    · rfl
  have hinf : ∀ w : InfinitePlace K, locHeight (Reduction.infAt w a) ≤ L := by
    intro w
    rw [Reduction.infAt_diagUnits_posIdele]
    refine locHeight_le hL1 (fun i j => ?_) (fun i j => ?_)
    · rw [Reduction.coe_diagUnits, Matrix.diagonal_apply]
      split_ifs with h
      · subst h
        rw [Reduction.norm_posRealToUnits w (hρ i)]
        exact (hL i).1
      · simp only [norm_zero]; linarith
    · rw [← map_inv, Reduction.coe_diagUnits, Matrix.diagonal_apply]
      split_ifs with h
      · subst h
        rw [Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv, Reduction.norm_posRealToUnits w (hρ i)]
        exact (hL i).2
      · simp only [norm_zero]; linarith
  unfold height
  rw [finprod_eq_one_of_forall_eq_one (fun v => by rw [hfin v, locHeight_one]), mul_one]
  calc ∏ w : InfinitePlace K, locHeight (Reduction.infAt w a) ^ w.mult
      ≤ ∏ _w : InfinitePlace K, L ^ 2 :=
        Finset.prod_le_prod (fun w _ => pow_nonneg (locHeight_pos _).le _) fun w _ =>
          (pow_le_pow_left₀ (locHeight_pos _).le (hinf w) _).trans
            (pow_le_pow_right₀ hL1 (mult_le_two w))
    _ = L ^ (2 * Fintype.card (InfinitePlace K)) := by
        rw [Finset.prod_const, Finset.card_univ, ← pow_mul]

theorem detModule_diagUnits_posIdele {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) :
    (Reduction.detModule K n (Reduction.diagUnits n fun i =>
      Reduction.posIdele (K := K) (ρ i) (hρ i)) : ℝ) = (∏ i, ρ i) ^ Module.finrank ℚ K := by
  rw [Reduction.detModule, MonoidHom.comp_apply, Reduction.det_diagUnits, map_prod,
    Reduction.coe_finset_prod_pos, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => Reduction.ideleModule_posIdele (ρ i) (hρ i)

theorem exists_height_le_normOne {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      ∀ kk ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)),
      ∀ x : AdelicGLn.AdelicGL K n, x ∈ Reduction.normOneGL K n →
      x = b * Reduction.diagUnits n (fun i => Reduction.posIdele (K := K) (ρ i) (hρ i)) * kk →
      ∀ A : ℝ, 1 ≤ A → (∀ i j : Fin n, ρ i / ρ j ≤ A) →
      height x ≤ C * A ^ (2 * Fintype.card (InfinitePlace K)) := by
  obtain ⟨Mb, hMb⟩ := exists_height_le_of_isCompact hω
  have hdc : Continuous fun g : AdelicGLn.AdelicGL K n => (Reduction.detModule K n g : ℝ) :=
    continuous_subtype_val.comp Reduction.continuous_detModule
  obtain ⟨M₁, hM₁⟩ := hω.exists_bound_of_continuousOn hdc.continuousOn
  obtain ⟨M₂, hM₂⟩ := hω.exists_bound_of_continuousOn
    (hdc.inv₀ fun g => (Reduction.detModule K n g).2.ne').continuousOn
  set e := 2 * Fintype.card (InfinitePlace K)
  set c₀ := max 1 (max M₁ M₂)
  have hc₀1 : 1 ≤ c₀ := le_max_left _ _
  set c := heightConst K n
  have hc0 : 0 ≤ c := le_trans zero_le_one one_le_heightConst
  have hMb1 : 0 ≤ max Mb 1 := le_trans zero_le_one (le_max_right _ _)
  refine ⟨c * (c * max Mb 1 * c₀ ^ e), by positivity, ?_⟩
  intro b hb ρ hρ kk hkk x hx hxe A hA1 hA
  set a := Reduction.diagUnits n fun i => Reduction.posIdele (K := K) (ρ i) (hρ i) with ha
  set d := Module.finrank ℚ K
  have hd : d ≠ 0 := Module.finrank_pos.ne'
  set P := ∏ i, ρ i
  have hP : 0 < P := Finset.prod_pos fun i _ => hρ i
  have hdet : (Reduction.detModule K n b : ℝ) * P ^ d = 1 := by
    have h1 := Reduction.mem_normOneGL_iff_detModule.1 hx
    have hk := Reduction.mem_normOneGL_iff_detModule.1 (Reduction.maxCompact_le_normOneGL hkk)
    rw [hxe, map_mul, map_mul, hk, mul_one] at h1
    have h2 := congrArg Subtype.val h1
    rw [Positive.val_mul, detModule_diagUnits_posIdele, Positive.val_one] at h2
    exact h2
  have hb0 : 0 < (Reduction.detModule K n b : ℝ) := (Reduction.detModule K n b).2
  have hPd : P ^ d ≤ c₀ := by
    have h1 := hM₂ b hb
    have h2 : P ^ d = (Reduction.detModule K n b : ℝ)⁻¹ := eq_inv_of_mul_eq_one_right hdet
    rw [h2]
    refine le_trans (le_abs_self _) ?_
    refine le_trans ?_ (le_max_right _ _)
    exact (by simpa [Real.norm_eq_abs] using h1 : |(Reduction.detModule K n b : ℝ)⁻¹| ≤ M₂).trans
      (le_max_right _ _)
  have hPd' : (P⁻¹) ^ d ≤ c₀ := by
    have h1 := hM₁ b hb
    have h2 : (P⁻¹) ^ d = (Reduction.detModule K n b : ℝ) := by
      rw [inv_pow, eq_inv_of_mul_eq_one_right hdet, inv_inv]
    rw [h2]
    refine le_trans (le_abs_self _) ?_
    refine le_trans ?_ (le_max_right _ _)
    exact (by simpa [Real.norm_eq_abs] using h1 : |(Reduction.detModule K n b : ℝ)| ≤ M₁).trans
      (le_max_left _ _)
  have hPc : P ≤ c₀ := by
    rcases le_or_gt P 1 with h | h
    · exact h.trans hc₀1
    · exact (le_self_pow₀ h.le hd).trans hPd
  have hPc' : P⁻¹ ≤ c₀ := by
    rcases le_or_gt P⁻¹ 1 with h | h
    · exact h.trans hc₀1
    · exact (le_self_pow₀ h.le hd).trans hPd'
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hbound : ∀ i, ρ i ≤ c₀ * A ∧ (ρ i)⁻¹ ≤ c₀ * A := by
    intro i
    have hn : n ≠ 0 := (Fin.pos i).ne'
    have hpow : c₀ * A ^ n ≤ (c₀ * A) ^ n := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ hc₀1 hn) (pow_nonneg hA0 _)
    have hprodA : ∀ f : Fin n → ℝ, (∀ j, 0 ≤ f j) → (∀ j, f j ≤ A) → ∏ j, f j ≤ A ^ n := by
      intro f hf0 hfA
      calc ∏ j, f j ≤ ∏ _j : Fin n, A := Finset.prod_le_prod (fun j _ => hf0 j) fun j _ => hfA j
        _ = A ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    constructor
    · have e1 : ρ i ^ n = P * ∏ j, (ρ i / ρ j) := by
        have hPe : ∏ j, ρ j = P := rfl
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hPe]
        field_simp
      have h1 : ρ i ^ n ≤ (c₀ * A) ^ n := by
        rw [e1]
        refine le_trans ?_ hpow
        exact mul_le_mul hPc (hprodA _ (fun j => (div_pos (hρ i) (hρ j)).le) fun j => hA i j)
          (Finset.prod_nonneg fun j _ => (div_pos (hρ i) (hρ j)).le) (by linarith)
      exact le_of_pow_le_pow_left₀ hn (by positivity) h1
    · have e1 : (ρ i)⁻¹ ^ n = P⁻¹ * ∏ j, (ρ j / ρ i) := by
        have hPe : ∏ j, ρ j = P := rfl
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hPe,
          ← mul_div_assoc, inv_mul_cancel₀ hP.ne', one_div, inv_pow]
      have h1 : (ρ i)⁻¹ ^ n ≤ (c₀ * A) ^ n := by
        rw [e1]
        refine le_trans ?_ hpow
        exact mul_le_mul hPc' (hprodA _ (fun j => (div_pos (hρ j) (hρ i)).le) fun j => hA j i)
          (Finset.prod_nonneg fun j _ => (div_pos (hρ j) (hρ i)).le) (by linarith)
      exact le_of_pow_le_pow_left₀ hn (by positivity) h1
  have hL1 : 1 ≤ c₀ * A := one_le_mul_of_one_le_of_one_le hc₀1 hA1
  have hha := height_diagUnits_posIdele_le (K := K) hρ hL1 hbound
  rw [← ha] at hha
  rw [hxe]
  calc height (b * a * kk) ≤ c * height (b * a) * height kk := height_mul_le _ _
    _ = c * height (b * a) := by rw [height_eq_one_of_mem_maxCompact hkk, mul_one]
    _ ≤ c * (c * height b * height a) :=
        mul_le_mul_of_nonneg_left (height_mul_le _ _) hc0
    _ ≤ c * (c * max Mb 1 * (c₀ * A) ^ e) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left
          ((hMb b hb).trans (le_max_left _ _)) hc0) hha (height_pos _).le
          (mul_nonneg hc0 hMb1)) hc0
    _ = c * (c * max Mb 1 * c₀ ^ e) * A ^ e := by rw [mul_pow]; ring

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end
