import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsCuspHom
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantActionSmoothVectorsScalar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousRepresentativeProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevIteratedOneParameterSubgroupsWords
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUnique
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HeightBoundByInfinityNorm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativeAlongLieAlgebraPreservesSmoothSpace

section
section
open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

namespace GlobalTheory.SobolevBound

private lemma exists_re_trace_orthonormal_gLie {n : ℕ} (ε : Fin n → Bool) :
    ∃ E : Fin (n ^ 2) → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε,
      ∀ i j, (((E i : Matrix (Fin n) (Fin n) ℂ) * (E j : Matrix (Fin n) (Fin n) ℂ)ᴴ).trace).re =
        if i = j then 1 else 0 := by

  classical
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJJ' : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hmem : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      X ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε ↔ Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := fun X => Iff.rfl

  have hA : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      Z - Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε := by
    intro Z
    rw [hmem]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hJh, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJJ, Matrix.mul_one, hJJ']
    abel
  have hB : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      Complex.I • (Z + Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε := by
    intro Z
    rw [hmem]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJh, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hJJ,
      Matrix.mul_one, hJJ', smul_mul_assoc, mul_smul_comm, Complex.star_def, Complex.conj_I, neg_smul,
      smul_add, neg_mul]
    abel
  let L : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε × GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun p => (p.1 : Matrix (Fin n) (Fin n) ℂ) + Complex.I • (p.2 : Matrix (Fin n) (Fin n) ℂ)
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
        abel
      map_smul' := fun r p => by
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, smul_add]
        rw [smul_comm r Complex.I] }
  have hsurj : Function.Surjective L := by
    intro Z
    refine ⟨(⟨(2⁻¹ : ℝ) • (Z - Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε),
      (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε).smul_mem _ (hA Z)⟩,
      ⟨(-2⁻¹ : ℝ) • (Complex.I • (Z + Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε)),
      (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε).smul_mem _ (hB Z)⟩), ?_⟩
    change (2⁻¹ : ℝ) • (Z - Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε) +
      Complex.I • ((-2⁻¹ : ℝ) • (Complex.I • (Z + Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε))) = Z
    generalize Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε = W
    ext a b
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    linear_combination (-(1 : ℂ) / 2 * (Z a b + W a b)) * Complex.I_sq
  have hfin : n ^ 2 ≤ Module.finrank ℝ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε) := by
    have h1 := LinearMap.finrank_le_finrank_of_surjective hsurj
    rw [Module.finrank_prod, Module.finrank_matrix, Fintype.card_fin, Complex.finrank_real_complex] at h1
    nlinarith [h1]

  let Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin n × Bool) :=
    { toFun := fun X => WithLp.toLp 2 (fun q => if q.2.2 then (X q.1 q.2.1).re else (X q.1 q.2.1).im)
      map_add' := fun X Y => by
        ext q
        by_cases h : q.2.2 <;> simp [h]
      map_smul' := fun r X => by
        ext q
        by_cases h : q.2.2 <;> simp [h] }
  have hΦapp : ∀ X q, (Φ X) q = if q.2.2 then (X q.1 q.2.1).re else (X q.1 q.2.1).im := fun _ _ => rfl
  have hΦ : ∀ X Y, inner ℝ (Φ X) (Φ Y) = ((X * Yᴴ).trace).re := by
    intro X Y
    rw [PiLp.inner_apply]
    simp only [hΦapp, Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
      Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hΦinj : Function.Injective Φ := by
    intro X Y h
    ext a b
    apply Complex.ext
    · have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin n × Fin n × Bool) => v (a, b, true)) h
      simpa [hΦapp] using h1
    · have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin n × Fin n × Bool) => v (a, b, false)) h
      simpa [hΦapp] using h1
  let Ψ := Φ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε).subtype
  have hΨ : Function.Injective Ψ := by
    intro x y h
    apply Subtype.ext
    apply hΦinj
    simpa [Ψ] using h
  have hS : n ^ 2 ≤ Module.finrank ℝ (LinearMap.range Ψ) := by
    rw [LinearMap.finrank_range_of_inj hΨ]
    exact hfin
  let b := stdOrthonormalBasis ℝ (LinearMap.range Ψ)
  have hbo : Orthonormal ℝ (fun i => ((b i : LinearMap.range Ψ) : EuclideanSpace ℝ (Fin n × Fin n × Bool))) :=
    b.orthonormal.comp_linearIsometry (LinearMap.range Ψ).subtypeₗᵢ
  have hpre : ∀ i, ∃ X : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε, Φ (X : Matrix (Fin n) (Fin n) ℂ) = b i := by
    intro i
    obtain ⟨X, hX⟩ := LinearMap.mem_range.1 (b i).2
    exact ⟨X, by simpa [Ψ] using hX⟩
  choose X hX using hpre
  refine ⟨fun j => X (Fin.castLE hS j), fun i j => ?_⟩
  dsimp only
  rw [← hΦ, hX, hX]
  have h2 := orthonormal_iff_ite.1 hbo (Fin.castLE hS i) (Fin.castLE hS j)
  rw [h2]
  simp

theorem derivative_closed_class_bound : ∀ (B : RowsAut), 1 ≤ B.I.n → 1 ≤ B.g → ∃ m : ℕ, ∀ W : Set (B.I.GA → ℂ), (∀ f ∈ W, (∃ F, GlobalTheory.Dec.IsContRep B F f) ∧ (∀ k ∈ B.I.Kg B.g, ∀ y, f (y * (1, k)) = f y) ∧ ∀ (v : InfinitePlace B.I.F) (E : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (B.I.ε v)), ∃ f' ∈ W, ∀ y, HasDerivAt (fun t : ℝ => f (y * GlobalTheory.SobolevBound.onePar B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace B v E) t)) (f' y) 0) → ∀ f ∈ W, ∃ C : ℝ, ∀ y, ‖f y‖ ≤ C * (GlobalTheory.Count.tau1 B.I y)⁻¹ ^ m := by
  intro B hn hg
  classical
  refine ⟨2 * (B.I.n ^ 2 * B.I.f), ?_⟩
  intro W hW f hf

  choose E hE using fun v : InfinitePlace B.I.F => exists_re_trace_orthonormal_gLie (B.I.ε v)
  choose c hc using fun v : InfinitePlace B.I.F => GlobalTheory.GaugeConst.gauge_exists_pos_unique B.I.n (B.I.ε v)
  let e : Fin (Fintype.card (InfinitePlace B.I.F)) ≃ InfinitePlace B.I.F :=
    (Fintype.equivFin (InfinitePlace B.I.F)).symm

  have hnr : (1 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < B.I.n := by linarith
  have hp5 : (0 : ℝ) < (B.I.n : ℝ) ^ 5 := pow_pos hn0 5
  have h35 : (B.I.n : ℝ) ^ 3 ≤ (B.I.n : ℝ) ^ 5 := pow_le_pow_right₀ hnr (by norm_num)
  have hden : (0 : ℝ) < 12 * (B.I.n : ℝ) ^ 5 := by linarith
  have hs : (0 : ℝ) < 1 / (12 * (B.I.n : ℝ) ^ 5) := div_pos one_pos hden
  have h3 : 12 * (B.I.n : ℝ) ^ 3 * (1 / (12 * (B.I.n : ℝ) ^ 5)) ≤ 1 := by
    rw [mul_one_div, div_le_one hden]
    linarith
  have h5 : 8 * (B.I.n : ℝ) ^ 5 * (1 / (12 * (B.I.n : ℝ) ^ 5)) ≤ 1 := by
    rw [mul_one_div, div_le_one hden]
    linarith
  obtain ⟨C0, hC0, hsob⟩ := GlobalTheory.sobolev_iterated_one_parameter_subgroups_words B.I.GA
    (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)
    (fun l => onePar B (atPlace B (e l.divNat) (E _ l.modNat))) (1 / (12 * (B.I.n : ℝ) ^ 5)) hs
    (fun l => onePar_spec B _)

  have hder : ∀ g ∈ W, ∀ l : Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ∃ g' ∈ W, ∀ y,
      HasDerivAt (fun t : ℝ => g (y * onePar B (atPlace B (e l.divNat) (E _ l.modNat)) t)) (g' y) 0 :=
    fun g hgW l => (hW g hgW).2.2 (e l.divNat) (E _ l.modNat)
  choose! D hDW hD using hder
  let F : List (Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)) → B.I.GA → ℂ :=
    fun l => l.foldr (fun i g => D g i) f
  have hFW : ∀ l, F l ∈ W := by
    intro l
    induction l with
    | nil => exact hf
    | cons i l ih => exact hDW _ ih i
  have hrep : ∀ l, ∃ Fv, GlobalTheory.Dec.IsContRep B Fv (F l) := fun l => (hW (F l) (hFW l)).1
  choose Fv hFv using hrep

  set Mx : ℝ := ∑ k ∈ Finset.range ((Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) + 1), ∑ w : Fin k → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ‖Fv (List.ofFn w)‖ ^ 2 with hMx
  have hMx0 : 0 ≤ Mx := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hle : ∀ l : List (Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)), l.length ≤ (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) → ‖Fv l‖ ^ 2 ≤ Mx := by
    intro l hl
    calc ‖Fv l‖ ^ 2 = ‖Fv (List.ofFn l.get)‖ ^ 2 := by rw [List.ofFn_get]
      _ ≤ ∑ w : Fin l.length → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ‖Fv (List.ofFn w)‖ ^ 2 :=
          Finset.single_le_sum (f := fun w : Fin l.length → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) => ‖Fv (List.ofFn w)‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
      _ ≤ Mx :=
          Finset.single_le_sum (f := fun k => ∑ w : Fin k → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ‖Fv (List.ofFn w)‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
            (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
  have hP : 0 ≤ ∏ v, c v := Finset.prod_nonneg fun v _ => (hc v).1.le
  set K : ℝ := Real.exp B.I.f * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal with hK
  have hK0 : 0 ≤ K := div_nonneg (mul_nonneg (Real.exp_pos _).le hP) ENNReal.toReal_nonneg
  set a : ℝ := 4 * Real.sqrt B.I.n with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  set p := 2 * (B.I.n ^ 2 * B.I.f) with hp
  refine ⟨Real.sqrt (C0 * K * Mx * (1 + a) ^ p), fun y => ?_⟩
  have hτ : 0 < tau1 B.I y := GlobalTheory.TauLipschitz.trunc_pos B.I hn y
  have hτ1 : tau1 B.I y ≤ 1 := by
    have : tau1 B.I y ≤ 1 / 2 := by
      unfold GlobalTheory.Count.tau1
      exact min_le_left _ _
    linarith
  have hu0 : 0 < (tau1 B.I y)⁻¹ := inv_pos.2 hτ
  have hu1 : 1 ≤ (tau1 B.I y)⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_right hτ1 hu0.le
    rw [mul_inv_cancel₀ hτ.ne', one_mul] at h1
    exact h1
  have hu2 : 1 ≤ ((tau1 B.I y)⁻¹) ^ 2 := by nlinarith
  have hfrac : a / tau1 B.I y ^ 2 = a * ((tau1 B.I y)⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
  have hbase : 1 + a / tau1 B.I y ^ 2 ≤ (1 + a) * ((tau1 B.I y)⁻¹) ^ 2 := by
    rw [hfrac]
    nlinarith
  have hX1 : 0 ≤ 1 + a / tau1 B.I y ^ 2 := by
    have := div_nonneg ha0 (sq_nonneg (tau1 B.I y))
    linarith
  have hpow : (1 + a / tau1 B.I y ^ 2) ^ p ≤ (1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2 := by
    calc (1 + a / tau1 B.I y ^ 2) ^ p ≤ ((1 + a) * ((tau1 B.I y)⁻¹) ^ 2) ^ p :=
          pow_le_pow_left₀ hX1 hbase p
      _ = (1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2 := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 p]

  have hcube : ∀ l : List (Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)), l.length ≤ (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) →
      ∫ t in Set.pi Set.univ (fun _ : Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) => Set.Icc (0 : ℝ) (1 / (12 * (B.I.n : ℝ) ^ 5))),
        ‖F l (y * (List.ofFn fun i => onePar B (atPlace B (e i.divNat) (E _ i.modNat)) (t i)).prod)‖ ^ 2 ≤
        K * (1 + a / tau1 B.I y ^ 2) ^ p * Mx := by
    intro l hl
    have h1 := cube_bound B c (1 / (12 * (B.I.n : ℝ) ^ 5)) e E hn hg (fun v => (hc v).2.1) hE hs h3 h5
      (Fv l) (F l) (hFv l) (hW (F l) (hFW l)).2.1 y
    have h2 : Real.exp B.I.f * (1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) *
        (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal = K * (1 + a / tau1 B.I y ^ 2) ^ p := by
      rw [hK, ha, hp]
      ring
    rw [h2] at h1
    refine h1.trans ?_
    have hX0 : 0 ≤ K * (1 + a / tau1 B.I y ^ 2) ^ p := mul_nonneg hK0 (pow_nonneg hX1 _)
    exact mul_le_mul_of_nonneg_left (hle l hl) hX0
  have hmain := hsob F (fun l => (hFv l).1) (fun l i x => hD (F l) (hFW l) i x) y
    (K * (1 + a / tau1 B.I y ^ 2) ^ p * Mx) hcube
  have hsq : ‖f y‖ ^ 2 ≤ (Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * ((tau1 B.I y)⁻¹) ^ p) ^ 2 := by
    have hA : 0 ≤ C0 * K * Mx * (1 + a) ^ p :=
      mul_nonneg (mul_nonneg (mul_nonneg hC0 hK0) hMx0) (pow_nonneg (by linarith) _)
    rw [mul_pow, Real.sq_sqrt hA]
    have hQ : 0 ≤ C0 * K * Mx := mul_nonneg (mul_nonneg hC0 hK0) hMx0
    calc ‖f y‖ ^ 2 ≤ C0 * (K * (1 + a / tau1 B.I y ^ 2) ^ p * Mx) := hmain
      _ = (C0 * K * Mx) * (1 + a / tau1 B.I y ^ 2) ^ p := by ring
      _ ≤ (C0 * K * Mx) * ((1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2) :=
          mul_le_mul_of_nonneg_left hpow hQ
      _ = C0 * K * Mx * (1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2 := by ring
  have hnn : 0 ≤ Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * ((tau1 B.I y)⁻¹) ^ p :=
    mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hu0.le _)
  calc ‖f y‖ = Real.sqrt (‖f y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * ((tau1 B.I y)⁻¹) ^ p) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * (tau1 B.I y)⁻¹ ^ p := Real.sqrt_sq hnn

end GlobalTheory.SobolevBound
end

open MeasureTheory NumberField Matrix Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivativeClosedClass_bounded_by_inverseLeastSize : ∀ (B : RowsAut), 1 ≤ B.I.n → 1 ≤ B.g → ∃ m : ℕ, ∀ W : Set (B.I.GA → ℂ), (∀ f ∈ W, (∃ F, GlobalTheory.Dec.IsContRep B F f) ∧ (∀ k ∈ B.I.Kg B.g, ∀ y, f (y * (1, k)) = f y) ∧ ∀ (v : InfinitePlace B.I.F) (E : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (B.I.ε v)), ∃ f' ∈ W, ∀ y, HasDerivAt (fun t : ℝ => f (y * GlobalTheory.SobolevBound.onePar B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace B v E) t)) (f' y) 0) → ∀ f ∈ W, ∃ C : ℝ, ∀ y, ‖f y‖ ≤ C * (GlobalTheory.Count.tau1 B.I y)⁻¹ ^ m := by
  atlas_forward_decl GlobalTheory.SobolevBound.derivative_closed_class_bound
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_along_lie_algebra_preserves_smooth_space : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam θ → ∀ W : Set (GA D V → ℂ), (∀ f ∈ W, Continuous f ∧ ∀ τ, ∃ L : Matrix (Fin V.rank) (Fin V.rank) ℂ → GA D V → ℂ, (∀ X ∈ lieAt V τ, L X ∈ W ∧ ∀ x, HasDerivAt (fun t : ℝ => f (x * oneP θ V τ X t)) (L X x) 0) ∧ ∀ (a : ℝ), ∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt V τ, L (a • X + Y) = (a : ℂ) • L X + L Y) → ∀ f ∈ W, ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  first | exact @GlobalTheory.DerClosedSmooth.smooth_of_closed | exact GlobalTheory.DerClosedSmooth.smooth_of_closed | (intros; apply GlobalTheory.DerClosedSmooth.smooth_of_closed <;> assumption)
end

section
noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev GlobalTheory.SmVec NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepSmooth

variable {D : D7} {θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S} {Φ : MMap M}

def IsEquiv (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (Φ : MMap M) : Prop :=
  ∀ τ, ∀ a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (u : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ a (u τ) → Φ (Function.update u τ w) = rTr V (atTau θ V τ a) (Φ u)

def IsSob (Φ : MMap M) : Prop :=
  ∀ τ (u : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = Φ (Function.update u τ w) x

def der (u : M.Vec) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : M.sm τ :=
  ⟨dRep (trRep (M.σ τ) (M.fr τ)) X (u τ), (MultGelf.mem_sm M τ).2
    (dRep_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (MultGelf.isURep M τ) ((MultGelf.mem_sm M τ).1 (u τ).2) hX)⟩

theorem hasDerivAt_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (u : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (x : GA D V) :
    HasDerivAt (fun t : ℝ => Φ u (x * oneP θ V τ X t)) (Φ (Function.update u τ (der u τ hX)) x) 0 := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  obtain ⟨ℓ, hℓ, hℓT⟩ := hs τ u x
  obtain ⟨m, ls, a, hls, ha⟩ := GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ℓ hℓ
  have hu := (MultGelf.mem_sm M τ).1 (u τ).2
  have hmem : ∀ t : ℝ, trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) (u τ) ∈
      smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := fun t =>
    rep_mem hG (MultGelf.isURep M τ) hu (exp_mem_UH hG hX t)
  have h1 : (fun t : ℝ => Φ u (x * oneP θ V τ X t)) = fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i)
        (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) (u τ))⟫_ℂ := by
    funext t
    rw [← ha _ (hmem t)]
    have h2 := he τ _ (exp_mem_UH hG hX t) u ⟨_, (MultGelf.mem_sm M τ).2 (hmem t)⟩ rfl
    have h3 := hℓT ⟨_, (MultGelf.mem_sm M τ).2 (hmem t)⟩
    rw [h2] at h3
    exact h3.symm
  rw [h1, ← hℓT, show ((der u τ hX : M.sm τ) : M.H τ) = dRep (trRep (M.σ τ) (M.fr τ)) X (u τ) from rfl,
    ha _ (dRep_mem hG (MultGelf.isURep M τ) hu hX)]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h5 := (hasDerivAt_const (0 : ℝ) (a i)).inner ℂ
    (GlobalTheory.T.lieWord_commutes_oneParameter_derivative _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (ls i) (hls i) _ hu X hX)
  simpa using h5

theorem rder_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (u : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Rder θ V τ X (Φ u) = Φ (Function.update u τ (der u τ hX)) :=
  funext fun x => (hasDerivAt_apply he hs τ u hX x).deriv

theorem rderC_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (v : M.Vec)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z u) :
    RderC θ V τ Z (Φ (Function.update v τ u)) = Φ (Function.update v τ w) := by
  have hp := parts_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ)) Z
  have h1 := rder_apply he hs τ (Function.update v τ u) hp.1
  have h2 := rder_apply he hs τ (Function.update v τ u) hp.2
  rw [Function.update_idem] at h1 h2
  have h3 : w = der (Function.update v τ u) τ hp.1 + Complex.I • der (Function.update v τ u) τ hp.2 :=
    Subtype.ext (by rw [hw]; simp only [der, Function.update_self]; rfl)
  rw [h3, Φ.map_update_add, Φ.map_update_smul, ← h1, ← h2]
  rfl

theorem foldr_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (v : M.Vec)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (u : M.sm τ) :
    ∃ w : M.sm τ, (w : M.H τ) =
        (l.map fun Z => dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z).foldr (fun f acc => f acc) (u : M.H τ) ∧
      (l.map fun Z => RderC θ V τ Z).foldr (fun f acc => f acc) (Φ (Function.update v τ u)) =
        Φ (Function.update v τ w) := by
  induction l with
  | nil => exact ⟨u, rfl, rfl⟩
  | cons Z l ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨⟨_, (MultGelf.mem_sm M τ).2 (dRepC_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ))
      (MultGelf.isURep M τ) Z ((MultGelf.mem_sm M τ).1 w.2))⟩, ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1]
    · rw [List.map_cons, List.foldr_cons, h2]
      exact rderC_apply he hs τ v Z w _ rfl

theorem gelf_scalar (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (k : ℕ) :
    ∃ c : ℂ, ∀ v : M.Vec, gelf θ V τ k (Φ v) = c • Φ v := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  obtain ⟨c, hc⟩ := GlobalTheory.SmVec.GelfScalar.gelfH_scalar _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
    (M.ds τ).2.2.2.1 k
  refine ⟨c, fun v => ?_⟩
  choose f hf1 hf2 using fun idx : Fin (k + 1) → Fin V.rank =>
    foldr_apply he hs τ v (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) (v τ)
  simp only [List.map_ofFn, Function.comp_def, Function.update_eq_self] at hf1 hf2
  have h1 : c • v τ = ∑ idx, f idx := by
    refine Subtype.ext ?_
    rw [Submodule.coe_smul, ← hc _ ((MultGelf.mem_sm M τ).1 (v τ).2), Submodule.coe_sum]
    exact Finset.sum_congr rfl fun idx _ => (hf1 idx).symm
  have h2 : c • Φ v = Φ (Function.update v τ (c • v τ)) := by
    rw [Φ.map_update_smul, Function.update_eq_self]
  rw [h2, h1]
  refine Eq.trans ?_ (map_sum (Φ.toLinearMap v τ) f Finset.univ).symm
  exact Finset.sum_congr rfl fun idx _ => hf2 idx

theorem zfin (he : IsEquiv θ Φ) (hs : IsSob Φ) (u : M.Vec) :
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ Φ u ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W := by
  refine ⟨Submodule.span ℂ {Φ u}, inferInstance, Submodule.mem_span_singleton_self _, fun τ k f hf => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
  obtain ⟨c, hc⟩ := gelf_scalar he hs τ k
  have h2 : a • Φ u = Φ (Function.update u τ (a • u τ)) := by
    rw [Φ.map_update_smul, Function.update_eq_self]
  rw [h2, hc, ← h2]
  exact Submodule.smul_mem _ _ hf

attribute [local instance 100] LieRing.ofAssociativeRing in
theorem smooth (hθ : IsInfFam θ) (he : IsEquiv θ Φ) (hs : IsSob Φ) (hc : ∀ u, Continuous (Φ u)) (u : M.Vec)
    (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hX : ∀ i, Xs i ∈ lieAt V (τs i)) (g : GA D V) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => Φ u (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  refine GlobalTheory.T.derivative_along_lie_algebra_preserves_smooth_space D θ V hθ (Set.range Φ) ?_ _ ⟨u, rfl⟩ k τs Xs hX g
  rintro _ ⟨v, rfl⟩
  refine ⟨hc v, fun τ => ⟨fun X => Rder θ V τ X (Φ v), fun X hX => ?_, fun a X hX Y hY => ?_⟩⟩
  · simp only [rder_apply he hs τ v hX]
    exact ⟨⟨_, rfl⟩, hasDerivAt_apply he hs τ v hX⟩
  · haveI : CompleteSpace (M.H τ) := (M.ds τ).1
    obtain ⟨h1, h2⟩ := GlobalTheory.SmVecLinear.dRep_linear _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 _
      ((MultGelf.mem_sm M τ).1 (v τ).2)
    have haX : a • X ∈ lieAt V τ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU (gramAt D V τ)).smul_mem' a hX
    have hXY : a • X + Y ∈ lieAt V τ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU (gramAt D V τ)).add_mem' haX hY
    have h3 : der v τ hXY = (a : ℂ) • der v τ hX + der v τ hY :=
      Subtype.ext ((h1 _ haX _ hY).trans (by rw [h2 a X hX]; rfl))
    simp only [rder_apply he hs τ v hX, rder_apply he hs τ v hY, rder_apply he hs τ v hXY]
    rw [h3, Φ.map_update_add, Φ.map_update_smul]

theorem foldr_rder (he : IsEquiv θ Φ) (hs : IsSob Φ) (u : M.Vec)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) :
    ∃ v, l.foldr (fun p f => Rder θ V p.1 p.2 f) (Φ u) = Φ v := by
  induction l with
  | nil => exact ⟨u, rfl⟩
  | cons p l ih =>
    obtain ⟨v, hv⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    exact ⟨_, by rw [List.foldr_cons, hv, rder_apply he hs p.1 v (hl p List.mem_cons_self)]⟩

section Inst

variable {pl : InfinitePlace D.host.F ≃ D.what₂.Tau} {X : ModInst D V M pl} {T : GA D V ≃* X.inst.GA}

theorem conj_lie (τ : D.what₂.Tau) {E : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hE : Formalism.REAL.inG (M.ε τ) E) :
    (M.fr τ)⁻¹ * E * M.fr τ ∈ lieAt V τ := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hk : Eᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * E = 0 := hE
  have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
  change ((M.fr τ)⁻¹ * E * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * E * M.fr τ) = 0
  calc _ = (M.fr τ)ᴴ * (Eᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) +
        Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * E) * M.fr τ := by
        rw [← M.fr_gram τ]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [h1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk]; simp

@[reducible] def bundle (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (H : InfinitePlace I.F → Type)
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)] (hC : ∀ v, CompleteSpace (H v))
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (Hs : Type)
    [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs))
    (tens : (∀ v, H v) → Hs) (hF : I.IsFundDom (I.muA μf) fund) (hR : I.IsRightReg μf fund R)
    (hH : I.IsHilbTensor σ σs tens) (g : ℕ) : RowsAut where
  I := I
  μf := μf
  fund := fund
  fund_spec := hF
  lam := fun _ _ => 0
  H := H
  hC := hC
  σ := σ
  w := fun _ => 0
  Hs := Hs
  σs := σs
  tens := tens
  tens_spec := hH
  R := R
  R_spec := hR
  g := g
  g₀ := 0
  e := fun _ => 0
  e_adm := ⟨IsLocallyConstant.const _, by funext x; simp [AutInst.convF], fun _ => by simp,
    fun _ _ _ => by simp, fun _ h => absurd rfl h, fun _ _ _ _ _ => rfl, fun _ h => absurd rfl h⟩
  Re := 0
  Re_spec := ⟨integrable_zero _ _ _, fun _ _ => by simp⟩

theorem isContRep_of_ae (B : RowsAut) {y : B.I.L2 B.μf B.fund} {f : B.I.GA → ℂ} (hc : Continuous f)
    (hl : ∀ γ ∈ B.I.GFset, ∀ x, f (γ * x) = f x) (h : ∀ᵐ x ∂(B.I.muA B.μf), f x = B.I.ext y x) :
    GlobalTheory.Dec.IsContRep B y f := by
  refine ⟨hc, hl, ?_⟩
  have h1 := B.R_spec 1 y
  rw [(GlobalTheory.RightRegFund.rightReg_unitary_continuous B).1] at h1
  filter_upwards [h1, ae_restrict_of_ae (s := B.fund) h] with x a b
  rw [b]
  simpa using a

theorem eq_of_ae (B : RowsAut) {f f' : B.I.GA → ℂ} (hc : Continuous f) (hc' : Continuous f')
    (h : f =ᵐ[B.I.muA B.μf] f') : f = f' := by
  obtain ⟨-, -, -, -, hop⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  have : (B.I.muA B.μf).IsOpenPosMeasure := ⟨fun U hU hne => (hop U hU hne).ne'⟩
  exact (Continuous.ae_eq_iff_eq (B.I.muA B.μf) hc hc').1 h

theorem eq_onePar (B : RowsAut) (w : InfinitePlace B.I.F) (E : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (B.I.ε w)) (t : ℝ) {h : B.I.GA}
    (h2 : h.2 = 1) (hw : uMat (h.1 w) = NormedSpace.exp (t • E.1)) (hv : ∀ v, v ≠ w → uMat (h.1 v) = 1) :
    h = GlobalTheory.SobolevBound.onePar B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace B w E) t := by
  refine Prod.ext (funext fun v => Subtype.ext (Units.ext ?_)) h2
  change uMat (h.1 v) = NormedSpace.exp (t • (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace B w E v).1)
  by_cases c : v = w
  · subst c
    rw [hw, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace, Pi.single_eq_same]
  · rw [hv v c, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace, Pi.single_eq_of_ne c]
    simp

theorem hasDerivAt_switch (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (u : M.Vec)
    {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ) {G : Type} [Group G] (T : GA D V ≃* G) (c : ℝ → G)
    (hc : ∀ t, T (oneP θ V τ Y t) = c t) (y : G) :
    HasDerivAt (fun t : ℝ => Φ u (T.symm (y * c t))) (Φ (Function.update u τ (der u τ hY)) (T.symm y)) 0 := by
  simp only [← hc, map_mul, T.symm_apply_apply]
  exact hasDerivAt_apply he hs τ u hY (T.symm y)

end Inst

end GlobalTheory.RepSmooth

end
end
