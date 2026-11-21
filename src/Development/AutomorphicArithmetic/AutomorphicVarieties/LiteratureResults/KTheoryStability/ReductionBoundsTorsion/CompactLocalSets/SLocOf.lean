import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.OverlapG
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.SimpBdM
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.LowbdSmul

section
noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.LocalOverlapAverage

def Yb (H : Type) : Type := H × Bool

instance (H : Type) [Group H] : MulAction H (Yb H) where
  smul h p := ((h * p.1 : H), p.2)
  one_smul p := by
    change ((1 * p.1 : H), p.2) = p
    rw [one_mul]
    rfl
  mul_smul g h p := by
    change ((g * h * p.1 : H), p.2) = ((g * (h * p.1) : H), p.2)
    rw [mul_assoc]

theorem marg {X : Type} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] {n : ℕ}
    (i : Fin (n + 1)) (f : (Fin n → X) → ℝ) :
    ∫ x, f (fun j => x (i.succAbove j)) ∂(Measure.pi fun _ : Fin (n + 1) => P) =
      ∫ x, f x ∂(Measure.pi fun _ : Fin n => P) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) i).integral_comp'
    (fun p : X × (Fin n → X) => f p.2)
  rw [integral_fun_snd] at h
  simp only [probReal_univ, one_smul] at h
  exact h

theorem marg_int {X : Type} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] {n : ℕ}
    (i : Fin (n + 1)) (f : (Fin n → X) → ℝ) (hf : Integrable f (Measure.pi fun _ : Fin n => P)) :
    Integrable (fun x => f (fun j => x (i.succAbove j))) (Measure.pi fun _ : Fin (n + 1) => P) := by
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) i
  have hφ : Measurable fun x : Fin (n + 1) → X => fun j => x (i.succAbove j) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hmap : Measure.map (fun x : Fin (n + 1) → X => fun j => x (i.succAbove j))
      (Measure.pi fun _ : Fin (n + 1) => P) = Measure.pi fun _ : Fin n => P := by
    have hcomp : (fun x : Fin (n + 1) → X => fun j => x (i.succAbove j))
        = Prod.snd ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) i) := by
      funext x
      rfl
    rw [hcomp, ← Measure.map_map measurable_snd he.measurable, he.map_eq, Measure.map_snd_prod,
      measure_univ, one_smul]
  rw [← hmap] at hf
  exact hf.comp_measurable hφ

theorem avgS_of (hEv : SEv) : AvgS := by
  intro G H Y X _ _ _ _ ρ k F P _ e y₀ hinv hcoc hint z hz
  let F' : (Fin (k + 2) → Yb H) → ℝ := fun p =>
    ∫ x, F (fun j => (p j).1 • (if (p j).2 = true then e (x j) else y₀)) ∂(Measure.pi fun _ => P)
  have hInv' : Inv ρ F' := by
    intro g p
    change ∫ x, F (fun j => (ρ g * (p j).1) • (if (p j).2 = true then e (x j) else y₀))
        ∂(Measure.pi fun _ => P) = F' p
    simp only [mul_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact hinv g (fun j => (p j).1 • (if (p j).2 = true then e (x j) else y₀))
  have hcoc' : dC F' = 0 := by
    funext p
    let Q : (Fin (k + 3) → X) → Fin (k + 3) → Y := fun x j =>
      (p j).1 • (if (p j).2 = true then e (x j) else y₀)
    have hint' : ∀ i : Fin (k + 3),
        Integrable (fun x => F (fun j => Q x (i.succAbove j))) (Measure.pi fun _ => P) := by
      intro i
      exact marg_int P i _ (hint (fun j => (p (i.succAbove j)).1) (fun j => (p (i.succAbove j)).2))
    have hterm : ∀ i : Fin (k + 3), F' (fun j => p (i.succAbove j))
        = ∫ x, F (fun j => Q x (i.succAbove j)) ∂(Measure.pi fun _ => P) :=
      fun i => (marg P i _).symm
    change ∑ i : Fin (k + 3), (-1 : ℝ) ^ (i : ℕ) * F' (fun j => p (i.succAbove j)) = 0
    calc ∑ i : Fin (k + 3), (-1 : ℝ) ^ (i : ℕ) * F' (fun j => p (i.succAbove j))
        = ∑ i : Fin (k + 3), ∫ x, (-1 : ℝ) ^ (i : ℕ) * F (fun j => Q x (i.succAbove j))
            ∂(Measure.pi fun _ => P) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hterm i, integral_const_mul]
      _ = ∫ x, ∑ i : Fin (k + 3), (-1 : ℝ) ^ (i : ℕ) * F (fun j => Q x (i.succAbove j))
            ∂(Measure.pi fun _ => P) :=
          (integral_finset_sum _ fun i _ => (hint' i).const_mul _).symm
      _ = ∫ x, dC F (Q x) ∂(Measure.pi fun _ => P) := rfl
      _ = 0 := by simp [hcoc]
  let b₀ : Yb H := ((1 : H), false)
  let b₁ : Yb H := ((1 : H), true)
  have key1 : ∀ q : Fin (k + 2) → H, F' (fun j => q j • b₀) = F (fun j => q j • y₀) := by
    intro q
    change ∫ x, F (fun j => (q j * 1) • (if false = true then e (x j) else y₀))
      ∂(Measure.pi fun _ => P) = _
    simp
  have key2 : ∀ q : Fin (k + 2) → H, F' (fun j => q j • b₁)
      = ∫ x, F (fun j => q j • e (x j)) ∂(Measure.pi fun _ => P) := by
    intro q
    change ∫ x, F (fun j => (q j * 1) • (if true = true then e (x j) else y₀))
      ∂(Measure.pi fun _ => P) = _
    simp
  have h := (hEv G H (Yb H) ρ k F' hInv' hcoc').2 b₀ b₁ z hz
  simp only [ev, key1, key2] at h
  simpa [ev] using h

end PositivityTheory.KB.LocalOverlapAverage

end
end

section
namespace PositivityTheory.KB.LocalOverlapAverage

theorem simpBd_holds : SimpBd := by
  intro V _ _ _ _ _ μ _ q A B hB
  exact SimpM.main μ q A B hB

end PositivityTheory.KB.LocalOverlapAverage
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexOrder

namespace PositivityTheory.KB.LocalOverlapAverage

theorem fac_exists {n : Type} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosDef) :
    ∃ B : Matrix n n ℂ, Bᴴ * B = Q := by
  set U : Matrix n n ℂ := (hQ.1.eigenvectorUnitary : Matrix n n ℂ)
  set D : Matrix n n ℂ := diagonal (fun i => ((Real.sqrt (hQ.1.eigenvalues i) : ℝ) : ℂ))
  refine ⟨D * star U, ?_⟩
  conv_rhs => rw [hQ.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  have hU : (star U)ᴴ = U := by rw [star_eq_conjTranspose, conjTranspose_conjTranspose]
  have hD : Dᴴ * D = diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues) := by
    simp only [D, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.star_apply, Function.comp, RCLike.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hQ.eigenvalues_pos i).le]
    rfl
  rw [conjTranspose_mul, hU, Matrix.mul_assoc, ← Matrix.mul_assoc Dᴴ, hD, ← Matrix.mul_assoc]

theorem gl_fac_exists {n : Type} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosDef) :
    ∃ Y : GL n ℂ, ((Y⁻¹ : GL n ℂ) : Matrix n n ℂ)ᴴ * ((Y⁻¹ : GL n ℂ) : Matrix n n ℂ) = Q ∧
      (Y : Matrix n n ℂ) * (Y : Matrix n n ℂ)ᴴ = Q⁻¹ := by
  obtain ⟨B, hB⟩ := fac_exists hQ
  have hdet : IsUnit B.det := by
    have h1 : Q.det ≠ 0 := (hQ.det_pos).ne'
    rw [← hB, det_mul, det_conjTranspose] at h1
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h1)
  have hBu : IsUnit B := (isUnit_iff_isUnit_det B).mpr hdet
  refine ⟨hBu.unit⁻¹, ?_, ?_⟩
  · simpa using hB
  · rw [coe_units_inv, IsUnit.unit_spec, ← hB, Matrix.mul_inv_rev, conjTranspose_nonsing_inv]

theorem norm_sq_le_diag {n : Type} [Fintype n] (Y : Matrix n n ℂ) (i j : n) :
    ‖Y i j‖ ^ 2 ≤ ‖(Y * Yᴴ) i i‖ := by
  have h : (Y * Yᴴ) i i = ((∑ k, ‖Y i k‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conjTranspose_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => by positivity)]
  exact Finset.single_le_sum (f := fun k => ‖Y i k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)

theorem sl_dec {N : ℕ} (hN : 1 ≤ N) (Y : GL (Fin N) ℂ) :
    ∃ (c : ℂˣ) (T : SpecialLinearGroup (Fin N) ℂ),
      Y = GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T ∧ (c : ℂ) ^ N = (Y : Matrix (Fin N) (Fin N) ℂ).det := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (Y : Matrix (Fin N) (Fin N) ℂ).det (by omega : 0 < N)
  have hY : (Y : Matrix (Fin N) (Fin N) ℂ).det ≠ 0 := (Matrix.isUnits_det_units Y).ne_zero
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hc
    exact hY hc.symm
  have hdetT : (c⁻¹ • (Y : Matrix (Fin N) (Fin N) ℂ)).det = 1 := by
    rw [det_smul, Fintype.card_fin, inv_pow, hc, inv_mul_cancel₀ hY]
  let T : SpecialLinearGroup (Fin N) ℂ := ⟨c⁻¹ • (Y : Matrix (Fin N) (Fin N) ℂ), hdetT⟩
  have hT : ((SpecialLinearGroup.toGL T : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      c⁻¹ • (Y : Matrix (Fin N) (Fin N) ℂ) := rfl
  refine ⟨Units.mk0 c hc0, T, ?_, by simpa using hc⟩
  ext i j
  simp only [GeneralLinearGroup.scalar, Units.val_mul, hT]
  simp
  rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

theorem isCompact_bddSL {ι : Type} [Fintype ι] {n : Type} [Fintype n] [DecidableEq n] (R : ℝ) :
    IsCompact {x : ι → SpecialLinearGroup n ℂ | ∀ w i j, ‖(x w : Matrix n n ℂ) i j‖ ≤ R} := by
  have hE : Topology.IsClosedEmbedding (fun x : ι → SpecialLinearGroup n ℂ => fun w => (x w : Matrix n n ℂ)) :=
    Topology.IsClosedEmbedding.piMap fun _ => SpecialLinearGroup.isClosedEmbedding_val
  have hC : IsCompact (Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : n => Set.pi Set.univ fun _ : n =>
      Metric.closedBall (0 : ℂ) R) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  convert hE.isCompact_preimage hC using 1
  ext x
  exact ⟨fun h w _ i _ j _ => by simpa using h w i j, fun h w i j => by simpa using h w trivial i trivial j trivial⟩

theorem coe_scal_mul {n : Type} [Fintype n] [DecidableEq n] (c : ℂˣ) (T : SpecialLinearGroup n ℂ) :
    ((GeneralLinearGroup.scalar n c * SpecialLinearGroup.toGL T : GL n ℂ) : Matrix n n ℂ) =
      (c : ℂ) • (T : Matrix n n ℂ) := by
  ext i j
  simp [GeneralLinearGroup.scalar]

theorem dec_bdd {N : ℕ} (hN : 1 ≤ N) (R2 R3 : ℝ) : ∃ R : ℝ, 0 ≤ R ∧
    ∀ Q : Matrix (Fin N) (Fin N) ℂ, Q.PosDef → (∀ i j, ‖Q⁻¹ i j‖ ≤ R2) → ‖Q.det‖ ≤ R3 →
      ∃ (c : ℂˣ) (T : SpecialLinearGroup (Fin N) ℂ),
        ((((GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T)⁻¹ : GL (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ)ᴴ *
          (((GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T)⁻¹ : GL (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ) = Q) ∧
        (∀ i j, ‖((GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T : GL (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R) ∧
        ∀ i j, ‖(T : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R := by
  set a : ℝ := max 1 R2
  set R3' : ℝ := max R3 1
  set m : ℝ := min 1 R3'⁻¹
  have hR3' : 0 < R3' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hm : 0 < m := lt_min one_pos (inv_pos.mpr hR3')
  have ha : 0 ≤ a := le_trans zero_le_one (le_max_left _ _)
  refine ⟨a / m, div_nonneg ha hm.le, fun Q hQ h2 h3 => ?_⟩
  obtain ⟨Y, hY1, hY2⟩ := gl_fac_exists hQ
  obtain ⟨c, T, hYd, hc⟩ := sl_dec hN Y
  subst hYd
  refine ⟨c, T, hY1, ?_⟩

  have hYb : ∀ i j, ‖((GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T : GL (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ a := by
    intro i j
    have h := norm_sq_le_diag ((GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T : GL (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) i j
    rw [hY2] at h
    have h' := h.trans (h2 i i)
    by_contra hlt
    rw [not_le] at hlt
    have h1 : 1 < ‖((GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T : GL (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) i j‖ := lt_of_le_of_lt (le_max_left _ _) hlt
    nlinarith [le_max_right 1 R2]

  set Y : GL (Fin N) ℂ := GeneralLinearGroup.scalar (Fin N) c * SpecialLinearGroup.toGL T with hYdef
  have hdQ : ‖Q.det‖ = ‖((Y⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).det‖ ^ 2 := by
    rw [← hY1, det_mul, det_conjTranspose, norm_mul, norm_star, sq]
  have hYY : ‖(Y : Matrix (Fin N) (Fin N) ℂ).det‖ * ‖((Y⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).det‖ = 1 := by
    rw [← norm_mul, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, norm_one]
  have hcN : ‖(c : ℂ)‖ ^ N = ‖(Y : Matrix (Fin N) (Fin N) ℂ).det‖ := by rw [← norm_pow, hc]
  have hQpos : 0 < ‖Q.det‖ := norm_pos_iff.mpr hQ.det_pos.ne'
  have hc2 : ‖(c : ℂ)‖ ^ (2 * N) * ‖Q.det‖ = 1 := by
    rw [pow_mul', hcN, hdQ, ← mul_pow, hYY, one_pow]
  have hcm : m ≤ ‖(c : ℂ)‖ := by
    by_contra hlt
    rw [not_le] at hlt
    have hc1 : ‖(c : ℂ)‖ ≤ 1 := hlt.le.trans (min_le_left _ _)
    have hpow : ‖(c : ℂ)‖ ^ (2 * N) ≤ ‖(c : ℂ)‖ := pow_le_of_le_one (norm_nonneg _) hc1 (by omega)
    have hle : ‖Q.det‖ ≤ R3' := h3.trans (le_max_left _ _)
    have : ‖(c : ℂ)‖ ^ (2 * N) * ‖Q.det‖ < 1 := by
      calc ‖(c : ℂ)‖ ^ (2 * N) * ‖Q.det‖ ≤ ‖(c : ℂ)‖ * R3' :=
            mul_le_mul hpow hle hQpos.le (norm_nonneg _)
        _ < m * R3' := mul_lt_mul_of_pos_right hlt hR3'
        _ ≤ R3'⁻¹ * R3' := mul_le_mul_of_nonneg_right (min_le_right _ _) hR3'.le
        _ = 1 := inv_mul_cancel₀ hR3'.ne'
    linarith
  refine ⟨fun i j => (hYb i j).trans (le_div_self ha hm ?_), fun i j => ?_⟩
  · exact min_le_left _ _
  · have hcT : (Y : Matrix (Fin N) (Fin N) ℂ) i j = (c : ℂ) * (T : Matrix (Fin N) (Fin N) ℂ) i j := by
      rw [hYdef, coe_scal_mul]; rfl
    have hc0 : 0 < ‖(c : ℂ)‖ := lt_of_lt_of_le hm hcm
    have : ‖(T : Matrix (Fin N) (Fin N) ℂ) i j‖ = ‖(Y : Matrix (Fin N) (Fin N) ℂ) i j‖ / ‖(c : ℂ)‖ := by
      rw [hcT, norm_mul, mul_div_cancel_left₀ _ hc0.ne']
    rw [this]
    exact div_le_div₀ ha (hYb i j) hm hcm

theorem lintegral_cle_ge {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (e : V ≃L[ℝ] V)
    (S K : Set V) (hK : K ⊆ e '' S) (G : V → ℝ≥0∞) :
    ENNReal.ofReal |(LinearMap.det ((e : V →L[ℝ] V) : V →ₗ[ℝ] V))⁻¹| * ∫⁻ p in K, G p ∂μ ≤
      ∫⁻ q in S, G (e q) ∂μ := by
  set E : V ≃ᵐ V := e.toHomeomorph.toMeasurableEquiv
  have hE : ∀ x, E x = e x := fun _ => rfl
  have hdet : LinearMap.det ((e : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0 :=
    (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hmap : Measure.map E μ = ENNReal.ofReal |(LinearMap.det ((e : V →L[ℝ] V) : V →ₗ[ℝ] V))⁻¹| • μ := by
    rw [← Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet]
    rfl
  have h1 : ∫⁻ q in S, G (e q) ∂μ = ∫⁻ p in e '' S, G p ∂(Measure.map E μ) := by
    rw [MeasurableEquiv.restrict_map]
    have hpre : E ⁻¹' (e '' S) = S := by
      ext x
      simp only [Set.mem_preimage, hE, Set.mem_image]
      exact ⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
    rw [hpre, lintegral_map_equiv]
    rfl
  rw [h1, hmap, Measure.restrict_smul, lintegral_smul_measure]
  exact mul_le_mul_right (lintegral_mono_set hK) _

end PositivityTheory.KB.LocalOverlapAverage

end
end

section
noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped ENNReal NNReal ComplexOrder

namespace PositivityTheory.KB.LocalOverlapAverage

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem ofS_apply (s : Sp L N) (w : InfinitePlace L) : ofS L N s w = SpecialLinearGroup.toGL (s w) := rfl

theorem coe_ofS_inv (s : Sp L N) (w : InfinitePlace L) :
    (((ofS L N s w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (((s w)⁻¹ : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
  rw [ofS_apply, ← map_inv]; rfl


theorem val_actL (g : Gp L N) (h : HS L N) : (actL g h : HS L N).1 = fun w =>
    (((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ * mat h w * ((g w)⁻¹ : GL (Fin N) ℂ) := rfl

theorem cont_act : Continuous (fun p : Sp L N × HS L N => actL (ofS L N p.1) p.2) := by
  refine continuous_induced_rng.2 ?_
  have e : (fun p : Sp L N × HS L N => (actL (ofS L N p.1) p.2 : HS L N).1) = fun p w =>
      (((p.1 w)⁻¹ : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ * mat p.2 w *
        (((p.1 w)⁻¹ : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
    funext p
    rw [val_actL]
    funext w
    rw [coe_ofS_inv]
    try rfl
  change Continuous (fun p : Sp L N × HS L N => (actL (ofS L N p.1) p.2 : HS L N).1)
  rw [e]
  refine continuous_pi fun w => ?_
  have h1 : Continuous fun p : Sp L N × HS L N =>
      (((p.1 w)⁻¹ : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) :=
    continuous_subtype_val.comp ((continuous_inv.comp (continuous_apply w)).comp continuous_fst)
  have h2 : Continuous fun p : Sp L N × HS L N => mat p.2 w :=
    (continuous_apply w).comp (continuous_subtype_val.comp continuous_snd)
  exact (h1.matrix_conjTranspose.matrix_mul h2).matrix_mul h1

def actE (g : Gp L N) : HS L N ≃L[ℝ] HS L N :=
  ContinuousLinearEquiv.equivOfInverse (actL g) (actL g⁻¹)
    (fun h => by rw [← actL_mul, inv_mul_cancel, actL_one])
    (fun h => by rw [← actL_mul, mul_inv_cancel, actL_one])

theorem actE_apply (g : Gp L N) (h : HS L N) : actE g h = actL g h := rfl

theorem cont_act_at (h : HS L N) : Continuous fun s : Sp L N => actL (ofS L N s) h := by
  have h1 : Continuous fun s : Sp L N => ((s, h) : Sp L N × HS L N) := continuous_id.prodMk continuous_const
  have h2 := cont_act.comp h1
  simpa only [Function.comp_def] using h2

theorem cont_actCLM : Continuous (fun s : Sp L N => (actL (ofS L N s) : HS L N →L[ℝ] HS L N)) := by
  rw [continuous_clm_apply]
  exact cont_act_at

theorem cont_det : Continuous (fun s : Sp L N =>
    LinearMap.det (((actE (ofS L N s) : HS L N →L[ℝ] HS L N)) : HS L N →ₗ[ℝ] HS L N)) :=
  ContinuousLinearMap.continuous_det.comp cont_actCLM

theorem fr_scal {q : ℕ} {ω : Form (HS L N) q} (c : InfinitePlace L → ℂˣ) (hc : FInv ω (scal L N c))
    (x : Gp L N) : fr ω (scal L N c * x) = fr ω x := by
  ext v
  have := congrArg (fun f => f (fun i => actL x (v i))) (hc (actL x (one L N).1) (actL_pos x (one L N).2))
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at this
  simp only [fr, ContinuousAlternatingMap.compContinuousLinearMap_apply, actL_mul]
  rw [show (⇑(actL (scal L N c * x)) ∘ v) = ⇑(actL (scal L N c)) ∘ fun i => actL x (v i) from
    funext fun i => actL_mul _ _ _]
  exact this

theorem om_fr {q : ℕ} (ω : Form (HS L N) q) (x : Gp L N) :
    ω (actL x (one L N).1) = (fr ω x).compContinuousLinearMap (actL x⁻¹) := by
  ext v
  simp only [fr, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  show v i = actL x (actL x⁻¹ (v i))
  rw [← actL_mul, mul_inv_cancel, actL_one]

theorem norm_om_le {q : ℕ} (ω : Form (HS L N) q) (x : Gp L N) :
    ‖ω (actL x (one L N).1)‖ ≤ ‖fr ω x‖ * ‖actL x⁻¹‖ ^ q := by
  rw [om_fr ω x]
  simpa using ContinuousAlternatingMap.norm_compContinuousLinearMap_le (fr ω x) (actL x⁻¹)

theorem entry_mul_le {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} {a b : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ a)
    (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin n) : ‖(A * B) i j‖ ≤ n * (a * b) := by
  rw [mul_apply]
  calc ‖∑ k, A i k * B k j‖ ≤ ∑ k : Fin n, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, a * b := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]; exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ((norm_nonneg _).trans (hA i k))
    _ = n * (a * b) := by simp

theorem entry_le_norm (h : HS L N) (w : InfinitePlace L) (i j : Fin N) : ‖mat h w i j‖ ≤ ‖h‖ := by
  calc ‖mat h w i j‖ = ‖h.1 w i j‖ := rfl
    _ ≤ ‖h.1 w i‖ := norm_le_pi_norm _ _
    _ ≤ ‖h.1 w‖ := norm_le_pi_norm _ _
    _ ≤ ‖h.1‖ := norm_le_pi_norm _ _
    _ = ‖h‖ := rfl

theorem norm_le_of_entry (h : HS L N) (r : ℝ) (hr : 0 ≤ r) (hh : ∀ w i j, ‖mat h w i j‖ ≤ r) : ‖h‖ ≤ r := by
  change ‖h.1‖ ≤ r
  refine (pi_norm_le_iff_of_nonneg hr).2 fun w => (pi_norm_le_iff_of_nonneg hr).2 fun i =>
    (pi_norm_le_iff_of_nonneg hr).2 fun j => hh w i j

theorem norm_actL_le (g : Gp L N) (r : ℝ) (hr : 0 ≤ r)
    (hg : ∀ w i j, ‖(((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ r) :
    ‖actL g‖ ≤ N * (N * r * r) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  refine norm_le_of_entry _ _ (by positivity) fun w i j => ?_
  rw [mat_actL]
  have h1 : ∀ i j, ‖((((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ) i j‖ ≤ r := fun i j => by
    rw [conjTranspose_apply, norm_star]; exact hg w j i
  have h2 := entry_mul_le h1 (fun i j => entry_le_norm h w i j)
  have h3 := entry_mul_le h2 (hg w) i j
  calc _ ≤ _ := h3
    _ = N * (N * r * r) * ‖h‖ := by ring

theorem comm_scal (g : Gp L N) (c : InfinitePlace L → ℂˣ) : g * scal L N c = scal L N c * g := by
  funext w
  apply Units.ext
  simp only [Pi.mul_apply, Units.val_mul, scal, GeneralLinearGroup.scalar]
  ext i j
  simp [mul_diagonal, diagonal_mul, mul_comm]

theorem coe_mul_ofS (s : Sp L N) (y : Gp L N) (w : InfinitePlace L) :
    (((ofS L N s * y) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((s w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * ((y w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := rfl

theorem point_bd {q : ℕ} {ω : Form (HS L N) q} (hω : ∀ s, FInv ω (scal L N s))
    (c : InfinitePlace L → ℂˣ) (t s : Sp L N) (B : ℝ) (hB : 0 ≤ B)
    (hX : ∀ w i j, ‖(((ofS L N s * (scal L N c * ofS L N t)) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ B) :
    ‖ω (actL (ofS L N s) (actL (scal L N c * ofS L N t) (one L N).1))‖ ≤
      ‖fr ω (ofS L N (s * t))‖ * (N * (N * B * B)) ^ q := by
  set X : Gp L N := ofS L N s * (scal L N c * ofS L N t) with hXdef
  have hXe : X = scal L N c * ofS L N (s * t) := by
    rw [hXdef, ← mul_assoc, comm_scal, mul_assoc, map_mul]
  rw [← actL_mul]
  refine (norm_om_le ω X).trans ?_
  have h1 : ‖fr ω X‖ = ‖fr ω (ofS L N (s * t))‖ := by rw [hXe, fr_scal c (hω c)]
  have h2 : ‖actL X⁻¹‖ ≤ N * (N * B * B) := by
    refine norm_actL_le X⁻¹ B hB fun w i j => ?_
    simpa [Pi.inv_apply, inv_inv] using hX w i j
  rw [h1]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h2 q) (norm_nonneg _)

theorem cont_entry (w : InfinitePlace L) (i j : Fin N) :
    Continuous fun s : Sp L N => ((s w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j :=
  (continuous_apply j).comp ((continuous_apply i).comp
    ((SpecialLinearGroup.isClosedEmbedding_val (n := Fin N) (R := ℂ)).continuous.comp (continuous_apply w)))

theorem cont_mat (w : InfinitePlace L) : Continuous fun q : HS L N => mat q w :=
  (continuous_apply w).comp continuous_subtype_val

theorem contOn_inv : ContinuousOn (fun q : HS L N => fun w i j => (mat q w)⁻¹ i j) (Pos L N) := by
  intro q hq
  refine ContinuousAt.continuousWithinAt ?_
  refine continuousAt_pi.2 fun w => continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
  have hd : ContinuousAt Ring.inverse (mat q w).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hq w).det_pos.ne'
  have hm : ContinuousAt (fun q' : HS L N => mat q' w) q := (cont_mat w).continuousAt
  have hinv : ContinuousAt (fun q' : HS L N => (mat q' w)⁻¹) q :=
    ContinuousAt.comp (f := fun q' : HS L N => mat q' w) (x := q) (continuousAt_matrix_inv (mat q w) hd) hm
  show ContinuousAt (fun q' : HS L N => (mat q' w)⁻¹ i j) q
  exact (continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hinv)

theorem cont_detq : Continuous (fun q : HS L N => fun w => (mat q w).det) :=
  continuous_pi fun w => (cont_mat w).matrix_det

theorem dec_K {K1 : Set (HS L N)} (hN : 1 ≤ N) (hK1 : IsCompact K1) (hP : K1 ⊆ Pos L N) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ q ∈ K1, ∃ (c : InfinitePlace L → ℂˣ) (t : Sp L N),
      actL (scal L N c * ofS L N t) (one L N).1 = q ∧
      (∀ w i j, ‖(((scal L N c * ofS L N t) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R) ∧
      ∀ w i j, ‖((t w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R := by
  obtain ⟨R2, hR2⟩ := hK1.exists_bound_of_continuousOn (contOn_inv.mono hP)
  obtain ⟨R3, hR3⟩ := hK1.exists_bound_of_continuousOn (cont_detq (L := L) (N := N)).continuousOn
  obtain ⟨R, hR0, hR⟩ := dec_bdd hN R2 R3
  refine ⟨R, hR0, fun q hq => ?_⟩
  have hb2 : ∀ w i j, ‖(mat q w)⁻¹ i j‖ ≤ R2 := fun w i j =>
    (norm_le_pi_norm (fun j => (mat q w)⁻¹ i j) j).trans
      ((norm_le_pi_norm (fun i j => (mat q w)⁻¹ i j) i).trans
        ((norm_le_pi_norm (fun w i j => (mat q w)⁻¹ i j) w).trans (hR2 q hq)))
  have hb3 : ∀ w, ‖(mat q w).det‖ ≤ R3 := fun w =>
    (norm_le_pi_norm (fun w => (mat q w).det) w).trans (hR3 q hq)
  have key := fun w => hR (mat q w) (hP hq w) (hb2 w) (hb3 w)
  choose c t h1 h2 h3 using key
  refine ⟨c, t, HS_ext fun w => ?_, h2, h3⟩
  rw [mat_actL]
  have hone : mat (one L N).1 w = 1 := rfl
  rw [hone, Matrix.mul_one]
  exact h1 w

def Wn (L : Type) [Field L] [NumberField L] (N : ℕ) : Set (Sp L N) :=
  {s | ∀ w i j, ‖((s w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j -
    (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ 1 / 2}

theorem isClosed_Wn : IsClosed (Wn L N) := by
  simp only [Wn, Set.ofPred_forall]
  exact isClosed_iInter fun w => isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_le ((cont_entry w i j).sub continuous_const).norm continuous_const

theorem isClosed_bdd (R : ℝ) :
    IsClosed {x : Sp L N | ∀ w i j, ‖((x w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun w => isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_le (cont_entry w i j).norm continuous_const

theorem Wn_bdd : ∀ s ∈ Wn L N, ∀ w i j,
    ‖((s w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ 3 / 2 := by
  intro s hs w i j
  have h1 : ‖(1 : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ 1 := by
    rw [one_apply]; split_ifs <;> simp
  calc _ = ‖(((s w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j -
        (1 : Matrix (Fin N) (Fin N) ℂ) i j) + (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ 1 / 2 + 1 := add_le_add (hs w i j) h1
    _ = 3 / 2 := by norm_num

theorem isCompact_Wn : IsCompact (Wn L N) :=
  (isCompact_bddSL (ι := InfinitePlace L) (n := Fin N) (3 / 2)).of_isClosed_subset isClosed_Wn
    fun s hs => Wn_bdd s hs

theorem Wn_pos (μ : Measure (Sp L N)) [μ.IsOpenPosMeasure] : μ (Wn L N) ≠ 0 := by
  have hU : IsOpen {s : Sp L N | ∀ w i j, ‖((s w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j -
      (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ < 1 / 2} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt ((cont_entry w i j).sub continuous_const).norm continuous_const
  have h1 : (1 : Sp L N) ∈ {s : Sp L N | ∀ w i j, ‖((s w : SpecialLinearGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ < 1 / 2} := fun w i j => by
    simp
  exact fun h0 => (hU.measure_ne_zero μ ⟨1, h1⟩) (measure_mono_null (fun s hs w i j => (hs w i j).le) h0)

theorem right_trans_le {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulRightInvariant] (W K' : Set G) (hW : MeasurableSet W) (hK' : MeasurableSet K') (t : G)
    (hWK : ∀ x, x * t⁻¹ ∈ W → x ∈ K') (F : G → ℝ≥0∞) :
    ∫⁻ s in W, F (s * t) ∂μ ≤ ∫⁻ x in K', F x ∂μ := by
  classical
  set h : G → ℝ≥0∞ := fun x => if x * t⁻¹ ∈ W then F x else 0 with hh
  have e1 : ∫⁻ s in W, F (s * t) ∂μ = ∫⁻ s, h (s * t) ∂μ := by
    rw [← lintegral_indicator hW]
    congr 1
    funext s
    simp [hh, Set.indicator, mul_inv_cancel_right]
  rw [e1, lintegral_mul_right_eq_self h t, ← lintegral_indicator hK']
  refine lintegral_mono fun x => ?_
  by_cases h1 : x * t⁻¹ ∈ W
  · simp [hh, h1, Set.indicator_of_mem (hWK x h1)]
  · simp [hh, h1]

theorem unfold_holds : Unfold := by
  intro L _ _ N q hN d μ _ K hK hKP
  haveI := d.haar
  haveI := d.right
  set W := Wn L N with hWdef
  have hWk : IsCompact W := isCompact_Wn
  have hWm : MeasurableSet W := isClosed_Wn.measurableSet
  have hW0 : d.μ W ≠ 0 := Wn_pos d.μ
  have hWT : d.μ W ≠ ⊤ := hWk.measure_lt_top.ne
  have hcK : Continuous fun p : Sp L N × HS L N => actL (ofS L N p.1⁻¹) p.2 := by
    have h1 : Continuous fun p : Sp L N × HS L N => ((p.1⁻¹, p.2) : Sp L N × HS L N) :=
      (continuous_inv.comp continuous_fst).prodMk continuous_snd
    have h2 := cont_act.comp h1
    simpa only [Function.comp_def] using h2
  set K1 : Set (HS L N) := (fun p : Sp L N × HS L N => actL (ofS L N p.1⁻¹) p.2) '' (W ×ˢ K) with hK1def
  have hK1 : IsCompact K1 := (hWk.prod hK).image hcK
  have hK1P : K1 ⊆ Pos L N := by
    rintro _ ⟨p, hp, rfl⟩
    exact actL_pos _ (hKP hp.2)
  have hK1m : MeasurableSet K1 := hK1.isClosed.measurableSet
  have hK1T : μ K1 ≠ ⊤ := hK1.measure_lt_top.ne
  have hsub : ∀ s ∈ W, K ⊆ actE (ofS L N s) '' K1 := by
    intro s hs p hp
    refine ⟨actL (ofS L N s⁻¹) p, ⟨(s, p), ⟨hs, hp⟩, rfl⟩, ?_⟩
    rw [actE_apply, ← actL_mul, ← map_mul, mul_inv_cancel, map_one, actL_one]
  obtain ⟨R, hR0, hR⟩ := dec_K hN hK1 hK1P
  set R' : ℝ := N * (3 / 2 * R) with hR'def
  have hR'0 : 0 ≤ R' := by positivity
  set K' : Set (Sp L N) :=
    {x | ∀ w i j, ‖((x w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R'} with hK'def
  have hK'k : IsCompact K' := isCompact_bddSL (ι := InfinitePlace L) (n := Fin N) R'
  have hK'm : MeasurableSet K' := (isClosed_bdd R').measurableSet
  obtain ⟨Dm, hDm⟩ := hWk.exists_bound_of_continuousOn (cont_det (L := L) (N := N)).continuousOn
  set D' : ℝ := max Dm 1 with hD'def
  have hD'0 : 0 < D' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set m0 : ℝ≥0∞ := ENNReal.ofReal D'⁻¹ with hm0def
  have hm0 : m0 ≠ 0 := by simp [hm0def, hD'0]
  set B0 : ℝ := ((N : ℝ) * (N * R' * R')) ^ q with hB0def
  have hB00 : 0 ≤ B0 := by positivity
  set Bd : ℝ≥0∞ := ENNReal.ofReal B0 with hBddef
  refine ⟨(m0 * d.μ W)⁻¹ * (Bd * μ K1), K', ?_, hK'k, fun ω hω hsc => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (mul_ne_zero hm0 hW0))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK1T)
  set G : HS L N → ℝ≥0∞ := fun p => (‖ω p‖₊ : ℝ≥0∞) with hGdef
  set Fr : Sp L N → ℝ≥0∞ := fun x => (‖fr ω (ofS L N x)‖₊ : ℝ≥0∞) with hFrdef
  have st1 : ∀ s ∈ W, m0 * ∫⁻ p in K, G p ∂μ ≤ ∫⁻ p in K1, G (actL (ofS L N s) p) ∂μ := by
    intro s hs
    have h := lintegral_cle_ge μ (actE (ofS L N s)) K1 K (hsub s hs) G
    simp only [actE_apply] at h
    have hdet0 : LinearMap.det (((actE (ofS L N s) : HS L N →L[ℝ] HS L N)) : HS L N →ₗ[ℝ] HS L N) ≠ 0 :=
      (LinearEquiv.isUnit_det' (actE (ofS L N s)).toLinearEquiv).ne_zero
    have hb : |LinearMap.det (((actE (ofS L N s) : HS L N →L[ℝ] HS L N)) : HS L N →ₗ[ℝ] HS L N)| ≤ D' := by
      have := hDm s hs
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    have hm : m0 ≤ ENNReal.ofReal
        |(LinearMap.det (((actE (ofS L N s) : HS L N →L[ℝ] HS L N)) : HS L N →ₗ[ℝ] HS L N))⁻¹| := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [abs_inv]
      exact inv_anti₀ (abs_pos.2 hdet0) hb
    calc m0 * ∫⁻ p in K, G p ∂μ ≤ ENNReal.ofReal
          |(LinearMap.det (((actE (ofS L N s) : HS L N →L[ℝ] HS L N)) : HS L N →ₗ[ℝ] HS L N))⁻¹| *
            ∫⁻ p in K, G p ∂μ := by gcongr
      _ ≤ _ := h
  have st2 : (m0 * ∫⁻ p in K, G p ∂μ) * d.μ W ≤
      ∫⁻ s in W, ∫⁻ p in K1, G (actL (ofS L N s) p) ∂μ ∂d.μ := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' hWm st1
  haveI : IsFiniteMeasure (d.μ.restrict W) := isFiniteMeasure_restrict.2 hWT
  haveI : IsFiniteMeasure (μ.restrict K1) := isFiniteMeasure_restrict.2 hK1T
  have hmeas : AEMeasurable (Function.uncurry fun (s : Sp L N) (p : HS L N) => G (actL (ofS L N s) p))
      ((d.μ.restrict W).prod (μ.restrict K1)) := by
    have e1 : d.μ.restrict W = (d.μ.restrict W).restrict W := by
      rw [Measure.restrict_restrict hWm, Set.inter_self]
    have e2 : μ.restrict K1 = (μ.restrict K1).restrict K1 := by
      rw [Measure.restrict_restrict hK1m, Set.inter_self]
    rw [e1, e2, Measure.prod_restrict]
    refine ContinuousOn.aemeasurable ?_ (hWm.prod hK1m)
    have hc : ContinuousOn (fun p : Sp L N × HS L N => ω (actL (ofS L N p.1) p.2)) (W ×ˢ K1) :=
      hω.comp cont_act.continuousOn fun p hp => actL_pos _ (hK1P hp.2)
    exact (ENNReal.continuous_coe.comp continuous_nnnorm).comp_continuousOn hc
  have st3 := lintegral_lintegral_swap hmeas
  have st4 : ∀ p ∈ K1, ∫⁻ s in W, G (actL (ofS L N s) p) ∂d.μ ≤ Bd * ∫⁻ x in K', Fr x ∂d.μ := by
    intro p hp
    obtain ⟨c, t, hct, hy, ht⟩ := hR p hp
    have hpt : ∀ s ∈ W, G (actL (ofS L N s) p) ≤ Bd * Fr (s * t) := by
      intro s hs
      have hX : ∀ w i j, ‖(((ofS L N s * (scal L N c * ofS L N t)) w : GL (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R' := by
        intro w i j
        rw [coe_mul_ofS]
        exact entry_mul_le (Wn_bdd s hs w) (hy w) i j
      have h := point_bd hsc c t s R' hR'0 hX
      rw [hct] at h
      simp only [hGdef, hFrdef, hBddef, ENNReal.ofReal, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
      rw [← NNReal.coe_le_coe, NNReal.coe_mul, Real.coe_toNNReal _ hB00, coe_nnnorm, coe_nnnorm, mul_comm]
      exact h
    have hts : ∀ x, x * t⁻¹ ∈ W → x ∈ K' := by
      intro x hx
      obtain ⟨y, hyW, rfl⟩ : ∃ y ∈ W, y * t = x := ⟨x * t⁻¹, hx, by group⟩
      intro w i j
      have e : (((y * t) w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
          ((y w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
            ((t w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := rfl
      have := entry_mul_le (Wn_bdd y hyW w) (ht w) i j
      rw [← e] at this
      exact this
    calc ∫⁻ s in W, G (actL (ofS L N s) p) ∂d.μ ≤ ∫⁻ s in W, Bd * Fr (s * t) ∂d.μ :=
          setLIntegral_mono' hWm hpt
      _ = Bd * ∫⁻ s in W, Fr (s * t) ∂d.μ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ Bd * ∫⁻ x in K', Fr x ∂d.μ := mul_le_mul_right (right_trans_le d.μ W K' hWm hK'm t hts Fr) _
  have st5 : ∫⁻ p in K1, ∫⁻ s in W, G (actL (ofS L N s) p) ∂d.μ ∂μ ≤
      (Bd * ∫⁻ x in K', Fr x ∂d.μ) * μ K1 := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' hK1m st4
  have hall : (m0 * ∫⁻ p in K, G p ∂μ) * d.μ W ≤ (Bd * ∫⁻ x in K', Fr x ∂d.μ) * μ K1 :=
    st2.trans (st3.le.trans st5)
  have ha0 : m0 * d.μ W ≠ 0 := mul_ne_zero hm0 hW0
  have haT : m0 * d.μ W ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWT
  calc ∫⁻ p in K, G p ∂μ = (m0 * d.μ W)⁻¹ * ((m0 * d.μ W) * ∫⁻ p in K, G p ∂μ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 haT, one_mul]
    _ ≤ (m0 * d.μ W)⁻¹ * ((Bd * ∫⁻ x in K', Fr x ∂d.μ) * μ K1) := by
        refine mul_le_mul_right ?_ _
        calc (m0 * d.μ W) * ∫⁻ p in K, G p ∂μ = (m0 * ∫⁻ p in K, G p ∂μ) * d.μ W := by ring
          _ ≤ _ := hall
    _ = (m0 * d.μ W)⁻¹ * (Bd * μ K1) * ∫⁻ x in K', Fr x ∂d.μ := by ring

end PositivityTheory.KB.LocalOverlapAverage

end
end

section
noncomputable section

open NumberField Matrix UpperTheory.V.KT

namespace PositivityTheory.KB.LocalOverlapAverage

theorem discr_holds : Discr := by
  unfold Discr
  intro L _ _ N K hK
  have hc : Continuous (fun γ : Sp L N => fun (w : InfinitePlace L) (i j : Fin N) =>
      ((γ w : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) := by
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  set S : Set (𝓞 L) := {x | ∀ w : InfinitePlace L, ‖w.embedding (x : L)‖ ≤ C} with hS
  have hSfin : S.Finite := by
    have h0 := Embeddings.finite_of_norm_le L ℂ C
    refine (h0.preimage (Set.injOn_of_injective (f := fun x : 𝓞 L => (x : L))
      RingOfIntegers.coe_injective)).subset ?_
    intro x hx
    refine ⟨RingOfIntegers.isIntegral_coe x, fun φ => ?_⟩
    have h1 := hx (InfinitePlace.mk φ)
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply] at h1
    exact h1
  have hT : (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => S).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hSfin
  have hU : {A : Matrix.SpecialLinearGroup (Fin N) (𝓞 L) |
      (A : Matrix (Fin N) (Fin N) (𝓞 L)) ∈ Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => S}.Finite :=
    hT.preimage (Set.injOn_of_injective Subtype.val_injective)
  refine (hU.image (MonoidHom.pi fun w => Matrix.SpecialLinearGroup.map (embO w))).subset ?_
  rintro γ ⟨⟨A, rfl⟩, hγK⟩
  refine ⟨A, ?_, rfl⟩
  intro i _ j _ w
  have h2 := hC _ hγK
  have h3 : ‖(fun (w : InfinitePlace L) (i j : Fin N) =>
      ((((MonoidHom.pi fun w => Matrix.SpecialLinearGroup.map (embO w)) A) w :
        Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) w i j‖ ≤ C :=
    (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans ((norm_le_pi_norm _ w).trans h2))
  exact h3

end PositivityTheory.KB.LocalOverlapAverage

end
end

section
noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace PositivityTheory.KB.LocalOverlapAverage

theorem overlapG_holds : OverlapG := by
  intro G _ _ _ _ _ _ Γ _ μ _ D hD hfin K hK
  have hT : IsCompact (K * K⁻¹) := hK.mul hK.inv
  have hF := hfin (K * K⁻¹) hT
  refine ⟨hF.toFinset.card, ?_⟩
  intro f hf hinv
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hsum : ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G)
      ≤ (hF.toFinset.card : ℝ≥0∞) := by
    calc ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G)
        = ∑' γ : Γ, {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹}.indicator (fun _ => (1 : ℝ≥0∞)) (γ : G) := by
          refine tsum_congr fun γ => ?_
          by_cases h : (γ : G) ∈ K * K⁻¹
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show (γ : G) ∈ {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹} from ⟨γ.2, h⟩)]
          · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show (γ : G) ∉ {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹} from fun h' => h h'.2)]
      _ ≤ ∑' g : G, {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹}.indicator (fun _ => (1 : ℝ≥0∞)) g :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
      _ = ∑ g ∈ hF.toFinset, {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹}.indicator (fun _ => (1 : ℝ≥0∞)) g := by
          refine tsum_eq_sum fun g hg => ?_
          rw [Set.Finite.mem_toFinset] at hg
          exact Set.indicator_of_notMem hg _
      _ ≤ ∑ _g ∈ hF.toFinset, (1 : ℝ≥0∞) := by
          refine Finset.sum_le_sum fun g _ => ?_
          unfold Set.indicator
          split_ifs <;> simp
      _ = (hF.toFinset.card : ℝ≥0∞) := by simp
  have hcount : ∀ x : G, ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)
      ≤ (hF.toFinset.card : ℝ≥0∞) := by
    intro x
    by_cases hS : ∃ γ₀ : Γ, γ₀ • x ∈ K
    · obtain ⟨γ₀, h₀⟩ := hS
      calc ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)
          ≤ ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) ((γ * γ₀⁻¹ : Γ) : G) := by
            refine ENNReal.tsum_le_tsum fun γ => ?_
            by_cases hγ : γ • x ∈ K
            · have hmem : ((γ * γ₀⁻¹ : Γ) : G) ∈ K * K⁻¹ := by
                refine ⟨γ • x, hγ, (γ₀ • x)⁻¹, by rw [Set.mem_inv, inv_inv]; exact h₀, ?_⟩
                simp [Subgroup.smul_def, mul_assoc]
              rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hmem]
            · rw [Set.indicator_of_notMem hγ]
              simp
        _ = ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G) :=
            (Equiv.mulRight γ₀⁻¹).tsum_eq (fun γ : Γ => (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G))
        _ ≤ _ := hsum
    · push_neg at hS
      calc ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) = ∑' _γ : Γ, (0 : ℝ≥0∞) :=
            tsum_congr fun γ => Set.indicator_of_notMem (hS γ) _
        _ ≤ _ := by simp
  have hpt : ∀ γ : Γ, ∀ x : G, K.indicator f (γ • x)
      = K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x := by
    intro γ x
    by_cases hx : γ • x ∈ K
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
      simpa [Subgroup.smul_def] using hinv γ γ.2 x
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have hmeas : ∀ γ : Γ, Measurable fun x : G => K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x :=
    fun γ => ((measurable_const.indicator hKm).comp (measurable_const_smul γ)).mul hf
  calc ∫⁻ x in K, f x ∂μ = ∑' γ : Γ, ∫⁻ x in D, K.indicator f (γ • x) ∂μ := by
        rw [← lintegral_indicator hKm]
        exact hD.lintegral_eq_tsum'' _
    _ = ∑' γ : Γ, ∫⁻ x in D, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x ∂μ := by
        simp_rw [hpt]
    _ = ∫⁻ x in D, ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x ∂μ :=
        (lintegral_tsum fun γ => (hmeas γ).aemeasurable).symm
    _ = ∫⁻ x in D, (∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)) * f x ∂μ := by
        simp_rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ x in D, (hF.toFinset.card : ℝ≥0∞) * f x ∂μ :=
        lintegral_mono fun x => by gcongr; exact hcount x
    _ = (hF.toFinset.card : ℝ≥0∞) * ∫⁻ x in D, f x ∂μ := lintegral_const_mul _ hf

end PositivityTheory.KB.LocalOverlapAverage

end
end

section
noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.LocalOverlapAverage

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

def actEq (x : Gp L N) : HS L N ≃L[ℝ] HS L N where
  toLinearEquiv :=
    { toFun := actL x
      invFun := actL x⁻¹
      map_add' := (actL x).map_add
      map_smul' := (actL x).map_smul
      left_inv := fun h => by rw [← actL_mul, inv_mul_cancel, actL_one]
      right_inv := fun h => by rw [← actL_mul, mul_inv_cancel, actL_one] }
  continuous_toFun := (actL x).continuous
  continuous_invFun := (actL x⁻¹).continuous

@[simp] theorem actEq_apply (x : Gp L N) (h : HS L N) : actEq x h = actL x h := rfl

theorem pos_convex : Convex ℝ (Pos L N) := by
  intro h hh k hk a b ha hb hab w
  rw [mat_add, mat_smul, mat_smul]
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    subst hab
    simpa using hk w
  · exact ((hh w).smul ha').add_posSemidef ((hk w).posSemidef.smul hb)

theorem kset_sub {q : ℕ} (x : Fin (q + 1) → Gp L N) {B : Set (HS L N)} (hB : B ⊆ Pos L N) :
    Kset (fun j => actL (x j)) B ⊆ Pos L N := by
  rintro p ⟨τ, hτ0, hτ1, y, hy, rfl⟩
  exact pos_convex.sum_mem (fun j _ => hτ0 j) hτ1 fun j _ => actL_pos (x j) (hB (hy j))

theorem isCompact_kset {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ℕ}
    (A : Fin (q + 1) → V →L[ℝ] V) {B : Set V} (hB : IsCompact B) : IsCompact (Kset A B) := by
  have hc : IsCompact ((stdSimplex ℝ (Fin (q + 1))) ×ˢ (Set.univ.pi fun _ : Fin (q + 1) => B)) :=
    IsCompact.prod (isCompact_stdSimplex ℝ (Fin (q + 1))) (isCompact_univ_pi fun _ => hB)
  have hcont : Continuous fun p : (Fin (q + 1) → ℝ) × (Fin (q + 1) → V) =>
      ∑ j, p.1 j • A j (p.2 j) := by fun_prop
  have e : Kset A B = (fun p : (Fin (q + 1) → ℝ) × (Fin (q + 1) → V) =>
      ∑ j, p.1 j • A j (p.2 j)) '' ((stdSimplex ℝ (Fin (q + 1))) ×ˢ (Set.univ.pi fun _ : Fin (q + 1) => B)) := by
    ext p
    constructor
    · rintro ⟨τ, hτ0, hτ1, y, hy, rfl⟩
      exact ⟨(τ, y), ⟨⟨hτ0, hτ1⟩, fun j _ => hy j⟩, rfl⟩
    · rintro ⟨⟨τ, y⟩, ⟨⟨hτ0, hτ1⟩, hy⟩, rfl⟩
      exact ⟨τ, hτ0, hτ1, y, fun j => hy j (Set.mem_univ _), rfl⟩
  rw [e]
  exact hc.image hcont

theorem simplex_pos {q : ℕ} (y : Fin (q + 1) → HS L N) (hy : ∀ j, y j ∈ Pos L N) (t : Fin q → ℝ)
    (ht : (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1) : y 0 + ∑ j, t j • (y j.succ - y 0) ∈ Pos L N := by
  have e : y 0 + ∑ j, t j • (y j.succ - y 0) =
      ∑ i, (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i • y i := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul, one_smul,
      ← Finset.sum_smul]
    abel
  rw [e]
  refine pos_convex.sum_mem (fun i _ => ?_) ?_ fun i _ => hy i
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      linarith [ht.2]
    · simpa only [Fin.cons_succ] using ht.1 j
  · rw [Fin.sum_univ_succ]
    simp

theorem measurableSet_simplex (q : ℕ) :
    MeasurableSet {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} := by
  have : {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} =
      (⋂ j, {t : Fin q → ℝ | 0 ≤ t j}) ∩ {t | ∑ j, t j ≤ 1} := by
    ext t
    simp
  rw [this]
  refine (IsClosed.inter (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j))
    (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)).measurableSet

theorem intP_inv {q : ℕ} (ω : Form (HS L N) q) (g : Gp L N) (hg : FInv ω g)
    (y : Fin (q + 1) → Pos L N) : intP ω (fun j => g • y j) = intP ω y := by
  simp only [intP, intS]
  refine setIntegral_congr_fun (measurableSet_simplex q) fun t ht => ?_
  have hv : ∀ j, ((g • y j : Pos L N) : HS L N) = actL g (y j).1 := fun j => rfl
  simp only [hv, ← map_sub, ← map_smul, ← map_sum, ← map_add]
  have hp := simplex_pos (fun j => (y j).1) (fun j => (y j).2) t ht
  have := congrArg (fun f => f (fun j => (y j.succ).1 - (y 0).1)) (hg _ hp)
  simpa [Function.comp_def, map_sub] using this

theorem cont_actL_apply (v : HS L N) : Continuous fun x : Gp L N => actL x v := by
  refine continuous_induced_rng.2 ?_
  change Continuous fun x : Gp L N => fun w i j =>
    ((((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ * mat v w *
      ((x w)⁻¹ : GL (Fin N) ℂ)) i j
  refine continuous_pi fun w => continuous_pi fun i => continuous_pi fun j => ?_
  have hi : Continuous fun x : Gp L N => (((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) :=
    Units.continuous_coe_inv.comp (continuous_apply w)
  exact ((hi.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hi).matrix_elem i j

theorem cont_actL : Continuous fun x : Gp L N => actL x :=
  continuous_clm_apply.2 fun v => cont_actL_apply v

theorem cont_fr {q : ℕ} (ω : Form (HS L N) q) (hω : ContinuousOn ω (Pos L N)) :
    Continuous (fr ω) := by
  have h1 : Continuous fun x : Gp L N => ω (actL x (one L N).1) :=
    hω.comp_continuous (cont_actL_apply _) fun x => actL_pos x (one L N).2
  exact (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp cont_actL).clm_apply h1

theorem cont_ofS : Continuous (ofS L N) :=
  continuous_pi fun w => Matrix.SpecialLinearGroup.continuous_toGL.comp (continuous_apply w)

theorem fr_mul {q : ℕ} (ω : Form (HS L N) q) (g x : Gp L N) (hg : FInv ω g) :
    fr ω (g * x) = fr ω x := by
  ext v
  have h := congrArg (fun f => f (fun i => actL x (v i))) (hg _ (actL_pos x (one L N).2))
  simpa [fr, actL_mul, Function.comp_def] using h

theorem ofS_lat {γ : Sp L N} (hγ : γ ∈ latS L N) : ∃ A : Gm L N, ofS L N γ = emb L N A := by
  obtain ⟨A, rfl⟩ := hγ
  refine ⟨Matrix.SpecialLinearGroup.toGL A, ?_⟩
  funext w
  ext i j
  rfl

theorem ball_pos : ∃ r : ℝ, 0 < r ∧ Metric.closedBall (one L N).1 r ⊆ Pos L N := by
  classical
  obtain ⟨c, hc, hev⟩ := UpperTheory.V.KT.lowbd L N (one L N).1 (one L N).2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε / 2, half_pos hε, fun k hk w => ?_⟩
  have hk' := hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hk) (half_lt_self hε))
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨mat_herm k w, fun x hx => ?_⟩
  let z : VR L N := Pi.single w x
  have hz : z ≠ 0 := fun h => hx (by simpa [z] using congrFun h w)
  have h1 := hk' z
  have h2 : qR k z = (star x ⬝ᵥ (mat k w *ᵥ x)).re := by
    simp only [qR, z]
    rw [Finset.sum_eq_single w]
    · simp
    · intro v _ hv
      simp [Pi.single_eq_of_ne hv]
    · simp
  have h3 : 0 < c * ‖z‖ ^ 2 := by
    have : 0 < ‖z‖ := norm_pos_iff.2 hz
    positivity
  rw [Complex.lt_def]
  refine ⟨by simp only [Complex.zero_re]; linarith, ?_⟩
  have h4 := (mat_herm k w).im_star_dotProduct_mulVec_self x
  simp only [Complex.zero_im]
  exact h4.symm

end PositivityTheory.KB.LocalOverlapAverage

end
end

section
noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped ENNReal NNReal

namespace PositivityTheory.KB.LocalOverlapAverage

theorem cs_bound {α : Type} [MeasurableSpace α] (μ : Measure α) (K : Set α) (f : α → ℝ≥0∞)
    (hf : AEMeasurable f (μ.restrict K)) :
    ∫⁻ x in K, f x ∂μ ≤ (∫⁻ x in K, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (μ K) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict K) Real.HolderConjugate.two_two hf
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simpa [ENNReal.rpow_two, Measure.restrict_apply_univ] using h

theorem ofReal_norm_sq {E : Type} [NormedAddCommGroup E] (v : E) :
    ENNReal.ofReal (‖v‖ ^ 2) = (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg v)]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]

instance countable_O (L : Type) [Field L] [NumberField L] : Countable (𝓞 L) :=
  (RingOfIntegers.basis L).equivFun.toEquiv.injective.countable

instance countable_SL (L : Type) [Field L] [NumberField L] (N : ℕ) :
    Countable (Matrix.SpecialLinearGroup (Fin N) (𝓞 L)) :=
  @Function.Injective.countable _ (Fin N → Fin N → 𝓞 L) _
    (fun A : Matrix.SpecialLinearGroup (Fin N) (𝓞 L) => ((A : Matrix (Fin N) (Fin N) (𝓞 L)) : Fin N → Fin N → 𝓞 L))
    Subtype.val_injective

instance countable_latS (L : Type) [Field L] [NumberField L] (N : ℕ) : Countable (latS L N) := by
  unfold latS
  exact (MonoidHom.rangeRestrict_surjective _).countable

private theorem integral_abs_intS_actL_le_mul_sqrt_integral (hS : SimpBd) (hU : Unfold) (hDi : Discr) (hO : OverlapG)
    {L : Type} [Field L] [NumberField L] {N k : ℕ} (hN : 1 ≤ N) (d : Dom L N)
    (μ : Measure (HS L N)) [μ.IsAddHaarMeasure] (B : Set (HS L N)) (hB : IsCompact B)
    (hBP : B ⊆ Pos L N) (h : Fin (k + 2) → Gp L N) :
    ∃ C : ℝ, ∀ ω : Form (HS L N) (k + 1), ContinuousOn ω (Pos L N) →
      (∀ γ : Gm L N, FInv ω (emb L N γ)) → (∀ s : InfinitePlace L → ℂˣ, FInv ω (scal L N s)) →
      IntegrableOn (fun x : Sp L N => ‖fr ω (ofS L N x)‖ ^ 2) d.D d.μ →
      ∫ y : Fin (k + 2) → HS L N, |intS ω (fun j => actL (h j) (y j))|
          ∂(Measure.pi fun _ => nrm μ B)
        ≤ C * √(∫ x in d.D, ‖fr ω (ofS L N x)‖ ^ 2 ∂d.μ) := by
  obtain ⟨C₁, hC₁⟩ := hS (HS L N) μ (k + 1) (fun j => actEq (h j)) B hB
  have hKeq : Kset (fun j => ((actEq (h j) : HS L N ≃L[ℝ] HS L N) : HS L N →L[ℝ] HS L N)) B
      = Kset (fun j => actL (h j)) B := by
    congr 1
  have hKP : Kset (fun j => actL (h j)) B ⊆ Pos L N := kset_sub h hBP
  have hKc : IsCompact (Kset (fun j => actL (h j)) B) := isCompact_kset _ hB
  obtain ⟨C₂, K', hC₂, hK'c, hC₂b⟩ := hU L N (k + 1) hN d μ _ hKc hKP
  haveI := d.haar
  obtain ⟨M, hM⟩ := hO (Sp L N) (latS L N) d.μ d.D d.fund (hDi L N) K' hK'c
  refine ⟨max C₁ 0 * C₂.toReal * M * ((d.μ d.D) ^ (1 / 2 : ℝ)).toReal, ?_⟩
  intro ω hωc hΓ hsc hint
  have hωK : ContinuousOn ω (Kset (fun j => actL (h j)) B) := hωc.mono hKP
  obtain ⟨-, hbd⟩ := hC₁ ω (hKeq ▸ hωK)
  rw [hKeq] at hbd
  simp only [actEq_apply] at hbd
  have hfc : Continuous fun x : Sp L N => fr ω (ofS L N x) := (cont_fr ω hωc).comp cont_ofS
  set f : Sp L N → ℝ≥0∞ := fun x => (‖fr ω (ofS L N x)‖₊ : ℝ≥0∞) with hf
  have hfm : Measurable f := (ENNReal.continuous_coe.comp hfc.nnnorm).measurable
  have hfinv : ∀ γ ∈ latS L N, ∀ x : Sp L N, f (γ * x) = f x := by
    intro γ hγ x
    obtain ⟨A, hA⟩ := ofS_lat hγ
    simp only [hf, map_mul, hA, fr_mul ω _ _ (hΓ A)]
  have hOv := hM f hfm hfinv
  have hUn := hC₂b ω hωc hsc
  have hcs := cs_bound d.μ d.D f hfm.aemeasurable
  have hsq : ∫⁻ x in d.D, f x ^ 2 ∂d.μ
      = ENNReal.ofReal (∫ x in d.D, ‖fr ω (ofS L N x)‖ ^ 2 ∂d.μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => by positivity)]
    congr 1
    funext x
    rw [ofReal_norm_sq]
  set I := ∫ x in d.D, ‖fr ω (ofS L N x)‖ ^ 2 ∂d.μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
  have hμD : d.μ d.D ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) d.fin.ne
  have hchain : ENNReal.ofReal (∫ y : Fin (k + 2) → HS L N, |intS ω (fun j => actL (h j) (y j))|
        ∂(Measure.pi fun _ => nrm μ B))
      ≤ ENNReal.ofReal (max C₁ 0) * (C₂ * (M * (ENNReal.ofReal I ^ (1 / 2 : ℝ)
          * d.μ d.D ^ (1 / 2 : ℝ)))) := by
    calc _ ≤ _ := hbd
      _ ≤ ENNReal.ofReal (max C₁ 0) * (C₂ * ∫⁻ x in K', f x ∂d.μ) := by
        gcongr
        exact le_max_left _ _
      _ ≤ ENNReal.ofReal (max C₁ 0) * (C₂ * (M * ∫⁻ x in d.D, f x ∂d.μ)) := by
        gcongr
      _ ≤ _ := by
        gcongr
        rw [← hsq]
        exact hcs
  have hR : ENNReal.ofReal (max C₁ 0) * (C₂ * (M * (ENNReal.ofReal I ^ (1 / 2 : ℝ)
          * d.μ d.D ^ (1 / 2 : ℝ))))
      = ENNReal.ofReal (max C₁ 0 * C₂.toReal * M * ((d.μ d.D) ^ (1 / 2 : ℝ)).toReal * √I) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hI0 (by norm_num), ← Real.sqrt_eq_rpow]
    rw [ENNReal.ofReal_mul, ENNReal.ofReal_mul, ENNReal.ofReal_mul, ENNReal.ofReal_mul,
      ENNReal.ofReal_toReal hC₂, ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hμD]
    · ring
    all_goals positivity
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (hchain.trans_eq hR)

theorem sLoc_of_parts (hA : AvgS) (hS : SimpBd) (hU : Unfold) (hDi : Discr) (hO : OverlapG) : SLoc := by
  intro L _ _ N k hN d z hz
  classical
  obtain ⟨r, hr, hrP⟩ := ball_pos (L := L) (N := N)
  set B : Set (HS L N) := Metric.closedBall ((one L N : HS L N)) r with hBdef
  have hB : IsCompact B := isCompact_closedBall _ _
  set μ : Measure (HS L N) := Measure.addHaar with hμ
  have hμB0 : μ B ≠ 0 := (Metric.measure_closedBall_pos μ _ hr).ne'
  have hμBt : μ B ≠ ⊤ := hB.measure_lt_top.ne
  haveI hP : IsProbabilityMeasure (nrm μ B) :=
    ⟨by simp [nrm, ENNReal.inv_mul_cancel hμB0 hμBt]⟩
  have h1B : ((one L N : HS L N)) ∈ B := Metric.mem_closedBall_self hr.le
  let e : HS L N → ↑(Pos L N) := fun x => if hx : x ∈ Pos L N then ⟨x, hx⟩ else one L N
  have hcoe : ∀ x ∈ Pos L N, ((e x : ↑(Pos L N)) : HS L N) = x := by
    intro x hx
    simp [e, hx]
  have hae : ∀ᵐ x ∂(Measure.pi fun _ : Fin (k + 2) => nrm μ B), ∀ j, x j ∈ B := by
    rw [Filter.eventually_all]
    intro j
    have h0 : ∀ᵐ y ∂(nrm μ B), y ∈ B := by
      unfold nrm
      exact Measure.ae_smul_measure (ae_restrict_mem hB.measurableSet) _
    exact (Measure.tendsto_eval_ae_ae (i := j)).eventually h0
  have hKeq : ∀ h : Fin (k + 2) → Gp L N,
      Kset (fun j => ((actEq (h j) : HS L N ≃L[ℝ] HS L N) : HS L N →L[ℝ] HS L N)) B
        = Kset (fun j => actL (h j)) B := by
    intro h
    congr 1
  choose C hC using fun g : Fin (k + 1) → Gm L N =>
    integral_abs_intS_actL_le_mul_sqrt_integral hS hU hDi hO hN d μ B hB hrP (fun j => emb L N (Fin.partialProd g j))
  refine ⟨∑ g ∈ z.support, |z g| * C g, ?_⟩
  intro ω hgood hΓ hsc hint
  have hInv : Inv (emb L N) (intP ω) := fun g y => intP_inv ω (emb L N g) (hΓ g) y
  have hintg : ∀ (h : Fin (k + 2) → Gp L N) (b : Fin (k + 2) → Bool),
      Integrable (fun x : Fin (k + 2) → HS L N =>
        intP ω fun j => h j • if b j = true then e (x j) else one L N)
        (Measure.pi fun _ => nrm μ B) := by
    intro h b
    obtain ⟨C₁, hC₁⟩ := hS (HS L N) μ (k + 1) (fun j => actEq (h j)) B hB
    obtain ⟨hi, -⟩ := hC₁ ω ((hKeq h) ▸ hgood.1.mono (kset_sub h hrP))
    refine (hi b _ h1B).congr ?_
    filter_upwards [hae] with x hx
    show intS ω _ = intS ω _
    congr 1
    funext j
    rw [actEq_apply]
    show _ = actL (h j) ((if b j = true then e (x j) else one L N : ↑(Pos L N)) : HS L N)
    by_cases hb : b j = true
    · simp only [hb, if_true, hcoe _ (hrP (hx j))]
    · simp only [hb]
      rfl
  have hev := hA (Gm L N) (Gp L N) ↑(Pos L N) (HS L N) (emb L N) k (intP ω) (nrm μ B) e
    (one L N) hInv hgood.2 hintg z hz
  rw [hev]
  have key : ∀ g : Fin (k + 1) → Gm L N,
      |∫ x : Fin (k + 2) → HS L N, intP ω (fun j => emb L N (Fin.partialProd g j) • e (x j))
          ∂(Measure.pi fun _ => nrm μ B)|
        ≤ C g * √(∫ x in d.D, ‖fr ω (ofS L N x)‖ ^ 2 ∂d.μ) := by
    intro g
    calc _ ≤ ∫ x : Fin (k + 2) → HS L N,
          |intP ω (fun j => emb L N (Fin.partialProd g j) • e (x j))|
          ∂(Measure.pi fun _ => nrm μ B) := abs_integral_le_integral_abs
      _ = ∫ y : Fin (k + 2) → HS L N,
          |intS ω (fun j => actL (emb L N (Fin.partialProd g j)) (y j))|
          ∂(Measure.pi fun _ => nrm μ B) := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with x hx
        show |intS ω _| = |intS ω _|
        congr 2
        funext j
        show actL _ ((e (x j) : ↑(Pos L N)) : HS L N) = _
        rw [hcoe _ (hrP (hx j))]
      _ ≤ _ := hC g ω hgood.1 hΓ hsc hint
  unfold Finsupp.sum
  calc _ ≤ ∑ g ∈ z.support, |z g * ∫ x : Fin (k + 2) → HS L N,
          intP ω (fun j => emb L N (Fin.partialProd g j) • e (x j))
          ∂(Measure.pi fun _ => nrm μ B)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ g ∈ z.support, |z g| * (C g * √(∫ x in d.D, ‖fr ω (ofS L N x)‖ ^ 2 ∂d.μ)) := by
      gcongr with g hg
      rw [abs_mul]
      gcongr
      exact key g
    _ = _ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      ring

end PositivityTheory.KB.LocalOverlapAverage

end
end

section
namespace PositivityTheory.KB

theorem sLoc_of (hEv : SEv) : SLoc :=
  LocalOverlapAverage.sLoc_of_parts (LocalOverlapAverage.avgS_of hEv) LocalOverlapAverage.simpBd_holds LocalOverlapAverage.unfold_holds
    LocalOverlapAverage.discr_holds LocalOverlapAverage.overlapG_holds

end PositivityTheory.KB
end
