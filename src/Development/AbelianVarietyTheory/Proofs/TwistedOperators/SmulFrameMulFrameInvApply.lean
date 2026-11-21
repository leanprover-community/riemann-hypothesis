import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NabsDetEqOfActEq
import BuildAid.ForwardExisting

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical

namespace GlobalTheory.IdealChain

theorem pi_nnreal_smul {ι X : Type} [Fintype ι] [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (c : NNReal) :
    (Measure.pi fun _ : ι => c • μ) = (c ^ Fintype.card ι) • Measure.pi fun _ : ι => μ := by
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi]
  simp only [Measure.coe_nnreal_smul_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ENNReal.coe_pow]

theorem integral_scale_change_haar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ι : Type) [Fintype ι] (ν νs : Measure k) (d : ι → kˣ), ν.IsAddHaarMeasure → νs.IsAddHaarMeasure → ∃ C : ℝ, (0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k (νs (𝒪[k] : Set k)).toReal → IsHalfPow k C)) ∧ ∀ F : (ι → k) → ℂ, ∫ e, F e ∂(Measure.pi fun _ => ν) = C * ∫ e, F (fun i => (d i : k) * e i) ∂(Measure.pi fun _ => νs) := by
  intro k _ _ _ _ _ _ ι _ ν νs d hν hνs
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨a, ha0, ha⟩ : ∃ a : NNReal, 0 < a ∧ ν = a • νs :=
    ⟨_, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν νs, Measure.isAddLeftInvariant_eq_smul ν νs⟩
  let g : GL ι k := ⟨Matrix.diagonal fun i => (d i : k), Matrix.diagonal fun i => ((d i)⁻¹ : kˣ),
    by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩
  have hpos := nabs_pos' (Matrix.GeneralLinearGroup.det g)
  refine ⟨(a : ℝ) ^ Fintype.card ι * nabs k (Matrix.GeneralLinearGroup.det g),
    ⟨mul_pos (pow_pos ha0 _) hpos, fun h1 h2 => isHalfPow_mul (isHalfPow_pow ?_ _) (isHalfPow_nabs _)⟩, fun F => ?_⟩
  · have h3 : (νs (𝒪[k] : Set k)).toReal ≠ 0 := by
      obtain ⟨e, he⟩ := h2
      rw [he]
      exact (Real.rpow_pos_of_pos resCard_pos _).ne'
    have h4 : (a : ℝ) = (ν (𝒪[k] : Set k)).toReal * ((νs (𝒪[k] : Set k)).toReal)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ h3, ha, Measure.coe_nnreal_smul_apply, ENNReal.toReal_mul, ENNReal.coe_toReal]
    rw [h4]
    exact isHalfPow_mul h1 (isHalfPow_inv h2)
  · have h := integral_comp_mulVec_eq_smul νs g F
    have h2 : ∀ x : ι → k, g.val.mulVec x = fun i => (d i : k) * x i := by
      intro x; funext i; simp [g, Matrix.mulVec_diagonal]
    simp only [h2] at h
    have h5 : (Measure.pi fun _ : ι => ν) = (a ^ Fintype.card ι) • Measure.pi fun _ : ι => νs := by
      rw [← pi_nnreal_smul, ← ha]
    rw [h, h5, integral_smul_nnreal_measure]
    have : (nabs k (Matrix.GeneralLinearGroup.det g) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [Complex.real_smul, NNReal.smul_def, Complex.real_smul]
    push_cast
    field_simp

end GlobalTheory.IdealChain
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_pi_change_constant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ι : Type) [Fintype ι] (ν νs : Measure k) (d : ι → kˣ), ν.IsAddHaarMeasure → νs.IsAddHaarMeasure → ∃ C : ℝ, (0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k (νs (𝒪[k] : Set k)).toReal → IsHalfPow k C)) ∧ ∀ F : (ι → k) → ℂ, ∫ e, F e ∂(Measure.pi fun _ => ν) = C * ∫ e, F (fun i => (d i : k) * e i) ∂(Measure.pi fun _ => νs) := by
  atlas_forward_decl GlobalTheory.IdealChain.integral_scale_change_haar
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical

namespace GlobalTheory.IdealChain

theorem smul_frame_mul_frame_inv_apply {k : Type} [Field k]
    {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ} (a : k) (b b' : ℕ → kˣ)
    (y : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (r : n ⊕ Fin c) (s : n' ⊕ Fin c') :
    (a • ((frame n c b).val * y * ((frame n' c' b')⁻¹).val)) r s =
      a * Sum.elim (fun _ : n => (1 : k)) (fun i : Fin c => (b (i.val + 1) : k)) r *
        Sum.elim (fun _ : n' => (1 : k)) (fun i : Fin c' => (b' (i.val + 1) : k)⁻¹) s * y r s := by
  have h1 : (frame n c b).val =
      Matrix.diagonal (Sum.elim (fun _ : n => (1 : k)) (fun i : Fin c => (b (i.val + 1) : k))) := by
    rw [← Matrix.fromBlocks_diagonal]; rfl
  have h2 : ((frame n' c' b')⁻¹).val =
      Matrix.diagonal (Sum.elim (fun _ : n' => (1 : k)) (fun i : Fin c' => (b' (i.val + 1) : k)⁻¹)) := by
    rw [← Matrix.fromBlocks_diagonal]
    simp only [← Units.val_inv_eq_inv_val]
    rfl
  rw [h1, h2, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul]
  ring

theorem opE_rescale_frame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (α β₀ : kˣ) (b' : ℕ → kˣ) (ν νs : Measure k), (∀ i, 1 ≤ i → i ≤ c → b' i / b' (i + 1) = β₀) → ν.IsAddHaarMeasure → νs.IsAddHaarMeasure → ∃ C : ℝ, (0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k (νs (𝒪[k] : Set k)).toReal → IsHalfPow k C)) ∧ ∀ (ψ : AddChar k Circle) (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix n n' k), opE ψ ν p Ψ x = C * opE (ψ.mulShift (β₀ : k)) νs p (fun y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => Ψ ((α : k) • ((frame n c fun i => α⁻¹ * b' i).val * y * ((frame n' (c + 1) b')⁻¹).val))) (((α⁻¹ : kˣ) : k) • x) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p α β₀ b' ν νs hb hν hνs
  let d : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → kˣ := fun rs =>
    α * Sum.elim (fun _ : n => 1) (fun i : Fin c => α⁻¹ * b' (i.val + 1)) rs.1.1 *
      (Sum.elim (fun _ : n' => 1) (fun i : Fin (c + 1) => b' (i.val + 1)) rs.1.2)⁻¹
  obtain ⟨C, hC, hF⟩ := @GlobalTheory.T.haar_measure_pi_change_constant k _ _ _ _ _ _ _ (@Subtype.fintype _ _ (Classical.decPred _) _) ν νs d hν hνs
  refine ⟨C, hC, fun ψ Ψ x => ?_⟩
  unfold opE
  rw [hF]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  dsimp only
  congr 1
  · congr 1
    ext r q
    rw [smul_frame_mul_frame_inv_apply]
    by_cases h : Free p (r, q)
    · rcases r with r | r <;> rcases q with q | q
      · exact absurd h (by simp [Free])
      · simp [affPt, basePt, h, d]
      · simp [affPt, basePt, h, d]
      · have : r.val ≠ q.val := by simp only [Free] at h; omega
        simp [affPt, basePt, h, d, this]
    · rcases r with r | r <;> rcases q with q | q
      · simp [affPt, basePt, h]
      · simp [affPt, basePt, h]
      · simp [affPt, basePt, h]
      · by_cases h' : r.val = q.val <;> simp [affPt, basePt, h, h']
  · rw [AddChar.mulShift_apply, mul_neg]
    congr 3
    unfold ch
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : Free (n := n) (n' := n') p (Sum.inr i, Sum.inr i.succ) := by simp [Free]
    rw [← hb (i.val + 1) (by omega) (by omega)]
    simp [affPt, basePt, h, d, div_eq_mul_inv]

end GlobalTheory.IdealChain
end
