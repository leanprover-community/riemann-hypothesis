import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.HpkMulVecMulVec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.OneLeGN

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Dec

open Formalism.QuantumDeterminants

theorem one_le_gN (k r : ℕ) (g : Mat k r) (hg : g ∈ UH (Hpk k r)) : 1 ≤ Formalism.FourierDecayAlt.B.gN g :=
  DecA.one_le_gN' hg

theorem gN_inv (k r : ℕ) (g : Mat k r) (hg : g ∈ UH (Hpk k r)) :
    Formalism.FourierDecayAlt.B.gN g⁻¹ = Formalism.FourierDecayAlt.B.gN g :=
  DecA.gN_inv' hg

theorem gN_mul_le (k r : ℕ) (a b : Mat k r) : Formalism.FourierDecayAlt.B.gN (a * b) ≤ Formalism.FourierDecayAlt.B.gN a * Formalism.FourierDecayAlt.B.gN b :=
  DecA.gN_mul_le' a b

theorem pair_bound (k r : ℕ) (a : ℝ) (ha : 0 ≤ a) (y g : Mat k r) (hy : y ∈ UH (Hpk k r))
    (hg : g ∈ UH (Hpk k r)) :
    Formalism.FourierDecayAlt.B.gN g ^ (-a) * Formalism.FourierDecayAlt.B.gN (y * g) ^ (-a) ≤
      Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4)) * (Formalism.FourierDecayAlt.B.gN g ^ (-(a / 2)) + Formalism.FourierDecayAlt.B.gN (y * g) ^ (-(a / 2))) := by
  have hA := DecA.one_le_gN' hg
  have hB := DecA.one_le_gN' (DecA.mul_mem hy hg)
  have hY := DecA.one_le_gN' hy
  have hYBA := DecA.gN_le_mul (y := y) hg
  have hAh : 0 ≤ Formalism.FourierDecayAlt.B.gN g ^ (-(a / 2)) := Real.rpow_nonneg (by linarith) _
  have hBh : 0 ≤ Formalism.FourierDecayAlt.B.gN (y * g) ^ (-(a / 2)) := Real.rpow_nonneg (by linarith) _
  have hYq : 0 ≤ Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4)) := Real.rpow_nonneg (by linarith) _
  rcases le_total (Formalism.FourierDecayAlt.B.gN g) (Formalism.FourierDecayAlt.B.gN (y * g)) with h | h
  · calc _ ≤ Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4)) * Formalism.FourierDecayAlt.B.gN (y * g) ^ (-(a / 2)) :=
          DecA.pb_real a _ _ _ ha hA hB (by linarith) hYBA h
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hAh) hYq
  · have := DecA.pb_real a (Formalism.FourierDecayAlt.B.gN (y * g)) (Formalism.FourierDecayAlt.B.gN g) (Formalism.FourierDecayAlt.B.gN y) ha hB hA (by linarith)
      (by rw [mul_comm]; exact hYBA) h
    rw [mul_comm] at this
    calc _ ≤ Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4)) * Formalism.FourierDecayAlt.B.gN g ^ (-(a / 2)) := this
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hBh) hYq

theorem of_cont (k r : ℕ) : Continuous (fun g : Mt k r => (Matrix.of g : Mat k r)) :=
  continuous_matrix fun i j => by
    simp only [Matrix.of_apply]; exact (continuous_apply j).comp (continuous_apply i)

theorem gN_cont (k r : ℕ) : Continuous (fun M : Mat k r => Formalism.FourierDecayAlt.B.gN M) := by
  unfold Formalism.FourierDecayAlt.B.gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp (continuous_id.matrix_elem i j))

theorem lmulM_cont {k r : ℕ} (s : Mat k r) : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) s) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Formalism.QuantumDeterminants.lmulM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun l _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply l))


theorem UW_inv_mem {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWset k r z := by
  obtain ⟨hU, hfix, hz⟩ := hh
  have hinv : h⁻¹ * h = 1 := DecA.inv_mul hU
  have key : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v := fun v hv => by
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  exact ⟨DecA.inv_mem hU, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩

theorem UH_closed (k r : ℕ) : IsClosed (UH (Hpk k r) : Set (Mat k r)) :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem UW_closed (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  have e : UWset k r z = UH (Hpk k r) ∩ ((⋂ a : Fin r, ({g : Mat k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
      {g | g *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {g | g *ᵥ z = z}) := by
    ext g; simp only [UWset, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  exact (UH_closed k r).inter ((isClosed_iInter fun a =>
    (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
      (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)).inter
    (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const))

theorem psiGen_cont (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (fun M : Mat k r => Formalism.MainNotions.S.psiGen k r z c M) := by
  have hell : ∀ a : Fin r, Continuous (fun M : Mat k r => Formalism.MainNotions.S.ellA k r z M a) := by
    intro a
    by_cases h : a.val + 1 < r
    · have e : (fun M : Mat k r => Formalism.MainNotions.S.ellA k r z M a) =
          fun M : Mat k r => M (eI k r a) (eI k r ⟨a.val + 1, h⟩) :=
        funext fun M => by unfold Formalism.MainNotions.S.ellA; rw [dif_pos h]
      rw [e]; exact continuous_id.matrix_elem _ _
    · have e : (fun M : Mat k r => Formalism.MainNotions.S.ellA k r z M a) = fun M : Mat k r => ∑ j, M (eI k r a) j * z j :=
        funext fun M => by unfold Formalism.MainNotions.S.ellA; rw [dif_neg h]; rfl
      rw [e]; exact continuous_finsetSum _ fun j _ => (continuous_id.matrix_elem _ _).mul continuous_const
  unfold Formalism.MainNotions.S.psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_const.mul (hell a)))))

theorem product_bound_of_factor_bounds (D M1 M2 X P Q C : ℝ) (hD : 0 ≤ D) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hX : 0 ≤ X)
    (h1 : M1 ≤ C * P) (h2 : M2 ≤ C * Q) : D * M1 * (M2 * X) ≤ D * C ^ 2 * X * (P * Q) := by
  have := mul_le_mul h1 h2 hM2 (hM1.trans h1)
  calc D * M1 * (M2 * X) = (D * X) * (M1 * M2) := by ring
    _ ≤ (D * X) * ((C * P) * (C * Q)) := mul_le_mul_of_nonneg_left this (mul_nonneg hD hX)
    _ = _ := by ring

def Sg3 (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (x₀ x : Mat k r) : Set (Mt k r × (Mt k r × Mt k r)) :=
  {q | Matrix.of q.1 ∈ UH (Hpk k r) ∧ (Matrix.of q.2.1 ∈ UWset k r z ∧
    x₀⁻¹ * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * Matrix.of q.1 ∈ UH (Hpk k r))}



end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Dec
