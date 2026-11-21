import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.InGOne
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyEq
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyK
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyG
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulInverseCayley
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DpDual
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.HermRealSmul
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EventuallyIteratedFDerivEqZeroOfRealSubspace
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopComp
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IILeft
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.InfInvA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TsContinuousNU

section
namespace PositivityTheory.Rg.Sw.LVs

theorem cayley : Cayley := cayley_of equivar reindex kappaFin

end PositivityTheory.Rg.Sw.LVs
end

section
noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.HolA

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {Kg : Type*} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
  {μ : Measure Kg} [IsFiniteMeasure μ]

theorem integrable_of_cont {W : Type*} [NormedAddCommGroup W] {f : Kg → W} (hf : Continuous f) :
    Integrable f μ := by
  have hm : AEStronglyMeasurable f μ := by
    simpa using (hf.continuousOn (s := univ)).aestronglyMeasurable_of_isCompact isCompact_univ
      MeasurableSet.univ (μ := μ)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hf.continuousOn (s := univ))
  exact Integrable.of_bound hm C (Eventually.of_forall fun k => hC k (mem_univ k))

theorem hasFDerivAt_int {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    {Ω : Set E} (hΩ : IsOpen Ω) {Φ : Kg → E → W} {Φ' : Kg → E → (E →L[ℂ] W)}
    (hc : ContinuousOn (fun y : Kg × E => Φ y.1 y.2) (univ ×ˢ Ω))
    (hc' : ContinuousOn (fun y : Kg × E => Φ' y.1 y.2) (univ ×ˢ Ω))
    (hd : ∀ k, ∀ x ∈ Ω, HasFDerivAt (Φ k) (Φ' k x) x) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    HasFDerivAt (fun x => ∫ k, Φ k x ∂μ) (∫ k, Φ' k x₀ ∂μ) x₀ := by
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  have hsub : closedBall x₀ (r / 2) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hrΩ
  have hK : IsCompact ((univ : Set Kg) ×ˢ closedBall x₀ (r / 2)) := isCompact_univ.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc'.mono (prod_mono subset_rfl hsub))
  have cont_k : ∀ x ∈ Ω, Continuous fun k => Φ k x := fun x hx =>
    continuousOn_univ.mp (hc.comp (f := fun k : Kg => (k, x)) (Continuous.continuousOn (by fun_prop))
      fun k _ => ⟨mem_univ _, hx⟩)
  have cont_k' : ∀ x ∈ Ω, Continuous fun k => Φ' k x := fun x hx =>
    continuousOn_univ.mp (hc'.comp (f := fun k : Kg => (k, x)) (Continuous.continuousOn (by fun_prop))
      fun k _ => ⟨mem_univ _, hx⟩)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (F := fun x k => Φ k x)
    (F' := fun x k => Φ' k x) (bound := fun _ => C) (ball_mem_nhds x₀ (half_pos hr)) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hΩ.mem_nhds hx₀] with x hx
    exact (integrable_of_cont (cont_k x hx)).aestronglyMeasurable
  · exact integrable_of_cont (cont_k x₀ hx₀)
  · exact (integrable_of_cont (cont_k' x₀ hx₀)).aestronglyMeasurable
  · exact Eventually.of_forall fun k x hx => hC (k, x) ⟨mem_univ _, ball_subset_closedBall hx⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun k x hx => hd k x (hsub (ball_subset_closedBall hx))

end PositivityTheory.Rg.Sw.LVs.HolA
end
end

section
noncomputable section

open Filter Topology Set Metric Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.HolC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.HolB

variable {n : ℕ}

theorem span_top (W : Submodule ℂ (M2 n))
    (hu : ∀ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b → (fromBlocks 0 b 0 0 : M2 n) ∈ W)
    (hl : ∀ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c → (fromBlocks 0 0 c 0 : M2 n) ∈ W)
    (hbr : ∀ b c : Matrix (Fin n) (Fin n) ℂ, bᴴ = b → cᴴ = c → (fromBlocks (-(b * c)) 0 0 (c * b) : M2 n) ∈ W)
    (h1 : (1 : M2 n) ∈ W) : W = ⊤ := by

  have dec : ∀ B : Matrix (Fin n) (Fin n) ℂ, ∃ b₁ b₂ : Matrix (Fin n) (Fin n) ℂ, b₁ᴴ = b₁ ∧ b₂ᴴ = b₂ ∧
      B = b₁ + Complex.I • b₂ := by
    intro B
    have hI : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      rw [mul_neg, mul_div_assoc', Complex.I_mul_I]; norm_num
    refine ⟨(1 / 2 : ℂ) • (B + Bᴴ), (-(Complex.I / 2)) • (B - Bᴴ), ?_, ?_, ?_⟩
    · rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
      congr 1
      simp [Complex.ext_iff]
    · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
      rw [show (Bᴴ - B) = -(B - Bᴴ) by abel, smul_neg, ← neg_smul]
      congr 1
      simp [Complex.ext_iff]
      norm_num
    · rw [smul_smul, hI]
      module
  have hU : ∀ B, (fromBlocks 0 B 0 0 : M2 n) ∈ W := by
    intro B
    obtain ⟨b₁, b₂, h₁, h₂, rfl⟩ := dec B
    have : (fromBlocks 0 (b₁ + Complex.I • b₂) 0 0 : M2 n) =
        fromBlocks 0 b₁ 0 0 + Complex.I • fromBlocks 0 b₂ 0 0 := by
      simp [fromBlocks_smul, fromBlocks_add]
    rw [this]
    exact W.add_mem (hu b₁ h₁) (W.smul_mem _ (hu b₂ h₂))
  have hL : ∀ C, (fromBlocks 0 0 C 0 : M2 n) ∈ W := by
    intro C
    obtain ⟨c₁, c₂, h₁, h₂, rfl⟩ := dec C
    have : (fromBlocks 0 0 (c₁ + Complex.I • c₂) 0 : M2 n) =
        fromBlocks 0 0 c₁ 0 + Complex.I • fromBlocks 0 0 c₂ 0 := by
      simp [fromBlocks_smul, fromBlocks_add]
    rw [this]
    exact W.add_mem (hl c₁ h₁) (W.smul_mem _ (hl c₂ h₂))
  have hBr : ∀ B C : Matrix (Fin n) (Fin n) ℂ, (fromBlocks (-(B * C)) 0 0 (C * B) : M2 n) ∈ W := by
    intro B C
    obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := dec B
    obtain ⟨c₁, c₂, hc₁, hc₂, rfl⟩ := dec C
    have e : (fromBlocks (-((b₁ + Complex.I • b₂) * (c₁ + Complex.I • c₂))) 0 0
        ((c₁ + Complex.I • c₂) * (b₁ + Complex.I • b₂)) : M2 n) =
        fromBlocks (-(b₁ * c₁)) 0 0 (c₁ * b₁) + Complex.I • fromBlocks (-(b₁ * c₂)) 0 0 (c₂ * b₁) +
          Complex.I • fromBlocks (-(b₂ * c₁)) 0 0 (c₁ * b₂) + (-1 : ℂ) • fromBlocks (-(b₂ * c₂)) 0 0 (c₂ * b₂) := by
      simp only [fromBlocks_smul, fromBlocks_add, smul_zero, add_zero]
      congr 1
      · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
        match_scalars <;> first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq
      · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
        match_scalars <;> first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq
    rw [e]
    exact W.add_mem (W.add_mem (W.add_mem (hbr _ _ hb₁ hc₁) (W.smul_mem _ (hbr _ _ hb₁ hc₂)))
      (W.smul_mem _ (hbr _ _ hb₂ hc₁))) (W.smul_mem _ (hbr _ _ hb₂ hc₂))

  let ιA : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n :=
    { toFun := fun A => fromBlocks A 0 0 0
      map_add' := fun A B => by simp [fromBlocks_add]
      map_smul' := fun c A => by simp [fromBlocks_smul] }
  let ιD : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n :=
    { toFun := fun D => fromBlocks 0 0 0 D
      map_add' := fun A B => by simp [fromBlocks_add]
      map_smul' := fun c A => by simp [fromBlocks_smul] }
  have sgl : ∀ (a b : Fin n) (c : ℂ), Matrix.single a b c = c • Matrix.single a b (1 : ℂ) := by
    intro a b c; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have offA : ∀ a b : Fin n, a ≠ b → ιA (Matrix.single a b 1) ∈ W := by
    intro a b hab
    have h := hBr (Matrix.single a b 1) (Matrix.single b b 1)
    rw [Matrix.single_mul_single_of_ne (h := Ne.symm hab), Matrix.single_mul_single_same, mul_one] at h
    have : ιA (Matrix.single a b 1) = -(fromBlocks (-(Matrix.single a b (1 : ℂ))) 0 0 0 : M2 n) := by
      simp [ιA, fromBlocks_neg]
    rw [this]; exact W.neg_mem h
  have offD : ∀ a b : Fin n, a ≠ b → ιD (Matrix.single a b 1) ∈ W := by
    intro a b hab
    have h := hBr (Matrix.single b b 1) (Matrix.single a b 1)
    rw [Matrix.single_mul_single_of_ne (h := Ne.symm hab), Matrix.single_mul_single_same, mul_one] at h
    simpa [ιD] using h
  have dif : ∀ a k : Fin n, ιD (Matrix.single k k 1) - ιA (Matrix.single a a 1) ∈ W := by
    intro a k
    have h := hBr (Matrix.single a k 1) (Matrix.single k a 1)
    rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_one] at h
    have : ιD (Matrix.single k k 1) - ιA (Matrix.single a a 1) =
        (fromBlocks (-(Matrix.single a a (1 : ℂ))) 0 0 (Matrix.single k k 1) : M2 n) := by
      simp [ιA, ιD, sub_eq_add_neg, fromBlocks_add, fromBlocks_neg]
    rw [this]; exact h
  have one_sum : (∑ a : Fin n, Matrix.single a a (1 : ℂ)) = 1 := by
    ext i j
    rw [Matrix.sum_apply]
    by_cases h : i = j
    · subst h; simp [Matrix.single_apply]
    · simp [Matrix.single_apply, Matrix.one_apply, h]
  have hST : ∑ a, ιA (Matrix.single a a 1) + ∑ k, ιD (Matrix.single k k 1) ∈ W := by
    rw [← map_sum, ← map_sum, one_sum]
    have : ιA 1 + ιD 1 = (1 : M2 n) := by simp [ιA, ιD, fromBlocks_add, ← fromBlocks_one]
    rw [this]; exact h1
  have hTS : ∑ k, ιD (Matrix.single k k 1) - ∑ a, ιA (Matrix.single a a 1) ∈ W := by
    rw [← Finset.sum_sub_distrib]
    exact W.sum_mem fun k _ => dif k k
  have hT : ∑ k, ιD (Matrix.single k k 1) ∈ W := by
    have h2 := W.add_mem hST hTS
    have : ∑ k, ιD (Matrix.single k k 1) = (1 / 2 : ℂ) • ((∑ a, ιA (Matrix.single a a 1) +
        ∑ k, ιD (Matrix.single k k 1)) + (∑ k, ιD (Matrix.single k k 1) - ∑ a, ιA (Matrix.single a a 1))) := by
      module
    rw [this]; exact W.smul_mem _ h2
  have hS : ∑ a, ιA (Matrix.single a a 1) ∈ W := by
    have := W.sub_mem hST hT
    simpa using this
  have diagA : ∀ a : Fin n, ιA (Matrix.single a a 1) ∈ W := by
    intro a
    have hn : (Fintype.card (Fin n) : ℂ) ≠ 0 := by
      simp only [Fintype.card_fin, ne_eq, Nat.cast_eq_zero]; exact Fin.pos a |>.ne'
    have hdiff : ∀ b : Fin n, ιA (Matrix.single a a 1) - ιA (Matrix.single b b 1) ∈ W := by
      intro b
      have := W.sub_mem (dif b a) (dif a a)
      have e : ιD (Matrix.single a a 1) - ιA (Matrix.single b b 1) - (ιD (Matrix.single a a 1) -
          ιA (Matrix.single a a 1)) = ιA (Matrix.single a a 1) - ιA (Matrix.single b b 1) := by abel
      rwa [e] at this
    have hsum := W.add_mem (W.sum_mem fun b (_ : b ∈ Finset.univ) => hdiff b) hS
    have e : ∑ b, (ιA (Matrix.single a a 1) - ιA (Matrix.single b b 1)) + ∑ a, ιA (Matrix.single a a 1) =
        (Fintype.card (Fin n) : ℂ) • ιA (Matrix.single a a 1) := by
      rw [Finset.sum_sub_distrib, sub_add_cancel, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [e] at hsum
    have := W.smul_mem ((Fintype.card (Fin n) : ℂ)⁻¹) hsum
    rwa [smul_smul, inv_mul_cancel₀ hn, one_smul] at this
  have diagD : ∀ k : Fin n, ιD (Matrix.single k k 1) ∈ W := by
    intro k
    have := W.add_mem (dif k k) (diagA k)
    simpa using this
  have allA : ∀ A : Matrix (Fin n) (Fin n) ℂ, ιA A ∈ W := by
    intro A
    rw [Matrix.matrix_eq_sum_single A, map_sum]
    refine W.sum_mem fun i _ => ?_
    rw [map_sum]
    refine W.sum_mem fun j _ => ?_
    rw [sgl, map_smul]
    refine W.smul_mem _ ?_
    by_cases hij : i = j
    · subst hij; exact diagA i
    · exact offA i j hij
  have allD : ∀ D : Matrix (Fin n) (Fin n) ℂ, ιD D ∈ W := by
    intro D
    rw [Matrix.matrix_eq_sum_single D, map_sum]
    refine W.sum_mem fun i _ => ?_
    rw [map_sum]
    refine W.sum_mem fun j _ => ?_
    rw [sgl, map_smul]
    refine W.smul_mem _ ?_
    by_cases hij : i = j
    · subst hij; exact diagD i
    · exact offD i j hij
  rw [eq_top_iff]
  intro M _
  rw [← Matrix.fromBlocks_toBlocks M]
  have e : (fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ : M2 n) =
      ιA M.toBlocks₁₁ + fromBlocks 0 M.toBlocks₁₂ 0 0 + fromBlocks 0 0 M.toBlocks₂₁ 0 + ιD M.toBlocks₂₂ := by
    simp [ιA, ιD, fromBlocks_add]
  rw [e]
  exact W.add_mem (W.add_mem (W.add_mem (allA _) (hU _)) (hL _)) (allD _)

end PositivityTheory.Rg.Sw.LVs.HolC
end
end

section
noncomputable section

open Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.HolD

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem line2 {H : E → V} {y w : E} {m : E →L[ℂ] E} (hfd : DifferentiableAt ℂ (fderiv ℂ H) y)
    (hz : ∀ t : ℝ, fderiv ℂ H (y + (t : ℂ) • w) (m (y + (t : ℂ) • w)) = 0) :
    fderiv ℂ (fderiv ℂ H) y w (m y) + fderiv ℂ H y (m w) = 0 := by
  have hψ : HasFDerivAt (fun z => fderiv ℂ H z (m z))
      ((fderiv ℂ H y).comp m + (fderiv ℂ (fderiv ℂ H) y).flip (m y)) y :=
    hfd.hasFDerivAt.clm_apply m.hasFDerivAt
  have h := GlobalTheory.SCV.fderiv_apply_eq_zero_of_frequently hψ.differentiableAt (s := w)
    (GlobalTheory.SCV.frequently_nhdsNE_of_eventually_ofReal
      (p := fun t : ℂ => fderiv ℂ H (y + t • w) (m (y + t • w)) = fderiv ℂ H y (m y))
      (Eventually.of_forall fun t => by
        have h0 := hz 0
        simp only [Complex.ofReal_zero, zero_smul, add_zero] at h0
        rw [hz t, h0]))
  rw [hψ.fderiv] at h
  simpa [add_comm] using h

theorem scalar_dir {H : E → V} {y : E} (hd : DifferentiableAt ℂ H y)
    (h : ∀ t : ℝ, H (Complex.exp ((t : ℂ) * Complex.I) • y) = 0) : fderiv ℂ H y y = 0 := by
  have hγ := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp).smul_const y
  have hc := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hd.hasFDerivAt.restrictScalars ℝ) hγ (by simp)
  have hc0 := hc.congr_of_eventuallyEq (f₁ := fun _ : ℝ => (0 : V)) (Eventually.of_forall fun t => (h t).symm)
  have := hc0.unique (hasDerivAt_const (0 : ℝ) (0 : V))
  simp only [ContinuousLinearMap.coe_restrictScalars', id, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_mul, map_smul, Complex.ofReal_one] at this
  exact (smul_eq_zero.mp this).resolve_left Complex.I_ne_zero

end PositivityTheory.Rg.Sw.LVs.HolD
end
end

section
noncomputable section

open MeasureTheory Filter Topology Set Metric Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs.HolB PositivityTheory.Rg.Sw.LVs.HolC

variable {n : ℕ}

theorem two_le_infty : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

theorem det_ne_zero_of_inG {y : M2 n} (hy : InG y) : y.det ≠ 0 := by
  intro h
  have hJ : (JJ n).det ≠ 0 := by
    intro hJ
    have := congrArg Matrix.det (JJ_sq (n := n))
    rw [det_mul, hJ, mul_zero, det_neg, det_one] at this
    simp at this
  have := congrArg Matrix.det hy
  rw [det_mul, det_mul, h, mul_zero] at this
  exact hJ this.symm

theorem fderiv_eq_zero_of_vanish {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hG : GSet n ⊆ Ω) {H : M2 n → V} (hH : ContDiffOn ℂ ∞ H Ω)
    (h0 : ∀ g, InG g → H g = 0) {y : M2 n} (hy : InG y) : fderiv ℂ H y = 0 := by
  have hdiff : ∀ g, InG g → DifferentiableAt ℂ H g := fun g hg =>
    (hH.contDiffAt (hΩ.mem_nhds (hG hg))).differentiableAt (by simp)
  have hlow : ∀ g, InG g → ∀ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c →
      fderiv ℂ H g (g * fromBlocks 0 0 c 0) = 0 := by
    intro g hg c hc
    refine fderiv_line (hdiff g hg) (fun t => ?_)
    rw [lower_line, h0 _ (inG_mul hg (inG_lower (herm_real_smul hc t))), h0 g hg]
  have hup : ∀ g, InG g → ∀ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b →
      fderiv ℂ H g (g * fromBlocks 0 b 0 0) = 0 := by
    intro g hg b hb
    refine fderiv_line (hdiff g hg) (fun t => ?_)
    rw [upper_line, h0 _ (inG_mul hg (inG_upper (herm_real_smul hb t))), h0 g hg]
  have hone : fderiv ℂ H y (y * 1) = 0 := by
    rw [mul_one]
    refine HolD.scalar_dir (hdiff y hy) (fun t => h0 _ ?_)
    have e : Complex.exp (↑t * Complex.I) • y = y * (Complex.exp (↑t * Complex.I) • (1 : M2 n)) := by
      rw [mul_smul_comm, mul_one]
    rw [e]
    refine inG_mul hy (inG_scalar ?_)
    rw [Complex.star_def, Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]
    simp
  have hCy : ContDiffAt ℂ ∞ H y := hH.contDiffAt (hΩ.mem_nhds (hG hy))
  have hsymm : IsSymmSndFDerivAt ℂ H y :=
    hCy.isSymmSndFDerivAt (by simpa [minSmoothness_of_isRCLikeNormedField] using two_le_infty)
  have hD : DifferentiableAt ℂ (fderiv ℂ H) y :=
    (hCy.fderiv_right (m := 1) (by simpa [one_add_one_eq_two] using two_le_infty)).differentiableAt one_ne_zero
  have hcomm : ∀ b c : Matrix (Fin n) (Fin n) ℂ, bᴴ = b → cᴴ = c →
      fderiv ℂ H y (y * fromBlocks (-(b * c)) 0 0 (c * b)) = 0 := by
    intro b c hb hc
    set U : M2 n := fromBlocks 0 b 0 0 with hU
    set L : M2 n := fromBlocks 0 0 c 0 with hL
    let mL : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ L)
    let mU : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ U)
    have e1 := HolD.line2 (H := H) (y := y) (w := y * U) (m := mL) hD (fun t => by
      have hg := inG_mul hy (inG_upper (herm_real_smul hb t))
      show fderiv ℂ H _ ((y + (t : ℂ) • (y * U)) * L) = 0
      rw [upper_line]
      exact hlow _ hg c hc)
    have e2 := HolD.line2 (H := H) (y := y) (w := y * L) (m := mU) hD (fun t => by
      have hg := inG_mul hy (inG_lower (herm_real_smul hc t))
      show fderiv ℂ H _ ((y + (t : ℂ) • (y * L)) * U) = 0
      rw [lower_line]
      exact hup _ hg b hb)
    change fderiv ℂ (fderiv ℂ H) y (y * U) (y * L) + fderiv ℂ H y (y * U * L) = 0 at e1
    change fderiv ℂ (fderiv ℂ H) y (y * L) (y * U) + fderiv ℂ H y (y * L * U) = 0 at e2
    have key : fromBlocks (-(b * c)) 0 0 (c * b) = L * U - U * L := by
      simp only [hU, hL, Matrix.fromBlocks_multiply]
      rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
      simp
    rw [key, mul_sub, ← mul_assoc, ← mul_assoc, map_sub]
    have a1 := eq_neg_of_add_eq_zero_right e1
    have a2 := eq_neg_of_add_eq_zero_right e2
    have hs : fderiv ℂ (fderiv ℂ H) y (y * L) (y * U) = fderiv ℂ (fderiv ℂ H) y (y * U) (y * L) :=
      hsymm _ _
    rw [sub_eq_zero]
    exact a2.trans ((congrArg Neg.neg hs).trans a1.symm)
  let W : Submodule ℂ (M2 n) :=
    LinearMap.ker ((fderiv ℂ H y : M2 n →ₗ[ℂ] V) ∘ₗ LinearMap.mulLeft ℂ y)
  have hW : W = ⊤ :=
    span_top W (fun b hb => LinearMap.mem_ker.mpr (hup y hy b hb))
      (fun c hc => LinearMap.mem_ker.mpr (hlow y hy c hc))
      (fun b c hb hc => LinearMap.mem_ker.mpr (hcomm b c hb hc))
      (LinearMap.mem_ker.mpr hone)
  have hdet : IsUnit y.det := isUnit_iff_ne_zero.mpr (det_ne_zero_of_inG hy)
  ext u
  have hu : y⁻¹ * u ∈ W := hW ▸ Submodule.mem_top
  have e := LinearMap.mem_ker.mp hu
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    ContinuousLinearMap.coe_coe, Matrix.mul_nonsing_inv_cancel_left _ _ hdet] at e
  simpa using e

theorem nat_lt_infty (N : ℕ) : ((N : ℕ) : WithTop ℕ∞) < ∞ := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top N)

private theorem iteratedFDeriv_eq_zero_of_eq_zero_on_inG {n : ℕ} {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hG : GSet n ⊆ Ω) (N : ℕ) :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (H : M2 n → V),
      ContDiffOn ℂ ∞ H Ω → (∀ g, InG g → H g = 0) → ∀ g, InG g → iteratedFDeriv ℂ N H g = 0 := by
  induction N with
  | zero =>
    intro V _ _ _ H _ h0 g hg
    ext v
    simp [h0 g hg]
  | succ N ih =>
    intro V _ _ _ H hH h0 g hg
    have hH' := (contDiffOn_infty_iff_fderiv_of_isOpen hΩ).mp hH
    letI : NormedAddCommGroup (M2 n →L[ℂ] V) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℂ (M2 n →L[ℂ] V) := ContinuousLinearMap.toNormedSpace
    haveI : SequentialSpace (M2 n) :=
      inferInstanceAs (SequentialSpace ((Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ))
    haveI : @CompleteSpace (M2 n →L[ℂ] V) PseudoMetricSpace.toUniformSpace :=
      ContinuousLinearMap.instCompleteSpace
    have e : iteratedFDeriv ℂ N (fun y => fderiv ℂ H y) g = 0 :=
      ih (fun y => fderiv ℂ H y) hH'.2 (fun g' hg' => fderiv_eq_zero_of_vanish hΩ hG hH h0 hg') g hg
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
    have e' := congrArg (continuousMultilinearCurryRightEquiv' ℂ N (M2 n) V).symm e
    exact e'.trans (map_zero _)

theorem holZero : HolZero := by
  intro n Ω F hΩ hG hF h0 N g hg
  exact iteratedFDeriv_eq_zero_of_eq_zero_on_inG hΩ hG N F hF (fun g hg => h0 g hg) g hg

private theorem contDiffOn_integral_and_iteratedFDeriv_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] {Ω : Set E} (F : Kg → E → ℂ) (hΩ : IsOpen Ω)
    (hcont : ∀ N : ℕ, ContinuousOn (fun y : Kg × E => iteratedFDeriv ℂ N (F y.1) y.2) (univ ×ˢ Ω))
    (hF : ∀ k, ContDiffOn ℂ ∞ (F k) Ω) :
    ContDiffOn ℂ ∞ (fun x => ∫ k, F k x ∂μ) Ω ∧ ∀ (N : ℕ) (x : E) (v : Fin N → E), x ∈ Ω →
      iteratedFDeriv ℂ N (fun x => ∫ k, F k x ∂μ) x v = ∫ k, iteratedFDeriv ℂ N (F k) x v ∂μ := by
  have hFd : ∀ k, ∀ x ∈ Ω, ContDiffAt ℂ ∞ (F k) x := fun k x hx =>
    (hF k).contDiffAt (hΩ.mem_nhds hx)
  have hA : ∀ N : ℕ, ∀ x ∈ Ω, HasFDerivAt (fun x => ∫ k, iteratedFDeriv ℂ N (F k) x ∂μ)
      (∫ k, fderiv ℂ (iteratedFDeriv ℂ N (F k)) x ∂μ) x := by
    intro N x hx
    refine HolA.hasFDerivAt_int hΩ (hcont N) ?_ ?_ hx
    · have e : (fun y : Kg × E => fderiv ℂ (iteratedFDeriv ℂ N (F y.1)) y.2) =
          fun y => continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ
            (iteratedFDeriv ℂ (N + 1) (F y.1) y.2) := by
        funext y
        rw [fderiv_iteratedFDeriv]
        rfl
      rw [e]
      exact (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ).continuous.comp_continuousOn
        (hcont (N + 1))
    · intro k x hx
      exact ((hFd k x hx).differentiableAt_iteratedFDeriv (by simpa using nat_lt_infty N)).hasFDerivAt
  have hB : ∀ N : ℕ, ∀ x ∈ Ω, iteratedFDeriv ℂ N (fun x => ∫ k, F k x ∂μ) x =
      ∫ k, iteratedFDeriv ℂ N (F k) x ∂μ := by
    intro N
    induction N with
    | zero =>
      intro x _
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℂ E ℂ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
    | succ N ih =>
      intro x hx
      have hev : iteratedFDeriv ℂ N (fun x => ∫ k, F k x ∂μ) =ᶠ[𝓝 x]
          fun x => ∫ k, iteratedFDeriv ℂ N (F k) x ∂μ :=
        Filter.eventually_of_mem (hΩ.mem_nhds hx) ih
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hev.fderiv_eq, (hA N x hx).fderiv]
      exact ((continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ).symm.toContinuousLinearEquiv.integral_comp_comm
        (fun k => fderiv ℂ (iteratedFDeriv ℂ N (F k)) x)).symm
  have hD : ∀ m : ℕ, DifferentiableOn ℂ (fun x => iteratedFDerivWithin ℂ m (fun x => ∫ k, F k x ∂μ) Ω x) Ω :=
    fun m x hx => ((hA m x hx).differentiableAt.differentiableWithinAt).congr
      (fun y hy => (iteratedFDerivWithin_of_isOpen m hΩ hy).trans (hB m y hy))
      ((iteratedFDerivWithin_of_isOpen m hΩ hx).trans (hB m x hx))
  refine ⟨contDiffOn_of_continuousOn_differentiableOn (n := ⊤) (fun m _ => (hD m).continuousOn)
    (fun m _ => hD m), ?_⟩
  intro N x v hx
  rw [hB N x hx]
  have hint : Integrable (fun k => iteratedFDeriv ℂ N (F k) x) μ :=
    HolA.integrable_of_cont ((hcont N).comp_continuous (continuous_id.prodMk continuous_const)
      (fun k => ⟨mem_univ _, hx⟩))
  exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin N => E) ℂ v).integral_comp_comm hint).symm

theorem holInt : HolInt := by
  intro n Kg _ _ _ _ μ _ Ω F hΩ hcont hF
  exact contDiffOn_integral_and_iteratedFDeriv_integral μ F hΩ hcont hF

end PositivityTheory.Rg.Sw.LVs
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw

namespace STD

variable {n : ℕ}

abbrev Vr (n : ℕ) := Fin n → Fin n → ℝ

def hermLin (n : ℕ) : Vr n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := herm
  map_add' x y := by
    ext i j
    simp only [herm, Pi.add_apply, Matrix.add_apply]
    push_cast
    ring
  map_smul' c x := by
    ext i j
    simp only [herm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Matrix.smul_apply, Complex.real_smul]
    push_cast
    ring

def hermL (n : ℕ) : Vr n →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap (hermLin n)

theorem hermL_apply (x : Vr n) : hermL n x = herm x := rfl

theorem herm_zero : herm (0 : Vr n) = 0 := by
  ext i j; simp [herm]

def v1 (r c : Fin n) : Vr n := fun i j =>
  ((if i = r ∧ j = c then 1 else 0) + (if i = c ∧ j = r then 1 else 0)) / 2

def v2 (r c : Fin n) : Vr n := fun i j =>
  ((if i = c ∧ j = r then 1 else 0) - (if i = r ∧ j = c then 1 else 0)) / 2

theorem herm_v (r c : Fin n) : herm (v1 r c) + Complex.I • herm (v2 r c) = Matrix.single r c 1 := by
  ext i j
  have e1 : (if j = r ∧ i = c then (1:ℝ) else 0) = if i = c ∧ j = r then 1 else 0 := by
    simp only [and_comm]
  have e2 : (if j = c ∧ i = r then (1:ℝ) else 0) = if i = r ∧ j = c then 1 else 0 := by
    simp only [and_comm]
  have e3 : (Matrix.single r c (1:ℂ)) i j = (((if i = r ∧ j = c then (1:ℝ) else 0 : ℝ)) : ℂ) := by
    rw [Matrix.single_apply]
    by_cases h : i = r ∧ j = c
    · obtain ⟨rfl, rfl⟩ := h; simp
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]; simp
  rw [e3]
  simp only [herm, v1, v2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, e1, e2]
  generalize (if i = r ∧ j = c then (1:ℝ) else 0) = a
  generalize (if i = c ∧ j = r then (1:ℝ) else 0) = b
  push_cast
  linear_combination ((b:ℂ) - a) / 2 * Complex.I_sq

def dc (a : Fin n × Fin n) (f : Vr n → ℂ) : Vr n → ℂ :=
  fun x => fderiv ℝ f x (v1 a.1 a.2) + Complex.I * fderiv ℝ f x (v2 a.1 a.2)

def dList : List (Fin n × Fin n) → (Vr n → ℂ) → Vr n → ℂ
  | [], f => f
  | a :: l, f => dc a (dList l f)

end STD

end PositivityTheory.Rg.Sw.LVs
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace STD

variable {n : ℕ}

theorem contDiffOn_dc {U : Set (Vr n)} (hU : IsOpen U) {f : Vr n → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    (a : Fin n × Fin n) : ContDiffOn ℝ ∞ (dc a f) U := by
  have h1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x) U := hf.fderiv_of_isOpen hU (by simp)
  exact (h1.clm_apply contDiffOn_const).add (contDiffOn_const.mul (h1.clm_apply contDiffOn_const))

theorem contDiffOn_dList {U : Set (Vr n)} (hU : IsOpen U) {f : Vr n → ℂ} (hf : ContDiffOn ℝ ∞ f U) :
    ∀ l : List (Fin n × Fin n), ContDiffOn ℝ ∞ (dList l f) U
  | [] => hf
  | a :: l => contDiffOn_dc hU (contDiffOn_dList hU hf l) a

structure IsT (U : Set (Vr n)) (φ : Vr n → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  cpt : HasCompactSupport φ
  sub : tsupport φ ⊆ U

theorem support_dc_subset (f : Vr n → ℂ) (a : Fin n × Fin n) : support (dc a f) ⊆ tsupport f := by
  intro x hx
  by_contra h
  apply hx
  have : fderiv ℝ f x = 0 := by
    by_contra h'
    exact h (support_fderiv_subset (𝕜 := ℝ) h')
  simp [dc, this]

theorem isT_dc {U : Set (Vr n)} {φ : Vr n → ℂ} (h : IsT U φ) (a : Fin n × Fin n) : IsT U (dc a φ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact contDiffOn_univ.mp (contDiffOn_dc isOpen_univ (contDiffOn_univ.mpr h.smooth) a)
  · exact h.cpt.mono' (support_dc_subset φ a)
  · exact (closure_minimal (support_dc_subset φ a) (isClosed_tsupport φ)).trans h.sub

theorem isT_dList {U : Set (Vr n)} {φ : Vr n → ℂ} (h : IsT U φ) : ∀ l : List (Fin n × Fin n), IsT U (dList l φ)
  | [] => h
  | a :: l => isT_dc (isT_dList h l) a

theorem tsupport_dList_subset (φ : Vr n → ℂ) : ∀ l : List (Fin n × Fin n), tsupport (dList l φ) ⊆ tsupport φ
  | [] => le_rfl
  | a :: l => (closure_minimal ((support_dc_subset _ a).trans (tsupport_dList_subset φ l))
      (isClosed_tsupport φ))

theorem integrable_mul_of_contOn {U : Set (Vr n)} (hU : IsOpen U) {h φ : Vr n → ℂ} (hh : ContinuousOn h U)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    Integrable (fun x => h x * φ x) := by
  have hc' : Continuous (fun x => h x * φ x) :=
    (hh.mul hφ.continuousOn).continuous_of_tsupport_subset hU ((tsupport_mul_subset_right).trans hs)
  exact hc'.integrable_of_hasCompactSupport hc.mul_left

theorem ibp_dc {U : Set (Vr n)} (hU : IsOpen U) {F φ : Vr n → ℂ} (hF : ContDiffOn ℝ ∞ F U)
    (hφ : IsT U φ) (a : Fin n × Fin n) :
    ∫ x, F x * dc a φ x = - ∫ x, dc a F x * φ x := by
  have hFd : ∀ x ∈ tsupport φ, DifferentiableAt ℝ F x := fun x hx =>
    (hF.contDiffAt (hU.mem_nhds (hφ.sub hx))).differentiableAt (by simp)
  have hφd : ∀ x ∈ tsupport F, DifferentiableAt ℝ φ x := fun x _ =>
    (hφ.smooth.differentiable (by simp)) x
  have hFc : ContinuousOn (fun x => fderiv ℝ F x) U := hF.continuousOn_fderiv_of_isOpen hU (by simp)
  have hφc : Continuous (fun x => fderiv ℝ φ x) := hφ.smooth.continuous_fderiv (by simp)
  have hA : ∀ v : Vr n, Integrable (fun x => fderiv ℝ F x v * φ x) := fun v =>
    integrable_mul_of_contOn hU (hFc.clm_apply continuousOn_const) hφ.smooth.continuous hφ.cpt hφ.sub
  have hB : ∀ v : Vr n, Integrable (fun x => F x * fderiv ℝ φ x v) := fun v =>
    integrable_mul_of_contOn hU hF.continuousOn (hφc.clm_apply continuous_const)
      (hφ.cpt.fderiv_apply ℝ v)
      ((closure_minimal (fun x hx => support_fderiv_subset ℝ
        (fun h0 => (Function.mem_support.mp hx) (by simp [h0])))
        (isClosed_tsupport φ)).trans hφ.sub)
  have key : ∀ v : Vr n, ∫ x, F x * fderiv ℝ φ x v = - ∫ x, fderiv ℝ F x v * φ x := fun v =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hA v) (hB v)
      (integrable_mul_of_contOn hU hF.continuousOn hφ.smooth.continuous hφ.cpt hφ.sub) hFd hφd
  have e1 : ∫ x, F x * dc a φ x
      = (∫ x, F x * fderiv ℝ φ x (v1 a.1 a.2)) + Complex.I * ∫ x, F x * fderiv ℝ φ x (v2 a.1 a.2) := by
    rw [← integral_const_mul, ← integral_add (hB _) ((hB _).const_mul _)]
    congr 1
    funext x
    simp only [dc]
    ring
  have e2 : ∫ x, dc a F x * φ x
      = (∫ x, fderiv ℝ F x (v1 a.1 a.2) * φ x) + Complex.I * ∫ x, fderiv ℝ F x (v2 a.1 a.2) * φ x := by
    rw [← integral_const_mul, ← integral_add (hA _) ((hA _).const_mul _)]
    congr 1
    funext x
    simp only [dc]
    ring
  rw [e1, e2, key, key]
  ring

theorem ibp_dList {U : Set (Vr n)} (hU : IsOpen U) :
    ∀ (l : List (Fin n × Fin n)) {F φ : Vr n → ℂ}, ContDiffOn ℝ ∞ F U → IsT U φ →
      ∫ x, F x * dList l φ x = (-1) ^ l.length * ∫ x, dList l.reverse F x * φ x := by
  intro l
  match l with
  | [] => intro F φ _ _; simp [dList]
  | a :: l =>
    intro F φ hF hφ
    have happ : ∀ (l m : List (Fin n × Fin n)) (f : Vr n → ℂ), dList (l ++ m) f = dList l (dList m f) := by
      intro l m f
      induction l with
      | nil => simp [dList]
      | cons b l ih => simp [dList, ih]
    have h1 := ibp_dc hU hF (isT_dList hφ l) a
    have h2 := ibp_dList hU l (contDiffOn_dc hU hF a) hφ
    rw [dList, h1, h2, List.reverse_cons, happ]
    simp only [dList, List.length_cons, pow_succ]
    ring

end STD

end PositivityTheory.Rg.Sw.LVs
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw

namespace STD

variable {n : ℕ}

theorem dc_comp {Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ} {x : Vr n} (hΨ : DifferentiableAt ℂ Ψ (herm x))
    (a : Fin n × Fin n) :
    dc a (fun y => Ψ (herm y)) x = fderiv ℂ Ψ (herm x) (Matrix.single a.1 a.2 1) := by
  have hd : HasFDerivAt (fun y => Ψ (hermL n y)) (((fderiv ℂ Ψ (herm x)).restrictScalars ℝ).comp (hermL n)) x :=
    (hΨ.hasFDerivAt.restrictScalars ℝ).comp x (hermL n).hasFDerivAt
  have hf : fderiv ℝ (fun y => Ψ (herm y)) x = ((fderiv ℂ Ψ (herm x)).restrictScalars ℝ).comp (hermL n) :=
    hd.fderiv
  simp only [dc, hf, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', hermL_apply]
  rw [← herm_v, map_add, map_smul, smul_eq_mul]

theorem dList_ofFn {r : ℝ} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hG : ContDiffOn ℂ ∞ G (Metric.ball 0 r)) :
    ∀ (k : ℕ) (m : Fin k → Fin n × Fin n) (x : Vr n), herm x ∈ Metric.ball 0 r →
      dList (List.ofFn m) (fun y => G (herm y)) x =
        iteratedFDeriv ℂ k G (herm x) (fun i => Matrix.single (m i).1 (m i).2 1)
  | 0, m, x, _ => by simp [dList]
  | k + 1, m, x, hx => by
    have hU : IsOpen ((hermL n) ⁻¹' Metric.ball 0 r) := Metric.isOpen_ball.preimage (hermL n).continuous
    set V : Fin k → Matrix (Fin n) (Fin n) ℂ := fun i => Matrix.single (m i.succ).1 (m i.succ).2 1 with hV
    set Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ := fun H => iteratedFDeriv ℂ k G H V with hΨ
    have hIt : DifferentiableOn ℂ (fun H => iteratedFDeriv ℂ k G H) (Metric.ball 0 r) := by
      have := hG.differentiableOn_iteratedFDerivWithin (m := k) (by exact_mod_cast ENat.natCast_lt_top k)
        Metric.isOpen_ball.uniqueDiffOn
      exact this.congr (fun H hH => (iteratedFDerivWithin_of_isOpen k Metric.isOpen_ball hH).symm)
    have hA : HasFDerivAt (fun H => iteratedFDeriv ℂ k G H)
        (fderiv ℂ (fun H => iteratedFDeriv ℂ k G H) (herm x)) (herm x) :=
      ((hIt _ hx).differentiableAt (Metric.isOpen_ball.mem_nhds hx)).hasFDerivAt
    have hΨ' := (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => Matrix (Fin n) (Fin n) ℂ) ℂ V).hasFDerivAt.comp
      (herm x) hA
    have hΨd : DifferentiableAt ℂ Ψ (herm x) := hΨ'.differentiableAt
    have heq : dList (List.ofFn fun i : Fin k => m i.succ) (fun y => G (herm y)) =ᶠ[𝓝 x] fun y => Ψ (herm y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact dList_ofFn hG k (fun i => m i.succ) y hy
    rw [List.ofFn_succ]
    simp only [dList]
    have h1 : dc (m 0) (dList (List.ofFn fun i : Fin k => m i.succ) (fun y => G (herm y))) x =
        dc (m 0) (fun y => Ψ (herm y)) x := by
      simp only [dc, heq.fderiv_eq]
    rw [h1, dc_comp hΨd]
    rw [iteratedFDeriv_succ_apply_left, show fderiv ℂ Ψ (herm x) = _ from hΨ'.fderiv]
    rfl

end STD

end PositivityTheory.Rg.Sw.LVs
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw

namespace STD

variable {n : ℕ}

def ell (β : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((2 * Real.pi * Complex.I) • ((Matrix.traceLinearMap (Fin n) ℂ ℂ).comp (LinearMap.mulLeft ℂ β)))

theorem ell_apply (β H : Matrix (Fin n) (Fin n) ℂ) : ell β H = 2 * Real.pi * Complex.I * (β * H).trace := by
  simp [ell]

theorem eTr_eq (β : Matrix (Fin n) (Fin n) ℂ) (x : Vr n) : eTr β x = Complex.exp (ell β (herm x)) := by
  simp [eTr, ell_apply]

theorem trace_mul_single' (β : Matrix (Fin n) (Fin n) ℂ) (r c : Fin n) :
    (β * Matrix.single r c 1).trace = β c r := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem dList_exp (β : Matrix (Fin n) (Fin n) ℂ) :
    ∀ (l : List (Fin n × Fin n)) (c : ℂ) (x : Vr n),
      dList l (fun y => c * Complex.exp (ell β (herm y))) x =
        c * (l.map fun a => ell β (Matrix.single a.1 a.2 1)).prod * Complex.exp (ell β (herm x))
  | [], c, x => by simp [dList]
  | a :: l, c, x => by
    have h : dList l (fun y => c * Complex.exp (ell β (herm y))) =
        fun y => (c * (l.map fun a => ell β (Matrix.single a.1 a.2 1)).prod) * Complex.exp (ell β (herm y)) := by
      funext y; rw [dList_exp β l c y]
    simp only [dList]
    rw [h]
    set c' := c * (l.map fun a => ell β (Matrix.single a.1 a.2 1)).prod
    have hd : HasFDerivAt (fun H => c' * Complex.exp (ell β H))
        (c' • (Complex.exp (ell β (herm x)) • ell β)) (herm x) :=
      ((ell β).hasFDerivAt.cexp).const_mul c'
    rw [dc_comp hd.differentiableAt, hd.fderiv]
    simp only [_root_.smul_apply, smul_eq_mul, List.map_cons, List.prod_cons, c']
    ring

def ml (σ : Equiv.Perm (Fin n)) : Fin (Fintype.card (Fin n)) → Fin n × Fin n :=
  fun i => ((Fintype.equivFin (Fin n)).symm i, σ ((Fintype.equivFin (Fin n)).symm i))

theorem sum_sign_prod_ell (β : Matrix (Fin n) (Fin n) ℂ) :
    ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      ((List.ofFn (ml σ)).map fun a => ell β (Matrix.single a.1 a.2 1)).prod =
      (2 * Real.pi * Complex.I) ^ Fintype.card (Fin n) * β.det := by
  rw [Matrix.det_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply, ml, ell_apply, trace_mul_single', Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show (∏ i : Fin (Fintype.card (Fin n)), β (σ ((Fintype.equivFin (Fin n)).symm i))
      ((Fintype.equivFin (Fin n)).symm i)) = ∏ a : Fin n, β (σ a) a from
    Fintype.prod_equiv (Fintype.equivFin (Fin n)).symm _ _ (fun _ => rfl)]
  rw [Units.smul_def, zsmul_eq_mul]
  push_cast
  ring

theorem fourier_test (β : Matrix (Fin n) (Fin n) ℂ) (hdet : β.det = 0) {φ : Vr n → ℂ} (hφ : IsT Set.univ φ) :
    ∫ x, (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * dList (List.ofFn (ml σ)).reverse φ x) * eTr β x = 0 := by
  set E : Vr n → ℂ := fun y => 1 * Complex.exp (ell β (herm y)) with hE
  have hEs : ContDiffOn ℝ ∞ E Set.univ := by
    refine (contDiff_const.mul ?_).contDiffOn
    exact Complex.contDiff_exp.comp (((ell β).restrictScalars ℝ).contDiff.comp (hermL n).contDiff)
  have hT : ∀ σ : Equiv.Perm (Fin n), IsT Set.univ (dList (List.ofFn (ml σ)).reverse φ) := fun σ => isT_dList hφ _
  have hint : ∀ σ : Equiv.Perm (Fin n), Integrable (fun x => E x * dList (List.ofFn (ml σ)).reverse φ x) :=
    fun σ => integrable_mul_of_contOn isOpen_univ hEs.continuousOn (hT σ).smooth.continuous (hT σ).cpt
      (Set.subset_univ _)
  have h1 : (fun x => (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * dList (List.ofFn (ml σ)).reverse φ x) *
      eTr β x) = fun x => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
        (E x * dList (List.ofFn (ml σ)).reverse φ x) := by
    funext x; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun σ _ => ?_; rw [eTr_eq]; simp only [E]; ring
  rw [h1, integral_finsetSum _ (fun σ _ => (hint σ).const_mul _)]
  have h2 : ∀ σ : Equiv.Perm (Fin n), ∫ x, (Equiv.Perm.sign σ : ℂ) * (E x * dList (List.ofFn (ml σ)).reverse φ x) =
      (Equiv.Perm.sign σ : ℂ) * ((-1) ^ Fintype.card (Fin n) *
        (((List.ofFn (ml σ)).map fun a => ell β (Matrix.single a.1 a.2 1)).prod *
          ∫ x, Complex.exp (ell β (herm x)) * φ x)) := by
    intro σ
    rw [integral_const_mul, ibp_dList isOpen_univ _ hEs hφ, List.reverse_reverse, List.length_reverse,
      List.length_ofFn]
    congr 2
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [E]
    rw [dList_exp β _ 1 x]
    ring
  rw [Finset.sum_congr rfl (fun σ _ => h2 σ)]
  have h3 : ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * ((-1) ^ Fintype.card (Fin n) *
        (((List.ofFn (ml σ)).map fun a => ell β (Matrix.single a.1 a.2 1)).prod *
          ∫ x, Complex.exp (ell β (herm x)) * φ x)) =
      (-1) ^ Fintype.card (Fin n) * (∫ x, Complex.exp (ell β (herm x)) * φ x) *
        ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
          ((List.ofFn (ml σ)).map fun a => ell β (Matrix.single a.1 a.2 1)).prod := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun σ _ => ?_; ring
  rw [h3, sum_sign_prod_ell, hdet]
  ring

end STD

open STD in
theorem singToDiff : SingToDiff := by
  intro n G r hr hG hyp
  classical
  set U : Set (Vr n) := (hermL n) ⁻¹' Metric.ball 0 r with hUdef
  have hU : IsOpen U := Metric.isOpen_ball.preimage (hermL n).continuous
  have h0U : (0 : Vr n) ∈ U := by simp [U, hermL_apply, herm_zero, hr]
  set F : Vr n → ℂ := fun y => G (herm y) with hFdef
  have hF : ContDiffOn ℝ ∞ F U :=
    (hG.restrict_scalars ℝ).comp (hermL n).contDiff.contDiffOn (fun y hy => hy)
  let H : Vr n → ℂ := fun x => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * dList (List.ofFn (ml σ)) F x
  have hHU : ContinuousOn H U := by
    refine continuousOn_finsetSum _ fun σ _ => continuousOn_const.mul ?_
    exact (contDiffOn_dList hU hF _).continuousOn
  have hH0 : H 0 = detD G := by
    simp only [H, detD]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [dList_ofFn hG _ (ml σ) 0 (by simpa [herm_zero] using hr), herm_zero]
    rfl
  obtain ⟨ε0, hε0, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
  have key : ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : ContDiffBump (0 : Vr n), b.rOut = ε →
      ∫ x, H x * ((b.normed volume x : ℝ) : ℂ) = 0 := by
    intro ε hε hεε b hb
    set φ : Vr n → ℂ := fun x => ((b.normed volume x : ℝ) : ℂ) with hφdef
    have hφsup : tsupport φ ⊆ Metric.closedBall 0 ε := by
      refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
      have h1 : b.normed volume x ≠ 0 := fun h0 => hx (by simp [φ, h0])
      have hx' : x ∈ Function.support (b.normed volume) := h1
      rw [b.support_normed_eq, hb] at hx'
      exact Metric.ball_subset_closedBall hx'
    have hφ : IsT U φ := by
      refine ⟨Complex.ofRealCLM.contDiff.comp b.contDiff_normed, ?_, ?_⟩
      · exact b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
      · exact hφsup.trans ((Metric.closedBall_subset_ball hεε).trans hball)
    have hφu : IsT Set.univ φ := ⟨hφ.smooth, hφ.cpt, Set.subset_univ _⟩
    set ψ : Vr n → ℂ := fun x =>
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * dList (List.ofFn (ml σ)).reverse φ x with hψdef
    have hψT : ∀ σ : Equiv.Perm (Fin n), IsT U (dList (List.ofFn (ml σ)).reverse φ) := fun σ => isT_dList hφ _
    have hψ0 : ∀ x, x ∉ tsupport φ → ψ x = 0 := by
      intro x hx
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_dList_subset φ _ h)), mul_zero]
    have hSing : IsSingTest ψ := by
      refine ⟨continuous_finsetSum _ fun σ _ => continuous_const.mul (hψT σ).smooth.continuous,
        HasCompactSupport.intro hφ.cpt hψ0, ?_⟩
      intro β _ hdet
      exact fourier_test β hdet hφu
    have h1 := hyp ψ hSing
    have hint : ∀ σ : Equiv.Perm (Fin n), Integrable (fun x => F x * dList (List.ofFn (ml σ)).reverse φ x) :=
      fun σ => integrable_mul_of_contOn hU hF.continuousOn (hψT σ).smooth.continuous (hψT σ).cpt (hψT σ).sub
    have h2 : ∫ x, G (herm x) * ψ x = (-1) ^ Fintype.card (Fin n) * ∫ x, H x * φ x := by
      have e1 : (fun x => G (herm x) * ψ x) = fun x => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
          (F x * dList (List.ofFn (ml σ)).reverse φ x) := by
        funext x; simp only [ψ, F, Finset.mul_sum]; refine Finset.sum_congr rfl fun σ _ => ?_; ring
      have hintH : ∀ σ : Equiv.Perm (Fin n), Integrable (fun x => dList (List.ofFn (ml σ)) F x * φ x) :=
        fun σ => integrable_mul_of_contOn hU (contDiffOn_dList hU hF _).continuousOn hφ.smooth.continuous
          hφ.cpt hφ.sub
      have e2 : (fun x => H x * φ x) = fun x => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
          (dList (List.ofFn (ml σ)) F x * φ x) := by
        funext x; simp only [H, Finset.sum_mul]; refine Finset.sum_congr rfl fun σ _ => ?_; ring
      rw [e1, e2, integral_finsetSum _ (fun σ _ => (hint σ).const_mul _),
        integral_finsetSum _ (fun σ _ => (hintH σ).const_mul _), Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [integral_const_mul, integral_const_mul, ibp_dList hU _ hF hφ, List.reverse_reverse, List.length_reverse,
        List.length_ofFn]
      ring
    rw [h2] at h1
    have hne : ((-1 : ℂ)) ^ Fintype.card (Fin n) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.1 h1).resolve_left hne

  rw [← hH0]
  by_contra hne
  have hδ : 0 < ‖H 0‖ / 2 := by positivity
  obtain ⟨ε1, hε1, hcont⟩ := Metric.continuousAt_iff.1 (hHU.continuousAt (hU.mem_nhds h0U)) _ hδ
  set ε := min (ε0 / 2) (ε1 / 2) with hεdef
  have hε : 0 < ε := lt_min (half_pos hε0) (half_pos hε1)
  have hεε0 : ε < ε0 := (min_le_left _ _).trans_lt (half_lt_self hε0)
  have hεε1 : ε < ε1 := (min_le_right _ _).trans_lt (half_lt_self hε1)
  let b : ContDiffBump (0 : Vr n) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have hk := key ε hε hεε0 b rfl
  set φr : Vr n → ℝ := b.normed volume
  have hφr1 : ∫ x, φr x = 1 := b.integral_normed
  have hφint : Integrable φr := b.integrable_normed
  have hcpt : HasCompactSupport (fun x => ((φr x : ℝ) : ℂ)) := b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  have hφc : Continuous (fun x => ((φr x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp b.continuous_normed
  have hsub : tsupport (fun x => ((φr x : ℝ) : ℂ)) ⊆ U := by
    refine (closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall).trans
      ((Metric.closedBall_subset_ball hεε0).trans hball)
    have h1 : φr x ≠ 0 := fun h0 => hx (by simp [h0])
    have hx' : x ∈ Function.support φr := h1
    rw [b.support_normed_eq] at hx'
    exact Metric.ball_subset_closedBall hx'
  have hi1 : Integrable (fun x => H x * ((φr x : ℝ) : ℂ)) := integrable_mul_of_contOn hU hHU hφc hcpt hsub
  have hi2 : Integrable (fun x => (H 0 - H x) * ((φr x : ℝ) : ℂ)) :=
    integrable_mul_of_contOn hU (continuousOn_const.sub hHU) hφc hcpt hsub
  have hrep : H 0 = ∫ x, (H 0 - H x) * ((φr x : ℝ) : ℂ) := by
    have : ∫ x, (H 0 - H x) * ((φr x : ℝ) : ℂ) = H 0 * (∫ x, ((φr x : ℝ) : ℂ)) - ∫ x, H x * ((φr x : ℝ) : ℂ) := by
      have hA : Integrable (fun x => H 0 * ((φr x : ℝ) : ℂ)) :=
        integrable_mul_of_contOn hU continuousOn_const hφc hcpt hsub
      have e : (fun x => (H 0 - H x) * ((φr x : ℝ) : ℂ)) =
          fun x => H 0 * ((φr x : ℝ) : ℂ) - H x * ((φr x : ℝ) : ℂ) := by
        funext x; ring
      rw [e, integral_sub hA hi1, integral_const_mul]
    rw [this, hk, integral_complex_ofReal, hφr1]; simp
  have hbound : ‖∫ x, (H 0 - H x) * ((φr x : ℝ) : ℂ)‖ ≤ ∫ x, ‖H 0‖ / 2 * φr x := by
    refine norm_integral_le_of_norm_le (hφint.const_mul _) (Eventually.of_forall fun x => ?_)
    by_cases hx : φr x = 0
    · simp [hx]
    · have hx' : x ∈ Function.support φr := hx
      rw [b.support_normed_eq] at hx'
      have hd : dist x 0 < ε1 := (Metric.mem_ball.1 hx').trans hεε1
      have := hcont hd
      rw [dist_eq_norm, norm_sub_rev] at this
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (b.nonneg_normed x)]
      exact mul_le_mul_of_nonneg_right this.le (b.nonneg_normed x)
  rw [integral_const_mul, hφr1, mul_one, ← hrep] at hbound
  have : ‖H 0‖ ≤ 0 := by linarith
  exact hne (norm_le_zero_iff.1 this)

end PositivityTheory.Rg.Sw.LVs
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def rmulL (x : M2 n) : M2 n →L[ℝ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M * x
      map_add' := fun _ _ => Matrix.add_mul _ _ _
      map_smul' := fun c M => by simp }

theorem deriv_piece (Θ : M2 n → ℂ) (x : M2 n) (hΘ : DifferentiableAt ℂ Θ x)
    (γ : ℝ → M2 n) (Y : M2 n) (hγ : HasDerivAt γ Y 0) (hγ0 : γ 0 = 1)
    (f : ℝ → ℂ) (r : ℂ) (hf : HasDerivAt f r 0)
    (hlaw : ∀ᶠ t in 𝓝 (0 : ℝ), Θ (γ t * x) = f t * Θ x) :
    fderiv ℂ Θ x (Y * x) = r * Θ x := by
  have h1 : HasDerivAt (fun t => γ t * x) (Y * x) 0 := by
    have := (rmulL x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ
    exact this
  have hx : γ 0 * x = x := by simp [hγ0]
  have hF : HasFDerivAt Θ ((fderiv ℂ Θ x).restrictScalars ℝ) (γ 0 * x) := by
    rw [hx]; exact hΘ.hasFDerivAt.restrictScalars ℝ
  have h2 : HasDerivAt (fun t => Θ (γ t * x)) (fderiv ℂ Θ x (Y * x)) 0 := by
    have := hF.comp_hasDerivAt (0 : ℝ) h1
    exact this
  have h3 : HasDerivAt (fun t => Θ (γ t * x)) (r * Θ x) 0 :=
    (hf.mul_const (Θ x)).congr_of_eventuallyEq hlaw
  exact h2.unique h3

theorem one_add_smul_fromBlocks (t : ℝ) (A B C D : Matrix (Fin n) (Fin n) ℂ) :
    (1 : M2 n) + t • fromBlocks A B C D = fromBlocks (1 + t • A) (t • B) (t • C) (1 + t • D) := by
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]; simp

theorem inG_one_add (P : M2 n) (h1 : Pᴴ * JJ n + JJ n * P = 0) (h2 : Pᴴ * JJ n * P = 0) (t : ℝ) :
    InG ((1 : M2 n) + t • P) := by
  unfold InG
  have key : ((1 : M2 n) + t • P)ᴴ * JJ n * (1 + t • P)
      = JJ n + t • (Pᴴ * JJ n + JJ n * P) + (t * t) • (Pᴴ * JJ n * P) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, star_trivial]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
      smul_smul, Matrix.mul_assoc]
    abel
  rw [key, h1, h2]
  simp

theorem inG_fromBlocks_diag (a d : Matrix (Fin n) (Fin n) ℂ) (h1 : aᴴ * d = 1) (h2 : dᴴ * a = 1) :
    InG (fromBlocks a 0 0 d) := by
  unfold InG JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [h1, h2]

theorem det_one_add_smul_single_same (i : Fin n) (s : ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + s • Matrix.single i i 1).det = 1 + s := by
  have h : (1 : Matrix (Fin n) (Fin n) ℂ) + s • Matrix.single i i 1 =
      Matrix.diagonal (fun j => if j = i then 1 + s else 1) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hai : a = i
      · subst hai
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, hai, Ne.symm hai]
    · have hn : ¬ (i = a ∧ i = b) := fun h => hab (h.1.symm.trans h.2)
      simp [Matrix.single_apply, hn, hab, Matrix.one_apply_ne hab]
  rw [h, Matrix.det_diagonal]
  simp

def LawH (Θ : M2 n → ℂ) : Prop :=
  ∀ p x, InG p → p.toBlocks₂₁ = 0 → InG x → Θ (p * x) = ((‖(p.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) * Θ x

def lam (Y : M2 n) : ℂ := (n : ℂ) * (Y.toBlocks₁₁.trace - Y.toBlocks₂₂.trace)

theorem hasDerivAt_affine (P : M2 n) : HasDerivAt (fun t : ℝ => (1 : M2 n) + t • P) P 0 := by
  exact (((hasDerivAt_id (0 : ℝ)).smul_const P).const_add (1 : M2 n)).congr_deriv (one_smul ℝ P)

theorem pieceN (Θ : M2 n → ℂ) (hl : LawH Θ) (x : M2 n) (hx : InG x) (hd : DifferentiableAt ℂ Θ x)
    (β : Matrix (Fin n) (Fin n) ℂ) (hβ : βᴴ = β) :
    fderiv ℂ Θ x (fromBlocks 0 β 0 0 * x) = lam (fromBlocks 0 β 0 0) * Θ x := by
  have hc1 : (fromBlocks 0 β 0 0 : M2 n)ᴴ * JJ n + JJ n * fromBlocks 0 β 0 0 = 0 := by
    simp [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, hβ]
  have hc2 : (fromBlocks 0 β 0 0 : M2 n)ᴴ * JJ n * fromBlocks 0 β 0 0 = 0 := by
    simp [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hβ]
  have key := deriv_piece Θ x hd (fun t : ℝ => 1 + t • (fromBlocks 0 β 0 0 : M2 n)) _
    (hasDerivAt_affine _) (by simp) (fun _ => (1 : ℂ)) 0 (hasDerivAt_const _ _)
    (Filter.Eventually.of_forall fun t => by
      have h21 : ((1 : M2 n) + t • (fromBlocks 0 β 0 0 : M2 n)).toBlocks₂₁ = 0 := by
        rw [one_add_smul_fromBlocks]
        simp
      rw [hl _ x (inG_one_add _ hc1 hc2 t) h21 hx, one_add_smul_fromBlocks]
      simp)
  rw [key]
  simp [lam]

def Pij (c : ℂ) (i j : Fin n) : M2 n := fromBlocks (c • Matrix.single i j 1) 0 0 (-(conj c) • Matrix.single j i 1)

theorem pieceOff (Θ : M2 n → ℂ) (hl : LawH Θ) (x : M2 n) (hx : InG x) (hd : DifferentiableAt ℂ Θ x)
    (c : ℂ) (i j : Fin n) (hij : i ≠ j) :
    fderiv ℂ Θ x (Pij c i j * x) = lam (Pij c i j) * Θ x := by
  have hc1 : (Pij c i j)ᴴ * JJ n + JJ n * Pij c i j = 0 := by
    simp [Pij, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_single, Complex.star_def]
  have hc2 : (Pij c i j)ᴴ * JJ n * Pij c i j = 0 := by
    simp [Pij, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_single, Complex.star_def,
      Matrix.single_mul_single_of_ne, hij, Ne.symm hij]
  have hdet : ∀ t : ℝ, ((1 : Matrix (Fin n) (Fin n) ℂ) + t • (-(conj c) • Matrix.single j i 1)).det = 1 := by
    intro t
    rw [← smul_assoc, Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.det_transvection_of_ne j i (Ne.symm hij) _
  have key := deriv_piece Θ x hd (fun t : ℝ => 1 + t • Pij c i j) _
    (hasDerivAt_affine _) (by simp) (fun _ => (1 : ℂ)) 0 (hasDerivAt_const _ _)
    (Filter.Eventually.of_forall fun t => by
      have h21 : ((1 : M2 n) + t • Pij c i j).toBlocks₂₁ = 0 := by
        rw [Pij, one_add_smul_fromBlocks]
        simp
      rw [hl _ x (inG_one_add _ hc1 hc2 t) h21 hx, Pij, one_add_smul_fromBlocks,
        Matrix.toBlocks_fromBlocks₂₂, hdet]
      simp)
  rw [key]
  simp [lam, Pij, Matrix.trace_smul, Matrix.trace_single_eq_of_ne _ _ _ hij,
    Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hij)]

theorem one_add_smul_single_mul (i : Fin n) (u v : ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + u • Matrix.single i i 1) * (1 + v • Matrix.single i i 1) =
      1 + (u + v + u * v) • Matrix.single i i 1 := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
    Matrix.single_mul_single_same, add_smul]
  simp only [mul_comm v u]
  abel

private theorem one_add_smul_single_conjTranspose_mul_eq_one (a b : ℂ) (h : (1 + star a) * (1 + b) = 1) (i : Fin n) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + a • Matrix.single i i 1)ᴴ * (1 + b • Matrix.single i i 1) = 1 := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_single, star_one, one_add_smul_single_mul]
  have h0 : star a + b + star a * b = 0 := by linear_combination h
  rw [h0, zero_smul, add_zero]

theorem pieceDiag (Θ : M2 n → ℂ) (hl : LawH Θ) (x : M2 n) (hx : InG x) (hd : DifferentiableAt ℂ Θ x)
    (c : ℂ) (i : Fin n) :
    fderiv ℂ Θ x (Pij c i i * x) = lam (Pij c i i) * Θ x := by
  have e : ∀ w : ℂ, (1 : ℂ) + (w - 1) = w := fun w => by ring
  have hu : HasDerivAt (fun t : ℝ => Complex.exp (↑t * c) - 1) c 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).ofReal_comp).mul_const c).cexp.sub_const 1
    exact h.congr_deriv (by simp)
  have hv : HasDerivAt (fun t : ℝ => Complex.exp (-↑t * conj c) - 1) (-(conj c)) 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).ofReal_comp).neg.mul_const (conj c)).cexp.sub_const 1
    exact h.congr_deriv (by simp)
  have hγ : HasDerivAt (fun t : ℝ => (1 : M2 n) +
      ((Complex.exp (↑t * c) - 1) • (fromBlocks (Matrix.single i i 1) 0 0 0 : M2 n) +
        (Complex.exp (-↑t * conj c) - 1) • (fromBlocks 0 0 0 (Matrix.single i i 1) : M2 n)))
      (Pij c i i) 0 := by
    have h := ((hu.smul_const (fromBlocks (Matrix.single i i 1) 0 0 0 : M2 n)).add
      (hv.smul_const (fromBlocks 0 0 0 (Matrix.single i i 1) : M2 n))).const_add (1 : M2 n)
    refine h.congr_deriv ?_
    rw [Pij, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp
  have hform : ∀ t : ℝ, (1 : M2 n) +
      ((Complex.exp (↑t * c) - 1) • (fromBlocks (Matrix.single i i 1) 0 0 0 : M2 n) +
        (Complex.exp (-↑t * conj c) - 1) • (fromBlocks 0 0 0 (Matrix.single i i 1) : M2 n)) =
      fromBlocks (1 + (Complex.exp (↑t * c) - 1) • Matrix.single i i 1) 0 0
        (1 + (Complex.exp (-↑t * conj c) - 1) • Matrix.single i i 1) := by
    intro t
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul,
      Matrix.fromBlocks_add, Matrix.fromBlocks_add]
    simp
  have hG : ∀ t : ℝ, InG (fromBlocks (1 + (Complex.exp (↑t * c) - 1) • Matrix.single i i 1) 0 0
      (1 + (Complex.exp (-↑t * conj c) - 1) • Matrix.single i i 1) : M2 n) := by
    intro t
    apply inG_fromBlocks_diag
    · apply one_add_smul_single_conjTranspose_mul_eq_one
      rw [star_sub, star_one, e, e, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add,
        show (conj (↑t * c) + -↑t * conj c : ℂ) = 0 by rw [map_mul, Complex.conj_ofReal]; ring,
        Complex.exp_zero]
    · apply one_add_smul_single_conjTranspose_mul_eq_one
      rw [star_sub, star_one, e, e, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add,
        show (conj (-↑t * conj c) + ↑t * c : ℂ) = 0 by
          rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj]; ring,
        Complex.exp_zero]
  have hf := (((hasDerivAt_id' (0 : ℝ)).const_mul (2 * (n : ℝ) * c.re)).exp).ofReal_comp
  have key := deriv_piece Θ x hd _ _ hγ (by simp) _ _ hf
    (Filter.Eventually.of_forall fun t => by
      have h21 : ((1 : M2 n) +
          ((Complex.exp (↑t * c) - 1) • (fromBlocks (Matrix.single i i 1) 0 0 0 : M2 n) +
            (Complex.exp (-↑t * conj c) - 1) • (fromBlocks 0 0 0 (Matrix.single i i 1) : M2 n))).toBlocks₂₁ = 0 := by
        rw [hform]
        simp
      rw [hl _ x (by rw [hform]; exact hG t) h21 hx, hform, Matrix.toBlocks_fromBlocks₂₂,
        det_one_add_smul_single_same, e, Complex.norm_exp]
      congr 2
      rw [← Real.rpow_intCast, ← Real.exp_mul]
      congr 1
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_im,
        Complex.conj_re, Complex.conj_im]
      push_cast
      ring)
  rw [key]
  congr 1
  simp [lam, Pij, Matrix.trace_smul]
  apply Complex.ext <;> simp <;> ring

theorem lam_add (Y Y' : M2 n) : lam (Y + Y') = lam Y + lam Y' := by
  have e1 : (Y + Y').toBlocks₁₁ = Y.toBlocks₁₁ + Y'.toBlocks₁₁ := by ext; rfl
  have e2 : (Y + Y').toBlocks₂₂ = Y.toBlocks₂₂ + Y'.toBlocks₂₂ := by ext; rfl
  simp only [lam, e1, e2, Matrix.trace_add]
  ring

theorem lam_smul (c : ℂ) (Y : M2 n) : lam (c • Y) = c * lam Y := by
  simp only [lam]
  have h1 : (c • Y).toBlocks₁₁ = c • Y.toBlocks₁₁ := by ext; simp [Matrix.toBlocks₁₁]
  have h2 : (c • Y).toBlocks₂₂ = c • Y.toBlocks₂₂ := by ext; simp [Matrix.toBlocks₂₂]
  rw [h1, h2, Matrix.trace_smul, Matrix.trace_smul]; simp only [smul_eq_mul]; ring

def Gen (n : ℕ) : Set (M2 n) :=
  {Y | (∃ β : Matrix (Fin n) (Fin n) ℂ, βᴴ = β ∧ Y = fromBlocks 0 β 0 0) ∨ ∃ c i j, Y = Pij c i j}

theorem sum_single_mem (W : Submodule ℂ (M2 n)) (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n)
    (h : ∀ i j a, Φ (Matrix.single i j a) ∈ W) (M : Matrix (Fin n) (Fin n) ℂ) : Φ M ∈ W := by
  rw [Matrix.matrix_eq_sum_single M, map_sum]
  exact Submodule.sum_mem _ fun i _ => by rw [map_sum]; exact Submodule.sum_mem _ fun j _ => h i j _

def fb11 (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n where
  toFun A := fromBlocks A 0 0 0
  map_add' A B := by rw [Matrix.fromBlocks_add]; simp
  map_smul' c A := by rw [Matrix.fromBlocks_smul]; simp

def fb22 (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n where
  toFun A := fromBlocks 0 0 0 A
  map_add' A B := by rw [Matrix.fromBlocks_add]; simp
  map_smul' c A := by rw [Matrix.fromBlocks_smul]; simp

theorem mem_span_gen (Y : M2 n) (hY : Y.toBlocks₂₁ = 0) : Y ∈ Submodule.span ℂ (Gen n) := by
  have hE1 : ∀ i j (a : ℂ), (fromBlocks (Matrix.single i j a) 0 0 0 : M2 n) ∈ Submodule.span ℂ (Gen n) := by
    intro i j a
    have h : (fromBlocks (Matrix.single i j a) 0 0 0 : M2 n) =
        (a / 2) • (Pij 1 i j - Complex.I • Pij Complex.I i j) := by
      ext (p|p) (q|q)
      all_goals simp [Pij, Matrix.single_apply]
      all_goals split_ifs
      all_goals ring_nf
      all_goals simp [Complex.I_sq]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.subset_span (Or.inr ⟨1, i, j, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨Complex.I, i, j, rfl⟩))))
  have hE2 : ∀ i j (a : ℂ), (fromBlocks 0 0 0 (Matrix.single i j a) : M2 n) ∈ Submodule.span ℂ (Gen n) := by
    intro i j a
    have h : (fromBlocks 0 0 0 (Matrix.single i j a) : M2 n) =
        (-a / 2) • (Pij 1 j i + Complex.I • Pij Complex.I j i) := by
      ext (p|p) (q|q)
      all_goals simp [Pij, Matrix.single_apply]
      all_goals split_ifs
      all_goals ring_nf
      all_goals simp [Complex.I_sq]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (Submodule.subset_span (Or.inr ⟨1, j, i, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨Complex.I, j, i, rfl⟩))))
  have hA : ∀ A, fb11 n A ∈ Submodule.span ℂ (Gen n) :=
    sum_single_mem _ (fb11 n) (fun i j a => hE1 i j a)
  have hD : ∀ D, fb22 n D ∈ Submodule.span ℂ (Gen n) :=
    sum_single_mem _ (fb22 n) (fun i j a => hE2 i j a)
  have hB : ∀ B : Matrix (Fin n) (Fin n) ℂ, (fromBlocks 0 B 0 0 : M2 n) ∈ Submodule.span ℂ (Gen n) := by
    intro B
    have hH1 : ((1 / 2 : ℂ) • (B + Bᴴ))ᴴ = (1 / 2 : ℂ) • (B + Bᴴ) := by
      ext p q
      simp [Matrix.conjTranspose_apply]
      ring
    have hH2 : ((-Complex.I / 2) • (B - Bᴴ))ᴴ = (-Complex.I / 2) • (B - Bᴴ) := by
      ext p q
      simp [Matrix.conjTranspose_apply]
      ring
    have hsplit : (fromBlocks 0 B 0 0 : M2 n) = fromBlocks 0 ((1 / 2 : ℂ) • (B + Bᴴ)) 0 0 +
        Complex.I • fromBlocks 0 ((-Complex.I / 2) • (B - Bᴴ)) 0 0 := by
      ext (p|p) (q|q)
      all_goals simp
      ring_nf
      simp [Complex.I_sq]
      ring
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.subset_span (Or.inl ⟨_, hH1, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨_, hH2, rfl⟩)))
  have hYe : Y = fb11 n Y.toBlocks₁₁ + fromBlocks 0 Y.toBlocks₁₂ 0 0 + fb22 n Y.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks Y, hY]
    simp [fb11, fb22, Matrix.fromBlocks_add]
  rw [hYe]
  exact Submodule.add_mem _ (Submodule.add_mem _ (hA _) (hB _)) (hD _)

theorem lawDeriv : LawDeriv := by
  intro n Θ Ω hΩ hsub hdiff hlaw x hx Y hY
  have hd : DifferentiableAt ℂ Θ x := hdiff.differentiableAt (hΩ.mem_nhds (hsub hx))
  show fderiv ℂ Θ x (Y * x) = lam Y * Θ x
  refine Submodule.span_induction (p := fun Y _ => fderiv ℂ Θ x (Y * x) = lam Y * Θ x)
    ?_ ?_ ?_ ?_ (mem_span_gen Y hY)
  · intro Z hZ
    rcases hZ with ⟨β, hβ, rfl⟩ | ⟨c, i, j, rfl⟩
    · exact pieceN Θ hlaw x hx hd β hβ
    · by_cases hij : i = j
      · subst hij
        exact pieceDiag Θ hlaw x hx hd c i
      · exact pieceOff Θ hlaw x hx hd c i j hij
  · have h0 : lam (0 : M2 n) = 0 := by simpa using lam_smul 0 (0 : M2 n)
    rw [zero_mul, map_zero, h0, zero_mul]
  · intro a b _ _ ha hb
    rw [add_mul, map_add, ha, hb, lam_add, add_mul]
  · intro a b _ hb
    rw [smul_mul_assoc, map_smul, hb, lam_smul, smul_eq_mul, mul_assoc]

end PositivityTheory.Rg.Sw.LVs.II
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiff_entry (i j : Fin n ⊕ Fin n) : ContDiff ℝ ∞ (fun x : M2 n => x i j) :=
  contDiff_apply_apply (𝕜 := ℝ) (E := ℂ) i j

theorem xZx_apply (x Z : M2 n) (i j : Fin n ⊕ Fin n) :
    (x * Z * xᴴ) i j = ∑ l, (∑ m, x i m * Z m l) * starRingEnd ℂ (x j l) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem contDiff_xZx (Z : M2 n) (i j : Fin n ⊕ Fin n) : ContDiff ℝ ∞ (fun x : M2 n => (x * Z * xᴴ) i j) := by
  simp_rw [xZx_apply]
  refine ContDiff.sum fun l _ => ContDiff.mul (ContDiff.sum fun m _ => (contDiff_entry i m).mul contDiff_const) ?_
  exact Complex.conjCLE.contDiff.comp (contDiff_entry j l)

theorem cDiff : CDiff := by
  intro n Z a b
  exact ⟨contDiff_xZx Z (Sum.inr a) (Sum.inr b), (contDiff_xZx Z (Sum.inr a) (Sum.inl b)).neg⟩

theorem fderiv_xZx (Z x v : M2 n) (i j : Fin n ⊕ Fin n) :
    fderiv ℝ (fun y : M2 n => (y * Z * yᴴ) i j) x v = (v * Z * xᴴ + x * Z * vᴴ) i j := by
  have hd : DifferentiableAt ℝ (fun y : M2 n => (y * Z * yᴴ) i j) x :=
    ((contDiff_xZx Z i j).differentiable (by simp)).differentiableAt
  refine (hd.lineDeriv_eq_fderiv (v := v)).symm.trans ?_
  have e : (fun t : ℝ => ((x + t • v) * Z * (x + t • v)ᴴ) i j) = fun t : ℝ =>
      (x * Z * xᴴ) i j + (t : ℂ) * (v * Z * xᴴ + x * Z * vᴴ) i j + (t : ℂ) ^ 2 * (v * Z * vᴴ) i j := by
    funext t
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_smul]
    ring
  have hr : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
  have h : HasDerivAt (fun t : ℝ => ((x + t • v) * Z * (x + t • v)ᴴ) i j) ((v * Z * xᴴ + x * Z * vᴴ) i j) 0 := by
    rw [e]
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (v * Z * xᴴ + x * Z * vᴴ) i j) ((v * Z * xᴴ + x * Z * vᴴ) i j) 0 := by
      simpa using hr.mul_const ((v * Z * xᴴ + x * Z * vᴴ) i j)
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2 * (v * Z * vᴴ) i j) 0 0 := by
      simpa using (hr.pow 2).mul_const ((v * Z * vᴴ) i j)
    have h3 := ((hasDerivAt_const (0 : ℝ) ((x * Z * xᴴ) i j)).add h1).add h2
    refine (h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv (by simp)
    simp
  simpa [lineDeriv] using h.deriv

theorem reK_add_imK (e : M2 n) : reK e + Complex.I • imK e = e := by
  simp only [reK, imK, smul_smul, smul_sub, smul_add]
  have h : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I]; ring
  rw [h]
  module

theorem reK_conj (e : M2 n) : (reK e)ᴴ = -reK e := by
  simp only [reK, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this]; module

theorem imK_conj (e : M2 n) : (imK e)ᴴ = -imK e := by
  simp only [imK, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  have : star (-Complex.I / 2) = -(-Complex.I / 2) := by simp [Complex.conj_I]; ring
  rw [this]; module

theorem fderiv_xZx_skew (Z x E : M2 n) (hE : Eᴴ = -E) (i j : Fin n ⊕ Fin n) :
    fderiv ℝ (fun y : M2 n => (y * Z * yᴴ) i j) x (E * x) = (E * (x * Z * xᴴ) - (x * Z * xᴴ) * E) i j := by
  rw [fderiv_xZx, Matrix.conjTranspose_mul, hE]
  congr 1
  simp only [Matrix.mul_assoc, Matrix.mul_neg, sub_eq_add_neg]

theorem dK_xZx (Z x e : M2 n) (i j : Fin n ⊕ Fin n) :
    dK (fun y : M2 n => (y * Z * yᴴ) i j) x e = (e * (x * Z * xᴴ) - (x * Z * xᴴ) * e) i j := by
  rw [dK, fderiv_xZx_skew Z x _ (reK_conj e), fderiv_xZx_skew Z x _ (imK_conj e)]
  conv_rhs => rw [← reK_add_imK e]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem toBlocks₂₂_apply' (M : M2 n) (a b : Fin n) : M.toBlocks₂₂ a b = M (Sum.inr a) (Sum.inr b) := rfl
theorem toBlocks₂₁_apply' (M : M2 n) (a b : Fin n) : M.toBlocks₂₁ a b = M (Sum.inr a) (Sum.inl b) := rfl
theorem toBlocks₁₁_apply' (M : M2 n) (a b : Fin n) : M.toBlocks₁₁ a b = M (Sum.inl a) (Sum.inl b) := rfl

theorem decomp (M : M2 n) : M = fromBlocks (M.toBlocks₁₁ - M.toBlocks₂₂) (M.toBlocks₁₂ + M.toBlocks₂₁) 0 0 +
    ∑ a, ∑ b, (M.toBlocks₂₂ a b • eA a b + (-M.toBlocks₂₁ a b) • eB a b) := by
  ext i j
  rcases i with a' | a' <;> rcases j with b' | b' <;>
    simp [eA, eB, Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

theorem eA_mul_apply (M : M2 n) (a b : Fin n) : (eA a b * M) (Sum.inr a) (Sum.inr b) = M (Sum.inr b) (Sum.inr b) := by
  simp [eA, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

theorem mul_eA_apply (M : M2 n) (a b : Fin n) : (M * eA a b) (Sum.inr a) (Sum.inr b) = M (Sum.inr a) (Sum.inr a) := by
  simp [eA, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

theorem eB_mul_apply (M : M2 n) (a b : Fin n) : (eB a b * M) (Sum.inr a) (Sum.inl b) = -M (Sum.inl b) (Sum.inl b) := by
  simp [eB, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

theorem mul_eB_apply (M : M2 n) (a b : Fin n) : (M * eB a b) (Sum.inr a) (Sum.inl b) = -M (Sum.inr a) (Sum.inr a) := by
  simp [eB, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

theorem sumA (M : M2 n) : ∑ a, ∑ b, ((eA a b * M - M * eA a b : M2 n) (Sum.inr a) (Sum.inr b)) = 0 := by
  simp only [Matrix.sub_apply, eA_mul_apply, mul_eA_apply, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => M (Sum.inr b) (Sum.inr b))]
  simp

theorem sumB (M : M2 n) : ∑ a, ∑ b, -((eB a b * M - M * eB a b : M2 n) (Sum.inr a) (Sum.inl b)) =
    (n : ℂ) * (M.toBlocks₁₁.trace - M.toBlocks₂₂.trace) := by
  simp only [Matrix.sub_apply, eB_mul_apply, mul_eB_apply, neg_sub, neg_neg, sub_neg_eq_add, Finset.sum_sub_distrib]
  simp only [Matrix.trace, Matrix.diag, toBlocks₁₁_apply', toBlocks₂₂_apply', Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_sub]
  have h : ∀ a b : Fin n, -(-M (Sum.inl b) (Sum.inl b) + M (Sum.inr a) (Sum.inr a)) =
      M (Sum.inl b) (Sum.inl b) - M (Sum.inr a) (Sum.inr a) := fun _ _ => by ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.mul_sum]

theorem ptId : PtId := by
  intro n Θ x Z hx hΘ hlaw
  set M := x * Z * xᴴ with hM
  have hxZ : x * Z = M * x := by rw [hM, Matrix.mul_assoc (x * Z), hx.2, Matrix.mul_one]
  have hΘd : DifferentiableAt ℂ Θ x := hΘ.differentiableAt (by simp)
  have hR : ∀ v, fderiv ℝ Θ x v = fderiv ℂ Θ x v := fun v => by
    have h := (hΘd.hasFDerivAt.restrictScalars ℝ).fderiv
    exact (congrArg (fun L => L v) h).trans rfl
  have hdK : ∀ e, dK Θ x e = fderiv ℂ Θ x (e * x) := fun e => by
    rw [dK, hR, hR]
    conv_rhs => rw [← reK_add_imK e]
    rw [Matrix.add_mul, Matrix.smul_mul, map_add, map_smul, smul_eq_mul]
  have hLeib : ∀ c : M2 n → ℂ, DifferentiableAt ℝ c x → ∀ e,
      dK (fun y => c y * Θ y) x e = dK c x e * Θ x + c x * dK Θ x e := fun c hc e => by
    have hΘr : DifferentiableAt ℝ Θ x := hΘd.restrictScalars ℝ
    have h := (hc.hasFDerivAt.mul hΘr.hasFDerivAt).fderiv
    have hv : ∀ v, fderiv ℝ (fun y => c y * Θ y) x v = c x * fderiv ℝ Θ x v + Θ x * fderiv ℝ c x v := fun v => by
      exact (congrArg (fun L : M2 n →L[ℝ] ℂ => L v) h).trans rfl
    simp only [dK, hv]
    ring
  have hcA : ∀ a b, DifferentiableAt ℝ (cA Z a b) x := fun a b =>
    ((cDiff n Z a b).1.differentiable (by simp)).differentiableAt
  have hcB : ∀ a b, DifferentiableAt ℝ (cB Z a b) x := fun a b =>
    ((cDiff n Z a b).2.differentiable (by simp)).differentiableAt
  have hdA : ∀ a b e, dK (cA Z a b) x e = (e * M - M * e) (Sum.inr a) (Sum.inr b) := fun a b e =>
    dK_xZx Z x e (Sum.inr a) (Sum.inr b)
  have hdB : ∀ a b e, dK (cB Z a b) x e = -((e * M - M * e) (Sum.inr a) (Sum.inl b)) := fun a b e => by
    have : cB Z a b = fun y => -((y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) := rfl
    have hd : DifferentiableAt ℝ (fun y : M2 n => (y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x :=
      ((contDiff_xZx Z _ _).differentiable (by simp)).differentiableAt
    have hn := hd.hasFDerivAt.neg.fderiv
    have hv : ∀ v, fderiv ℝ (fun y : M2 n => -(y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x v =
        -fderiv ℝ (fun y : M2 n => (y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x v := fun v => by
      exact (congrArg (fun L : M2 n →L[ℝ] ℂ => L v) hn).trans rfl
    have h := dK_xZx Z x e (Sum.inr a) (Sum.inl b)
    rw [dK] at h
    rw [this, dK, hv, hv, ← h]; ring

  have hL : fderiv ℂ Θ x (x * Z) = (n : ℂ) * (M.toBlocks₁₁.trace - M.toBlocks₂₂.trace) * Θ x +
      ∑ a, ∑ b, (cA Z a b x * dK Θ x (eA a b) + cB Z a b x * dK Θ x (eB a b)) := by
    rw [hxZ]
    conv_lhs => rw [decomp M]
    rw [Matrix.add_mul, map_add, hlaw _ (by simp)]
    simp only [Matrix.sum_mul, map_sum, Matrix.add_mul, Matrix.smul_mul, map_add, map_smul, smul_eq_mul, hdK]
    congr 1
    · simp [Matrix.trace_sub]
  rw [hL]
  simp only [hLeib _ (hcA _ _), hLeib _ (hcB _ _), hdA, hdB]
  have e1 : ∀ a b, (eA a b * M - M * eA a b) (Sum.inr a) (Sum.inr b) * Θ x + cA Z a b x * dK Θ x (eA a b) +
      (-((eB a b * M - M * eB a b) (Sum.inr a) (Sum.inl b)) * Θ x + cB Z a b x * dK Θ x (eB a b)) =
      ((eA a b * M - M * eA a b) (Sum.inr a) (Sum.inr b) + -((eB a b * M - M * eB a b) (Sum.inr a) (Sum.inl b))) * Θ x +
      (cA Z a b x * dK Θ x (eA a b) + cB Z a b x * dK Θ x (eB a b)) := fun a b => by ring
  simp only [e1, Finset.sum_add_distrib, ← Finset.sum_mul, sumA, sumB]
  ring

end PositivityTheory.Rg.Sw.LVs.II
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem eA_comm {n : ℕ} (a b : Fin n) : eA a b * JJ n = JJ n * eA a b := by
  simp [eA, JJ, Matrix.fromBlocks_multiply]

theorem eB_comm {n : ℕ} (a b : Fin n) : eB a b * JJ n = JJ n * eB a b := by
  simp [eB, JJ, Matrix.fromBlocks_multiply]

theorem infInv_of (hL : LeftDeriv) (hP : LawDeriv) (hI : PtId) (hC : CDiff) : InfInv := by
  intro n F1 F2 Ω hΩ hGΩ hF1 hF2 hlaw Kg _ _ _ _ _ _ μ _ ι hι hK Z
  have hΘc : ContDiffOn ℂ ∞ (fun y => F1 y * F2 y) Ω := hF1.mul hF2
  have hKk : ∀ k : Kg, InK (ι k) := fun k => (hK (ι k)).2 ⟨k, rfl⟩
  have hmem : ∀ k : Kg, ι k ∈ Ω := fun k => hGΩ (hKk k).1
  have hlawΘ := hP n (fun y => F1 y * F2 y) Ω hΩ hGΩ (hΘc.differentiableOn (by simp))
    (fun p x hp hp0 hx => hlaw p x hp hp0 hx)
  have hU : KSet n ⊆ Ω := fun g hg => hGΩ hg.1
  have hcd : ∀ c : M2 n → ℂ, ContDiff ℝ ∞ c →
      ContDiffOn ℝ 1 (fun y => c y * (F1 y * F2 y)) Ω := fun c hc =>
    (hc.contDiffOn.mul (hΘc.restrict_scalars ℝ)).of_le (by simp)
  have hA : ∀ a b : Fin n, Integrable (fun k => dK (fun y => cA Z a b y * (F1 y * F2 y)) (ι k) (eA a b)) μ ∧
      ∫ k, dK (fun y => cA Z a b y * (F1 y * F2 y)) (ι k) (eA a b) ∂μ = 0 := fun a b =>
    hL n Kg μ ι hι hK _ Ω hΩ hU (hcd _ (hC n Z a b).1) (eA a b) (eA_comm a b)
  have hB : ∀ a b : Fin n, Integrable (fun k => dK (fun y => cB Z a b y * (F1 y * F2 y)) (ι k) (eB a b)) μ ∧
      ∫ k, dK (fun y => cB Z a b y * (F1 y * F2 y)) (ι k) (eB a b) ∂μ = 0 := fun a b =>
    hL n Kg μ ι hι hK _ Ω hΩ hU (hcd _ (hC n Z a b).2) (eB a b) (eB_comm a b)
  have key : ∀ k : Kg, fderiv ℂ F1 (ι k) (ι k * Z) * F2 (ι k) + F1 (ι k) * fderiv ℂ F2 (ι k) (ι k * Z) =
      ∑ a : Fin n, ∑ b : Fin n, (dK (fun y => cA Z a b y * (F1 y * F2 y)) (ι k) (eA a b) +
        dK (fun y => cB Z a b y * (F1 y * F2 y)) (ι k) (eB a b)) := by
    intro k
    have hnh : Ω ∈ nhds (ι k) := hΩ.mem_nhds (hmem k)
    have hd1 : DifferentiableAt ℂ F1 (ι k) :=
      ((hF1.differentiableOn (by simp)) _ (hmem k)).differentiableAt hnh
    have hd2 : DifferentiableAt ℂ F2 (ι k) :=
      ((hF2.differentiableOn (by simp)) _ (hmem k)).differentiableAt hnh
    have hprod : fderiv ℂ (fun y => F1 y * F2 y) (ι k) (ι k * Z) =
        fderiv ℂ F1 (ι k) (ι k * Z) * F2 (ι k) + F1 (ι k) * fderiv ℂ F2 (ι k) (ι k * Z) := by
      have h : HasFDerivAt (fun y => F1 y * F2 y)
          (F1 (ι k) • fderiv ℂ F2 (ι k) + F2 (ι k) • fderiv ℂ F1 (ι k)) (ι k) :=
        hd1.hasFDerivAt.mul hd2.hasFDerivAt
      rw [h.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [← hprod]
    exact hI n (fun y => F1 y * F2 y) (ι k) Z (hKk k) ((hΘc.contDiffAt hnh).of_le (by simp))
      (fun Y hY => hlawΘ (ι k) (hKk k).1 Y hY)
  simp_rw [key]
  rw [integral_finset_sum]
  · refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [integral_add (hA a b).1 (hB a b).1, (hA a b).2, (hB a b).2, add_zero]
    · intro b _
      exact (hA a b).1.add (hB a b).1
  · intro a _
    exact integrable_finset_sum _ (fun b _ => (hA a b).1.add (hB a b).1)

end PositivityTheory.Rg.Sw.LVs.II

namespace PositivityTheory.Rg.Sw.LVs

theorem infInv : InfInv := II.infInv_of II.leftDeriv II.lawDeriv II.ptId II.cDiff

end PositivityTheory.Rg.Sw.LVs
end
end

section
namespace PositivityTheory.Rg.Sw

open LVs

theorem lv : LV :=
  lv_of cayley uAct (djSec_of cayley) (dpDual cayley uAct) holInt holZero singToDiff topComp infInv

theorem twoSided' : TwoSided := LVs.twoSided

end PositivityTheory.Rg.Sw
end
