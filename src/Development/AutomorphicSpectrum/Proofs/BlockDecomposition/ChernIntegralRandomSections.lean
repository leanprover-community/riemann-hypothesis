import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableZeroCount
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
import Development.AbelianVarietyTheory.Definitions.Divisors.ChartMeasApplyOfSubset
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian

section
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem integral_exp_neg_norm_sq : ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) (b := 1) one_pos
  have hd : (Module.finrank ℝ ℂ : ℝ) / 2 = 1 := by simp [Complex.finrank_real_complex]
  simp only [one_mul, div_one, hd, Real.rpow_one, neg_mul] at h
  exact h

theorem lintegral_exp_neg_norm_sq :
    ∫⁻ z : ℂ, ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) = ENNReal.ofReal Real.pi := by
  have hi : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) := by
    by_contra hn
    have h0 := integral_undef hn
    rw [integral_exp_neg_norm_sq] at h0
    exact Real.pi_ne_zero h0
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le), integral_exp_neg_norm_sq]

theorem lintegral_gW (d : ℕ) (α : Type) [Fintype α] :
    ∫⁻ C : Fin d → α → ℂ, gW d α C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) := by
  have hw : ∀ C : Fin d → α → ℂ, gW d α C =
      ∏ k, ∏ j, ENNReal.ofReal (Real.exp (-‖C k j‖ ^ 2)) := by
    intro C
    unfold gW
    simp only [← Finset.sum_neg_distrib, Real.exp_sum]
    rw [ENNReal.ofReal_prod_of_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le]
    exact Finset.prod_congr rfl fun k _ =>
      ENNReal.ofReal_prod_of_nonneg fun _ _ => (Real.exp_pos _).le
  have hm : Measurable fun z : ℂ => ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) := by fun_prop
  have hrow : ∫⁻ r : α → ℂ, ∏ j, ENNReal.ofReal (Real.exp (-‖r j‖ ^ 2)) =
      ENNReal.ofReal Real.pi ^ Fintype.card α := by
    rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (fun _ => hm.aemeasurable)]
    simp [lintegral_exp_neg_norm_sq]
  have hmr : Measurable fun r : α → ℂ => ∏ j, ENNReal.ofReal (Real.exp (-‖r j‖ ^ 2)) :=
    Finset.measurable_prod _ fun j _ => hm.comp (measurable_pi_apply j)
  simp only [hw]
  rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (fun _ => hmr.aemeasurable)]
  simp only [hrow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, mul_comm, ENNReal.ofReal_pow Real.pi_pos.le, mul_comm]

end GlobalTheory.CompanionTheory.FSCrofton
end
end

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_weight_total_mass : ∀ (d : ℕ) (α : Type) [Fintype α], ∫⁻ C : Fin d → α → ℂ, gW d α C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW
end

section
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.CroftonPartition

theorem isSigmaCompact_of_isOpen_compact {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] {U : Set X} (hU : IsOpen U) : IsSigmaCompact U := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance

theorem isSigmaCompact_inter_isClosed {X : Type} [TopologicalSpace X] {s C : Set X}
    (hs : IsSigmaCompact s) (hC : IsClosed C) : IsSigmaCompact (s ∩ C) := by
  obtain ⟨K, hK, hKs⟩ := hs
  refine ⟨fun n => K n ∩ C, fun n => (hK n).inter_right hC, ?_⟩
  rw [← hKs, Set.iUnion_inter]

theorem exists_sigmaCompact_partition : ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] (ι : Type) (S : ι → Set X), (∀ i, IsOpen (S i)) →
    (⋃ i, S i) = Set.univ → ∃ (m : ℕ) (l : Fin m → ι) (A : Fin m → Set X),
      Pairwise (Function.onFun Disjoint A) ∧ (⋃ t, A t) = Set.univ ∧ (∀ t, A t ⊆ S (l t)) ∧
      ∀ t, IsSigmaCompact (A t) := by
  intro X _ _ _ _ ι S hS hcov
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover S hS hcov.ge
  let e := t.equivFin
  let l : Fin t.card → ι := fun j => (e.symm j : ι)
  let A : Fin t.card → Set X := fun j => S (l j) \ ⋃ (i : Fin t.card) (_ : i < j), S (l i)
  refine ⟨t.card, l, A, ?_, ?_, ?_, ?_⟩
  · intro j j' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact Set.disjoint_left.2 fun x hx hx' => hx'.2 (Set.mem_iUnion₂.2 ⟨j, h, hx.1⟩)
    · exact Set.disjoint_left.2 fun x hx hx' => hx.2 (Set.mem_iUnion₂.2 ⟨j', h, hx'.1⟩)
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    have hl : l (e ⟨i, hit⟩) = i := by simp [l]
    obtain ⟨j, hj, hmin⟩ := wellFounded_lt.has_min {j : Fin t.card | x ∈ S (l j)}
      ⟨e ⟨i, hit⟩, by simpa [hl] using hxi⟩
    refine Set.mem_iUnion.2 ⟨j, hj, fun hx => ?_⟩
    obtain ⟨i', hi', hxi'⟩ := Set.mem_iUnion₂.1 hx
    exact hmin i' hxi' hi'
  · intro j
    exact Set.sdiff_subset
  · intro j
    show IsSigmaCompact (S (l j) \ ⋃ (i : Fin t.card) (_ : i < j), S (l i))
    rw [Set.sdiff_eq]
    exact isSigmaCompact_inter_isClosed (isSigmaCompact_of_isOpen_compact (hS _))
      (isClosed_compl_iff.2 (isOpen_iUnion fun i => isOpen_iUnion fun _ => hS _))

end GlobalTheory.CompanionTheory.CroftonPartition
end

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigma_compact_disjoint_refinement : ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X] (ι : Type) (S : ι → Set X), (∀ i, IsOpen (S i)) → (⋃ i, S i) = Set.univ → ∃ (m : ℕ) (l : Fin m → ι) (A : Fin m → Set X), Pairwise (Function.onFun Disjoint A) ∧ (⋃ t, A t) = Set.univ ∧ (∀ t, A t ⊆ S (l t)) ∧ ∀ t, IsSigmaCompact (A t) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CroftonPartition.exists_sigmaCompact_partition
end

section
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton.GaussDet

theorem integral_exp_sq : ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := Complex.integral_exp_neg_rpow (p := 2) (by norm_num)
  simp only [Real.rpow_two] at h
  rw [h]
  norm_num

theorem integral_sq_exp_sq : ∫ z : ℂ, ‖z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := Complex.integral_rpow_mul_exp_neg_rpow (p := 2) (q := 2) (by norm_num) (by norm_num)
  simp only [Real.rpow_two] at h
  rw [h]
  norm_num

theorem integrable_exp_sq : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) :=
  Integrable.of_integral_ne_zero (by rw [integral_exp_sq]; exact Real.pi_ne_zero)

theorem integrable_sq_exp_sq : Integrable (fun z : ℂ => ‖z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) :=
  Integrable.of_integral_ne_zero (by rw [integral_sq_exp_sq]; exact Real.pi_ne_zero)

def hf (p q : Prop) [Decidable p] [Decidable q] (z : ℂ) : ℂ :=
  (if p then z else 1) * (if q then conj z else 1) * (Real.exp (-‖z‖ ^ 2) : ℂ)

theorem continuous_hf (p q : Prop) [Decidable p] [Decidable q] : Continuous (hf p q) := by
  unfold hf
  by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, if_true, if_false] <;> fun_prop

theorem integrable_hf (p q : Prop) [Decidable p] [Decidable q] : Integrable (hf p q) := by
  refine Integrable.mono' (integrable_exp_sq.add integrable_sq_exp_sq)
    (continuous_hf p q).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  have he : 0 < Real.exp (-‖z‖ ^ 2) := Real.exp_pos _
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have hn : ‖((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ)‖ = Real.exp (-‖z‖ ^ 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
  have hb : ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - 1)]
  simp only [hf, norm_mul, hn, Pi.add_apply]
  by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, if_true, if_false, norm_one, Complex.norm_conj] <;>
    nlinarith [mul_le_mul_of_nonneg_right hb he.le, mul_pos he he, mul_nonneg (sq_nonneg ‖z‖) he.le]

theorem hf_neg_of_ne (p q : Prop) [Decidable p] [Decidable q] (h : ¬ (p ↔ q)) (z : ℂ) :
    hf p q (-z) = - hf p q z := by
  unfold hf
  by_cases hp : p <;> by_cases hq : q <;> simp_all

theorem integral_hf (p q : Prop) [Decidable p] [Decidable q] :
    ∫ z, hf p q z = if p ↔ q then (Real.pi : ℂ) else 0 := by
  by_cases h : p ↔ q
  · rw [if_pos h]
    by_cases hp : p
    · have hq : q := h.1 hp
      have : hf p q = fun z : ℂ => ((‖z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
        funext z
        simp only [hf, hp, hq, if_true, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        ring
      simp_rw [this]
      rw [integral_complex_ofReal, integral_sq_exp_sq]
    · have hq : ¬ q := fun hq => hp (h.2 hq)
      have : hf p q = fun z : ℂ => ((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
        funext z
        simp only [hf, hp, hq, if_false, one_mul]
      simp_rw [this]
      rw [integral_complex_ofReal, integral_exp_sq]
  · rw [if_neg h]
    have h1 : ∫ z, hf p q (-z) = ∫ z, hf p q z := integral_neg_eq_self _ _
    simp only [hf_neg_of_ne p q h, integral_neg] at h1
    have h2 : (2 : ℂ) * ∫ z, hf p q z = 0 := by linear_combination -h1
    simpa using h2

variable {β : Type} [Fintype β] [DecidableEq β]

def eR (r : β → ℂ) : ℂ := (Real.exp (-∑ k, ‖r k‖ ^ 2) : ℂ)

theorem row_prod (i j : β) (r : β → ℂ) :
    r i * conj (r j) * eR r = ∏ k, hf (k = i) (k = j) (r k) := by
  simp only [hf, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true, eR]
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  push_cast
  rfl

theorem integrable_row (i j : β) :
    Integrable (fun r : β → ℂ => r i * conj (r j) * eR r) := by
  simp_rw [row_prod, volume_pi]
  exact Integrable.fintype_prod (f := fun k : β => hf (k = i) (k = j)) (μ := fun _ => volume)
    fun k => integrable_hf _ _

theorem integral_row (i j : β) :
    ∫ r : β → ℂ, r i * conj (r j) * eR r =
      if i = j then (Real.pi : ℂ) ^ Fintype.card β else 0 := by
  simp_rw [row_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun k : β => hf (k = i) (k = j))]
  simp_rw [integral_hf]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg h]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [h]

variable {d : ℕ}

def rowF (G : Matrix β (Fin d) ℂ) (a c : Fin d) (r : β → ℂ) : ℂ :=
  (∑ i, r i * G i a) * conj (∑ j, r j * G j c) * eR r

theorem rowF_eq (G : Matrix β (Fin d) ℂ) (a c : Fin d) (r : β → ℂ) :
    rowF G a c r = ∑ i, ∑ j, (G i a * conj (G j c)) * (r i * conj (r j) * eR r) := by
  rw [rowF, map_sum, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring

theorem integrable_rowF (G : Matrix β (Fin d) ℂ) (a c : Fin d) : Integrable (rowF G a c) := by
  have : rowF G a c = fun r => ∑ i, ∑ j, (G i a * conj (G j c)) * (r i * conj (r j) * eR r) :=
    funext (rowF_eq G a c)
  rw [this]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    (integrable_row i j).const_mul _

theorem integral_rowF (G : Matrix β (Fin d) ℂ) (a c : Fin d) :
    ∫ r, rowF G a c r = (Real.pi : ℂ) ^ Fintype.card β * (G.conjTranspose * G) c a := by
  simp_rw [rowF_eq]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    (integrable_row i j).const_mul _]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => (integrable_row i j).const_mul _]
  simp only [integral_const_mul, integral_row, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  simp only [Complex.star_def]
  ring

theorem det_expand (G : Matrix β (Fin d) ℂ) (C : Fin d → β → ℂ) :
    ((Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) * ‖(Matrix.of C * G).det‖ ^ 2 : ℝ) : ℂ) =
      ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
          ∏ k, rowF G (σ k) (τ k) (C k) := by
  set M := Matrix.of C * G with hMdef
  have hM : ∀ k a, M k a = ∑ i, C k i * G i a := fun k a => by
    simp [hMdef, Matrix.mul_apply]
  have hd : M.det = ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, M k (σ k) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    simp [Matrix.transpose_apply]
  have hc : conj M.det =
      ∑ τ : Equiv.Perm (Fin d), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, conj (M k (τ k)) := by
    rw [hd, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, map_prod]
    simp
  have hn : ((‖M.det‖ ^ 2 : ℝ) : ℂ) = M.det * conj M.det := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hE : ((Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) : ℝ) : ℂ) = ∏ k, eR (C k) := by
    simp only [eR]
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    push_cast
    rfl
  have hp : ∀ σ τ : Equiv.Perm (Fin d), ∏ k, rowF G (σ k) (τ k) (C k) =
      (∏ k, M k (σ k)) * (∏ k, conj (M k (τ k))) * ∏ k, eR (C k) := fun σ τ => by
    simp only [rowF, Finset.prod_mul_distrib, hM]
  rw [Complex.ofReal_mul, hn, hE]
  conv_lhs => rw [hc]; rw [hd]
  simp only [hp]
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

theorem perm_sum (p : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
          ∏ k, (p * A (τ k) (σ k)) = p ^ d * (d.factorial : ℂ) * A.det := by
  have h1 : ∀ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
        ∏ k, (p * A (τ k) (σ k)) = p ^ d * A.det := fun σ => by
    have h2 := Matrix.det_permute' σ A
    rw [Matrix.det_apply'] at h2
    simp only [Matrix.submatrix_apply, id] at h2
    have hs : ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    calc _ = ((Equiv.Perm.sign σ : ℤ) : ℂ) * p ^ d *
          ∑ τ : Equiv.Perm (Fin d), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, A (τ k) (σ k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          ring
      _ = p ^ d * A.det := by
          rw [h2]
          linear_combination (p ^ d * A.det) * hs
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem integrable_prod_rowF (G : Matrix β (Fin d) ℂ) (σ τ : Equiv.Perm (Fin d)) :
    Integrable (fun C : Fin d → β → ℂ => ∏ k, rowF G (σ k) (τ k) (C k)) := by
  rw [volume_pi]
  exact Integrable.fintype_prod (f := fun k : Fin d => rowF G (σ k) (τ k)) (μ := fun _ => volume)
    fun k => integrable_rowF G _ _

theorem integral_prod_rowF (G : Matrix β (Fin d) ℂ) (σ τ : Equiv.Perm (Fin d)) :
    ∫ C : Fin d → β → ℂ, ∏ k, rowF G (σ k) (τ k) (C k) =
      ∏ k, ((Real.pi : ℂ) ^ Fintype.card β * (G.conjTranspose * G) (τ k) (σ k)) := by
  rw [integral_fintype_prod_volume_eq_prod (fun k : Fin d => rowF G (σ k) (τ k))]
  simp_rw [integral_rowF]

def fR (G : Matrix β (Fin d) ℂ) (C : Fin d → β → ℂ) : ℝ :=
  Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) * ‖(Matrix.of C * G).det‖ ^ 2

theorem integrable_fR_complex (G : Matrix β (Fin d) ℂ) :
    Integrable (fun C => ((fR G C : ℝ) : ℂ)) := by
  simp_rw [fR, det_expand]
  exact integrable_finset_sum _ fun σ _ => integrable_finset_sum _ fun τ _ =>
    (integrable_prod_rowF G σ τ).const_mul _

theorem integral_fR_complex (G : Matrix β (Fin d) ℂ) :
    ∫ C, ((fR G C : ℝ) : ℂ) = ((Real.pi : ℂ) ^ Fintype.card β) ^ d * (d.factorial : ℂ) *
      (G.conjTranspose * G).det := by
  simp_rw [fR, det_expand]
  rw [integral_finset_sum _ fun σ _ => integrable_finset_sum _ fun τ _ =>
    (integrable_prod_rowF G σ τ).const_mul _]
  rw [← perm_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finset_sum _ fun τ _ => (integrable_prod_rowF G σ τ).const_mul _]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul, integral_prod_rowF]

end GlobalTheory.CompanionTheory.FSCrofton.GaussDet

open GlobalTheory.CompanionTheory.FSCrofton.GaussDet in

theorem GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW_norm_det_sq (d : ℕ) (β : Type) [Fintype β] [DecidableEq β]
    (G : Matrix β (Fin d) ℂ) :
    ∫⁻ C : Fin d → β → ℂ, gW d β C * ENNReal.ofReal (‖(Matrix.of C * G).det‖ ^ 2) =
      ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) *
        (G.conjTranspose * G).det.re) := by
  have hint : Integrable (fR G) := by
    have := (integrable_fR_complex G).re
    simpa using this
  have hnn : 0 ≤ᵐ[volume] fR G := ae_of_all _ fun C => by
    simp only [fR, Pi.zero_apply]
    positivity
  have hval : ∫ C, fR G C = Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) *
      (G.conjTranspose * G).det.re := by
    have h := integral_fR_complex G
    rw [integral_complex_ofReal] at h
    have h2 := congrArg Complex.re h
    rw [Complex.ofReal_re] at h2
    rw [h2, pow_mul' ]
    have : ((Real.pi : ℂ) ^ Fintype.card β) ^ d * (d.factorial : ℂ) =
        (((Real.pi ^ Fintype.card β) ^ d * (d.factorial : ℝ) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [this, Complex.re_ofReal_mul]
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hint hnn]
  refine lintegral_congr fun C => ?_
  rw [gW, fR, ENNReal.ofReal_mul (Real.exp_pos _).le]
end
end

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_det_square_integral : ∀ (d : ℕ) (β : Type) [Fintype β] [DecidableEq β] (G : Matrix β (Fin d) ℂ), ∫⁻ C : Fin d → β → ℂ, gW d β C * ENNReal.ofReal (‖(Matrix.of C * G).det‖ ^ 2) = ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) * (G.conjTranspose * G).det.re) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW_norm_det_sq
end

section
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton.GaussLevi

open Matrix

variable {β : Type} [Fintype β] [DecidableEq β]

def rk (f : β → ℂ) : Matrix β β ℂ := vecMulVec f (star f)

def nS (f : β → ℂ) : ℝ := 1 + ∑ j, ‖f j‖ ^ 2

theorem nS_pos (f : β → ℂ) : 0 < nS f := by
  unfold nS; positivity

theorem star_dot (f : β → ℂ) : star f ⬝ᵥ f = ((nS f - 1 : ℝ) : ℂ) := by
  simp [nS, dotProduct, Complex.conj_mul']

theorem rk_mul_rk (f : β → ℂ) : rk f * rk f = ((nS f - 1 : ℝ) : ℂ) • rk f := by
  unfold rk
  rw [vecMulVec_mul_vecMulVec, star_dot, vecMulVec_smul]

theorem rk_conjTranspose (f : β → ℂ) : (rk f)ᴴ = rk f := by
  unfold rk
  rw [conjTranspose_vecMulVec, star_star]

theorem one_add_mul_one_sub (A : Matrix β β ℂ) (c t u : ℂ) (h : A * A = c • A) :
    (1 + t • A) * (1 - u • A) = 1 + (t - u - t * u * c) • A := by
  simp only [mul_sub, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h, smul_smul]
  module

theorem one_sub_mul_one_sub (A : Matrix β β ℂ) (c u : ℂ) (h : A * A = c • A) :
    (1 - u • A) * (1 - u • A) = 1 + (-(2 * u) + u * u * c) • A := by
  simp only [mul_sub, sub_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h, smul_smul]
  module

def pM (f : β → ℂ) : Matrix β β ℂ := 1 + ((1 / (1 + √(nS f)) : ℝ) : ℂ) • rk f

def rM (f : β → ℂ) : Matrix β β ℂ := 1 - ((1 / (√(nS f) * (1 + √(nS f))) : ℝ) : ℂ) • rk f

theorem sqrt_facts (f : β → ℂ) : 0 < √(nS f) ∧ √(nS f) * √(nS f) = nS f :=
  ⟨Real.sqrt_pos.2 (nS_pos f), Real.mul_self_sqrt (nS_pos f).le⟩

theorem pM_mul_rM (f : β → ℂ) : pM f * rM f = 1 := by
  obtain ⟨h0, h1⟩ := sqrt_facts f
  unfold pM rM
  rw [one_add_mul_one_sub _ _ _ _ (rk_mul_rk f)]
  have : ((1 / (1 + √(nS f)) : ℝ) : ℂ) - ((1 / (√(nS f) * (1 + √(nS f))) : ℝ) : ℂ) -
      ((1 / (1 + √(nS f)) : ℝ) : ℂ) * ((1 / (√(nS f) * (1 + √(nS f))) : ℝ) : ℂ) *
        ((nS f - 1 : ℝ) : ℂ) = 0 := by
    norm_cast
    generalize √(nS f) = s at h0 h1 ⊢
    rw [← h1]
    field_simp
    ring
  rw [this, zero_smul, add_zero]

theorem rM_conjTranspose (f : β → ℂ) : (rM f)ᴴ = rM f := by
  unfold rM
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, rk_conjTranspose]
  simp

theorem rM_mul_rM (f : β → ℂ) : rM f * rM f = 1 - ((1 / nS f : ℝ) : ℂ) • rk f := by
  obtain ⟨h0, h1⟩ := sqrt_facts f
  unfold rM
  rw [one_sub_mul_one_sub _ _ _ (rk_mul_rk f), sub_eq_add_neg 1, ← neg_smul]
  congr 2
  norm_cast
  generalize √(nS f) = s at h0 h1 ⊢
  rw [← h1]
  field_simp
  ring

theorem det_pM (f : β → ℂ) : (pM f).det = ((√(nS f) : ℝ) : ℂ) := by
  obtain ⟨h0, h1⟩ := sqrt_facts f
  have e : pM f = 1 + replicateCol Unit (((1 / (1 + √(nS f)) : ℝ) : ℂ) • f) *
      replicateRow Unit (star f) := by
    unfold pM rk
    congr 1
    ext i j
    simp [vecMulVec_apply, Matrix.mul_apply, mul_assoc]
  rw [e, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, star_dot]
  simp only [smul_eq_mul]
  norm_cast
  generalize √(nS f) = s at h0 h1 ⊢
  rw [← h1]
  field_simp
  ring

theorem vecMul_pM_apply (f r : β → ℂ) (j : β) :
    (r ᵥ* pM f) j = r j + ((1 / (1 + √(nS f)) : ℝ) : ℂ) * (∑ i, r i * f i) * conj (f j) := by
  unfold pM rk
  rw [vecMul_add, vecMul_one, vecMul_smul, vecMul_vecMulVec]
  simp [dotProduct, mul_assoc]

theorem sum_norm_sq_vecMul_pM (f r : β → ℂ) :
    ∑ j, ‖(r ᵥ* pM f) j‖ ^ 2 = ‖∑ i, r i * f i‖ ^ 2 + ∑ j, ‖r j‖ ^ 2 := by
  obtain ⟨h0, h1⟩ := sqrt_facts f
  have ht1 : (1 / (1 + √(nS f))) ^ 2 * (nS f - 1) + 2 * (1 / (1 + √(nS f))) = 1 := by
    generalize √(nS f) = s at h0 h1 ⊢
    rw [← h1]
    field_simp
    ring
  generalize ha : ∑ i, r i * f i = a
  generalize htt : 1 / (1 + √(nS f)) = t at ht1
  have hterm : ∀ j, ‖(r ᵥ* pM f) j‖ ^ 2 =
      ‖r j‖ ^ 2 + t ^ 2 * ‖a‖ ^ 2 * ‖f j‖ ^ 2 + 2 * t * (r j * f j * conj a).re := by
    intro j
    rw [vecMul_pM_apply, ha, htt, Complex.sq_norm, Complex.normSq_add, ← Complex.sq_norm (r j)]
    have e1 : Complex.normSq ((t : ℂ) * a * conj (f j)) = t ^ 2 * ‖a‖ ^ 2 * ‖f j‖ ^ 2 := by
      simp [Complex.normSq_eq_norm_sq, mul_pow]
    have e2 : r j * conj ((t : ℂ) * a * conj (f j)) = (t : ℂ) * (r j * f j * conj a) := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
      ring
    rw [e1, e2, Complex.re_ofReal_mul]
    ring
  have hs : ∑ j, (r j * f j * conj a).re = ‖a‖ ^ 2 := by
    rw [← Complex.re_sum, ← Finset.sum_mul, ha, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hf : ∑ j, ‖f j‖ ^ 2 = nS f - 1 := by simp [nS]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, hf]
  linear_combination ‖a‖ ^ 2 * ht1

theorem lintegral_rows (d : ℕ) (P : Matrix β β ℂ) (hP : P.det ≠ 0)
    (H : (Fin d → β → ℂ) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ C : Fin d → β → ℂ, H (fun k => C k ᵥ* P) =
      ENNReal.ofReal |((Complex.normSq P.det) ^ d)⁻¹| * ∫⁻ D, H D := by
  let T : (β → ℂ) →ₗ[ℝ] (β → ℂ) := (Matrix.toLin' Pᵀ).restrictScalars ℝ
  let L : (Fin d → β → ℂ) →ₗ[ℝ] (Fin d → β → ℂ) := LinearMap.pi fun k => T ∘ₗ LinearMap.proj k
  have hdT : LinearMap.det T = Complex.normSq P.det := by
    simp only [T]
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose,
      Algebra.norm_complex_apply]
  have hdL : LinearMap.det L = (Complex.normSq P.det) ^ d := by
    simp only [L]
    rw [LinearMap.det_pi, Finset.prod_const, hdT]
    simp
  have hne : LinearMap.det L ≠ 0 := by
    rw [hdL]
    exact pow_ne_zero _ (Complex.normSq_pos.2 hP).ne'
  have hL : (fun C : Fin d → β → ℂ => fun k => C k ᵥ* P) = L := by
    funext C k
    simp [L, T, toLin'_apply, mulVec_transpose]
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  haveI : (volume : Measure (β → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin d → β → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have e : ∫⁻ C : Fin d → β → ℂ, H (fun k => C k ᵥ* P) = ∫⁻ C, H (L C) := by
    rw [← hL]
  rw [e, ← lintegral_map hH hLm, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hne,
    lintegral_smul_measure, hdL]
  rfl

theorem gram_eq {d : ℕ} (f : β → ℂ) (F : Matrix β (Fin d) ℂ) :
    (rM f * F)ᴴ * (rM f * F) =
      Fᴴ * F - ((1 / nS f : ℝ) : ℂ) • vecMulVec (Fᴴ *ᵥ f) (star f ᵥ* F) := by
  rw [conjTranspose_mul, rM_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (rM f), rM_mul_rM,
    Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]
  congr 2
  unfold rk
  rw [vecMulVec_mul, mul_vecMulVec]

theorem fsLevi_eq {d : ℕ} (f : β → ℂ) (F : Matrix β (Fin d) ℂ) :
    fsLevi f F = ((1 / nS f : ℝ) : ℂ) • ((rM f * F)ᴴ * (rM f * F))ᵀ := by
  have hS : ((nS f : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nS_pos f).ne'
  rw [gram_eq]
  ext a c
  have hX : ∑ j, F j a * conj (F j c) = (Fᴴ * F) c a := by
    simp [Matrix.mul_apply, mul_comm]
  have hY : ∑ j, F j a * conj (f j) = (star f ᵥ* F) a := by
    simp [vecMul, dotProduct, mul_comm]
  have hZ : ∑ j, f j * conj (F j c) = (Fᴴ *ᵥ f) c := by
    simp [mulVec, dotProduct, mul_comm]
  have h1 : ((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) = ((nS f : ℝ) : ℂ) := rfl
  simp only [fsLevi, of_apply, hX, hY, hZ, h1, Matrix.smul_apply, transpose_apply, Matrix.sub_apply,
    vecMulVec_apply, smul_eq_mul]
  push_cast
  field_simp

theorem lintegral_gauss_levi : ∀ (d : ℕ) (β : Type) [Fintype β] [DecidableEq β] (f : β → ℂ)
    (F : Matrix β (Fin d) ℂ),
    ∫⁻ C : Fin d → β → ℂ, gW d β C *
        ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * f j‖ ^ 2) * ‖(Matrix.of C * F).det‖ ^ 2) =
      ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) * (fsLevi f F).det.re) := by
  intro d β _ _ f F
  obtain ⟨h0, h1⟩ := sqrt_facts f
  have hSp := nS_pos f
  let G : Matrix β (Fin d) ℂ := rM f * F
  let H : (Fin d → β → ℂ) → ℝ≥0∞ := fun D =>
    gW d β D * ENNReal.ofReal (‖(Matrix.of D * G).det‖ ^ 2)
  have hH : Measurable H := by
    have c1 : Continuous fun D : Fin d → β → ℂ => Real.exp (-∑ k, ∑ j, ‖D k j‖ ^ 2) := by
      fun_prop
    have c2 : Continuous fun D : Fin d → β → ℂ => (Matrix.of D * G).det :=
      Continuous.matrix_det (Continuous.matrix_mul continuous_id continuous_const)
    exact (ENNReal.measurable_ofReal.comp c1.measurable).mul
      (ENNReal.measurable_ofReal.comp (c2.norm.pow 2).measurable)
  have hpt : ∀ C : Fin d → β → ℂ, gW d β C *
      ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * f j‖ ^ 2) * ‖(Matrix.of C * F).det‖ ^ 2) =
      H (fun k => C k ᵥ* pM f) := by
    intro C
    have hrow : Matrix.of (fun k => C k ᵥ* pM f) = Matrix.of C * pM f := by
      ext k j
      simp [vecMul, Matrix.mul_apply, dotProduct]
    have hdet : Matrix.of (fun k => C k ᵥ* pM f) * G = Matrix.of C * F := by
      rw [hrow, Matrix.mul_assoc]
      simp only [G]
      rw [← Matrix.mul_assoc (pM f), pM_mul_rM, Matrix.one_mul]
    simp only [H, gW]
    rw [hdet]
    simp_rw [sum_norm_sq_vecMul_pM]
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, Finset.sum_add_distrib]
    congr 3
    ring
  have hPd : (pM f).det ≠ 0 := by
    rw [det_pM]
    exact_mod_cast h0.ne'
  simp_rw [hpt]
  rw [lintegral_rows d (pM f) hPd H hH]
  have hI : ∫⁻ D, H D = ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) *
      (G.conjTranspose * G).det.re) := GlobalTheory.T.gaussian_det_square_integral d β G
  rw [hI, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  have hn : Complex.normSq (pM f).det = nS f := by
    rw [det_pM, Complex.normSq_ofReal, h1]
  have hL : (fsLevi f F).det.re = (1 / nS f) ^ d * (G.conjTranspose * G).det.re := by
    rw [fsLevi_eq, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
    simp only [G]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  rw [hn, hL, abs_of_pos (inv_pos.2 (pow_pos hSp d)), one_div, inv_pow]
  ring

end GlobalTheory.CompanionTheory.FSCrofton.GaussLevi
end
end

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_det_levi_integral : ∀ (d : ℕ) (β : Type) [Fintype β] [DecidableEq β] (f : β → ℂ) (F : Matrix β (Fin d) ℂ), ∫⁻ C : Fin d → β → ℂ, gW d β C * ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * f j‖ ^ 2) * ‖(Matrix.of C * F).det‖ ^ 2) = ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) * (fsLevi f F).det.re) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.lintegral_gauss_levi
end

section
section
noncomputable section

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton Filter Topology
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

variable {n : ℕ}

theorem hessLog_chain {k : ℝ → ℝ} {v : V n → ℝ} {x : V n} (hv : ContDiffAt ℝ 2 v x)
    (hk : ContDiffAt ℝ 2 k (v x)) (j c : Fin n) :
    wd n j (wdb n c (fun y => ((k (v y) : ℝ) : ℂ))) x =
      ((deriv (deriv k) (v x) : ℝ) : ℂ) * wd n j (fun y => ((v y : ℝ) : ℂ)) x *
          conj (wd n c (fun y => ((v y : ℝ) : ℂ)) x) +
        ((deriv k (v x) : ℝ) : ℂ) * wd n j (wdb n c (fun y => ((v y : ℝ) : ℂ))) x := by
  have hv1 : DifferentiableAt ℝ v x := hv.differentiableAt (by simp)
  have hk1 : DifferentiableAt ℝ (deriv k) (v x) := differentiableAt_deriv_of_contDiffAt hk
  have hv' : ContDiffAt ℝ 2 (fun y => ((v y : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hv
  have hvd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y := eventually_differentiableAt_of_contDiffAt hv
  have hkd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ k (v y) :=
    hv1.continuousAt.tendsto.eventually (eventually_differentiableAt_of_contDiffAt hk)
  have hE : wdb n c (fun y => ((k (v y) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun y => ((deriv k (v y) : ℝ) : ℂ) * wdb n c (fun y => ((v y : ℝ) : ℂ)) y := by
    filter_upwards [hvd, hkd] with y hy1 hy2
    exact wdb_ofReal_comp hy2 hy1
  have hD1 : DifferentiableAt ℝ (fun y => ((deriv k (v y) : ℝ) : ℂ)) x :=
    differentiableAt_ofReal (hk1.comp x hv1)
  rw [wd_congr hE,
    wd_mul (f := fun y => ((deriv k (v y) : ℝ) : ℂ)) (g := wdb n c (fun y => ((v y : ℝ) : ℂ)))
      hD1 (differentiableAt_wdb hv'),
    wd_ofReal_comp hk1 hv1, wdb_ofReal hv1]

theorem hessLog_normSq {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) (j c : Fin n) :
    wd n j (wdb n c (fun y => ((Complex.normSq (g y) : ℝ) : ℂ))) x =
      wd n j g x * conj (wd n c g x) := by
  have hgd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y :=
    (hg.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by simp)
  have hgx : DifferentiableAt ℂ g x := hg.differentiableAt (by simp)
  have hf : (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) := by
    funext y; rw [Complex.mul_conj]
  have h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x := hg.fderiv_right (by norm_num)
  have hh : DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n c)) x :=
    (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
  have hE : wdb n c (fun y => g y * conj (g y)) =ᶠ[𝓝 x]
      fun y => g y * conj (fderiv ℂ g y (bas n c)) := by
    filter_upwards [hgd] with y hy
    rw [wdb_mul (hy.restrictScalars ℝ) (differentiableAt_conj (hy.restrictScalars ℝ)),
      wdb_of_differentiableAt hy, wdb_conj (hy.restrictScalars ℝ), wd_of_differentiableAt hy]
    ring
  rw [hf, wd_congr hE, wd_mul (f := g) (g := fun y => conj (fderiv ℂ g y (bas n c)))
    (hgx.restrictScalars ℝ) (differentiableAt_conj (hh.restrictScalars ℝ)),
    wd_conj (hh.restrictScalars ℝ), wdb_of_differentiableAt hh]
  simp [wd_of_differentiableAt hgx]

theorem cHess_log_one_add_sum : ∀ (d : ℕ) (β : Type) [Fintype β] (U : Set (V d)) (f : β → V d → ℂ),
    IsOpen U → (∀ j, DifferentiableOn ℂ (f j) U) → ∀ z ∈ U,
    cHess d (fun v => ((Real.log (1 + ∑ j, ‖f j v‖ ^ 2) : ℝ) : ℂ)) z =
      fsLevi (fun j => f j z) (Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1)) := by
  intro d β _ U f hU hf z hz
  have hC : ∀ j, ContDiffAt ℂ 2 (f j) z := fun j =>
    ((contDiffOn_of_differentiableOn d (f j) U hU (hf j)).contDiffAt (hU.mem_nhds hz)).of_le
      ENat.LEInfty.out
  have hu : ∀ j, ContDiffAt ℝ 2 (fun y => Complex.normSq (f j y)) z := fun j =>
    H.contDiffAt_normSq_comp (hC j)
  have hu' : ∀ j, ContDiffAt ℝ 2 (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) z := fun j =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (hu j)
  have hnorm : ∀ v, (1 + ∑ j, ‖f j v‖ ^ 2 : ℝ) = 1 + ∑ j, Complex.normSq (f j v) := fun v => by
    simp only [Complex.normSq_eq_norm_sq]
  set S : V d → ℝ := fun y => 1 + ∑ j, Complex.normSq (f j y) with hSdef
  have hSpos : 0 < S z :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)
  have hS : ContDiffAt ℝ 2 S z := contDiffAt_const.add (ContDiffAt.sum fun j _ => hu j)
  have hlog : ContDiffAt ℝ 2 Real.log (S z) := Real.contDiffAt_log.2 hSpos.ne'
  have hSc : (fun y => ((S y : ℝ) : ℂ)) =
      fun y => 1 + ∑ j, ((Complex.normSq (f j y) : ℝ) : ℂ) := by
    funext y; simp [hSdef]
  have hTd : ∀ {y}, (∀ j, DifferentiableAt ℝ (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) y) →
      DifferentiableAt ℝ (fun y => ∑ j, ((Complex.normSq (f j y) : ℝ) : ℂ)) y := fun h =>
    DifferentiableAt.fun_sum fun j _ => h j
  have hwd : ∀ a, wd d a (fun y => ((S y : ℝ) : ℂ)) z =
      ∑ j, wd d a (f j) z * conj (f j z) := fun a => by
    have h1 : ∀ j, DifferentiableAt ℝ (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) z := fun j =>
      (hu' j).differentiableAt (by simp)
    rw [hSc, wd_add (differentiableAt_const _) (hTd h1), wd_sum Finset.univ fun j _ => h1 j]
    simp only [fun j => H.wd_normSq_comp (j := a) (hC j)]
    simp [wd]
  have hhess : ∀ a c, wd d a (wdb d c (fun y => ((S y : ℝ) : ℂ))) z =
      ∑ j, wd d a (f j) z * conj (wd d c (f j) z) := fun a c => by
    have hev : wdb d c (fun y => ((S y : ℝ) : ℂ)) =ᶠ[𝓝 z]
        fun y => ∑ j, wdb d c (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) y := by
      have : ∀ᶠ y in 𝓝 z, ∀ j,
          DifferentiableAt ℝ (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) y := by
        rw [Filter.eventually_all]
        exact fun j => eventually_differentiableAt_of_contDiffAt (hu' j)
      filter_upwards [this] with y hy
      rw [hSc, wdb_add (differentiableAt_const _) (hTd hy), wdb_sum Finset.univ fun j _ => hy j]
      simp [wdb]
    rw [wd_congr hev, wd_sum Finset.univ fun j _ => differentiableAt_wdb (hu' j)]
    exact Finset.sum_congr rfl fun j _ => hessLog_normSq (hC j) a c
  have hd1 : deriv Real.log (S z) = (S z)⁻¹ := by rw [Real.deriv_log']
  have hd2 : deriv (deriv Real.log) (S z) = -((S z) ^ 2)⁻¹ := by
    rw [Real.deriv_log']; exact deriv_inv
  have hS0 : ((S z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hSpos.ne'
  ext a c
  have hfun : (fun v => ((Real.log (1 + ∑ j, ‖f j v‖ ^ 2) : ℝ) : ℂ)) =
      fun v => ((Real.log (S v) : ℝ) : ℂ) := by
    funext v; rw [hnorm]
  have hF : ∀ (j : β) (a : Fin d), fderiv ℂ (f j) z (EuclideanSpace.single a 1) = wd d a (f j) z :=
    fun j a => (wd_of_differentiableAt ((hC j).differentiableAt (by simp))).symm
  have hval : ((1 + ∑ j, ‖f j z‖ ^ 2 : ℝ) : ℂ) = ((S z : ℝ) : ℂ) := by rw [hnorm]
  simp only [cHess, fsLevi, Matrix.of_apply, hF, hfun, hval]
  rw [hessLog_chain hS hlog a c, hd1, hd2, hwd a, hwd c, hhess a c, map_sum]
  have hconj : ∑ j, conj (wd d c (f j) z * conj (f j z)) = ∑ j, f j z * conj (wd d c (f j) z) :=
    Finset.sum_congr rfl fun j _ => by rw [map_mul, Complex.conj_conj, mul_comm]
  rw [hconj]
  push_cast
  field_simp
  ring

end GlobalTheory.CompanionTheory.FSCrofton
end
end

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_hessian_log_fubini_study : ∀ (d : ℕ) (β : Type) [Fintype β] (U : Set (V d)) (f : β → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (f j) U) → ∀ z ∈ U, cHess d (fun v => ((Real.log (1 + ∑ j, ‖f j v‖ ^ 2) : ℝ) : ℂ)) z = fsLevi (fun j => f j z) (Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FSCrofton.cHess_log_one_add_sum
end

section
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.CompanionTheory.FSCrofton.HessFrame

private lemma contDiffOn_norm_sq_of_differentiableOn {d : ℕ} {U : Set (V d)} (hU : IsOpen U) {f : V d → ℂ}
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℝ ∞ (fun v => ‖f v‖ ^ 2) U :=
  (contDiff_norm_sq ℝ).comp_contDiffOn
    ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn d f U hU hf).restrict_scalars ℝ)

theorem cHess_log_sum_normSq_eq (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α)
    (U : Set (V d)) (b : α → V d → ℂ) (hU : IsOpen U) (hb : ∀ j, DifferentiableOn ℂ (b j) U)
    (h0 : ∀ z ∈ U, b j₀ z ≠ 0) : ∀ z ∈ U,
    cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z =
      cHess d (fun v => ((Real.log (1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2) : ℝ) : ℂ))
        z := by
  intro z hz
  obtain ⟨R, hRdef⟩ : ∃ R : V d → ℝ,
      R = fun v => 1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2 := ⟨_, rfl⟩
  have hpos : ∀ v ∈ U, 0 < ‖b j₀ v‖ ^ 2 := fun v hv => pow_pos (norm_pos_iff.2 (h0 v hv)) 2
  have hRpos : ∀ v, 0 < R v := fun v => by rw [hRdef]; positivity
  have hp : ContDiffOn ℝ ∞ (fun v => Real.log (‖b j₀ v‖ ^ 2)) U :=
    (contDiffOn_norm_sq_of_differentiableOn hU (hb j₀)).log fun v hv => (hpos v hv).ne'
  have hq : ContDiffOn ℝ ∞ (fun v => Real.log (R v)) U := by
    refine ContDiffOn.log ?_ fun v _ => (hRpos v).ne'
    rw [hRdef]
    exact contDiffOn_const.add
      (ContDiffOn.sum fun j _ => contDiffOn_norm_sq_of_differentiableOn hU (by
        simpa only [div_eq_mul_inv] using (hb j.1).fun_mul ((hb j₀).fun_inv h0)))
  have hsplit : ∀ v ∈ U, ∑ j, ‖b j v‖ ^ 2 = ‖b j₀ v‖ ^ 2 * R v := by
    intro v hv
    have hn : ‖b j₀ v‖ ^ 2 ≠ 0 := (hpos v hv).ne'
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀),
      Finset.sum_subtype (F := inferInstance) (Finset.univ.erase j₀) (p := fun j => j ≠ j₀) (by simp),
      hRdef]
    simp only [mul_add, mul_one, Finset.mul_sum, norm_div, div_pow, mul_div_cancel₀ _ hn]
  have hev : (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) =ᶠ[nhds z]
      fun v => ((Real.log (‖b j₀ v‖ ^ 2) + 1 * Real.log (R v) : ℝ) : ℂ) := by
    refine Filter.eventually_of_mem (hU.mem_nhds hz) fun v hv => ?_
    simp only
    rw [hsplit v hv, Real.log_mul (hpos v hv).ne' (hRpos v).ne', one_mul]
  have hzero : cHess d (fun w => ((Real.log (‖b j₀ w‖ ^ 2) : ℝ) : ℂ)) z = 0 := by
    ext j k
    simp only [cHess, Matrix.of_apply, Matrix.zero_apply]
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log hU hz (hb j₀) h0 j k
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr hev,
    ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul hU hp hq 1 hz, hzero, zero_add, Complex.ofReal_one,
    one_smul, hRdef]

end GlobalTheory.CompanionTheory.FSCrofton.HessFrame
end

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_hessian_log_dehomogenise : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U : Set (V d)) (b : α → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (b j) U) → (∀ z ∈ U, b j₀ z ≠ 0) → ∀ z ∈ U, cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z = cHess d (fun v => ((Real.log (1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2) : ℝ) : ℂ)) z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FSCrofton.HessFrame.cHess_log_sum_normSq_eq
end

section
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem clm_apply_eq_sum {d : ℕ} (T : V d →L[ℂ] ℂ) (v : V d) :
    T v = ∑ a, v a * T (EuclideanSpace.single a 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℂ).sum_repr v]
  simp [map_sum]

theorem abs_det_restrictScalars_toEuclideanCLM {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    |((Matrix.toEuclideanCLM (𝕜 := ℂ) M : V d →L[ℂ] V d).restrictScalars ℝ).det| =
      ‖M.det‖ ^ 2 := by
  have h1 : ((Matrix.toEuclideanCLM (𝕜 := ℂ) M : V d →L[ℂ] V d).restrictScalars ℝ).det =
      Algebra.norm ℝ (LinearMap.det (Matrix.toEuclideanLin M : V d →ₗ[ℂ] V d)) := by
    rw [← LinearMap.det_restrictScalars]
    rfl
  rw [h1, Matrix.toEuclideanLin_eq_toLin, LinearMap.det_toLin, Algebra.norm_complex_eq]
  simp [Complex.normSq_eq_norm_sq]

theorem area_formula_neg_comb (d : ℕ) (β : Type) [Fintype β] (U A : Set (V d)) (f : β → V d → ℂ)
    (C : Fin d → β → ℂ) (h : (Fin d → ℂ) → ℝ≥0∞) (hU : IsOpen U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (hAU : A ⊆ U) (hA : MeasurableSet A)
    (hh : Measurable h) :
    ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞) =
      ∫⁻ z in A, h (fun k => -∑ j, C k j * f j z) *
        ENNReal.ofReal (‖(Matrix.of C * (Matrix.of fun j a =>
          fderiv ℂ (f j) z (EuclideanSpace.single a 1) : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by
  classical
  let F : V d → Matrix β (Fin d) ℂ := fun z =>
    Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1)
  let M : V d → Matrix (Fin d) (Fin d) ℂ := fun z => -(Matrix.of C * F z)
  let g : V d → V d := fun z => WithLp.toLp 2 (fun k => -∑ j, C k j * f j z)
  let L : V d → V d →L[ℂ] V d := fun z => Matrix.toEuclideanCLM (𝕜 := ℂ) (M z)
  let f' : V d → V d →L[ℝ] V d := fun z => (L z).restrictScalars ℝ
  have hderC : ∀ z ∈ A, HasFDerivWithinAt g (L z) A z := by
    intro z hz
    rw [hasFDerivWithinAt_euclidean]
    intro k
    have hj : ∀ j, HasFDerivAt (f j) (fderiv ℂ (f j) z) z := fun j =>
      ((hf j).differentiableAt (hU.mem_nhds (hAU hz))).hasFDerivAt
    have hs : HasFDerivAt (fun w => -∑ j, C k j * f j w)
        (-∑ j, C k j • fderiv ℂ (f j) z) z :=
      (HasFDerivAt.fun_sum fun j _ => (hj j).const_mul (C k j)).neg
    have he : PiLp.proj 2 (fun _ : Fin d => ℂ) k ∘L L z = -∑ j, C k j • fderiv ℂ (f j) z := by
      ext v
      have hv : ∀ j, fderiv ℂ (f j) z v = ∑ a, v a * F z j a := fun j => clm_apply_eq_sum _ v
      change ((Matrix.toEuclideanCLM (𝕜 := ℂ) (M z)) v).ofLp k = _
      rw [Matrix.ofLp_toEuclideanCLM]
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, hv]
      simp only [M, Matrix.mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply,
        neg_mul, Finset.sum_neg_distrib, neg_inj]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [he]
    exact hs.hasFDerivWithinAt
  have hder : ∀ z ∈ A, HasFDerivWithinAt g (f' z) A z := fun z hz =>
    (hderC z hz).restrictScalars ℝ
  have hdet : ∀ z, |(f' z).det| = ‖(Matrix.of C * F z).det‖ ^ 2 := by
    intro z
    have := abs_det_restrictScalars_toEuclideanCLM (M z)
    rw [show (M z).det = (-1) ^ Fintype.card (Fin d) * (Matrix.of C * F z).det from
      Matrix.det_neg _] at this
    simpa using this
  have hp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin d → ℂ))
      (volume : Measure (Fin d → ℂ)) (volume : Measure (V d)) :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm
      (GlobalTheory.volume_preserving_ofLp_complex (Fin d))
  have hw := (GroundTheory.Heights₂.Heights.AreaMultiplicityWeight.proof (V d) volume A g f' hA hder).2
    (fun y => h y.ofLp) (hh.comp (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm.measurable)
  have hfib : ∀ c : Fin d → ℂ, {z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0} =
      {z ∈ A | g z = WithLp.toLp 2 c} := by
    intro c
    ext z
    simp only [Set.mem_setOf_eq, g]
    refine and_congr_right fun _ => ?_
    rw [(WithLp.toLp_injective 2).eq_iff, funext_iff]
    refine forall_congr' fun k => ?_
    rw [neg_eq_iff_add_eq_zero, add_comm]
  calc ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞)
      = ∫⁻ c : Fin d → ℂ, (fun y : V d => (({z ∈ A | g z = y}.encard : ℕ∞) : ℝ≥0∞) * h y.ofLp)
          (MeasurableEquiv.toLp 2 (Fin d → ℂ) c) := by
        refine lintegral_congr fun c => ?_
        rw [hfib c, mul_comm]
        rfl
    _ = ∫⁻ y : V d, (({z ∈ A | g z = y}.encard : ℕ∞) : ℝ≥0∞) * h y.ofLp :=
        hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
          (fun y : V d => (({z ∈ A | g z = y}.encard : ℕ∞) : ℝ≥0∞) * h y.ofLp)
    _ = ∫⁻ z in A, h (g z).ofLp * ENNReal.ofReal |(f' z).det| := hw.symm
    _ = _ := by
        refine lintegral_congr fun z => ?_
        rw [hdet z]

end GlobalTheory.CompanionTheory.FSCrofton
end
end

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.change_variables_zero_count : ∀ (d : ℕ) (β : Type) [Fintype β] (U A : Set (V d)) (f : β → V d → ℂ) (C : Fin d → β → ℂ) (h : (Fin d → ℂ) → ℝ≥0∞), IsOpen U → (∀ j, DifferentiableOn ℂ (f j) U) → A ⊆ U → MeasurableSet A → Measurable h → ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞) = ∫⁻ z in A, h (fun k => -∑ j, C k j * f j z) * ENNReal.ofReal (‖(Matrix.of C * (Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1) : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FSCrofton.area_formula_neg_comb
end

section
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem measurePreserving_funUnique_symm {U : Type} [inst : Fintype U] [Unique U] :
    MeasurePreserving (MeasurableEquiv.funUnique U ℂ).symm (volume : Measure ℂ)
      (Measure.pi fun _ : U => (volume : Measure ℂ)) := by
  obtain rfl : inst = Unique.fintype := Subsingleton.elim _ _
  exact (measurePreserving_funUnique (volume : Measure ℂ) U).symm

theorem measurePreserving_joinEntry {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) :
    MeasurePreserving
      (fun p : ℂ × ({j : α // j ≠ j₀} → ℂ) =>
        (fun j => if h : j = j₀ then p.1 else p.2 ⟨j, h⟩ : α → ℂ))
      ((volume : Measure ℂ).prod (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)))
      (Measure.pi fun _ : α => (volume : Measure ℂ)) := by
  haveI : Unique {j : α // ¬ j ≠ j₀} :=
    { default := ⟨j₀, by simp⟩
      uniq := fun x => Subtype.ext (by simpa using x.2) }
  have h1 := (measurePreserving_piEquivPiSubtypeProd (fun _ : α => (volume : Measure ℂ))
    (fun j => j ≠ j₀)).symm
  have h2 : MeasurePreserving (MeasurableEquiv.funUnique {j : α // ¬ j ≠ j₀} ℂ).symm
      (volume : Measure ℂ) (Measure.pi fun _ : {j : α // ¬ j ≠ j₀} => (volume : Measure ℂ)) :=
    measurePreserving_funUnique_symm
  have h3 := (MeasurePreserving.id
    (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ))).prod h2
  have h4 : MeasurePreserving (Prod.swap : ℂ × ({j : α // j ≠ j₀} → ℂ) → _)
      ((volume : Measure ℂ).prod (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)))
      ((Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)).prod (volume : Measure ℂ)) :=
    Measure.measurePreserving_swap
  have h5 := h1.comp (h3.comp h4)
  convert h5 using 1
  funext p j
  by_cases h : j = j₀
  · subst h
    simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
  · simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, h]

theorem measurePreserving_joinCol (d : ℕ) {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) :
    MeasurePreserving
      (fun p : (Fin d → ℂ) × (Fin d → {j : α // j ≠ j₀} → ℂ) => joinCol j₀ p.1 p.2)
      volume volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow ℂ ({j : α // j ≠ j₀} → ℂ) (Fin d)).symm
  have h2 := measurePreserving_pi (fun _ : Fin d => (volume : Measure (ℂ × ({j : α // j ≠ j₀} → ℂ))))
    (fun _ : Fin d => (volume : Measure (α → ℂ))) (fun _ => measurePreserving_joinEntry j₀)
  exact h2.comp h1

theorem lintegral_joinCol : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (Φ : (Fin d → α → ℂ) → ℝ≥0∞), Measurable Φ → ∫⁻ C : Fin d → α → ℂ, Φ C = ∫⁻ C' : Fin d → {j : α // j ≠ j₀} → ℂ, ∫⁻ c : Fin d → ℂ, Φ (joinCol j₀ c C') := by
  intro d α _ _ j₀ Φ hΦ
  have hT := measurePreserving_joinCol d j₀
  rw [← hT.lintegral_comp hΦ]
  exact lintegral_prod_symm _ (hΦ.comp hT.measurable).aemeasurable

end GlobalTheory.CompanionTheory.FSCrofton
end

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_split_column : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (Φ : (Fin d → α → ℂ) → ℝ≥0∞), Measurable Φ → ∫⁻ C : Fin d → α → ℂ, Φ C = ∫⁻ C' : Fin d → {j : α // j ≠ j₀} → ℂ, ∫⁻ c : Fin d → ℂ, Φ (joinCol j₀ c C') := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FSCrofton.lintegral_joinCol
end

section
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton

theorem measurable_gW (d : ℕ) (α : Type) [Fintype α] : Measurable (gW d α) := by
  have hc : Continuous fun C : Fin d → α → ℂ => Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) := by
    fun_prop
  exact ENNReal.measurable_ofReal.comp hc.measurable

theorem gW_ne_top (d : ℕ) (α : Type) [Fintype α] (C : Fin d → α → ℂ) : gW d α C ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem measurable_gauss (d : ℕ) :
    Measurable fun c : Fin d → ℂ => ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2)) := by
  have hc : Continuous fun c : Fin d → ℂ => Real.exp (-∑ k, ‖c k‖ ^ 2) := by
    fun_prop
  exact ENNReal.measurable_ofReal.comp hc.measurable

theorem gW_joinCol {d : ℕ} {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) (c : Fin d → ℂ)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) :
    gW d α (joinCol j₀ c C) =
      gW d {j : α // j ≠ j₀} C * ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2)) := by
  unfold gW
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  rw [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [joinCol, j.2]
  · simp [joinCol]

theorem joinCol_zero_iff {X : Type} {d : ℕ} {α : Type} [Fintype α] [DecidableEq α] (j₀ : α)
    (c : Fin d → ℂ) (C : Fin d → {j : α // j ≠ j₀} → ℂ) (b : α → X → ℂ) (z : X)
    (hz : b j₀ z ≠ 0) :
    (∀ k, ∑ j, joinCol j₀ c C k j * b j z = 0) ↔
      ∀ k, c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z) = 0 := by
  refine forall_congr' fun k => ?_
  have h : ∑ j, joinCol j₀ c C k j * b j z =
      b j₀ z * (c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z)) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, mul_add, Finset.mul_sum]
    congr 1
    · simp [joinCol, mul_comm]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [joinCol, j.2, dite_false]
      field_simp
  rw [h, mul_eq_zero]
  simp [hz]

theorem continuous_kernel (d : ℕ) (β : Type) [Fintype β] :
    Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      Real.exp (-∑ k, ‖∑ j, q.1 k j * q.2.1 j‖ ^ 2) *
        ‖(Matrix.of q.1 * (Matrix.of q.2.2 : Matrix β (Fin d) ℂ)).det‖ ^ 2 := by
  have h1 : Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      (Matrix.of q.1 : Matrix (Fin d) β ℂ) := continuous_fst
  have h2 : Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      (Matrix.of q.2.2 : Matrix β (Fin d) ℂ) := continuous_snd.comp continuous_snd
  have h3 : Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      (Matrix.of q.1 * (Matrix.of q.2.2 : Matrix β (Fin d) ℂ)).det :=
    (h1.matrix_mul h2).matrix_det
  have h4 : Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      Real.exp (-∑ k, ‖∑ j, q.1 k j * q.2.1 j‖ ^ 2) := by
    refine Real.continuous_exp.comp (continuous_neg.comp ?_)
    refine continuous_finset_sum _ fun k _ => (Continuous.norm ?_).pow 2
    refine continuous_finset_sum _ fun j _ => Continuous.mul ?_ ?_
    · exact (continuous_apply j).comp ((continuous_apply k).comp continuous_fst)
    · exact (continuous_apply j).comp (continuous_fst.comp continuous_snd)
  exact h4.mul (h3.norm.pow 2)

theorem measurable_kernel {X : Type} [MeasurableSpace X] (d : ℕ) (β : Type) [Fintype β]
    (g : β → X → ℂ) (F : β → Fin d → X → ℂ) (hg : ∀ j, Measurable (g j))
    (hF : ∀ j a, Measurable (F j a)) :
    Measurable fun p : (Fin d → β → ℂ) × X =>
      gW d β p.1 * ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, p.1 k j * g j p.2‖ ^ 2) *
        ‖(Matrix.of p.1 * (Matrix.of fun j a => F j a p.2 : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by
  have hm : Measurable fun p : (Fin d → β → ℂ) × X =>
      ((p.1, (fun j => g j p.2), (fun j a => F j a p.2)) :
        (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ))) := by
    refine measurable_fst.prodMk (Measurable.prodMk ?_ ?_)
    · exact measurable_pi_lambda _ fun j => (hg j).comp measurable_snd
    · exact measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun a =>
        (hF j a).comp measurable_snd
  have hq := (continuous_kernel d β).measurable.comp hm
  exact ((measurable_gW d β).comp measurable_fst).mul (ENNReal.measurable_ofReal.comp hq)

theorem differentiableOn_quot {d : ℕ} {α : Type} (U : Set (V d)) (b : α → V d → ℂ)
    (hb : ∀ j, DifferentiableOn ℂ (b j) U) (j₀ : α) (hne : ∀ z ∈ U, b j₀ z ≠ 0) (j : α) :
    DifferentiableOn ℂ (fun v => b j v / b j₀ v) U := by
  have h : DifferentiableOn ℂ (fun v => b j v * (b j₀ v)⁻¹) U := (hb j).mul ((hb j₀).inv hne)
  simpa only [div_eq_mul_inv] using h

theorem inner_integral (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U A : Set (V d))
    (b : α → V d → ℂ) (hU : IsOpen U) (hb : ∀ j, DifferentiableOn ℂ (b j) U)
    (hne : ∀ z ∈ U, b j₀ z ≠ 0) (hAU : A ⊆ U) (hAm : MeasurableSet A)
    (g : {j : α // j ≠ j₀} → V d → ℂ) (hgA : ∀ j, ∀ z ∈ A, g j z = b j.1 z / b j₀ z)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) :
    ∫⁻ c : Fin d → ℂ, gW d α (joinCol j₀ c C) * zeroCnt d A b (joinCol j₀ c C) =
      ∫⁻ z in A, gW d {j : α // j ≠ j₀} C *
        ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * g j z‖ ^ 2) *
          ‖(Matrix.of C * (Matrix.of fun j a =>
            fderiv ℂ (fun v => b (j : {j : α // j ≠ j₀}).1 v / b j₀ v) z
              (EuclideanSpace.single a 1) : Matrix {j : α // j ≠ j₀} (Fin d) ℂ)).det‖ ^ 2) := by
  have hf : ∀ j : {j : α // j ≠ j₀}, DifferentiableOn ℂ (fun v => b j.1 v / b j₀ v) U :=
    fun j => differentiableOn_quot U b hb j₀ hne j.1
  have e1 : ∀ c : Fin d → ℂ, gW d α (joinCol j₀ c C) * zeroCnt d A b (joinCol j₀ c C) =
      gW d {j : α // j ≠ j₀} C * (ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2)) *
        (({z ∈ A | ∀ k, c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z) = 0}.encard :
          ℕ∞) : ℝ≥0∞)) := by
    intro c
    have hs : {z ∈ A | ∀ k, ∑ j, joinCol j₀ c C k j * b j z = 0} =
        {z ∈ A | ∀ k, c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z) = 0} := by
      ext z
      simp only [Set.mem_setOf_eq]
      refine and_congr_right fun hz => ?_
      exact joinCol_zero_iff j₀ c C b z (hne z (hAU hz))
    rw [gW_joinCol, mul_assoc]
    unfold zeroCnt
    rw [hs]
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ (gW_ne_top d _ C),
    GlobalTheory.T.change_variables_zero_count d {j : α // j ≠ j₀} U A (fun j v => b j.1 v / b j₀ v) C
      (fun c => ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2))) hU hf hAU hAm (measurable_gauss d),
    ← lintegral_const_mul' _ _ (gW_ne_top d _ C)]
  refine setLIntegral_congr_fun hAm fun z hz => ?_
  simp only [norm_neg]
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp only [hgA _ z hz]

theorem const_arith (d m n : ℕ) (hn : n = m + 1) (x : ℝ) :
    ENNReal.ofReal (Real.pi ^ (d * m) * (d.factorial : ℝ) * x) =
      ENNReal.ofReal (Real.pi ^ (d * n)) *
        ENNReal.ofReal ((d.factorial : ℝ) / Real.pi ^ d * x) := by
  rw [← ENNReal.ofReal_mul (pow_nonneg Real.pi_pos.le _)]
  congr 1
  subst hn
  have hp : (Real.pi ^ d) ≠ 0 := pow_ne_zero _ Real.pi_pos.ne'
  rw [Nat.mul_succ, pow_add]
  field_simp

theorem crofton_local : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U A : Set (V d)) (b : α → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (b j) U) → (∀ z ∈ U, b j₀ z ≠ 0) → A ⊆ U → IsSigmaCompact A → ∫⁻ C : Fin d → α → ℂ, gW d α C * zeroCnt d A b C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) * ∫⁻ z in A, ENNReal.ofReal ((d.factorial : ℝ) / Real.pi ^ d * (cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z).det.re) := by
  intro d α _ _ j₀ U A b hU hb hne hAU hA
  classical
  have hAm : MeasurableSet A := by
    obtain ⟨K, hK, hKA⟩ := hA
    rw [← hKA]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  have hΦ : Measurable fun C : Fin d → α → ℂ => gW d α C * zeroCnt d A b C :=
    (measurable_gW d α).mul (GlobalTheory.T.measurable_zero_count d α U A b (fun j => (hb j).continuousOn) hAU hA)
  have hf : ∀ j : {j : α // j ≠ j₀}, DifferentiableOn ℂ (fun v => b j.1 v / b j₀ v) U :=
    fun j => differentiableOn_quot U b hb j₀ hne j.1
  obtain ⟨g, hg, hgA⟩ : ∃ g : {j : α // j ≠ j₀} → V d → ℂ, (∀ j, Measurable (g j)) ∧
      ∀ j, ∀ z ∈ A, g j z = b j.1 z / b j₀ z := by
    refine ⟨fun j => U.piecewise (fun v => b j.1 v / b j₀ v) (fun _ => 0), fun j => ?_,
      fun j z hz => by simp [Set.piecewise, hAU hz]⟩
    exact (hf j).continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hF : ∀ (j : {j : α // j ≠ j₀}) (a : Fin d), Measurable fun z =>
      fderiv ℂ (fun v => b j.1 v / b j₀ v) z (EuclideanSpace.single a 1) :=
    fun j a => measurable_fderiv_apply_const ℂ _ _
  have hK := measurable_kernel d {j : α // j ≠ j₀} g _ hg hF
  rw [GlobalTheory.T.lintegral_split_column d α j₀ _ hΦ]
  simp_rw [inner_integral d α j₀ U A b hU hb hne hAU hAm g hgA]
  rw [lintegral_lintegral_swap (ν := volume.restrict A) hK.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun hAm fun z hz => ?_
  have hcard : Fintype.card α = Fintype.card {j : α // j ≠ j₀} + 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨j₀⟩
    omega
  have h1 := GlobalTheory.T.gaussian_det_levi_integral d {j : α // j ≠ j₀} (fun j => b j.1 z / b j₀ z)
    (Matrix.of fun j a => fderiv ℂ (fun v => b (j : {j : α // j ≠ j₀}).1 v / b j₀ v) z
      (EuclideanSpace.single a 1))
  rw [GlobalTheory.T.complex_hessian_log_dehomogenise d α j₀ U b hU hb hne z (hAU hz),
    GlobalTheory.T.complex_hessian_log_fubini_study d {j : α // j ≠ j₀} U (fun j v => b j.1 v / b j₀ v) hU hf z (hAU hz),
    ← const_arith d _ _ hcard, ← h1]
  simp only [hgA _ z hz]

end GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton
end
end

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.random_section_zero_count : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U A : Set (V d)) (b : α → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (b j) U) → (∀ z ∈ U, b j₀ z ≠ 0) → A ⊆ U → IsSigmaCompact A → ∫⁻ C : Fin d → α → ℂ, gW d α C * zeroCnt d A b C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) * ∫⁻ z in A, ENNReal.ofReal ((d.factorial : ℝ) / Real.pi ^ d * (cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z).det.re) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.crofton_local
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.FSCrofton.Chart

theorem measurableSet_of_isSigmaCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {A : Set X} (hA : IsSigmaCompact A) :
    MeasurableSet A := by
  obtain ⟨K, hK, rfl⟩ := hA
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

variable {Y : Var ℂ} {L : LB Y.X}

noncomputable def chartVal {n : ℕ} (b : Fin n → L.Sec) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim)
    (i : L.ι) (j : Fin n) (v : ReciprocityTheory.L2DbarEstimates.V Y.dim) : ℂ :=
  secVal Y.str (RingHom.id ℂ) (b j) i (c.e.symm v)

theorem encard_eq_zeroCnt {n : ℕ} (b : Fin n → L.Sec) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim)
    (i : L.ι) (A : Set (CxPts Y.str (RingHom.id ℂ))) (hAc : A ⊆ c.e.source)
    (hAi : A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i)) (C : Fin Y.dim → Fin n → ℂ) :
    (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι),
        y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞) =
      zeroCnt Y.dim (c.e '' A) (chartVal b c i) C := by
  have hinj : Set.InjOn c.e {y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι),
        y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0} :=
    c.e.injOn.mono fun y hy => hAc hy.1
  have himg : c.e '' {y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι),
        y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0} =
      {z ∈ c.e '' A | ∀ k, ∑ j, C k j * chartVal b c i j z = 0} := by
    ext v
    constructor
    · rintro ⟨y, ⟨hyA, hy⟩, rfl⟩
      refine ⟨⟨y, hyA, rfl⟩, fun k => ?_⟩
      simpa only [chartVal, c.e.left_inv (hAc hyA)] using hy k i (hAi hyA)
    · rintro ⟨⟨y, hyA, rfl⟩, hy⟩
      refine ⟨y, ⟨hyA, fun k i' hi' => ?_⟩, rfl⟩
      have h0 : ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0 := by
        simpa only [chartVal, c.e.left_inv (hAc hyA)] using hy k
      have e : ∀ j, secVal Y.str (RingHom.id ℂ) (b j) i' y =
          gv Y.str (RingHom.id ℂ) L i' i y * secVal Y.str (RingHom.id ℂ) (b j) i y :=
        fun j => (secVal_mem (b j)).1 i' i y hi' (hAi hyA)
      simp only [e]
      calc ∑ j, C k j * (gv Y.str (RingHom.id ℂ) L i' i y * secVal Y.str (RingHom.id ℂ) (b j) i y)
          = gv Y.str (RingHom.id ℂ) L i' i y *
              ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [h0, mul_zero]
  rw [zeroCnt, ← himg, hinj.encard_image]

theorem fsBasis_φ_chart (hL : L.IsLB) {n : ℕ} (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤)
    (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι) (v : ReciprocityTheory.L2DbarEstimates.V Y.dim) :
    (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).φ i (c.e.symm v) =
      Real.log (∑ j, ‖chartVal b c i j v‖ ^ 2) := by
  rw [Weight.fsBasis_φ]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rfl

theorem chernPart_eq_lintegral (hL : L.IsLB) {n : ℕ} (b : Fin n → L.Sec)
    (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι)
    (A : Set (CxPts Y.str (RingHom.id ℂ))) (hAm : MeasurableSet A) (hAc : A ⊆ c.e.source)
    (hAi : A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i)) (hBm : MeasurableSet (c.e '' A)) :
    (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernPart Y.dim 1 A =
      ∫⁻ z in c.e '' A, ENNReal.ofReal ((Y.dim.factorial : ℝ) / Real.pi ^ Y.dim *
        (ReciprocityTheory.L2DbarEstimates.cHess Y.dim
          (fun v => ((Real.log (∑ j, ‖chartVal b c i j v‖ ^ 2) : ℝ) : ℂ)) z).det.re) := by
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  have hC := Weight.isCInf_fsBasis (p := Y.str) (σ := RingHom.id ℂ) hL b hb 1 (by simp)
  rw [Weight.chernPart_apply hC 1 c hAm hAc]
  refine setLIntegral_congr_fun hBm fun v hv => ?_
  obtain ⟨y, hy, rfl⟩ := hv
  have hys := c.e.left_inv (hAc hy)
  simp only [hys]
  rw [c.chernDens_eq hC (hAc hy) (hAi hy), AlgChart.hess]
  simp only [fsBasis_φ_chart hL b hb c i, Units.val_one, Int.cast_one, one_mul]

end GlobalTheory.CompanionTheory.FSCrofton.Chart

open GlobalTheory.CompanionTheory.FSCrofton.Chart in

theorem GlobalTheory.CompanionTheory.FSCrofton.crofton_chart : ∀ (Y : Var ℂ) (L : LB Y.X) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι) (j₀ : Fin n) (A : Set (CxPts Y.str (RingHom.id ℂ))), A ⊆ c.e.source → A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i) → (∀ y ∈ A, secVal Y.str (RingHom.id ℂ) (b j₀) i y ≠ 0) → IsSigmaCompact A → Measurable (fun C : Fin Y.dim → Fin n → ℂ => (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞)) ∧ ∫⁻ C : Fin Y.dim → Fin n → ℂ, gW Y.dim (Fin n) C * (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal (Real.pi ^ (Y.dim * n)) * (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernPart Y.dim 1 A := by
  intro Y L hL n b hb c i j₀ A hAc hAi hA0 hAs
  have hAm : MeasurableSet A := measurableSet_of_isSigmaCompact hAs
  have hBs : IsSigmaCompact (c.e '' A) :=
    hAs.image_of_continuousOn (c.e.continuousOn.mono hAc)
  have hBm : MeasurableSet (c.e '' A) := measurableSet_of_isSigmaCompact hBs
  have hcnt := encard_eq_zeroCnt b c i A hAc hAi

  set W : Y.X.Opens := L.U i ⊓ nonzeroLocus (b j₀) with hW
  set U : Set (ReciprocityTheory.L2DbarEstimates.V Y.dim) := c.e.target ∩ c.e.symm ⁻¹' ptsIn Y.str (RingHom.id ℂ) W
    with hU
  have hUo : IsOpen U := ChartGlue.isOpen_over c.e (isOpen_ptsIn W)
  have hUi : ∀ v ∈ U, c.e.symm v ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) := fun v hv =>
    (mem_ptsIn_inf.1 hv.2).1
  have hd : ∀ j, DifferentiableOn ℂ (chartVal b c i j) U := fun j =>
    (c.holo (L.U i) ((b j).f i)).mono fun v hv => ⟨hv.1, hUi v hv⟩
  have h0 : ∀ z ∈ U, chartVal b c i j₀ z ≠ 0 := fun z hz =>
    (secVal_ne_zero_iff (b j₀) (hUi z hz)).2 (mem_ptsIn_inf.1 hz.2).2
  have hBU : c.e '' A ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨c.e.map_source (hAc hy), ?_⟩
    change c.e.symm (c.e y) ∈ ptsIn Y.str (RingHom.id ℂ) W
    rw [c.e.left_inv (hAc hy)]
    exact mem_ptsIn_inf.2 ⟨hAi hy, (secVal_ne_zero_iff (b j₀) (hAi hy)).1 (hA0 y hy)⟩
  refine ⟨?_, ?_⟩
  · simp only [hcnt]
    exact GlobalTheory.T.measurable_zero_count Y.dim (Fin n) U (c.e '' A) (chartVal b c i)
      (fun j => (hd j).continuousOn) hBU hBs
  · simp only [hcnt]
    have key := GlobalTheory.T.random_section_zero_count Y.dim (Fin n) j₀ U (c.e '' A) (chartVal b c i) hUo hd h0 hBU hBs
    rw [key, Fintype.card_fin, chernPart_eq_lintegral hL b hb c i A hAm hAc hAi hBm]
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_local_zero_count : ∀ (Y : Var ℂ) (L : LB Y.X) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι) (j₀ : Fin n) (A : Set (CxPts Y.str (RingHom.id ℂ))), A ⊆ c.e.source → A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i) → (∀ y ∈ A, secVal Y.str (RingHom.id ℂ) (b j₀) i y ≠ 0) → IsSigmaCompact A → Measurable (fun C : Fin Y.dim → Fin n → ℂ => (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞)) ∧ ∫⁻ C : Fin Y.dim → Fin n → ℂ, gW Y.dim (Fin n) C * (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal (Real.pi ^ (Y.dim * n)) * (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernPart Y.dim 1 A := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FSCrofton.crofton_chart
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem measurable_gW (d : ℕ) (α : Type) [Fintype α] : Measurable (gW d α) := by
  unfold gW
  fun_prop

theorem encard_iUnion_fin {X : Type} {m : ℕ} (B : Fin m → Set X)
    (h : Pairwise (Function.onFun Disjoint B)) :
    (((⋃ t, B t).encard : ℕ∞) : ℝ≥0∞) = ∑ t, (((B t).encard : ℕ∞) : ℝ≥0∞) := by
  classical
  have key : ∀ s : Finset (Fin m), (((⋃ t ∈ s, B t).encard : ℕ∞) : ℝ≥0∞) =
      ∑ t ∈ s, (((B t).encard : ℕ∞) : ℝ≥0∞) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.set_biUnion_insert, Set.encard_union_eq, ENat.toENNReal_add,
        ih]
      exact Set.disjoint_iUnion₂_right.2 fun t ht => h (fun e => ha (e ▸ ht))
  simpa using key Finset.univ

theorem crofton : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → ∃ μ : Measure (Fin Y.dim → Fin n → ℂ), IsProbabilityMeasure μ ∧ μ ≪ volume ∧ (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernInt Y.dim Set.univ (fun _ => 1) = ∫ C, (({y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}).ncard : ℝ) ∂μ := by
  intro Y Δ L r hL n b hb _
  have := CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (RingHom.id ℂ) Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  set φ := Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp) with hφdef
  have hφ : φ.IsCInf := Weight.isCInf_fsBasis hL b hb _ _
  have hneg : φ.chernPart Y.dim (-1) = 0 :=
    Weight.chernPart_neg_eq_zero hφ (Weight.semiPosReg_fsBasis hL b hb _ _)
  have hint := GlobalTheory.Published.ChernDegreeComplexModel.integrable Y φ hφ
  have hfin : φ.chernPart Y.dim 1 Set.univ ≠ ⊤ := by
    have h1 := hint.1
    rw [IntegrableOn, Measure.restrict_univ, integrable_const_iff] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 one_ne_zero
    · exact ((isFiniteMeasure_iff _).1 (by simpa using h1)).ne

  let ι := AlgChart Y.str (RingHom.id ℂ) Y.dim × L.ι × Fin n
  let S : ι → Set (CxPts Y.str (RingHom.id ℂ)) := fun t => t.1.e.source ∩
    (ptsIn Y.str (RingHom.id ℂ) (L.U t.2.1) ∩ ptsIn Y.str (RingHom.id ℂ) (nonzeroLocus (b t.2.2)))
  have hSo : ∀ t, IsOpen (S t) := fun t =>
    t.1.e.open_source.inter ((isOpen_ptsIn _).inter (isOpen_ptsIn _))
  have hSc : (⋃ t, S t) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := Y.dim) (p := Y.str) (σ := RingHom.id ℂ) y
    obtain ⟨j, hj⟩ := exists_mem_ptsIn hb y
    exact Set.mem_iUnion.2 ⟨⟨c, pick hL y, j⟩, hc, mem_pick hL y, hj⟩
  obtain ⟨m, l, A, hdis, hun, hsub, hσ⟩ := GlobalTheory.T.sigma_compact_disjoint_refinement _ ι S hSo hSc
  set G : ℝ≥0∞ := ENNReal.ofReal (Real.pi ^ (Y.dim * n)) with hG
  have hGpos : G ≠ 0 := by
    rw [hG, Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hGtop : G ≠ ⊤ := ENNReal.ofReal_ne_top
  let Z : (Fin Y.dim → Fin n → ℂ) → Set (CxPts Y.str (RingHom.id ℂ)) := fun C =>
    {y | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
      ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}
  let P : Fin m → (Fin Y.dim → Fin n → ℂ) → Set (CxPts Y.str (RingHom.id ℂ)) := fun t C =>
    {y | y ∈ A t ∧ ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
      ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}
  have hpiece : ∀ t, Measurable (fun C => (((P t C).encard : ℕ∞) : ℝ≥0∞)) ∧
      ∫⁻ C, gW Y.dim (Fin n) C * (((P t C).encard : ℕ∞) : ℝ≥0∞) =
        G * φ.chernPart Y.dim 1 (A t) := fun t =>
    GlobalTheory.T.measurable_local_zero_count Y L hL n b hb (l t).1 (l t).2.1 (l t).2.2 (A t)
      (fun y hy => (hsub t hy).1) (fun y hy => (hsub t hy).2.1)
      (fun y hy => (secVal_ne_zero_iff _ (hsub t hy).2.1).2 (hsub t hy).2.2) (hσ t)
  have hZ : ∀ C, (((Z C).encard : ℕ∞) : ℝ≥0∞) = ∑ t, (((P t C).encard : ℕ∞) : ℝ≥0∞) := by
    intro C
    rw [← encard_iUnion_fin]
    · congr 2
      ext y
      simp only [Set.mem_iUnion, P, Z, Set.mem_setOf_eq]
      constructor
      · intro h
        obtain ⟨t, ht⟩ := Set.mem_iUnion.1 (hun ▸ Set.mem_univ y)
        exact ⟨t, ht, h⟩
      · rintro ⟨t, -, h⟩
        exact h
    · intro s t hst
      exact (hdis hst).mono (fun y hy => hy.1) (fun y hy => hy.1)
  have hNm : Measurable fun C => (((Z C).encard : ℕ∞) : ℝ≥0∞) := by
    simp only [hZ]
    exact Finset.measurable_fun_sum _ fun t _ => (hpiece t).1
  have hAm : ∀ t, MeasurableSet (A t) := fun t => by
    obtain ⟨K, hK, e⟩ := hσ t
    rw [← e]
    exact MeasurableSet.iUnion fun i => (hK i).measurableSet
  have hmass : φ.chernPart Y.dim 1 Set.univ = ∑ t, φ.chernPart Y.dim 1 (A t) := by
    rw [← hun, measure_iUnion hdis hAm, tsum_fintype]
  have hgm := measurable_gW Y.dim (Fin n)
  have hsum : ∫⁻ C, gW Y.dim (Fin n) C * (((Z C).encard : ℕ∞) : ℝ≥0∞) =
      G * φ.chernPart Y.dim 1 Set.univ := by
    simp only [hZ, Finset.mul_sum]
    rw [lintegral_finset_sum Finset.univ (f := fun t C => gW Y.dim (Fin n) C *
      (((P t C).encard : ℕ∞) : ℝ≥0∞)) fun t _ => hgm.mul (hpiece t).1, hmass, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => (hpiece t).2
  let μ : Measure (Fin Y.dim → Fin n → ℂ) := G⁻¹ • volume.withDensity (gW Y.dim (Fin n))
  have hlin : ∀ f : (Fin Y.dim → Fin n → ℂ) → ℝ≥0∞, Measurable f →
      ∫⁻ C, f C ∂μ = G⁻¹ * ∫⁻ C, gW Y.dim (Fin n) C * f C := by
    intro f hf
    rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hgm hf]
    rfl
  have hprob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    have h1 := hlin (fun _ => 1) measurable_const
    simp only [lintegral_one, mul_one] at h1
    rw [h1, GlobalTheory.T.gaussian_weight_total_mass, Fintype.card_fin]
    exact ENNReal.inv_mul_cancel hGpos hGtop
  have hN : ∫⁻ C, (((Z C).encard : ℕ∞) : ℝ≥0∞) ∂μ = φ.chernPart Y.dim 1 Set.univ := by
    rw [hlin _ hNm, hsum, ← mul_assoc, ENNReal.inv_mul_cancel hGpos hGtop, one_mul]
  refine ⟨μ, hprob, ?_, ?_⟩
  · exact (withDensity_absolutelyContinuous _ _).smul_left _
  · have hcast : ∀ C, ((Z C).ncard : ℝ) = ((((Z C).encard : ℕ∞) : ℝ≥0∞)).toReal := by
      intro C
      rw [Set.ncard]
      cases h : (Z C).encard with
      | top => simp
      | coe a => simp
    have hae : ∀ᵐ C ∂μ, (((Z C).encard : ℕ∞) : ℝ≥0∞) < ⊤ :=
      ae_lt_top hNm (by rw [hN]; exact hfin)
    have e := integral_toReal hNm.aemeasurable hae
    rw [hN] at e
    simp only [Z] at hcast e
    simp only [hcast]
    rw [e, Weight.chernInt, hneg]
    simp [Measure.real]
end GlobalTheory.CompanionTheory.FSCrofton
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_random_sections : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → ∃ μ : Measure (Fin Y.dim → Fin n → ℂ), IsProbabilityMeasure μ ∧ μ ≪ volume ∧ (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernInt Y.dim Set.univ (fun _ => 1) = ∫ C, (({y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}).ncard : ℝ) ∂μ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FSCrofton.crofton
end
