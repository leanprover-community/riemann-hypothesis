import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt

section
noncomputable section

set_option linter.unusedSimpArgs false

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  simp [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem isUnit_det_of_inG' {g : M2 n} (hg : InG g) : IsUnit g.det := by
  have h := congrArg Matrix.det hg
  rw [det_mul, det_mul, det_conjTranspose] at h
  have hJ : (JJ n).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (JJ_mul_JJ (n := n))
    rw [det_mul, h0, zero_mul, det_neg, det_one] at this
    simp at this
  refine isUnit_iff_ne_zero.2 fun h0 => hJ ?_
  rw [h0, mul_zero] at h
  exact h.symm

theorem mul_JJ_conjTranspose {g : M2 n} (hg : InG g) : g * JJ n * gᴴ = JJ n := by
  have h1 : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
    have : -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
    rw [this, hg, Matrix.neg_mul, JJ_mul_JJ, neg_neg]
  have h2 : g * (-(JJ n) * gᴴ * JJ n) = 1 := mul_eq_one_comm.1 h1
  have h3 : g * (-(JJ n) * gᴴ * JJ n) * JJ n = JJ n := by rw [h2, Matrix.one_mul]
  have h4 : g * (-(JJ n) * gᴴ * JJ n) * JJ n = g * JJ n * gᴴ := by
    simp only [Matrix.mul_assoc, JJ_mul_JJ, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, neg_neg]
  rw [← h4, h3]

theorem lower_rel {g : M2 n} (hg : InG g) : g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = g.toBlocks₂₂ * g.toBlocks₂₁ᴴ := by
  have h := congrArg Matrix.toBlocks₂₂ (mul_JJ_conjTranspose hg)
  rw [← fromBlocks_toBlocks g] at h
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h
  simp only [Matrix.mul_zero, zero_add, Matrix.mul_neg, Matrix.mul_one, add_zero] at h
  have : -(g.toBlocks₂₂ * g.toBlocks₂₁ᴴ) + g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = 0 := by
    rw [← h]; simp
  rw [neg_add_eq_zero] at this
  exact this.symm

theorem first_cayley_block_mul_conjTranspose_eq {g : M2 n} (hg : InG g) :
    u1 g * (u1 g)ᴴ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  have h := lower_rel hg
  simp only [u1, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h]
  match_scalars <;> simp [Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_sq]

theorem second_cayley_block_mul_conjTranspose_eq {g : M2 n} (hg : InG g) :
    u2 g * (u2 g)ᴴ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  have h := lower_rel hg
  simp only [u2, conjTranspose_add, conjTranspose_neg, conjTranspose_smul, Complex.star_def, Complex.conj_I,
    Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h]
  match_scalars <;> simp [Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_sq]

theorem inv_eq_of_inG {g : M2 n} (hg : InG g) : g⁻¹ = -(JJ n) * gᴴ * JJ n := by
  have h1 : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
    have : -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
    rw [this, hg, Matrix.neg_mul, JJ_mul_JJ, neg_neg]
  exact Matrix.inv_eq_left_inv h1

theorem inverse_first_block_eq_of_group {g : M2 n} (hg : InG g) : ub1 g = (u1 g)ᴴ := by
  rw [ub1, inv_eq_of_inG hg, u1]
  conv_lhs => rw [← fromBlocks_toBlocks g]
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₂₁, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I]
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    zero_add, add_zero, neg_zero, neg_neg]
  module

theorem posDef_lower {g : M2 n} (hg : InG g) :
    (g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ).PosDef := by
  have hu : IsUnit gᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, det_conjTranspose]
    exact (isUnit_det_of_inG' hg).star
  have hP : (gᴴᴴ * gᴴ).PosDef := Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 hu)
  rw [conjTranspose_conjTranspose] at hP
  have h2 := hP.submatrix (e := (Sum.inr : Fin n → Fin n ⊕ Fin n)) Sum.inr_injective
  convert h2 using 1
  conv_rhs => rw [← fromBlocks_toBlocks g]
  ext i j
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.submatrix]

theorem det_first_cayley_block_ne_zero {g : M2 n} (hg : InG g) : (u1 g).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (first_cayley_block_mul_conjTranspose_eq hg)
  rw [det_mul, h, zero_mul] at h1
  exact (posDef_lower hg).det_pos.ne' h1.symm

theorem det_second_cayley_block_ne_zero {g : M2 n} (hg : InG g) : (u2 g).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (second_cayley_block_mul_conjTranspose_eq hg)
  rw [det_mul, h, zero_mul] at h1
  exact (posDef_lower hg).det_pos.ne' h1.symm

theorem automorphy_first_mul_parabolic {P : M2 n} (x : M2 n) (hP : P.toBlocks₂₁ = 0) : u1 (P * x) = P.toBlocks₂₂ * u1 x := by
  conv_lhs => rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks x, hP]
  simp only [u1, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
    Matrix.mul_add, Matrix.mul_smul]

theorem automorphy_second_mul_parabolic {P : M2 n} (x : M2 n) (hP : P.toBlocks₂₁ = 0) : u2 (P * x) = P.toBlocks₂₂ * u2 x := by
  conv_lhs => rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks x, hP]
  simp only [u2, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]

theorem det_par {P : M2 n} (hP : P.toBlocks₂₁ = 0) : P.det = P.toBlocks₁₁.det * P.toBlocks₂₂.det := by
  conv_lhs => rw [← fromBlocks_toBlocks P, hP]
  exact det_fromBlocks_zero₂₁ _ _ _

theorem par_rel {P : M2 n} (hG : InG P) (hP : P.toBlocks₂₁ = 0) : P.toBlocks₁₁ᴴ * P.toBlocks₂₂ = 1 := by
  have h := congrArg Matrix.toBlocks₁₂ hG
  rw [← fromBlocks_toBlocks P, hP] at h
  simpa [JJ, fromBlocks_conjTranspose, fromBlocks_multiply] using h

theorem inverse_first_block_mul_parabolic {P x : M2 n} (hP : P.toBlocks₂₁ = 0) (hPu : IsUnit P.det) :
    ub1 (P * x) = ub1 x * (P.toBlocks₁₁)⁻¹ := by
  have hA : IsUnit P.toBlocks₁₁.det := by
    rw [det_par hP] at hPu; exact isUnit_of_mul_isUnit_left hPu
  have hD : IsUnit P.toBlocks₂₂.det := by
    rw [det_par hP] at hPu; exact isUnit_of_mul_isUnit_right hPu
  have hinv : P⁻¹ = fromBlocks (P.toBlocks₁₁)⁻¹ (-((P.toBlocks₁₁)⁻¹ * P.toBlocks₁₂ * (P.toBlocks₂₂)⁻¹)) 0
      (P.toBlocks₂₂)⁻¹ := by
    conv_lhs => rw [← fromBlocks_toBlocks P, hP]
    refine Matrix.inv_eq_right_inv ?_
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add, Matrix.mul_neg,
      Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hD]
    rw [← fromBlocks_one]
    congr 1 <;> simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hD]
  rw [ub1, ub1, Matrix.mul_inv_rev, hinv]
  conv_lhs => rw [← fromBlocks_toBlocks x⁻¹]
  simp only [fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, Matrix.mul_zero, add_zero,
    Matrix.add_mul, Matrix.smul_mul]

theorem lower_mul_conjTranspose (g : M2 n) :
    (g * gᴴ).toBlocks₂₂ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  conv_lhs => rw [← fromBlocks_toBlocks g]
  simp [fromBlocks_conjTranspose, fromBlocks_multiply]

theorem first_cayley_block_unitary {k : M2 n} (hk : InG k ∧ kᴴ * k = 1) : u1 k * (u1 k)ᴴ = 1 := by
  rw [first_cayley_block_mul_conjTranspose_eq hk.1, ← lower_mul_conjTranspose, mul_eq_one_comm.1 hk.2]
  simp [← fromBlocks_one]

theorem second_cayley_block_unitary {k : M2 n} (hk : InG k ∧ kᴴ * k = 1) : u2 k * (u2 k)ᴴ = 1 := by
  rw [second_cayley_block_mul_conjTranspose_eq hk.1, ← lower_mul_conjTranspose, mul_eq_one_comm.1 hk.2]
  simp [← fromBlocks_one]

end PositivityTheory.Rg.Sw.LVs
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Dom (n : ℕ) : Set (M2 n) := {x | IsUnit x.det ∧ (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0 ∧ (ub1 x).det ≠ 0}

def hF (j : ℕ) (p q : ℤ) (y : M2 n) : ℂ := f0 p q y * minorOn (blkA j) (wM y) * minorOn (blkB j) (wM y)⁻¹

def InP (P : M2 n) : Prop := InG P ∧ P.toBlocks₂₁ = 0

def c1 (p q : ℤ) (P : M2 n) : ℂ := P.toBlocks₂₂.det ^ (-p) * P.toBlocks₂₂.det ^ (-q)

def c2 (p q : ℤ) (P : M2 n) : ℂ := P.toBlocks₂₂.det ^ (p - n) * P.toBlocks₂₂.det ^ q * P.toBlocks₁₁.det ^ (n : ℤ)

theorem inG_mul {a b : M2 n} (ha : InG a) (hb : InG b) : InG (a * b) := by
  unfold InG at *
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * JJ n * (a * b) = bᴴ * (aᴴ * JJ n * a) * b := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [ha, hb]

theorem isUnit_det_of_inG {g : M2 n} (hg : InG g) : IsUnit g.det := isUnit_det_of_inG' hg

theorem gset_sub_dom : GSet n ⊆ Dom n := fun g hg => by
  refine ⟨isUnit_det_of_inG' hg, det_first_cayley_block_ne_zero hg, det_second_cayley_block_ne_zero hg, ?_⟩
  rw [inverse_first_block_eq_of_group hg, det_conjTranspose]
  exact star_ne_zero.2 (det_first_cayley_block_ne_zero hg)

theorem continuous_toBlocks₂₁' : Continuous (fun x : M2 n => x.toBlocks₂₁) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inr i))

theorem continuous_toBlocks₂₂' : Continuous (fun x : M2 n => x.toBlocks₂₂) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inr i))

theorem continuous_toBlocks₁₁' : Continuous (fun x : M2 n => x.toBlocks₁₁) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inl i))

theorem continuous_first_cayley_block_map : Continuous (fun x : M2 n => u1 x) := by
  show Continuous (fun x : M2 n => Complex.I • x.toBlocks₂₁ + x.toBlocks₂₂)
  exact ((continuous_const (y := Complex.I)).smul (continuous_toBlocks₂₁' (n := n))).add
    (continuous_toBlocks₂₂' (n := n))

theorem continuous_second_cayley_block_map : Continuous (fun x : M2 n => u2 x) := by
  show Continuous (fun x : M2 n => -(Complex.I • x.toBlocks₂₁) + x.toBlocks₂₂)
  exact ((continuous_const (y := Complex.I)).smul (continuous_toBlocks₂₁' (n := n))).neg.add
    (continuous_toBlocks₂₂' (n := n))

theorem continuousOn_inv' {m : Type} [Fintype m] [DecidableEq m] :
    ContinuousOn (fun x : Matrix m m ℂ => x⁻¹) {x | x.det ≠ 0} := by
  have h : ContinuousOn (fun x : Matrix m m ℂ => (x.det)⁻¹ • x.adjugate) {x | x.det ≠ 0} :=
    ((continuous_id.matrix_det).continuousOn.inv₀ fun x hx => hx).smul continuous_id.matrix_adjugate.continuousOn
  refine h.congr fun x hx => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']

theorem continuousOn_inverse_first_block : ContinuousOn (fun x : M2 n => ub1 x) {x | x.det ≠ 0} := by
  have h1 : ContinuousOn (fun x : M2 n => x⁻¹) {x | x.det ≠ 0} := continuousOn_inv'
  have h11 : ContinuousOn (fun x : M2 n => x⁻¹.toBlocks₁₁) {x | x.det ≠ 0} :=
    (continuous_toBlocks₁₁' (n := n)).comp_continuousOn h1
  have h21 : ContinuousOn (fun x : M2 n => x⁻¹.toBlocks₂₁) {x | x.det ≠ 0} :=
    (continuous_toBlocks₂₁' (n := n)).comp_continuousOn h1
  show ContinuousOn (fun x : M2 n => x⁻¹.toBlocks₁₁ + Complex.I • x⁻¹.toBlocks₂₁) _
  refine ContinuousOn.add h11 ?_
  exact fun x hx => (h21 x hx).const_smul Complex.I

theorem continuousOn_wM : ContinuousOn (fun x : M2 n => wM x) {x | (u2 x).det ≠ 0} := by
  have h : ContinuousOn (fun x : M2 n => (u2 x)⁻¹) {x | (u2 x).det ≠ 0} :=
    continuousOn_inv'.comp continuous_second_cayley_block_map.continuousOn fun x hx => hx
  exact h.mul continuous_first_cayley_block_map.continuousOn

theorem continuous_minorOn (s : Finset (Fin n)) : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => minorOn s M) :=
  (continuous_id.matrix_submatrix _ _).matrix_det

theorem isOpen_dom : IsOpen (Dom n) := by
  have hdet : Continuous (fun x : M2 n => x.det) := continuous_id.matrix_det
  have h0 : IsOpen {x : M2 n | x.det ≠ 0} := isOpen_ne_fun hdet continuous_const
  have e : Dom n = ({x : M2 n | x.det ≠ 0} ∩ (fun x => ub1 x) ⁻¹' {M | M.det ≠ 0}) ∩
      ({x | (u1 x).det ≠ 0} ∩ {x | (u2 x).det ≠ 0}) := by
    ext x
    simp only [Dom, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, isUnit_iff_ne_zero]
    tauto
  rw [e]
  refine IsOpen.inter (continuousOn_inverse_first_block.isOpen_inter_preimage h0
    (isOpen_ne_fun continuous_id.matrix_det continuous_const)) (IsOpen.inter ?_ ?_)
  · exact isOpen_ne_fun continuous_first_cayley_block_map.matrix_det continuous_const
  · exact isOpen_ne_fun continuous_second_cayley_block_map.matrix_det continuous_const

theorem det_lower_right_parabolic_ne_zero {P : M2 n} (hP : InP P) : P.toBlocks₂₂.det ≠ 0 := by
  have h := isUnit_det_of_inG' hP.1
  rw [det_par hP.2] at h
  exact (isUnit_of_mul_isUnit_right h).ne_zero

theorem det_upper_left_parabolic_ne_zero {P : M2 n} (hP : InP P) : P.toBlocks₁₁.det ≠ 0 := by
  have h := isUnit_det_of_inG' hP.1
  rw [det_par hP.2] at h
  exact (isUnit_of_mul_isUnit_left h).ne_zero

theorem mul_mem_dom {P x : M2 n} (hP : InP P) (hx : x ∈ Dom n) : P * x ∈ Dom n := by
  obtain ⟨h0, h1, h2, h3⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [det_mul]; exact (isUnit_det_of_inG' hP.1).mul h0
  · rw [automorphy_first_mul_parabolic x hP.2, det_mul]; exact mul_ne_zero (det_lower_right_parabolic_ne_zero hP) h1
  · rw [automorphy_second_mul_parabolic x hP.2, det_mul]; exact mul_ne_zero (det_lower_right_parabolic_ne_zero hP) h2
  · rw [inverse_first_block_mul_parabolic hP.2 (isUnit_det_of_inG' hP.1), det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero h3 (inv_ne_zero (det_upper_left_parabolic_ne_zero hP))

theorem wM_mul_par {P : M2 n} (hP : InP P) (x : M2 n) : wM (P * x) = wM x := by
  have hD : IsUnit P.toBlocks₂₂ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_lower_right_parabolic_ne_zero hP))
  rw [wM, wM, automorphy_first_mul_parabolic x hP.2, automorphy_second_mul_parabolic x hP.2, Matrix.mul_inv_rev, Matrix.mul_assoc,
    ← Matrix.mul_assoc (P.toBlocks₂₂)⁻¹, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hD),
    Matrix.one_mul]

theorem hF_law (j : ℕ) (p q : ℤ) {P x : M2 n} (hP : InP P) (hx : x ∈ Dom n) :
    hF j p q (P * x) = c1 p q P * hF j p q x := by
  simp only [hF, wM_mul_par hP, f0, c1, automorphy_first_mul_parabolic x hP.2, automorphy_second_mul_parabolic x hP.2, det_mul, mul_zpow]
  ring

theorem fV_law (p q : ℤ) {P x : M2 n} (hP : InP P) (hx : x ∈ Dom n) :
    fV p q (P * x) = c2 p q P * fV p q x := by
  simp only [fV, c2, automorphy_first_mul_parabolic x hP.2, automorphy_second_mul_parabolic x hP.2, inverse_first_block_mul_parabolic hP.2 (isUnit_det_of_inG' hP.1), det_mul,
    det_nonsing_inv, Ring.inverse_eq_inv', mul_zpow, _root_.inv_zpow', neg_neg, zpow_natCast]
  ring

theorem modulus_characters_product (p q : ℤ) {P : M2 n} (hP : InP P) :
    c1 p q P * c2 p q P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) := by
  have hd := det_lower_right_parabolic_ne_zero hP
  have hrel : star P.toBlocks₁₁.det * P.toBlocks₂₂.det = 1 := by
    have := congrArg Matrix.det (par_rel hP.1 hP.2)
    rwa [det_mul, det_conjTranspose, det_one] at this
  have ha : P.toBlocks₁₁.det = (star P.toBlocks₂₂.det)⁻¹ := by
    have h2 : star (star P.toBlocks₁₁.det * P.toBlocks₂₂.det) = 1 := by rw [hrel, star_one]
    rw [star_mul, star_star] at h2
    exact eq_inv_of_mul_eq_one_right h2
  have hn : ((‖P.toBlocks₂₂.det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) =
      (P.toBlocks₂₂.det * star P.toBlocks₂₂.det) ^ (-(n : ℤ)) := by
    rw [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_zpow, Complex.normSq_eq_norm_sq]
    congr 1
    rw [← zpow_natCast, ← _root_.zpow_mul]
    congr 1
    push_cast; ring
  rw [hn, c1, c2, ha, mul_zpow]
  set d := P.toBlocks₂₂.det
  have e : d ^ (-p) * d ^ (-q) * (d ^ (p - n) * d ^ q * (star d)⁻¹ ^ (n : ℤ)) =
      (d ^ (-p) * d ^ (-q) * d ^ (p - n) * d ^ q) * (star d)⁻¹ ^ (n : ℤ) := by ring
  rw [e, ← zpow_add₀ hd, ← zpow_add₀ hd, ← zpow_add₀ hd,
    show -p + -q + (p - (n : ℤ)) + q = -(n : ℤ) by ring, _root_.inv_zpow']

theorem wM_mem_unitary {k : M2 n} (hk : InK k) : wM k ∈ unitaryGroup (Fin n) ℂ := by
  have h1 : u1 k ∈ unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff.2 (first_cayley_block_unitary hk)
  have h2 : u2 k ∈ unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff.2 (second_cayley_block_unitary hk)
  have hi : (u2 k)⁻¹ = star (u2 k) := Matrix.inv_eq_right_inv (second_cayley_block_unitary hk)
  rw [wM, hi]
  exact Submonoid.mul_mem _ (Matrix.mem_unitaryGroup_iff.2 (by rw [star_star]; exact Matrix.mem_unitaryGroup_iff'.1 h2)) h1

theorem scalar_section_mul_conjugate_section {k : M2 n} (hk : InK k) (p q : ℤ) : f0 p q k * fV p q k = 1 := by
  have h1 := det_first_cayley_block_ne_zero hk.1
  have h2 := det_second_cayley_block_ne_zero hk.1
  have hs : (u1 k).det * star (u1 k).det = 1 := by
    have := congrArg Matrix.det (first_cayley_block_unitary hk)
    rwa [det_mul, det_conjTranspose, det_one] at this
  have hs' : star (u1 k).det ≠ 0 := star_ne_zero.2 h1
  rw [f0, fV, inverse_first_block_eq_of_group hk.1, det_conjTranspose]
  have e : (u1 k).det ^ (-p) * (u2 k).det ^ (-q) * ((u1 k).det ^ (p - n) * (u2 k).det ^ q * star (u1 k).det ^ (-(n : ℤ)))
      = ((u1 k).det ^ (-p) * (u1 k).det ^ (p - n)) * ((u2 k).det ^ (-q) * (u2 k).det ^ q) *
        star (u1 k).det ^ (-(n : ℤ)) := by ring
  rw [e, ← zpow_add₀ h1, ← zpow_add₀ h2, show -p + (p - (n : ℤ)) = -(n : ℤ) by ring, show -q + q = 0 by ring,
    zpow_zero, mul_one, ← mul_zpow, hs, _root_.one_zpow]

theorem minorOn_inv_of_unitary {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ unitaryGroup (Fin n) ℂ) (s : Finset (Fin n)) :
    minorOn s u⁻¹ = star (minorOn s u) := by
  have hi : u⁻¹ = star u := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hu)
  rw [hi, minorOn, minorOn, Matrix.star_eq_conjTranspose, ← conjTranspose_submatrix, det_conjTranspose]

theorem scalar_section_compact_block_invariant (hU : UAct) (j : ℕ) (p q : ℤ) (x : M2 n)
    (P' S' : Matrix (Fin n) (Fin n) ℂ) (hP : ∀ a b, P' a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j)
    (hS : ∀ a b, S' a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) : f0 p q (x * mX (1 + P') 0 0 (1 + S')) = f0 p q x := by
  have hmA : ∀ a : Fin n, a ∈ blkA j ↔ (a : ℕ) < j := fun a => by simp [blkA]
  have hmB : ∀ a : Fin n, a ∈ blkB j ↔ ¬ (a : ℕ) < j := fun a => by simp [blkB, blkA]
  have dP : (1 + P').det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      have : P' i i = 0 := by
        by_contra h0
        have := hP i i h0
        exact ((hmB i).1 this.2) ((hmA i).1 this.1)
      simp [this]
    · intro a b hba
      have hab : a ≠ b := fun h => (lt_irrefl _ (h ▸ hba))
      simp only [Matrix.add_apply, Matrix.one_apply_ne hab, zero_add]
      by_contra h0
      have := hP a b h0
      exact ((hmB b).1 this.2) (lt_trans (Fin.lt_def.1 hba) ((hmA a).1 this.1))
  have dS : (1 + S').det = 1 := by
    rw [← det_transpose, Matrix.transpose_add, Matrix.transpose_one, Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      have : S' i i = 0 := by
        by_contra h0
        have := hS i i h0
        exact ((hmB i).1 this.1) ((hmA i).1 this.2)
      simp [this]
    · intro a b hba
      have hab : a ≠ b := fun h => (lt_irrefl _ (h ▸ hba))
      simp only [Matrix.add_apply, Matrix.one_apply_ne hab, zero_add, Matrix.transpose_apply]
      by_contra h0
      have := hS b a h0
      exact ((hmB b).1 this.1) (lt_trans (Fin.lt_def.1 hba) ((hmA a).1 this.2))
  obtain ⟨e1, e2⟩ := hU n x (1 + P') 0 0 (1 + S')
  rw [f0, f0, e1, e2]
  simp only [Matrix.mul_zero, add_zero, zero_add, det_mul, dP, dS, mul_one]

theorem wM_one : wM (1 : M2 n) = 1 := by
  have h1 : u1 (1 : M2 n) = 1 := by simp [u1, ← fromBlocks_one]
  have h2 : u2 (1 : M2 n) = 1 := by simp [u2, ← fromBlocks_one]
  rw [wM, h1, h2, inv_one, Matrix.one_mul]

theorem pos_int (j : ℕ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g) :
    0 < ∫ k, ‖minorOn (blkA j) (wM (ι k))‖ ^ 2 * ‖minorOn (blkB j) (wM (ι k))‖ ^ 2 ∂μ := by
  have hw : Continuous (fun k => wM (ι k)) :=
    continuousOn_wM.comp_continuous hι fun k => by
      obtain ⟨g, hg⟩ : InK (ι k) := (hK (ι k)).2 ⟨k, rfl⟩
      exact det_second_cayley_block_ne_zero g
  have hc : Continuous (fun k => ‖minorOn (blkA j) (wM (ι k))‖ ^ 2 * ‖minorOn (blkB j) (wM (ι k))‖ ^ 2) :=
    (((continuous_minorOn _).comp hw).norm.pow 2).mul (((continuous_minorOn _).comp hw).norm.pow 2)
  have hm1 : ∀ s : Finset (Fin n), minorOn s (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := fun s => by
    rw [minorOn]
    have : (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n)) = 1 := by
      ext a b
      by_cases h : a = b
      · subst h; simp
      · have h' : (a : Fin n) ≠ b := fun e => h (Subtype.ext e)
        rw [Matrix.submatrix_apply, Matrix.one_apply_ne h', Matrix.one_apply_ne h]
    rw [this, det_one]
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
    (fun k => by positivity) (x := 1) ?_
  rw [map_one, wM_one, hm1, hm1]; norm_num

theorem isOpen_domK (Kg : Type) [TopologicalSpace Kg] [CompactSpace Kg] (ι : Kg → M2 n) (hι : Continuous ι) :
    IsOpen {x : M2 n | ∀ k, ι k * x ∈ Dom n} := by
  rw [isOpen_iff_mem_nhds]
  intro x0 hx0
  have key : ∀ k ∈ (Set.univ : Set Kg), ∀ᶠ z : M2 n × Kg in nhds (x0, k), ι z.2 * z.1 ∈ Dom n := fun k _ =>
    ((hι.comp continuous_snd).mul continuous_fst).continuousAt.preimage_mem_nhds (isOpen_dom.mem_nhds (hx0 k))
  have h := isCompact_univ.eventually_forall_of_forall_eventually
    (P := fun (x : M2 n) (k : Kg) => ι k * x ∈ Dom n) key
  filter_upwards [h] with x hx k using hx k (Set.mem_univ k)

end PositivityTheory.Rg.Sw.LVs
end
end
