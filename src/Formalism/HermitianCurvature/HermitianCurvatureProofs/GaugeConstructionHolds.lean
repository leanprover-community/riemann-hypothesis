import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreDone
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolPhaseRel

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

namespace RRCentre

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

variable {k r : ℕ}

def genW (k r : ℕ) (w : Fin (k + 1) → ℝ) : Q.Mx k r :=
  Matrix.diagonal fun i =>
    if h : r ≤ i.val ∧ i.val ≤ r + k then Complex.I * ((w ⟨i.val - r, by omega⟩ : ℝ) : ℂ) else 0

def dW (k : ℕ) (w : Fin (k + 1) → ℝ) (t : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j => Complex.exp (Complex.I * ((t * w j : ℝ) : ℂ))

theorem exp_genW (w : Fin (k + 1) → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • genW k r w) = B2.embWb k r (dW k w t) := by
  unfold genW
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext i j
  unfold dW B2.embWb
  by_cases hij : i = j
  · subst hij
    by_cases h : r ≤ i.val ∧ i.val ≤ r + k
    · rw [dif_pos ⟨h, h⟩, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      simp only [Pi.coe_exp, Pi.smul_apply, dif_pos h, smul_eq_mul]
      rw [← Complex.exp_eq_exp_ℂ]
      congr 1
      push_cast
      ring
    · rw [dif_neg (fun h' => h h'.1), if_pos ⟨rfl, h⟩, Matrix.diagonal_apply_eq]
      simp only [Pi.coe_exp, Pi.smul_apply, dif_neg h, smul_zero]
      exact NormedSpace.exp_zero
  · rw [Matrix.diagonal_apply_ne _ hij]
    by_cases h1 : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
    · rw [dif_pos h1, Matrix.diagonal_apply_ne]
      intro he
      apply hij
      ext
      have := congrArg Fin.val he
      simp only at this
      omega
    · rw [dif_neg h1, if_neg (fun h2 => hij h2.1)]

theorem dW_uh (w : Fin (k + 1) → ℝ) (t : ℝ) : dW k w t ∈ UH (Hb k) := by
  show Matrix.conjTranspose (dW k w t) * Hb k * dW k w t = Hb k
  unfold dW Hb
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  have h : star (Complex.exp (Complex.I * ((t * w j : ℝ) : ℂ))) * Complex.exp (Complex.I * ((t * w j : ℝ) : ℂ)) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    simp
  simp only [Pi.star_apply]
  linear_combination (if j = Fin.last k then (-1 : ℂ) else 1) * h

theorem glev_mul_exp {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) (w : Fin (k + 1) → ℝ) (t : ℝ) :
    g * NormedSpace.exp ((t : ℂ) • genW k r w) ∈ Q.Glev k r (Fin.last r) := by
  rw [exp_genW]
  obtain ⟨μ, hμ, rfl⟩ := (TwoByOneBlock.UWb_iff g).1 (NFRadRedA.glev_uwb hg)
  rw [← TwoByOneBlock.emb_mul]
  exact NFRadRedA.uwb_glev (TwoByOneBlock.emb_mem_UWb (TwoByOneBlock.UH_mul hμ (dW_uh w t)))

theorem hasDerivAt_genW {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Φ : (Fin r → ℂ) → Q.Mx k r → E} {U : Set ((Fin r → ℂ) × Q.Mx k r)} {F : (Fin r → ℂ) × Q.Mx k r → E}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (he : ∀ y ∈ U, y.2 ∈ Q.Glev k r (Fin.last r) → Φ y.1 y.2 = F y)
    {x : (Fin r → ℂ) × Q.Mx k r} (hx : x ∈ U) (hxG : x.2 ∈ Q.Glev k r (Fin.last r)) (w : Fin (k + 1) → ℝ) :
    HasDerivAt (fun t : ℝ => Φ x.1 (x.2 * NormedSpace.exp ((t : ℂ) • genW k r w)))
      (fderiv ℝ F x ((0 : Fin r → ℂ), x.2 * genW k r w)) 0 := by
  have hγ : HasDerivAt (fun t : ℝ => (x.1, x.2 * NormedSpace.exp ((t : ℂ) • genW k r w)))
      ((0 : Fin r → ℂ), x.2 * genW k r w) 0 :=
    (hasDerivAt_const (0 : ℝ) x.1).prodMk (hasDerivAt_mul_exp_smul_zero x.2 _)
  have hγ0 : (fun t : ℝ => (x.1, x.2 * NormedSpace.exp ((t : ℂ) • genW k r w))) 0 = x := by
    simp [NormedSpace.exp_zero]
  have hd : DifferentiableAt ℝ F x := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hcomp := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hc : Filter.Tendsto (fun t : ℝ => (x.1, x.2 * NormedSpace.exp ((t : ℂ) • genW k r w))) (nhds 0) (nhds x) := by
    have h := hγ.continuousAt.tendsto
    first | (rw [hγ0] at h; exact h) | exact hγ0 ▸ h | (simp only [hγ0] at h; exact h)
  filter_upwards [hc (hU.mem_nhds hx)] with t ht
  exact he _ ht (glev_mul_exp hxG w t)

theorem hpk_col (p i : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    Hpk k r i p = if i = p then (if p.val = r + k then -1 else 1) else 0 := by
  unfold Hpk
  by_cases hip : i = p
  · subst hip
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hp.1, hp.2, rfl⟩, if_pos rfl]
  · have hv : i.val ≠ p.val := fun h => hip (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hip h.2.2), if_neg hip]

theorem hpk_row (p j : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    Hpk k r p j = if j = p then (if p.val = r + k then -1 else 1) else 0 := by
  unfold Hpk
  by_cases hip : j = p
  · subst hip
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hp.1, hp.2, rfl⟩, if_pos rfl]
  · have hv : j.val ≠ p.val := fun h => hip (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hip h.2.2.symm), if_neg hip]

theorem hs_apply (p i m : Fin (2 * r + k + 1)) :
    (Hpk k r * Matrix.single p p (1 : ℂ)) i m = if m = p then Hpk k r i p else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · by_cases hm : m = p
    · subst hm; simp [Matrix.single_apply]
    · simp [Matrix.single_apply, Ne.symm hm, hm]
  · intro l _ hl; simp [Matrix.single_apply, Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem hpk_single (p : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    (Hpk k r)⁻¹ * (Matrix.single p p (1 : ℂ)).conjTranspose * Hpk k r = Matrix.single p p 1 := by
  rw [Qx2.hpk_inv, Matrix.conjTranspose_single, star_one]
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · rw [hs_apply, if_pos rfl, hpk_col p i hp, hpk_row p j hp, Matrix.single_apply]
    by_cases hi : i = p <;> by_cases hj : j = p
    · subst hi; subst hj; simp only [if_true, and_self]; split_ifs <;> norm_num
    · simp [hi, hj, Ne.symm hj]
    · simp [hi, hj, Ne.symm hi]
    · simp [hi, hj, Ne.symm hi]
  · intro m _ hm
    rw [hs_apply, if_neg hm, zero_mul]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem hpart1_single (p : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    hpart1 (Hpk k r) (Matrix.single p p (1 : ℂ)) = 0 := by
  unfold hpart1
  rw [hpk_single p hp, sub_self, smul_zero]

theorem hpart2_single (n : ℕ) (p : Fin (2 * r + k + 1)) (hpn : p.val = r + n) (hn : n ≤ k) :
    hpart2 (Hpk k r) (Matrix.single p p (1 : ℂ)) = genW k r (fun j' => if j'.val = n then -1 else 0) := by
  have hp : r ≤ p.val ∧ p.val ≤ r + k := ⟨by omega, by omega⟩
  unfold hpart2
  rw [hpk_single p hp]
  ext i l
  unfold genW
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul, Matrix.diagonal_apply]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  by_cases hil : i = l
  · subst hil
    rw [if_pos rfl]
    by_cases hi : i = p
    · subst hi
      rw [if_pos ⟨rfl, rfl⟩, dif_pos hp]
      dsimp only
      rw [if_pos (by omega)]
      field_simp
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    · rw [if_neg (fun h => hi h.1.symm)]
      dsimp only
      split_ifs with h1 h2
      · exfalso; apply hi; apply Fin.ext; omega
      all_goals simp
  · rw [if_neg (fun h => hil (h.1.symm.trans h.2)), if_neg hil]
    simp

theorem rdV_zero' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Q.Mx k r → E) (g : Q.Mx k r) :
    RdV (0 : Q.Mx k r) f g = 0 := by
  unfold RdV
  simp [NormedSpace.exp_zero]

theorem genW_sum : ∑ a : Fin (Q.mdim k r (Fin.last r)),
    genW k r (fun j' : Fin (k + 1) => if j'.val = a.val then (-1 : ℝ) else 0) = -genW k r (fun _ => 1) := by
  ext i l
  rw [Matrix.sum_apply, Matrix.neg_apply]
  unfold genW
  simp only [Matrix.diagonal_apply]
  by_cases hil : i = l
  · subst hil
    simp only [if_true]
    by_cases h : r ≤ i.val ∧ i.val ≤ r + k
    · simp only [dif_pos h]
      have hm : i.val - r < Q.mdim k r (Fin.last r) := by unfold Q.mdim; simp; omega
      rw [Finset.sum_eq_single ⟨i.val - r, hm⟩]
      · simp
      · intro b _ hb
        rw [if_neg]
        · simp
        · intro hh; apply hb; ext; simp only at hh ⊢; omega
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · simp [dif_neg h]
  · simp [hil]

theorem zc_eq (φ : ℝ) : zc k r φ = NormedSpace.exp ((φ : ℂ) • genW k r (fun _ => 1)) := by
  rw [exp_genW]
  unfold zc dW
  congr 1
  ext i j
  rw [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · simp [h, mul_comm]
  · simp [h]

theorem eh_pp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Φ : (Fin r → ℂ) → Q.Mx k r → E} {U : Set ((Fin r → ℂ) × Q.Mx k r)} {F : (Fin r → ℂ) × Q.Mx k r → E}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (he : ∀ y ∈ U, y.2 ∈ Q.Glev k r (Fin.last r) → Φ y.1 y.2 = F y)
    {x : (Fin r → ℂ) × Q.Mx k r} (hx : x ∈ U) (hxG : x.2 ∈ Q.Glev k r (Fin.last r))
    (a : Fin (Q.mdim k r (Fin.last r))) :
    Q.EH k r (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) a) (Φ x.1) x.2 =
      Complex.I • fderiv ℝ F x ((0 : Fin r → ℂ),
        x.2 * genW k r (fun j' : Fin (k + 1) => if j'.val = a.val then (-1 : ℝ) else 0)) := by
  have ha : a.val ≤ k := by have := a.isLt; unfold Q.mdim at this; simp at this; omega
  have hpn : (Q.posL k r (Fin.last r) a).val = r + a.val := by simp [Q.posL]; omega
  have hp : r ≤ (Q.posL k r (Fin.last r) a).val ∧ (Q.posL k r (Fin.last r) a).val ≤ r + k :=
    ⟨by omega, by omega⟩
  show RdV _ _ _ + Complex.I • RdV _ _ _ = _
  rw [hpart1_single _ hp, hpart2_single a.val _ hpn ha, rdV_zero', zero_add]
  congr 1
  exact (hasDerivAt_genW hU hF he hx hxG _).deriv

end

end RRCentre

open RRCentre in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem rotation_centre_condition : GTRRCentre := by
  intro k r z z' Wp Wq _ _ _ _ π π' Φ x hx
  obtain ⟨U, F, hU, hxU, hF, he⟩ := Φ.2.2.1 x hx
  have hxG : x.2 ∈ Q.Glev k r (Fin.last r) := hx.2.1
  have hfun : (fun φ : ℝ => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 (x.2 * zc k r φ)) =
      fun φ : ℝ => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1
        (x.2 * NormedSpace.exp ((φ : ℂ) • genW k r (fun _ => 1))) := by
    funext φ; rw [zc_eq]
  rw [hfun]
  have hd := hasDerivAt_genW hU hF he hxU hxG (fun _ => 1)
  refine hd.congr_deriv ?_
  symm
  rw [Finset.sum_congr rfl (fun a _ => eh_pp hU hF he hxU hxG a), ← Finset.smul_sum, ← map_sum]
  have hs : ∑ a : Fin (Q.mdim k r (Fin.last r)), ((0 : Fin r → ℂ),
      x.2 * genW k r (fun j' : Fin (k + 1) => if j'.val = a.val then (-1 : ℝ) else 0)) =
      -((0 : Fin r → ℂ), x.2 * genW k r (fun _ => 1)) := by
    ext1
    · rw [Prod.fst_sum]; simp
    · rw [Prod.snd_sum, ← Finset.mul_sum, genW_sum]
      simp
  rw [hs, map_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.GTRRSecH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section block

variable {k : ℕ}

theorem phase_star_mul (φ : ℝ) :
    star (Complex.exp ((φ : ℂ) * Complex.I)) * Complex.exp ((φ : ℂ) * Complex.I) = 1 := by
  rw [show star (Complex.exp ((φ : ℂ) * Complex.I)) = (starRingEnd ℂ) (Complex.exp ((φ : ℂ) * Complex.I)) from rfl,
    ← Complex.exp_conj, ← Complex.exp_add]
  simp [Complex.conj_ofReal]

theorem Hb_mul_self : Hb k * Hb k = 1 := by
  unfold Hb
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

theorem inv_of_UH {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hg : g ∈ UH (Hb k)) :
    g⁻¹ * g = 1 ∧ g * g⁻¹ = 1 := by
  have hg' : gᴴ * Hb k * g = Hb k := hg
  have hl : (Hb k * gᴴ * Hb k) * g = 1 := by
    calc (Hb k * gᴴ * Hb k) * g = Hb k * (gᴴ * Hb k * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', Hb_mul_self]
  rw [Matrix.inv_eq_left_inv hl]
  exact ⟨hl, mul_eq_one_comm.1 hl⟩

theorem UH_mul {g h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hg : g ∈ UH (Hb k)) (hh : h ∈ UH (Hb k)) :
    g * h ∈ UH (Hb k) := by
  have e1 : gᴴ * Hb k * g = Hb k := hg
  have e2 : hᴴ * Hb k * h = Hb k := hh
  show (g * h)ᴴ * Hb k * (g * h) = Hb k
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * Hb k * (g * h) = hᴴ * (gᴴ * Hb k * g) * h := by simp only [Matrix.mul_assoc]
    _ = Hb k := by rw [e1, e2]

theorem UH_inv {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hg : g ∈ UH (Hb k)) : g⁻¹ ∈ UH (Hb k) := by
  have hg' : gᴴ * Hb k * g = Hb k := hg
  obtain ⟨_, h2⟩ := inv_of_UH hg
  show (g⁻¹)ᴴ * Hb k * g⁻¹ = Hb k
  calc (g⁻¹)ᴴ * Hb k * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hb k * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hb k * (g * g⁻¹) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hb k := by rw [h2]; simp

theorem diag_phase_UH (d : Fin (k + 1) → ℂ) (hd : ∀ j, star (d j) * d j = 1) : diagonal d ∈ UH (Hb k) := by
  show (diagonal d)ᴴ * Hb k * diagonal d = Hb k
  rw [diagonal_conjTranspose]
  simp only [Hb, diagonal_mul_diagonal]
  congr 1
  funext j
  simp only [Pi.star_apply]
  rw [mul_comm (star (d j)) _, mul_assoc, hd j, mul_one]

theorem dOne_UH (φ : ℝ) : dOne k φ ∈ UH (Hb k) := by
  refine diag_phase_UH _ fun j => ?_
  split_ifs
  · simp
  · exact phase_star_mul φ

theorem dTwo_UH (φ : ℝ) : dTwo k φ ∈ UH (Hb k) := by
  refine diag_phase_UH _ fun j => ?_
  split_ifs
  · exact phase_star_mul φ
  · simp

theorem smul_one_UH (φ : ℝ) :
    (Complex.exp ((φ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) ∈ UH (Hb k) := by
  have e : Complex.exp ((φ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) =
      diagonal (fun _ => Complex.exp ((φ : ℂ) * Complex.I)) := by
    ext i j
    simp [Matrix.one_apply, diagonal_apply]
  rw [e]
  exact diag_phase_UH _ (fun _ => phase_star_mul φ)

theorem exp_zero_I : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp

theorem exp_two_pi_I : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
  push_cast
  exact Complex.exp_two_pi_mul_I

theorem exp_add_I (φ ψ : ℝ) : Complex.exp (((φ + ψ : ℝ) : ℂ) * Complex.I) =
    Complex.exp ((φ : ℂ) * Complex.I) * Complex.exp ((ψ : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  push_cast
  ring_nf

theorem dOne_eq_one {φ : ℝ} (h : Complex.exp ((φ : ℂ) * Complex.I) = 1) : dOne k φ = 1 := by
  simp [dOne, h]

theorem dTwo_eq_one {φ : ℝ} (h : Complex.exp ((φ : ℂ) * Complex.I) = 1) : dTwo k φ = 1 := by
  simp [dTwo, h]

theorem dOne_add (φ ψ : ℝ) : dOne k (φ + ψ) = dOne k φ * dOne k ψ := by
  simp only [dOne, diagonal_mul_diagonal]
  congr 1
  funext j
  split_ifs
  · simp
  · rw [exp_add_I]

theorem dTwo_add (φ ψ : ℝ) : dTwo k (φ + ψ) = dTwo k φ * dTwo k ψ := by
  simp only [dTwo, diagonal_mul_diagonal]
  congr 1
  funext j
  split_ifs
  · rw [exp_add_I]
  · simp

end block

end Formalism.FourierDecayAlt.P.GTRRSecH

namespace Formalism.FourierDecayAlt.P.GTRRSecH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section block2

variable {k : ℕ}

theorem nu_rot (hk : 1 ≤ k) (w s : ℂ) (φ : ℝ) :
    nu k w s * (Complex.exp ((φ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) =
      dOne k φ * nu k (w * Complex.exp ((φ : ℂ) * Complex.I)) s * dTwo k φ := by
  have hl : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have he := phase_star_mul φ
  rw [Complex.star_def] at he
  rw [Matrix.mul_smul, Matrix.mul_one]
  ext i j
  simp only [dOne, dTwo, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  rcases eq_or_ne i 0 with rfl | hi0 <;> rcases eq_or_ne j 0 with rfl | hj0
  · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm]
    linear_combination (-(Complex.exp (↑φ * Complex.I) * (starRingEnd ℂ) w)) * he
  · rcases eq_or_ne j (Fin.last k) with rfl | hjl
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm]
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm, hj0, hjl, Ne.symm hj0, Ne.symm hjl]
  · rcases eq_or_ne i (Fin.last k) with rfl | hil
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm]
      ring
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm, hi0, hil, Ne.symm hi0, Ne.symm hil]
  · rcases eq_or_ne i (Fin.last k) with rfl | hil <;> rcases eq_or_ne j (Fin.last k) with rfl | hjl
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm]
      ring
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm, hj0, hjl, Ne.symm hj0, Ne.symm hjl]
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm, hi0, hil, Ne.symm hi0, Ne.symm hil]
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hi0, hil, hj0, hjl, Ne.symm hi0, Ne.symm hil, Ne.symm hj0, Ne.symm hjl]

theorem wZ_rot (T T' : ℝ) (ζ e : ℂ) : wZ T T' (ζ * e) = wZ T T' ζ * e := by
  unfold wZ; ring

theorem sZ_rot (T T' : ℝ) (ζ : ℂ) (φ : ℝ) : sZ T T' (ζ * Complex.exp ((φ : ℂ) * Complex.I)) = sZ T T' ζ := by
  have h1 : Complex.normSq (Complex.exp ((φ : ℂ) * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  simp only [sZ, Complex.normSq_mul, h1, mul_one]

theorem secB_rot (hk : 1 ≤ k) {a b : Fin (k + 1) → ℂ} {T T' : ℝ}
    (hA : gA k a T ∈ UH (Hb k)) (hB : gB k b T' ∈ UH (Hb k)) (ζ : ℂ) (φ : ℝ) :
    theSecB k a b T T' ζ * (Complex.exp ((φ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) =
      (gA k a T * dOne k φ * (gA k a T)⁻¹) * theSecB k a b T T' (ζ * Complex.exp ((φ : ℂ) * Complex.I)) *
        ((gB k b T')⁻¹ * dTwo k φ * gB k b T') := by
  obtain ⟨hA1, _⟩ := inv_of_UH hA
  obtain ⟨_, hB2⟩ := inv_of_UH hB
  set e := Complex.exp ((φ : ℂ) * Complex.I)
  set A := gA k a T
  set B := gB k b T'
  have hsc : B * (e • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) = (e • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) * B := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  simp only [theSecB]
  rw [wZ_rot, sZ_rot]
  have hn := nu_rot hk (wZ T T' ζ) (sZ T T' ζ) φ
  calc A * nu k (wZ T T' ζ) (sZ T T' ζ) * B * (e • 1)
      = A * (nu k (wZ T T' ζ) (sZ T T' ζ) * (e • 1)) * B := by
        rw [Matrix.mul_assoc _ B, hsc]
        simp only [Matrix.mul_assoc]
    _ = A * (dOne k φ * nu k (wZ T T' ζ * e) (sZ T T' ζ) * dTwo k φ) * B := by rw [hn]
    _ = A * dOne k φ * (A⁻¹ * A) * nu k (wZ T T' ζ * e) (sZ T T' ζ) * (B * B⁻¹) * dTwo k φ * B := by
        rw [hA1, hB2]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by
        simp only [Matrix.mul_assoc]
        rfl

theorem dOne_fix_last (φ : ℝ) (c : ℂ) :
    dOne k φ *ᵥ (c • Pi.single (Fin.last k) 1) = c • Pi.single (Fin.last k) 1 := by
  ext j
  simp only [dOne]
  rw [mulVec_diagonal]
  by_cases hj : j = Fin.last k
  · simp [dOne, hj]
  · simp [dOne, hj, Pi.single_apply]

theorem dTwo_fix_last (hk : 1 ≤ k) (φ : ℝ) (c : ℂ) :
    dTwo k φ *ᵥ (c • Pi.single (Fin.last k) 1) = c • Pi.single (Fin.last k) 1 := by
  ext j
  simp only [dTwo]
  rw [mulVec_diagonal]
  by_cases hj : j = Fin.last k
  · have h0 : (Fin.last k) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [dTwo, hj, h0]
  · simp [dTwo, hj, Pi.single_apply]

end block2

end Formalism.FourierDecayAlt.P.GTRRSecH

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
open Formalism.FourierDecayAlt.P.GTRRSecH

theorem jV_smul' {k r : ℕ} (c : ℂ) (u : Fin (k + 1) → ℂ) : jV k r (c • u) = c • jV k r u := by
  ext i
  simp only [jV, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem smul_one_mulVec' {k : ℕ} (c : ℂ) (u : Fin (k + 1) → ℂ) :
    (c • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) *ᵥ u = c • u := by
  rw [smul_mulVec, one_mulVec]

theorem herm_smul_left' {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (c : ℂ) (v w : ι → ℂ) :
    herm H (c • v) w = c * herm H v w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul]

private theorem herm_Hb_self_eq_ofReal_re {k : ℕ} (u : Fin (k + 1) → ℂ) :
    herm (Hb k) u u = ((herm (Hb k) u u).re : ℂ) := by
  have h : herm (Hb k) u u =
      ∑ j, (((if j = Fin.last k then (-1 : ℝ) else 1) * Complex.normSq (u j) : ℝ) : ℂ) := by
    simp only [herm, Hb, dotProduct, mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    split_ifs <;> push_cast <;> ring
  rw [h, ← Complex.ofReal_sum, Complex.ofReal_re]

theorem rotation_section_holds : GTRRSec := by
  intro k r z z' hk hz hz' hT hT'
  have hzj : jV k r (wbPart k r z) = z := jV_wbPart hz
  have hzj' : jV k r (wbPart k r z') = z' := jV_wbPart hz'
  have haa : herm (Hb k) (wbPart k r z) (wbPart k r z) = -↑(Tz k r z) := by
    rw [herm_Hb_self_eq_ofReal_re]
    simp only [Tz]
    conv_rhs => rw [← hzj, herm_jV]
    push_cast
    ring
  have hbb : herm (Hb k) (wbPart k r z') (wbPart k r z') = -↑(Tz k r z') := by
    rw [herm_Hb_self_eq_ofReal_re]
    simp only [Tz]
    conv_rhs => rw [← hzj', herm_jV]
    push_cast
    ring
  obtain ⟨hAU, hAv⟩ := gA_spec k hT haa
  obtain ⟨hBU, hBv⟩ := gB_spec k hT' hbb
  have hA : gA k (wbPart k r z) (Tz k r z) ∈ UH (Hb k) := hAU
  have hB : gB k (wbPart k r z') (Tz k r z') ∈ UH (Hb k) := hBU
  obtain ⟨hA1, hA2⟩ := inv_of_UH hA
  obtain ⟨hB1, hB2⟩ := inv_of_UH hB
  have hsec := theSection_isSection k r z z' hk hz hz' hT hT'
  refine ⟨fun φ => ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, fun φ ψ => ⟨?_, ?_⟩, ?_, ?_⟩
  · refine (UWset_iff hz _).2 ⟨_, Formalism.FourierDecayAlt.P.GTRRSecH.UH_mul (Formalism.FourierDecayAlt.P.GTRRSecH.UH_mul hA (dOne_UH φ)) (UH_inv hA), ?_, rfl⟩
    have hinv : (gA k (wbPart k r z) (Tz k r z))⁻¹ *ᵥ wbPart k r z =
        (↑√(Tz k r z) : ℂ) • Pi.single (Fin.last k) 1 := by
      calc (gA k (wbPart k r z) (Tz k r z))⁻¹ *ᵥ wbPart k r z
          = (gA k (wbPart k r z) (Tz k r z))⁻¹ *ᵥ (gA k (wbPart k r z) (Tz k r z) *ᵥ
              ((↑√(Tz k r z) : ℂ) • Pi.single (Fin.last k) 1)) := by rw [hAv]
        _ = (↑√(Tz k r z) : ℂ) • Pi.single (Fin.last k) 1 := by rw [mulVec_mulVec, hA1, one_mulVec]
    rw [← mulVec_mulVec, ← mulVec_mulVec, hinv, dOne_fix_last, hAv]
  · refine (UWset_iff hz' _).2 ⟨_, Formalism.FourierDecayAlt.P.GTRRSecH.UH_mul (Formalism.FourierDecayAlt.P.GTRRSecH.UH_mul (UH_inv hB) (dTwo_UH φ)) hB, ?_, rfl⟩
    rw [← mulVec_mulVec, ← mulVec_mulVec, hBv, dTwo_fix_last hk, ← hBv, mulVec_mulVec, hB1, one_mulVec]
  · simp only [hL]
    rw [dOne_eq_one exp_zero_I, Matrix.mul_one, hA2, emb_one]
  · simp only [hR]
    rw [dTwo_eq_one exp_zero_I, Matrix.mul_one, hB1, emb_one]
  · simp only [hL]
    rw [dOne_eq_one exp_two_pi_I, Matrix.mul_one, hA2, emb_one]
  · simp only [hR]
    rw [dTwo_eq_one exp_two_pi_I, Matrix.mul_one, hB1, emb_one]
  · simp only [hL]
    rw [← emb_mul, dOne_add]
    congr 1
    set A := gA k (wbPart k r z) (Tz k r z)
    calc A * (dOne k φ * dOne k ψ) * A⁻¹ = A * dOne k φ * (A⁻¹ * A) * dOne k ψ * A⁻¹ := by
          rw [hA1]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = A * dOne k φ * A⁻¹ * (A * dOne k ψ * A⁻¹) := by simp only [Matrix.mul_assoc]
  · simp only [hR]
    rw [← emb_mul, dTwo_add]
    congr 1
    set B := gB k (wbPart k r z') (Tz k r z')
    calc B⁻¹ * (dTwo k φ * dTwo k ψ) * B = B⁻¹ * dTwo k φ * (B * B⁻¹) * dTwo k ψ * B := by
          rw [hB2]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = B⁻¹ * dTwo k φ * B * (B⁻¹ * dTwo k ψ * B) := by simp only [Matrix.mul_assoc]
  · intro φ g hg
    obtain ⟨μ, _, _, rfl⟩ := (UWset_iff hz' g).1 hg
    simp only [zc]
    rw [← emb_mul, ← emb_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · intro ζ hζ φ
    have hSU : theSection k r z z' ζ ∈ UH (Hb k) := (hsec.2 ζ hζ).1
    refine ⟨?_, ?_⟩
    · simp only [NF.muZ, zc, hL, hR]
      rw [← emb_mul, show theSection k r z z' ζ = theSecB k (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r z') ζ from rfl,
        secB_rot hk hA hB ζ φ, emb_mul, emb_mul]
      rfl
    · intro c hc
      have hprod : NF.muZ k r (theSection k r z z') ζ * zc k r φ =
          embWb k r (theSection k r z z' ζ * (Complex.exp ((φ : ℂ) * Complex.I) • 1)) := by
        simp only [NF.muZ, zc]
        rw [emb_mul]
      refine ⟨hc, ?_, ?_⟩
      · rw [hprod]
        obtain ⟨hU, hfix⟩ := emb_mem_UWb (r := r) (Formalism.FourierDecayAlt.P.GTRRSecH.UH_mul hSU (smul_one_UH φ))
        exact ⟨hU, fun a _ => hfix a⟩
      · show 0 < Q.GGl k r z z' _
        simp only [Q.GGl]
        rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last]
        have hv : (NF.muZ k r (theSection k r z z') ζ * zc k r φ) *ᵥ z' =
            Complex.exp ((φ : ℂ) * Complex.I) • (embWb k r (theSection k r z z' ζ) *ᵥ z') := by
          rw [← mulVec_mulVec]
          simp only [NF.muZ, zc]
          conv_lhs => rw [← hzj', emb_mulVec_jV, smul_one_mulVec', jV_smul', hzj']
          rw [mulVec_smul]
        rw [hv, herm_smul_left', (sec_vec hz hz' hsec hζ).2.2, Complex.normSq_mul]
        have h1 : Complex.normSq (Complex.exp ((φ : ℂ) * Complex.I)) = 1 := by
          rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
          norm_num
        rw [h1, one_mul]
        linarith

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem rotation_ode_holds : GTRRODE := by
  intro ι _ _ Mf Bm h0 hadd hper hd hoff
  have hderiv : ∀ (φ : ℝ) (i j : ι), HasDerivAt (fun x => Mf x i j) (Bm i i * Mf φ i j) φ := by
    intro φ i j
    have hg0 := HasDerivAt.sum (u := Finset.univ) (fun k _ => (hd i k).mul_const (Mf φ k j))
    have ef : (∑ k : ι, fun (y : ℝ) => Mf y i k * Mf φ k j) = fun h : ℝ => ∑ k, Mf h i k * Mf φ k j := by
      funext h
      rw [Finset.sum_apply]
    rw [ef] at hg0
    have hsum : ∑ k, Bm i k * Mf φ k j = Bm i i * Mf φ i j := by
      rw [Finset.sum_eq_single i]
      · intro k _ hk
        rw [hoff i k (Ne.symm hk), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsum] at hg0
    have h2 := HasDerivAt.comp_sub_const φ φ (by rw [sub_self]; exact hg0)
    have e : (fun x => Mf x i j) = fun x : ℝ => ∑ k, Mf (x - φ) i k * Mf φ k j := by
      funext x
      rw [← Matrix.mul_apply, ← hadd, sub_add_cancel]
    rw [e]
    exact h2
  have hsol : ∀ (i j : ι) (x : ℝ), Mf x i j = Complex.exp (Bm i i * x) * (if i = j then 1 else 0) := by
    intro i j x
    have hf : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (-Bm i i * y) * Mf y i j) 0 y := by
      intro y
      have he : HasDerivAt (fun y : ℝ => Complex.exp (-Bm i i * y)) (Complex.exp (-Bm i i * y) * (-Bm i i * 1)) y :=
        (((hasDerivAt_id y).ofReal_comp).const_mul (-Bm i i)).cexp
      have hm := he.mul (hderiv y i j)
      have h3 : Complex.exp (-Bm i i * ↑y) * (-Bm i i * 1) * Mf y i j + Complex.exp (-Bm i i * ↑y) * (Bm i i * Mf y i j) = 0 := by
        ring
      rw [h3] at hm
      exact hm
    have hc := is_const_of_deriv_eq_zero (fun y => (hf y).differentiableAt) (fun y => (hf y).deriv) x 0
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, h0, Matrix.one_apply] at hc
    rw [← hc, ← mul_assoc, ← Complex.exp_add]
    simp
  have hn : ∀ i, ∃ n : ℤ, Bm i i = n * Complex.I := by
    intro i
    have h1 := hsol i i (2 * Real.pi)
    rw [hper] at h1
    simp only [Matrix.one_apply_eq, if_true, mul_one] at h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1.symm
    refine ⟨n, ?_⟩
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero]
    apply mul_right_cancel₀ hpi
    push_cast at hn
    linear_combination hn
  choose n hn using hn
  refine ⟨n, fun φ i j => ?_⟩
  rw [hsol]
  split_ifs with h
  · subst h
    rw [hn]
    ring_nf
  · simp

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem rot_alg (ζ D1 DI : ℂ) : -(ζ.im : ℂ) * D1 + (ζ.re : ℂ) * DI =
    Complex.I * (ζ * ((1 / 2 : ℂ) * (D1 + -Complex.I * DI)) - star ζ * ((1 / 2 : ℂ) * (D1 + Complex.I * DI))) := by
  have hz : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I := (Complex.re_add_im ζ).symm
  have hs : star ζ = (ζ.re : ℂ) - (ζ.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  linear_combination (-(Complex.I / 2) * D1 + (Complex.I ^ 2 / 2) * DI) * hz +
    ((Complex.I / 2) * D1 + (Complex.I ^ 2 / 2) * DI) * hs + ((ζ.re : ℂ) * DI - (ζ.im : ℂ) * D1) * Complex.I_sq

theorem rotation_wirtinger_holds : GTRRWirt := by
  intro r u x hu
  have h1 : HasDerivAt (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I))
      (Complex.exp ((((0 : ℝ) : ℂ)) * Complex.I) * (1 * Complex.I)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp
  have h2 : HasDerivAt (fun φ : ℝ => x.2 * Complex.exp ((φ : ℂ) * Complex.I)) (x.2 * Complex.I) 0 := by
    have h3 := h1.const_mul x.2
    simpa using h3
  have hγ : HasDerivAt (fun φ : ℝ => ((x.1, x.2 * Complex.exp ((φ : ℂ) * Complex.I)) : MA.E r))
      ((0 : Fin r → ℂ), x.2 * Complex.I) 0 := by
    first
    | exact (hasDerivAt_const (0 : ℝ) x.1).prodMk h2
    | exact (hasDerivAt_const (0 : ℝ) x.1).prod h2
  have hx : x = ((x.1, x.2 * Complex.exp ((((0 : ℝ) : ℂ)) * Complex.I)) : MA.E r) := by simp
  have hc := hu.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hx
  have hdir1 : MA.dirE (M.vz (r := r)) = ((0 : Fin r → ℂ), (1 : ℂ)) := by simp [MA.dirE, M.vz]
  have hdir2 : MA.dirE (M.vzb (r := r)) = ((0 : Fin r → ℂ), (1 : ℂ)) := by simp [MA.dirE, M.vzb]
  have hw1 : MA.wirt M.vz u x = (1 / 2 : ℂ) * (fderiv ℝ u x ((0 : Fin r → ℂ), (1 : ℂ)) +
      -Complex.I * fderiv ℝ u x ((0 : Fin r → ℂ), Complex.I)) := by
    rw [MA.wirt, hdir1]
    simp [M.vz]
  have hw2 : MA.wirt M.vzb u x = (1 / 2 : ℂ) * (fderiv ℝ u x ((0 : Fin r → ℂ), (1 : ℂ)) +
      Complex.I * fderiv ℝ u x ((0 : Fin r → ℂ), Complex.I)) := by
    rw [MA.wirt, hdir2]
    simp [M.vzb]
  have key : Complex.I * (x.2 * MA.wirt M.vz u x - star x.2 * MA.wirt M.vzb u x) =
      fderiv ℝ u x ((0 : Fin r → ℂ), x.2 * Complex.I) := by
    rw [hw1, hw2, ← rot_alg]
    have hv : ((0 : Fin r → ℂ), x.2 * Complex.I) = x.2.re • ((0 : Fin r → ℂ), Complex.I) +
        (-x.2.im) • ((0 : Fin r → ℂ), (1 : ℂ)) := by
      refine Prod.ext (by simp) ?_
      simp only [Prod.smul_snd, Prod.snd_add, Complex.real_smul, mul_one]
      apply Complex.ext <;> simp
    rw [hv, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [key]
  exact hc

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace RRMat

theorem normSq_rot (ζ : ℂ) (φ : ℝ) :
    Complex.normSq (ζ * Complex.exp ((φ : ℂ) * Complex.I)) = Complex.normSq ζ := by
  rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq (Complex.exp _), Complex.norm_exp_ofReal_mul_I]
  ring

theorem wR_rot (k : ℕ) (TT : ℝ) (ζ : ℂ) (φ : ℝ) :
    wR k TT (ζ * Complex.exp ((φ : ℂ) * Complex.I)) = wR k TT ζ := by
  unfold wR
  rw [normSq_rot]

theorem exists_ann (P : M.Par) : ∃ ζ : ℂ, P.TT < Complex.normSq ζ := by
  refine ⟨((|P.TT| + 1 : ℝ) : ℂ), ?_⟩
  rw [Complex.normSq_ofReal]
  nlinarith [abs_nonneg P.TT, le_abs_self P.TT]

theorem hsVec_zero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  simpa using VLem.hsV_smul (Wp := Wp) (Wq := Wq) 0 0

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def rotA (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (φ : ℝ) (X : Wq →L[ℂ] Wp) : Wq →L[ℂ] Wp :=
  (Bs.π (hL P.k P.r Bs.z φ)).comp (X.comp (Bs.π' (hR P.k P.r Bs.z' φ)))

theorem rotA_sum (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (φ : ℝ) {ι : Type} (s : Finset ι) (a : ι → ℂ)
    (X : ι → (Wq →L[ℂ] Wp)) : rotA P Bs φ (∑ i ∈ s, a i • X i) = ∑ i ∈ s, a i • rotA P Bs φ (X i) := by
  ext v
  simp [rotA, map_sum, map_smul]

theorem rotA_smul (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (φ : ℝ) (a : ℂ) (X : Wq →L[ℂ] Wp) :
    rotA P Bs φ (a • X) = a • rotA P Bs φ X := by
  ext v
  simp [rotA]


theorem ann_tz (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') {ζ : ℂ}
    (hζ : P.TT < Complex.normSq ζ) : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
  rw [SSTr.tz_eq P Bs hpl]; exact hζ

theorem rot_eqv (hS : GTRRSec) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hsec : Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z') (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r) (ζ : ℂ) (hζ : P.TT < Complex.normSq ζ) (φ : ℝ) :
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ * zc P.k P.r φ) =
      rotA P Bs φ ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
        (NF.muZ P.k P.r Bs.μsec (ζ * Complex.exp ((φ : ℂ) * Complex.I)))) := by
  have hB := SSTr.radBase P Bs hpl
  have hS' := hS P.k P.r Bs.z Bs.z' hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2.1
  have hζ1 := ann_tz P Bs hpl hζ
  have hζ2 : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq (ζ * Complex.exp ((φ : ℂ) * Complex.I)) := by
    rw [normSq_rot]; exact hζ1
  have hrot := (hS'.2.2.2.2 ζ hζ1 φ).1
  rw [← hsec] at hrot
  rw [hrot]
  exact Φ.2.2.2 (c, _) (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hB.2.1 hB.2.2.1 hB.2.2.2.2.2.1
    (q := (c, ζ * Complex.exp ((φ : ℂ) * Complex.I))) ⟨hc, hζ2⟩) _ (hS'.1 φ).1 _ (hS'.1 φ).2

theorem rot_fib (hS : GTRRSec) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hsec : Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z') (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r) (ζ : ℂ) (hζ : P.TT < Complex.normSq ζ) (ψ : ℝ) :
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ * zc P.k P.r ψ) ∈
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
  intro p hp
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have hB := SSTr.radBase P Bs hpl
  have hS' := hS P.k P.r Bs.z Bs.z' hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2.1
  have hζ1 := ann_tz P Bs hpl hζ
  have hD := (hS'.2.2.2.2 ζ hζ1 ψ).2 c hc
  rw [← hsec] at hD
  refine (Φ.2.2.2 _ hD _ hp1 _ hp2).symm.trans ?_
  dsimp only
  apply congrArg
  calc p.1 * (NF.muZ P.k P.r Bs.μsec ζ * zc P.k P.r ψ) * p.2
      = p.1 * NF.muZ P.k P.r Bs.μsec ζ * (zc P.k P.r ψ * p.2) := by simp only [mul_assoc]
    _ = p.1 * NF.muZ P.k P.r Bs.μsec ζ * (p.2 * zc P.k P.r ψ) := by rw [hS'.2.2.2.1 ψ p.2 hp2]
    _ = (p.1 * NF.muZ P.k P.r Bs.μsec ζ * p.2) * zc P.k P.r ψ := by simp only [mul_assoc]
    _ = NF.muZ P.k P.r Bs.μsec ζ * zc P.k P.r ψ := by rw [hp3]

theorem rotA_add (hS : GTRRSec) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (φ ψ : ℝ) (X : Wq →L[ℂ] Wp) : rotA P Bs (φ + ψ) X = rotA P Bs φ (rotA P Bs ψ X) := by
  have hB := SSTr.radBase P Bs hpl
  have hS' := hS P.k P.r Bs.z Bs.z' hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2.1
  have hL' : hL P.k P.r Bs.z (φ + ψ) = hL P.k P.r Bs.z φ * hL P.k P.r Bs.z ψ := (hS'.2.2.1 φ ψ).1
  have hR' : hR P.k P.r Bs.z' (φ + ψ) = hR P.k P.r Bs.z' ψ * hR P.k P.r Bs.z' φ := by
    rw [add_comm]; exact (hS'.2.2.1 ψ φ).2
  unfold rotA
  rw [hL', hR', hB.2.2.2.2.2.2.1.2 _ (hS'.1 φ).1 _ (hS'.1 ψ).1, hB.2.2.2.2.2.2.2.1.2 _ (hS'.1 ψ).2 _ (hS'.1 φ).2]
  ext v
  simp [ContinuousLinearMap.comp_apply]

theorem rotA_zero (hS : GTRRSec) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (X : Wq →L[ℂ] Wp) : rotA P Bs 0 X = X := by
  have hB := SSTr.radBase P Bs hpl
  have hS' := hS P.k P.r Bs.z Bs.z' hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2.1
  unfold rotA
  rw [hS'.2.1.1, hS'.2.1.2.1, hB.2.2.2.2.2.2.1.1, hB.2.2.2.2.2.2.2.1.1]
  ext v
  simp

theorem rotA_two_pi (hS : GTRRSec) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (X : Wq →L[ℂ] Wp) : rotA P Bs (2 * Real.pi) X = X := by
  have hB := SSTr.radBase P Bs hpl
  have hS' := hS P.k P.r Bs.z Bs.z' hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2.1
  unfold rotA
  rw [hS'.2.1.2.2.1, hS'.2.1.2.2.2, hB.2.2.2.2.2.2.1.1, hB.2.2.2.2.2.2.2.1.1]
  ext v
  simp

theorem hasDerivAt_pair (hC : GTRRCentre) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r)
    (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') (E : Wq →L[ℂ] Wp) (w : ℂ) :
    HasDerivAt (fun φ : ℝ => w * inner ℂ (B.hsVec E) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 (x.2 * zc P.k P.r φ))))
      (w * (Complex.I * inner ℂ (B.hsVec E) (B.hsVec (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
          Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
            ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2)))) 0 := by
  have h0 := hC P.k P.r Bs.z Bs.z' Wp Wq Bs.π Bs.π' Φ x hx
  have h1 := (hsCLM (Wp := Wp) (Wq := Wq)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
  have h2 := ((hasDerivAt_const (0 : ℝ) (B.hsVec E)).inner ℂ h1).const_mul w
  simp only [Function.comp_def, hsCLM_apply, inner_zero_left, add_zero, VLem.hsV_smul, inner_smul_right] at h2
  exact h2

end

end RRMat

open RRMat in
theorem rotation_matrix_form_holds : GTRRMatFrom := by
  intro hC hS hO Wp Wq _ _ _ _ _ _ P Bs X d hyp hsec e he hk hc Rt s hRK hRt
  obtain ⟨hpl, hk2, -⟩ := hyp
  have hB := SSTr.radBase P Bs hpl
  obtain ⟨ζ₀, hζ₀⟩ := exists_ann P
  set c₀ : Fin P.r → ℂ := fun _ => 1 with hc₀def
  have hc₀ : c₀ ∈ OmX P.r := fun _ => one_ne_zero
  set E : M.Ty P → (Wq →L[ℂ] Wp) := fun σ => e σ 0 with hEdef
  have heE : ∀ σ ζ, e σ ζ = E σ := fun σ ζ => hc σ ζ 0
  set w₀ : ℂ := ((wR P.k P.TT ζ₀ : ℝ) : ℂ) with hw₀def
  have hw₀ : w₀ ≠ 0 := by simp only [hw₀def]; exact_mod_cast (SSTr.wR_pos P hζ₀).ne'

  have hex : ∀ ρ' : M.Ty P, ∃ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      trR P Bs e Φ = (fun τ => if τ = ρ' then (1 : MA.SmQ P.r P.TT) else 0) ∧
      ∀ q : MA.Qp P.r P.TT, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
        ∑ ρ, ((((wR P.k P.TT q.1.2)⁻¹ : ℝ) : ℂ) *
          ((if ρ = ρ' then (1 : MA.SmQ P.r P.TT) else 0 : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) • e ρ q.1.2 :=
    fun ρ' => SSTr.exists_tr P Bs hpl hk2 e he _
  choose Φ hΦtr hΦv using hex

  have hval : ∀ ρ' (φ : ℝ), (Φ ρ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c₀
      (NF.muZ P.k P.r Bs.μsec (ζ₀ * Complex.exp ((φ : ℂ) * Complex.I))) = w₀⁻¹ • E ρ' := by
    intro ρ' φ
    have hq : ((c₀, ζ₀ * Complex.exp ((φ : ℂ) * Complex.I)) : MA.E P.r) ∈ MA.Qset P.r P.TT :=
      ⟨hc₀, by rw [normSq_rot]; exact hζ₀⟩
    have h := hΦv ρ' ⟨_, hq⟩
    simp only at h
    rw [h, Finset.sum_eq_single ρ']
    · simp [wR_rot, hw₀def, heE]
    · intro τ _ hτ
      simp [hτ]
    · simp

  have hAE : ∀ ρ' (φ : ℝ), rotA P Bs φ (E ρ') =
      w₀ • (Φ ρ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c₀ (NF.muZ P.k P.r Bs.μsec ζ₀ * zc P.k P.r φ) := by
    intro ρ' φ
    rw [rot_eqv hS P Bs hpl hsec (Φ ρ') c₀ hc₀ ζ₀ hζ₀ φ, hval, rotA_smul, smul_smul, mul_inv_cancel₀ hw₀, one_smul]
  have hfib : ∀ ρ' (ψ : ℝ), rotA P Bs ψ (E ρ') ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₀ := by
    intro ρ' ψ
    rw [hAE]
    intro p hp
    have h := rot_fib hS P Bs hpl hsec (Φ ρ') c₀ hc₀ ζ₀ hζ₀ ψ p hp
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, h]
  have hexp : ∀ Y ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₀,
      Y = ∑ σ, inner ℂ (B.hsVec (E σ)) (B.hsVec Y) • E σ := by
    intro Y hY
    have h := (he.2 ζ₀ hζ₀).2.2 Y hY
    simpa only [heE] using h
  have horth : ∀ ρ ρ', inner ℂ (B.hsVec (E ρ)) (B.hsVec (E ρ')) = if ρ = ρ' then (1 : ℂ) else 0 := by
    intro ρ ρ'
    have h := (he.2 ζ₀ hζ₀).2.1 ρ ρ'
    simpa only [heE] using h

  set Mf : ℝ → Matrix (M.Ty P) (M.Ty P) ℂ :=
    fun φ => Matrix.of fun ρ ρ' => rotM P Bs.z Bs.z' Bs.π Bs.π' (fun σ => e σ 0) φ ρ ρ' with hMfdef
  have hMf : ∀ φ ρ ρ', Mf φ ρ ρ' = inner ℂ (B.hsVec (E ρ)) (B.hsVec (rotA P Bs φ (E ρ'))) := fun _ _ _ => rfl
  set x₀ : (Fin P.r → ℂ) × Q.Mx P.k P.r := (c₀, NF.muZ P.k P.r Bs.μsec ζ₀) with hx₀def
  have hx₀ : x₀ ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hB.2.1 hB.2.2.1 hB.2.2.2.2.2.1 (q := (c₀, ζ₀)) ⟨hc₀, ann_tz P Bs hpl hζ₀⟩
  set Bm : Matrix (M.Ty P) (M.Ty P) ℂ := Matrix.of fun ρ ρ' =>
    w₀ * (Complex.I * inner ℂ (B.hsVec (E ρ)) (B.hsVec (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
      Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
        ((Φ ρ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x₀.1) x₀.2))) with hBmdef
  have h0 : Mf 0 = 1 := by
    ext ρ ρ'
    rw [hMf, rotA_zero hS P Bs hpl, horth, Matrix.one_apply]
  have h2π : Mf (2 * Real.pi) = 1 := by
    ext ρ ρ'
    rw [hMf, rotA_two_pi hS P Bs hpl, horth, Matrix.one_apply]
  have hmul : ∀ φ ψ, Mf (φ + ψ) = Mf φ * Mf ψ := by
    intro φ ψ
    ext ρ ρ'
    rw [hMf, rotA_add hS P Bs hpl, hexp _ (hfib ρ' ψ), rotA_sum, SSTr.hsVec_sum, inner_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [VLem.hsV_smul, inner_smul_right, hMf, hMf, mul_comm]
  have hder : ∀ ρ ρ', HasDerivAt (fun φ => Mf φ ρ ρ') (Bm ρ ρ') 0 := by
    intro ρ ρ'
    have h := hasDerivAt_pair hC P Bs (Φ ρ') x₀ hx₀ (E ρ) w₀
    have hfun : (fun φ => Mf φ ρ ρ') = fun φ : ℝ => w₀ * inner ℂ (B.hsVec (E ρ))
        (B.hsVec ((Φ ρ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x₀.1 (x₀.2 * zc P.k P.r φ))) := by
      funext φ
      rw [hMf, hAE, VLem.hsV_smul, inner_smul_right]
    rw [hfun]
    exact h
  have hoff : ∀ ρ ρ', ρ ≠ ρ' → Bm ρ ρ' = 0 := by
    intro ρ ρ' hne

    set f : M.Ty P → ℂ := fun τ => if τ = ρ then 1 else 0 with hfdef
    have hkz : (d.κ f).1 (Φ ρ') = 0 := by
      apply SSTr.trR_inj P Bs hpl hk2 e he
      funext τ
      apply Subtype.ext
      funext q
      rw [hk f (Φ ρ'), actA_kap, hΦtr ρ', SSTr.trR_apply P Bs hpl hk2 e he 0]
      simp only [rawR, ZeroMemClass.coe_zero, Pi.zero_apply, hsVec_zero, inner_zero_right, mul_zero]
      by_cases hτ : τ = ρ
      · subst hτ
        simp [hne]
      · simp [f, hτ]
    have hRz : (d.κ f).1 (Rt (Φ ρ')) = 0 := by
      rw [← hRK f (Φ ρ'), hkz, map_zero]
    set q₀ : MA.Qp P.r P.TT := ⟨(c₀, ζ₀), hc₀, hζ₀⟩ with hq₀def
    have h1 := congrArg (fun F : M.Ty P → MA.SmQ P.r P.TT => (F ρ : MA.Qp P.r P.TT → ℂ) q₀) (hk f (Rt (Φ ρ')))
    rw [hRz, actA_kap, SSTr.trR_apply P Bs hpl hk2 e he 0] at h1
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, hfdef, if_pos rfl, one_mul] at h1
    rw [SSTr.trR_apply P Bs hpl hk2 e he] at h1
    simp only [rawR, ZeroMemClass.coe_zero, Pi.zero_apply, hsVec_zero, inner_zero_right, mul_zero] at h1
    have hwq : ((wR P.k P.TT ζ₀ : ℝ) : ℂ) ≠ 0 := hw₀
    have hRt0 : inner ℂ (B.hsVec (E ρ)) (B.hsVec ((Rt (Φ ρ') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c₀
        (NF.muZ P.k P.r Bs.μsec ζ₀))) = 0 := by
      have h1' := h1.symm
      rw [heE] at h1'
      exact (mul_eq_zero.1 h1').resolve_left hwq
    have hsum := hRt (Φ ρ') x₀ hx₀
    have hS0 : (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
        Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
          ((Φ ρ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x₀.1) x₀.2) =
        (Rt (Φ ρ') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x₀.1 x₀.2 - ((s : ℂ)) • (Φ ρ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x₀.1 x₀.2 := by
      rw [hsum]; abel
    have hv0 : (Φ ρ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x₀.1 x₀.2 = w₀⁻¹ • E ρ' := by
      have h := hval ρ' 0
      simpa using h
    show w₀ * (Complex.I * inner ℂ (B.hsVec (E ρ)) (B.hsVec _)) = 0
    rw [hS0, hv0, sub_eq_add_neg, VLem.hsV_add, inner_add_right, ← neg_smul, smul_smul, VLem.hsV_smul,
      inner_smul_right, horth, if_neg hne, mul_zero, add_zero]
    simp only [hx₀def] at hRt0 ⊢
    rw [hRt0]
    ring
  obtain ⟨n, hn⟩ := hO (M.Ty P) Mf Bm h0 hmul h2π hder hoff
  exact ⟨n, fun φ ρ ρ' => hn φ ρ ρ'⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace RRFin

theorem hasDerivAt_rotExp (m : ℂ) :
    HasDerivAt (fun φ : ℝ => Complex.exp (m * (φ : ℂ) * Complex.I)) (m * Complex.I) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul m).mul_const Complex.I).cexp
  simpa using h

end RRFin

open RRMat RRFin in
theorem rotation_finite_from_matrix : GTRRFinFrom := by
  intro hC hS hW Wp Wq _ _ _ _ _ _ P Bs hpl hk2 hsec e he hc n hn Rt s hRt ρ Φ
  have hB := SSTr.radBase P Bs hpl
  have hTT0 : 0 ≤ P.TT := by
    rw [← SSTr.tz_eq P Bs hpl]; exact mul_nonneg hB.2.2.2.1.le hB.2.2.2.2.1.le
  set E : M.Ty P → (Wq →L[ℂ] Wp) := fun σ => e σ 0 with hEdef
  have heE : ∀ σ ζ, e σ ζ = E σ := fun σ ζ => hc σ ζ 0
  have hid : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => w) (Ann P) := contDiff_id.contDiffOn
  have hstar : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => star w) (Ann P) :=
    by
      have h : (fun w : ℂ => star w) = ⇑Complex.conjCLE := by funext w; simp
      rw [h]; exact Complex.conjCLE.contDiff.contDiffOn
  apply Subtype.ext
  funext q
  simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, SetLike.val_smul, Pi.add_apply,
    Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [dzQ_apply P hTT0, dzbQ_apply P hTT0, fnZ_val P hid, fnZ_val P hstar]
  have hcq : q.1.1 ∈ OmX P.r := q.2.1
  have hζq : P.TT < Complex.normSq q.1.2 := q.2.2

  have hsm : ContDiffOn ℝ MA.sm (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) :=
    (trR P Bs e Φ ρ).2
  have hdiff : DifferentiableAt ℝ (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) q.1 :=
    (hsm.differentiableOn (by simp [MA.sm])).differentiableAt ((MA.Qset_open P.r P.TT).mem_nhds q.2)
  have hWa := hW P.r (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) q.1 hdiff

  have hfibq : ∀ φ : ℝ, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
      (NF.muZ P.k P.r Bs.μsec (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I))) ∈
        NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) := by
    intro φ
    have hm := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hB Φ.1 Φ.2
    have hx : ((q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' :=
      ⟨hcq, by rw [normSq_rot]; exact ann_tz P Bs hpl hζq⟩
    have h2 := hm.2.1 _ hx
    simp only [NF.radR, Set.indicator_of_mem hx] at h2
    exact h2
  have hGy : ∀ φ : ℝ, inner ℂ (B.hsVec (E ρ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
        (NF.muZ P.k P.r Bs.μsec q.1.2 * zc P.k P.r φ))) =
      Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) * inner ℂ (B.hsVec (E ρ)) (B.hsVec
        ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I))))) := by
    intro φ
    have hζe : P.TT < Complex.normSq (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) := by rw [normSq_rot]; exact hζq
    have hexp := (he.2 _ hζe).2.2 _ (hfibq φ)
    simp only [heE] at hexp
    have hM : ∀ σ, inner ℂ (B.hsVec (E ρ)) (B.hsVec (rotA P Bs φ (E σ))) =
        if ρ = σ then Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) else 0 := fun σ => hn φ ρ σ
    rw [rot_eqv hS P Bs hpl hsec Φ q.1.1 hcq q.1.2 hζq φ]
    conv_lhs => rw [hexp]
    rw [rotA_sum, SSTr.hsVec_sum, inner_sum]
    simp only [VLem.hsV_smul, inner_smul_right, hM, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring

  have hD : ((q.1.1, NF.muZ P.k P.r Bs.μsec q.1.2) : (Fin P.r → ℂ) × Q.Mx P.k P.r) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hB.2.1 hB.2.2.1 hB.2.2.2.2.2.1 (q := q.1) ⟨hcq, ann_tz P Bs hpl hζq⟩
  have hG := hasDerivAt_pair hC P Bs Φ _ hD (E ρ) 1
  simp only [one_mul] at hG
  have hE := hasDerivAt_rotExp (-(n ρ : ℂ))
  have hprod := (hE.mul hG).const_mul ((wR P.k P.TT q.1.2 : ℝ) : ℂ)
  have hpt : ∀ φ : ℝ, MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ) (q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) =
      ((wR P.k P.TT q.1.2 : ℝ) : ℂ) * (Complex.exp (-(n ρ : ℂ) * (φ : ℂ) * Complex.I) *
        inner ℂ (B.hsVec (E ρ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
          (NF.muZ P.k P.r Bs.μsec q.1.2 * zc P.k P.r φ)))) := by
    intro φ
    have hmem : ((q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) : MA.E P.r) ∈ MA.Qset P.r P.TT :=
      ⟨hcq, by rw [normSq_rot]; exact hζq⟩
    unfold MA.ext
    rw [dif_pos hmem, SSTr.trR_apply P Bs hpl hk2 e he]
    simp only [rawR]
    rw [wR_rot, heE, hGy φ, ← mul_assoc (Complex.exp (-(n ρ : ℂ) * (φ : ℂ) * Complex.I)), ← Complex.exp_add]
    have h0 : -(n ρ : ℂ) * (φ : ℂ) * Complex.I + (n ρ : ℂ) * (φ : ℂ) * Complex.I = 0 := by ring
    rw [h0, Complex.exp_zero, one_mul]
  have hF := hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall hpt)
  have heq := hWa.unique hF

  have hsum := hRt Φ _ hD
  simp only at hsum
  have hG0 := hGy 0
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul, mul_one] at hG0 heq
  rw [SSTr.trR_apply P Bs hpl hk2 e he, SSTr.trR_apply P Bs hpl hk2 e he]
  simp only [rawR]
  rw [hG0] at heq
  rw [heE, hsum, VLem.hsV_add, inner_add_right, VLem.hsV_smul, inner_smul_right]
  push_cast
  apply mul_left_cancel₀ Complex.I_ne_zero
  linear_combination -heq

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem rotation_K_invariance_holds : GTRRotK :=
  gTRRotK_of_mat_fin_centre_sec_ode_wirt rotation_matrix_form_holds rotation_finite_from_matrix rotation_centre_condition rotation_section_holds rotation_ode_holds rotation_wirtinger_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gauge_construction_holds : GCore := gCore_of_rotK rotation_K_invariance_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_SSnRep (hJ : JfSmoothDS) (h : JA.SSn.SSnRep) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_rotK hJ Gauge.GC.rotation_K_invariance_holds h

end Formalism.FourierDecayAlt.P.CutMP
end
