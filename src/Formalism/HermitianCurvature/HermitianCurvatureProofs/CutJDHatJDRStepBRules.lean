module

import Formalism.SharpRestriction.CuspSpanNormBounds.StarVecMulDM
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightDerivativeRulePsi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds

@[expose] public section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.StepB

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx3 Formalism.FourierDecayAlt.P.WeylCellAction

variable {k r : ℕ}

theorem tailW (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (b : Fin r) : ∀ n : ℕ, ∀ i : Fin (r + 1), i.val = b.val + 1 + n →
    ∃ T : Mx k r, wCell k r i c = wCell k r b.succ c * T ∧ T ∈ Glev k r b.succ ∧
      (∀ v, inWb k r v → T *ᵥ v = v) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    have : i = b.succ := Fin.ext (by simp [hi])
    subst this
    exact ⟨1, by simp, glev_one _, fun v _ => by simp⟩
  | succ n ih =>
    intro i hi
    have hl : b.val + 1 + n < r := by have := i.isLt; omega
    set l : Fin r := ⟨b.val + 1 + n, hl⟩ with hldef
    have hil : i = l.succ := Fin.ext (by simp [l, hi]; omega)
    subst hil
    obtain ⟨T, hT, hTG, hTv⟩ := ih l.castSucc (by simp [l])
    have hw := (Formalism.FourierDecayAlt.P.weyl_level_element_properties k r l (c l) (hc l)).1
    refine ⟨T * w1 k r l (c l), ?_, ?_, ?_⟩
    · rw [Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hT, Matrix.mul_assoc]
    · exact glev_mul hTG (glev_mono (by rw [Fin.le_def]; simp [l]) hw)
    · intro v hv
      rw [← Matrix.mulVec_mulVec, Formalism.FourierDecayAlt.P.CutMP.unipotent_fixes_anisotropic_vector l _ v hv, hTv v hv]

theorem bvec_wI_inWb (v : Fin (k + 1)) : inWb k r (bvec (wI k r v)) := by
  apply _root_.Formalism.MainNotions.FrameBoundFromBesselTorus.inWb_bvec_wI <;> assumption

section rules

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rightRuleB (z' : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r)) (f : Mx k r → E) (hz' : inWb k r z')
    (hD : IsOpen D) (hS : SmoothLev k r 0 D f) (hR : RightEq k r z' 0 D f) (g : Mx k r) (hg : g ∈ Glev k r 0 ∩ D)
    (a : Fin r) (ha : a.val + 1 < r) (w : Fin (k + 1)) : EH k r (eI k r a) (wI k r w) f g = 0 := by
  have hjlt : r + w.val - a.val - 1 < mdim k r a.succ := by simp [mdim]; omega
  have hpos : posL k r a.succ ⟨r + w.val - a.val - 1, hjlt⟩ = wI k r w := by
    simp [posL, wI, Fin.ext_iff]; omega
  have h := (right_action_at hz' hD hS hR hg a).1 ⟨r + w.val - a.val - 1, hjlt⟩
  rw [hpos] at h
  rw [h]
  have hx : xv k r z' a.succ ⟨r + w.val - a.val - 1, hjlt⟩ = 0 := by
    simp only [xv, fvec, hpos]
    rw [dite_eq_left (show (a.succ : Fin (r + 1)).val < r by simp; omega)]
    simp only [bvec, Pi.single_apply]
    rw [ite_eq_right]
    intro h'
    have := congrArg Fin.val h'
    simp [wI, eI] at this
    omega
  rw [hx, zero_smul]

theorem leftRuleB (z : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r)) (f : Mx k r → E) (hz : inWb k r z)
    (hD : IsOpen D) (hDN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) (hS : SmoothLev k r 0 D f)
    (hL : LeftEq k r z 0 D f) (c : Fin r → ℂ) (hc : c ∈ OmX r) (g : Mx k r) (hg : g ∈ Glev k r (Fin.last r))
    (hWD : wCell k r (Fin.last r) c * g ∈ D) (b : Fin r) (hb : b.val + 1 < r) (v : Fin (k + 1)) :
    EH k r (wI k r v) (eI k r b) f (wCell k r (Fin.last r) c * g) = 0 := by
  obtain ⟨T, hT, hTG, hTv⟩ := tailW (k := k) c hc b (r - b.val - 1) (Fin.last r) (by simp; omega)
  have hjlt : r + v.val - b.val - 1 < mdim k r b.succ := by simp [mdim]; omega
  have hpos : posL k r b.succ ⟨r + v.val - b.val - 1, hjlt⟩ = wI k r v := by
    simp [posL, wI, Fin.ext_iff]; omega
  have h := (left_action_cell hz hD hDN hS hL hc hg hWD b hT hTG).1 ⟨r + v.val - b.val - 1, hjlt⟩
  rw [hpos] at h
  rw [h]
  have hb1 : (b.succ : Fin (r + 1)).val < r := by simp; omega
  have hy : ybv k r z b.succ (T * g) ⟨r + v.val - b.val - 1, hjlt⟩ = 0 := by
    simp only [ybv, hpos, fvec, dite_eq_left hb1]
    rw [Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI, ← Matrix.mulVec_mulVec]
    have hgw : inWb k r (g *ᵥ bvec (wI k r v)) :=
      Formalism.FourierDecayAlt.P.NFRadRedLocSec.inWb_uwb (Formalism.FourierDecayAlt.P5.Rad.glev_last_uwb hg) (bvec_wI_inWb v)
    rw [hTv _ hgw]
    exact hgw _ (Or.inr (by simp [esI]; omega))
  rw [hy, mul_zero, zero_smul]

end rules

section ring

theorem zcomm {A : Type} [Ring A] (z : ℤ) (X Y : A) : ((z : ℤ) : A) * (X * Y) = X * (((z : ℤ) : A) * Y) := by
  rw [← mul_assoc, (Int.cast_commute z X).eq, mul_assoc]

theorem succ_above_one_val {t : ℕ} (i : Fin (t + 1)) :
    ((Fin.succ (0 : Fin (t + 1))).succAbove i).val = if i.val = 0 then 0 else i.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]

theorem zmul {A : Type} [Ring A] [Algebra ℂ A] (z : ℤ) (x : A) : ((z : ℤ) : A) * x = ((z : ℂ)) • x := by
  rw [Algebra.smul_def, map_intCast]

theorem stepB_ring {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    {M : Type} [AddCommGroup M] [Module ℂ M] (Λ : A →ₗ[ℂ] M) (p0 p1 : Fin n) (h01 : p0 ≠ p1) (κ : ℂ)
    {t : ℕ} (a b : Fin (t + 2) → Fin n) (ha0 : a 0 = p0) (ha1 : a 1 = p1) (hb0 : b 0 = p0) (hb1 : b 1 = p1)
    (haR : ∀ m : Fin (t + 2), 2 ≤ m.val → a m ≠ p0)
    (hbR : ∀ m : Fin (t + 2), 2 ≤ m.val → b m ≠ p0)
    (hL0 : ∀ m : Fin (t + 2), 2 ≤ m.val → ∀ X, Λ (E (a m) p0 * X) = 0)
    (hL1 : ∀ X, Λ (E p1 p0 * X) = κ • Λ X)
    (hR0 : ∀ m : Fin (t + 2), 2 ≤ m.val → ∀ X, Λ (X * E p0 (b m)) = 0)
    (hR1 : ∀ X, Λ (X * E p0 p1) = Λ X) (u : ℂ) :
    Λ (qminor E a b u) = Λ (Tm E u p0 p0 * qminor E (a ∘ Fin.succ) (b ∘ Fin.succ) (u - 1)) -
      κ • Λ (qminor E (fun j : Fin t => a ⟨j.val + 2, by omega⟩) (fun j : Fin t => b ⟨j.val + 2, by omega⟩)
        (u - 1 - 1)) := by

  set a' : Fin (t + 1) → Fin n := a ∘ (Fin.succ (0 : Fin (t + 1))).succAbove with ha'
  set b' : Fin (t + 1) → Fin n := b ∘ Fin.succ with hb'
  set τ : Equiv.Perm (Fin (t + 1)) := (Fin.last t).cycleRange with hτ
  have hsq : ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign τ : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hsg : ((Equiv.Perm.sign τ : ℤ) : A) = (((-1 : ℤ) ^ t : ℤ) : A) := by
    rw [hτ, Fin.sign_cycleRange]
    simp
  have hlast : (a' ∘ τ) (Fin.last t) = p0 := by
    show a ((Fin.succ (0 : Fin (t + 1))).succAbove (τ (Fin.last t))) = p0
    rw [hτ, Fin.cycleRange_self, ← ha0]
    congr 1
  have hcs : (a' ∘ τ) ∘ Fin.castSucc = fun j : Fin t => a ⟨j.val + 2, by omega⟩ := by
    funext j
    simp only [Function.comp_apply, hτ, ha']
    congr 1
    apply Fin.ext
    rw [succ_above_one_val, Fin.coe_cycleRange_of_lt (by rw [Fin.lt_def]; simp)]
    try simp
  have hbs : b' ∘ Fin.succ = fun j : Fin t => b ⟨j.val + 2, by omega⟩ := by
    funext j
    simp only [Function.comp_apply, hb']
    rfl
  have hQ' : Λ (qminor E a' b' (u - 1)) =
      Λ (qminor E (fun j : Fin t => a ⟨j.val + 2, by omega⟩) (fun j : Fin t => b ⟨j.val + 2, by omega⟩)
        (u - 1 - 1)) := by
    have hsk := Formalism.REAL.quantumMinorRowSkew_holds A n (t + 1) E a' b' τ (u - 1)
    have e1 : qminor E a' b' (u - 1) = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E (a' ∘ τ) b' (u - 1) := by
      rw [hsk, ← mul_assoc, hsq, one_mul]

    rw [e1, Formalism.FourierDecayAlt.P.expansion_last_line A n t E hE (a' ∘ τ) b' (u - 1), Finset.mul_sum, map_sum,
    Fin.sum_univ_succ]
    have hrest : ∀ m : Fin t, Λ (((Equiv.Perm.sign τ : ℤ) : A) * ((((-1 : ℤ) ^ (t + ((m.succ : Fin (t + 1)) : ℕ)) : ℤ) : A) *
        (qminor E ((a' ∘ τ) ∘ Fin.castSucc) (b' ∘ m.succ.succAbove) (u - 1 - 1) *
          Tm E (u - 1) ((a' ∘ τ) (Fin.last t)) (b' m.succ)))) = 0 := by
      intro m
      have hbm : b' m.succ = b ⟨m.val + 2, by omega⟩ := rfl
      rw [hlast, hbm]
      unfold Tm
      rw [ite_eq_right (Ne.symm (hbR ⟨m.val + 2, by omega⟩ (by simp))), zero_add, ← mul_assoc, ← mul_assoc]
      exact hR0 ⟨m.val + 2, by omega⟩ (by simp) _
    rw [Finset.sum_eq_zero (fun m _ => hrest m), add_zero, hlast]
    have hb0' : b' 0 = p1 := by simp only [hb', Function.comp_apply]; exact hb1
    rw [hb0']
    unfold Tm
    rw [ite_eq_right h01, zero_add, ← mul_assoc, ← mul_assoc, hR1, Fin.succAbove_zero, hcs, hbs, hsg, ← Int.cast_mul]
    have h11 : ((-1 : ℤ) ^ t * (-1) ^ (t + ((0 : Fin (t + 1)) : ℕ))) = 1 := by
      rw [Fin.val_zero, add_zero, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [h11, Int.cast_one, one_mul]


  rw [Formalism.FourierDecayAlt.P.expansion_first_column A n (t + 1) E a b u, map_sum, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hrest : ∀ m : Fin t, Λ ((((-1 : ℤ) ^ ((m.succ.succ : Fin (t + 2)) : ℕ) : ℤ) : A) *
      (Tm E u (a m.succ.succ) (b 0) * qminor E (a ∘ m.succ.succ.succAbove) (b ∘ Fin.succ) (u - 1))) = 0 := by
    intro m
    rw [hb0]
    unfold Tm
    rw [ite_eq_right (haR _ (by simp)), zero_add, zcomm]
    exact hL0 _ (by simp) _
  rw [Finset.sum_eq_zero (fun m _ => hrest m), add_zero]
  have h1 : Λ ((((-1 : ℤ) ^ (((0 : Fin (t + 1)).succ : Fin (t + 2)) : ℕ) : ℤ) : A) *
      (Tm E u (a (0 : Fin (t + 1)).succ) (b 0) * qminor E (a ∘ (0 : Fin (t + 1)).succ.succAbove) (b ∘ Fin.succ) (u - 1))) =
      -(κ • Λ (qminor E a' b' (u - 1))) := by
    have ha1' : a (0 : Fin (t + 1)).succ = p1 := ha1
    rw [ha1', hb0]
    unfold Tm
    rw [ite_eq_right (Ne.symm h01), zero_add, zcomm, hL1, zmul, map_smul]
    simp <;> rfl
  rw [h1, hQ']
  simp only [Fin.val_zero, pow_zero, Int.cast_one, one_mul, Fin.succAbove_zero, hb0, ha0]
  rw [hb']
  exact (sub_eq_add_neg _ _).symm
