import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.FormalDegreeBessel.FinalG
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Inh

section

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB



theorem amp_lamS_lo (R : Ranks) (P : HCParam R) (i : Fin R.r) (h : i.val < R.k - 1) :
    lamS R P i = (P.v ⟨i.val, h⟩ : ℝ) := by
  unfold lamS
  rw [dif_pos h]

theorem amp_lamS_hi (R : Ranks) (P : HCParam R) (i : Fin R.r) (h : ¬ i.val < R.k - 1)
    (h' : i.val - (R.k - 1) < R.m) : lamS R P i = -(P.b ⟨i.val - (R.k - 1), h'⟩ : ℝ) := by
  unfold lamS
  rw [dif_neg h, dif_pos h']

theorem amp_b_lt (R : Ranks) (P : HCParam R) (j : ℕ) (h : j + 1 < R.m) :
    P.b ⟨j, by omega⟩ < P.b ⟨j + 1, h⟩ := by
  have h1 : ((R.t : ℚ) + 3) / 2 ≤ P.e ⟨j, by omega⟩ - P.b ⟨j, by omega⟩ := P.gap_be ⟨j, by omega⟩
  have h2 : ((R.t : ℚ) + 3) / 2 ≤ P.b ⟨j + 1, h⟩ - P.e ⟨j, by omega⟩ := P.gap_eb ⟨j, by omega⟩ h
  have ht : (0 : ℚ) ≤ (R.t : ℚ) := Nat.cast_nonneg _
  linarith

private theorem strictAnti_of_succ_lt' (n : ℕ) (f : Fin n → ℝ)
    (hf : ∀ (i : ℕ) (h : i + 1 < n), f ⟨i + 1, h⟩ < f ⟨i, by omega⟩) : StrictAnti f := by
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have hab' : a < b := hab
  clear hab
  induction b with
  | zero => omega
  | succ b ih =>
    rcases (show a < b ∨ a = b by omega) with h | h
    · exact lt_trans (hf b hb) (ih (by omega) h)
    · have e : (⟨a, ha⟩ : Fin n) = ⟨b, by omega⟩ := Fin.ext h
      rw [e]
      exact hf b hb

private theorem strictAnti_lamS (R : Ranks) (P : HCParam R) : StrictAnti (lamS R P) := by
  have hr : R.r = R.k + R.m - 1 := rfl
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  apply strictAnti_of_succ_lt'
  intro i hi
  by_cases h1 : i + 1 < R.k - 1
  · rw [amp_lamS_lo R P ⟨i + 1, hi⟩ h1, amp_lamS_lo R P ⟨i, by omega⟩ (show i < R.k - 1 by omega)]
    have key : P.v ⟨i + 1, h1⟩ < P.v ⟨i, by omega⟩ :=
      lt_trans (P.u_gt_v ⟨i + 1, h1⟩) (P.v_gt_u ⟨i, by omega⟩)
    exact_mod_cast key
  · by_cases h2 : i < R.k - 1
    · rw [amp_lamS_hi R P ⟨i + 1, hi⟩ h1 (show i + 1 - (R.k - 1) < R.m by omega),
        amp_lamS_lo R P ⟨i, by omega⟩ h2]
      have e1 : P.b ⟨i + 1 - (R.k - 1), by omega⟩ = P.b ⟨0, by omega⟩ :=
        congrArg P.b (Fin.ext (show i + 1 - (R.k - 1) = 0 by omega))
      have e2 : P.u ⟨i + 1, by omega⟩ = P.u ⟨R.k - 1, by omega⟩ :=
        congrArg P.u (Fin.ext (show i + 1 = R.k - 1 by omega))
      have k1 := P.u_last_gt (by omega) (by omega)
      have k2' : P.u ⟨i + 1, by omega⟩ < P.v ⟨i, h2⟩ := P.v_gt_u ⟨i, h2⟩
      rw [e2] at k2'
      have key : -P.b ⟨i + 1 - (R.k - 1), by omega⟩ < P.v ⟨i, h2⟩ := by
        rw [e1]
        exact lt_trans k1 k2'
      exact_mod_cast key
    · rw [amp_lamS_hi R P ⟨i + 1, hi⟩ h1 (show i + 1 - (R.k - 1) < R.m by omega),
        amp_lamS_hi R P ⟨i, by omega⟩ h2 (show i - (R.k - 1) < R.m by omega)]
      have e1 : P.b ⟨i + 1 - (R.k - 1), by omega⟩ = P.b ⟨i - (R.k - 1) + 1, by omega⟩ :=
        congrArg P.b (Fin.ext (show i + 1 - (R.k - 1) = i - (R.k - 1) + 1 by omega))
      have key := amp_b_lt R P (i - (R.k - 1)) (by omega)
      rw [← e1] at key
      exact_mod_cast neg_lt_neg key

theorem amp_lamSH_strictAnti (R : Ranks) (P : HCParam R) : StrictAnti (lamSH R P) := by
  intro a b hab
  exact strictAnti_lamS R P (show Fin.cast (dimS_eq R) a < Fin.cast (dimS_eq R) b from hab)

theorem amp_isHCParam_lamSH (R : Ranks) (P : HCParam R) : IsHCParam (lamSH R P) := by
  refine ⟨amp_lamSH_strictAnti R P, fun a => ?_⟩
  have hval : ∃ z : ℤ, lamSH R P a = z := by
    simp only [lamSH, lamS]
    split_ifs with h1 h2
    · obtain ⟨z, hz⟩ := P.v_int ⟨_, h1⟩
      exact ⟨z, by have h3 := congrArg (fun x : ℚ => (x : ℝ)) hz; simpa using h3⟩
    · obtain ⟨z, hz⟩ := P.b_int ⟨_, h2⟩
      exact ⟨-z, by have h3 := congrArg (fun x : ℚ => -(x : ℝ)) hz; simpa using h3⟩
    · exact ⟨0, by simp⟩
  obtain ⟨z, hz⟩ := hval
  obtain ⟨q, hq⟩ := R.k_even
  refine ⟨z - (R.rS : ℤ) - (q : ℤ), ?_⟩
  have hk : (R.k : ℝ) = (q : ℝ) + q := by exact_mod_cast hq
  push_cast
  linarith [hz, hk]

theorem amp_isHCParam_lamD (D : D7) (τ : D.what₂.Tau) : IsHCParam (lamD D τ) := amp_isHCParam_lamSH D.R (D.hc τ)


def amp_lam (k r N M : ℕ) : Fin (2 * r + k + 1) → ℝ := fun s =>
  (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 +
    (if s.val < k - 1 then (N : ℝ) * ((k : ℝ) - (s.val : ℝ)) else -(M : ℝ) - (N : ℝ) * (s.val : ℝ))

def amp_u (k r N : ℕ) (δ : ℝ) : Fin k → ℝ := fun i =>
  (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (N : ℝ) * ((k : ℝ) - (i.val : ℝ)) + (if i.val = 1 then δ else 1 / 2)
















def amp_HType (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) : Prop :=
  ∃ (Wp : Type) (_ : NormedAddCommGroup Wp) (_ : InnerProductSpace ℂ Wp) (_ : FiniteDimensional ℂ Wp)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)), IsHCTypeW k r z u π

def amp_HDS (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), IsDSHpk k r ε lam σ

def amp_HHaarW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∃ μ : Measure (Mt k r), IsHaarOn (UWset k r z) μ ∧ μ Set.univ = 1

def amp_HHaarG (k r : ℕ) : Prop := ∃ μ : Measure (Mt k r), IsHaarOn (UH (Hpk k r)) μ

def amp_HQuot (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ (μG μW : Measure (Mt k r)) (κ : ℝ≥0∞), IsHaarOn (UH (Hpk k r)) μG → IsHaarOn (UWset k r z) μW → μW Set.univ = 1 →
    0 < κ → κ ≠ ⊤ → ∃ ν : Measure (Mt k r), IsQuotMeas μG (muS μW (haarLie (Nset k r) κ)) ν







theorem amp_v_pos (D : D7) : 0 < D.host.v := by
  unfold Host.v Host.rdE
  apply div_pos ?_ two_pos
  apply Real.rpow_pos_of_pos
  rw [abs_pos]
  exact_mod_cast NumberField.discr_ne_zero _



def amp_HAmp (D : D7) (large₂ : SizeData₂ D) (C1 : ℝ) : Prop :=
  ∃ (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (A : LocS W) (γ : MatKR D.R.k D.R.rS)
    (p : Point ℂ (D.R.rS + 1)) (θ' : ℝ) (νR : Measure (Mt D.R.k D.R.rS)),
    HypTT D w w' ∧ normWin D large₂ C1 θ ∧ GoodW D τ w w' θ W ∧ GoodS D (lamD D τ) A ∧ A.deg = D.dsig τ ∧
      RelPt D W.z W.z' γ p ∧ normWin D large₂ C1 θ' ∧ RMeas D W γ θ' νR





def amp_HRepD (D : D7) : Prop :=
  (∀ lam, IsHCParam lam → amp_HDS D.R.k D.R.rS (epsSH D.R) lam) ∧
  (∀ z u, inWb D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z → IsHCParam u → amp_HType D.R.k D.R.rS z u) ∧
  (∀ z, inWb D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z → amp_HHaarW D.R.k D.R.rS z)


def amp_HNumB (D : D7) (Ch Cg : ℝ) (T T' : ℕ) (b : ℝ) (u u' : D.what₂.Tau → Fin D.R.k → ℝ) : Prop :=
  (∀ v, IsHCParam (u v) ∧ IsHCParam (u' v) ∧
    StdHyp Ch Cg D.R.k D.R.rS (epsSH D.R) (lamSH D.R (D.hc v)) (u v) (u' v) T T' (kaRe D) b) ∧
  1 ≤ (T : ℝ) * kaRe D ^ (2 * D.R.rS) ∧ 1 ≤ (T' : ℝ) * kaRe D ^ (2 * D.R.rS)














end

end Formalism.MainNotions.S.Inh
