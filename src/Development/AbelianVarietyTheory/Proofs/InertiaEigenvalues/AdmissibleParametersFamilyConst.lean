import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogLevelGroupLeAndLevelLarge
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem log_card_levelGroup_le_scale_pow_mul_length : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x →
    ∀ i : Fm.Ix x, Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ C * x ^ C * (Fm.L x i).sc.L := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := GlobalTheory.log_levelGroup_le_and_level_large eps Fm
  refine ⟨15, max x0 1, fun x hx hx1 i => ?_⟩
  have h := (hx0 x (le_trans (le_max_left _ _) hx) hx1 i).1
  have h1x : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hL : 1 ≤ (Fm.L x i).sc.L := Real.one_le_rpow (Fm.L x i).sc.one_lt_alt.le (Fm.L x i).sc.eps_pos.le
  have hp : (0 : ℝ) ≤ x ^ (15 : ℝ) := Real.rpow_nonneg (by linarith) _
  unfold Formalism.BasicNotions.lam0 at h
  calc Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ x ^ (15 : ℝ) := h
    _ ≤ 15 * x ^ (15 : ℝ) := by linarith
    _ = 15 * x ^ (15 : ℝ) * 1 := by ring
    _ ≤ 15 * x ^ (15 : ℝ) * (Fm.L x i).sc.L := by gcongr

end GlobalTheory.NLink
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_log_card_restRows_le_pow_mul_length : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ C * x ^ C * (Fm.L x i).sc.L := by
  atlas_forward_decl GlobalTheory.NLink.log_card_levelGroup_le_scale_pow_mul_length
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.ClassNumHost

theorem totCx (D : D7) : IsTotallyComplex D.host.E := by
  first
  | exact inferInstance
  | (haveI : IsCMField D.host.E := D.host.isCMField_hostE; exact inferInstance)

theorem log_hE_le_rd (D : D7) :
    Real.log (Formalism.MainNotions.N.hE D.host : ℝ) ≤ (D.R.f : ℝ) * Real.log D.host.rdE +
      2 * D.R.f * Real.log (1 + D.R.f * Real.log D.host.rdE) := by
  haveI := totCx D
  have hf := Formalism.MainNotions.TwistedPlaces.finrank_E_host D
  have h := GlobalTheory.log_classNumber_le_log_abs_discr_div D.host.E D.R.f hf
  have hd : 0 < |(discr D.host.E : ℝ)| := by
    have := NumberField.discr_ne_zero D.host.E
    positivity
  have hrd : Real.log D.host.rdE = Real.log |(discr D.host.E : ℝ)| / (2 * D.R.f) := by
    unfold Formalism.BasicNotions.Host.rdE
    rw [Real.log_rpow hd, hf]
    push_cast
    ring
  rw [hrd]
  unfold Formalism.MainNotions.N.hE
  exact h

theorem log_hE_le_lin (D : D7) (h1 : 1 ≤ D.host.rdE) :
    Real.log (Formalism.MainNotions.N.hE D.host : ℝ) ≤ (1 + 2 * D.R.f) * ((D.R.f : ℝ) * Real.log D.host.rdE) := by
  have h := log_hE_le_rd D
  have hY : 0 ≤ (D.R.f : ℝ) * Real.log D.host.rdE := mul_nonneg (by positivity) (Real.log_nonneg h1)
  have hl : Real.log (1 + D.R.f * Real.log D.host.rdE) ≤ D.R.f * Real.log D.host.rdE := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + D.R.f * Real.log D.host.rdE by linarith)
    linarith
  have hf0 : (0:ℝ) ≤ 2 * D.R.f := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hl hf0]

end GlobalTheory.ClassNumHost

namespace GlobalTheory.ClassNumHost

theorem log_rd_le (D : D7) (h1 : 1 ≤ D.host.rdE)
    (h2 : D.host.rdE ≤ (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d)) :
    Real.log D.host.rdE ≤ 2 * D.R.n + (Real.log D.host.q + Real.log D.host.d) / 2 := by
  have hn : (0:ℝ) < D.R.n := by
    have : 0 < D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hqd : (0:ℝ) < (D.host.q : ℝ) * D.host.d := by
    rcases (show (0:ℝ) ≤ (D.host.q : ℝ) * D.host.d by positivity).lt_or_eq with h | h
    · exact h
    · rw [← h, Real.sqrt_zero] at h2; linarith
  have hq : (0:ℝ) < D.host.q := by
    rcases (show (0:ℝ) ≤ D.host.q by positivity).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hqd; exact absurd hqd (lt_irrefl 0)
  have hd : (0:ℝ) < D.host.d := by
    rcases (show (0:ℝ) ≤ D.host.d by positivity).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hqd; exact absurd hqd (lt_irrefl 0)
  have hQ : (D.host.QS : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by exact_mod_cast D.host.QS_le
  have h3 : D.host.rdE ≤ (D.R.n : ℝ) ^ 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) :=
    h2.trans (mul_le_mul_of_nonneg_right (by have : (0:ℝ) ≤ D.host.QS := Nat.cast_nonneg _; linarith) (Real.sqrt_nonneg _))
  have hl := Real.log_le_log (by linarith) h3
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_sqrt hqd.le, Real.log_mul hq.ne' hd.ne'] at hl
  push_cast at hl
  have hn' : Real.log (D.R.n : ℝ) ≤ D.R.n := by
    have := Real.log_le_sub_one_of_pos hn; linarith
  linarith

end GlobalTheory.ClassNumHost

namespace GlobalTheory

theorem log_hE_le_pow : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x →
    ∀ i : Fm.Ix x, Real.log (Formalism.MainNotions.N.hE (Fm.D x i).host : ℝ) ≤ C * x ^ C := by
  intro eps Fm
  set A : ℝ := |2 + 8 * eps + eps / 100| + |eps / 5 + eps / 100| + 1 with hA
  have hA1 : 1 ≤ A := by have := abs_nonneg (2 + 8 * eps + eps / 100); have := abs_nonneg (eps / 5 + eps / 100); linarith
  refine ⟨30 + 3 * A, 1, fun x hx1 hx i => ?_⟩
  have hs := Fm.sizes x hx i
  obtain ⟨hN, -, -, -, -, -, hQD, -⟩ := hs
  have hLx := Fm.L_x x i hx
  have hLe := Fm.L_eps x i
  unfold SizeN szTh at hN
  unfold SizeQD szTh at hQD
  rw [hLx, hLe] at hN hQD
  obtain ⟨-, -, hq, -, hd, -, hr1, hr2⟩ := hQD
  set D := Fm.D x i with hD
  have hx0 : (0:ℝ) < x := by linarith
  have mono : ∀ a : ℝ, a ≤ A → x ^ a ≤ x ^ A := fun a ha => Real.rpow_le_rpow_of_exponent_le hx1 ha
  have hP1 : 1 ≤ x ^ A := Real.one_le_rpow hx1 (by linarith)
  set P := x ^ A with hP
  have hn : (D.R.n : ℝ) ≤ P := hN.2.trans (mono _ (by
    have := le_abs_self (2 + 8 * eps + eps / 100); have := abs_nonneg (eps / 5 + eps / 100); linarith))
  have hqP : Real.log D.host.q ≤ P := hq.trans (mono _ (by
    have := le_abs_self (eps / 5 + eps / 100); have := abs_nonneg (2 + 8 * eps + eps / 100); linarith))
  have hdP : Real.log D.host.d ≤ P := hd.trans (mono _ (by
    have := le_abs_self (eps / 5 + eps / 100); have := abs_nonneg (2 + 8 * eps + eps / 100); linarith))
  have hrd := GlobalTheory.ClassNumHost.log_rd_le D hr1 hr2
  have hrdP : Real.log D.host.rdE ≤ 3 * P := by linarith
  have hrd0 : 0 ≤ Real.log D.host.rdE := Real.log_nonneg hr1
  have hf : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hfP : (D.R.f : ℝ) ≤ 2 * P := by rw [hf]; linarith
  have hf0 : (0:ℝ) ≤ D.R.f := by positivity
  have hmain := GlobalTheory.ClassNumHost.log_hE_le_lin D hr1
  have hY : (D.R.f : ℝ) * Real.log D.host.rdE ≤ 6 * P ^ 2 := by
    calc (D.R.f : ℝ) * Real.log D.host.rdE ≤ (2 * P) * (3 * P) :=
          mul_le_mul hfP hrdP hrd0 (by linarith)
      _ = 6 * P ^ 2 := by ring
  have hY0 : 0 ≤ (D.R.f : ℝ) * Real.log D.host.rdE := mul_nonneg hf0 hrd0
  have h1f : 1 + 2 * (D.R.f : ℝ) ≤ 5 * P := by linarith
  have hbound : Real.log (Formalism.MainNotions.N.hE D.host : ℝ) ≤ 30 * P ^ 3 := by
    calc _ ≤ (1 + 2 * D.R.f) * ((D.R.f : ℝ) * Real.log D.host.rdE) := hmain
      _ ≤ (5 * P) * (6 * P ^ 2) := mul_le_mul h1f hY hY0 (by linarith)
      _ = 30 * P ^ 3 := by ring
  have hP3 : P ^ 3 = x ^ (3 * A) := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  have hxC : x ^ (3 * A) ≤ x ^ (30 + 3 * A) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hx3 : 1 ≤ x ^ (3 * A) := Real.one_le_rpow hx1 (by linarith)
  rw [hP3] at hbound
  calc _ ≤ 30 * x ^ (3 * A) := hbound
    _ ≤ (30 + 3 * A) * x ^ (30 + 3 * A) := by nlinarith

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_hostClassNumber_le_scale_pow_family : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, Real.log (Formalism.MainNotions.N.hE (Fm.D x i).host : ℝ) ≤ C * x ^ C := by
  atlas_forward_decl GlobalTheory.log_hE_le_pow
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem mul_rpow_self_le {x c C : ℝ} (hx : 1 ≤ x) (hc : c ≤ C) (hC : 0 ≤ C) :
    c * x ^ c ≤ C * x ^ C := by
  have h0 : 0 ≤ x ^ c := Real.rpow_nonneg (by linarith) _
  calc c * x ^ c ≤ C * x ^ c := mul_le_mul_of_nonneg_right hc h0
    _ ≤ C * x ^ C := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hc) hC

theorem admissible_parameters_design_family : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, 1 ≤ C ∧ ∀ x ≥ x0, ∀ (hx : Fm.x1 < x)
    (i : Fm.Ix x), TwistedPlaces.ParametersPolynomiallyBounded (Fm.L x i) C (Fm.params x hx i) := by
  intro eps Fm
  obtain ⟨C1, y1, h1⟩ := GlobalTheory.T.log_hostClassNumber_le_scale_pow_family Fm
  obtain ⟨C2, y2, h2⟩ := GlobalTheory.T.exists_log_card_restRows_le_pow_mul_length Fm
  set C : ℝ := max 1 (max (Fm.PK.getD 7 0) (max (Fm.PK.getD 19 0) (max (9 / 2 + 10 * eps + eps / 100)
    (max (2 + 8 * eps + eps / 100) (max (Fm.Ct + eps / 100) (max C1 C2)))))) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := by linarith
  have hCLw : Fm.PK.getD 7 0 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCYL : Fm.PK.getD 19 0 ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hrest : max (9 / 2 + 10 * eps + eps / 100)
      (max (2 + 8 * eps + eps / 100) (max (Fm.Ct + eps / 100) (max C1 C2))) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hK : 9 / 2 + 10 * eps + eps / 100 ≤ C := le_trans (le_max_left _ _) hrest
  have hN : 2 + 8 * eps + eps / 100 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hrest
  have hT : Fm.Ct + eps / 100 ≤ C :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hrest
  have hc12 : max C1 C2 ≤ C :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hrest
  have hCC1 : C1 ≤ C := le_trans (le_max_left _ _) hc12
  have hCC2 : C2 ≤ C := le_trans (le_max_right _ _) hc12
  refine ⟨C, max y1 y2, hC1, fun x hxy hx i => ?_⟩
  have hx1 : 1 ≤ x := le_of_lt (lt_trans Fm.one_lt_family_threshold hx)
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have heps : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hPK := Fm.params_K x hx i
  obtain ⟨sN, -, sK, -, sT, -, -, -, -, -, -, sDe2, -⟩ := Fm.sizes x hx i
  unfold SizeN szTh at sN
  unfold SizeK szTh at sK
  unfold SizeT szTh at sT
  unfold SizeDe2 at sDe2
  rw [hsx, heps] at sN sK
  rw [hsx, heps, Fm.Ct_eq x i] at sT
  have hmono : ∀ a : ℝ, a ≤ C → x ^ a ≤ x ^ C := fun a ha => Real.rpow_le_rpow_of_exponent_le hx1 ha
  have hLg : 0 ≤ (Fm.L x i).sc.L := by
    unfold Scale.L
    exact Real.rpow_nonneg (le_trans zero_le_one (le_of_lt (Fm.L x i).sc.one_lt_alt)) _
  unfold TwistedPlaces.ParametersPolynomiallyBounded
  refine ⟨?_, ?_, ?_, ?_, ?_, sDe2, ?_, ?_⟩
  · have e : (Fm.params x hx i).CLw = Fm.PK.getD 7 0 := by rw [← hPK]; rfl
    rw [e]; exact hCLw
  · have e : (Fm.params x hx i).CYL = Fm.PK.getD 19 0 := by rw [← hPK]; rfl
    rw [e]; exact hCYL
  · rw [hsx]; exact le_trans sK.2 (hmono _ hK)
  · rw [hsx]; exact le_trans sN.2 (hmono _ hN)
  · rw [hsx]; exact le_trans sT.2 (hmono _ hT)
  · rw [hsx]
    exact le_trans (h1 x (le_trans (le_max_left _ _) hxy) hx i) (mul_rpow_self_le hx1 hCC1 hC0)
  · rw [hsx]
    refine le_trans (h2 x (le_trans (le_max_right _ _) hxy) hx i) ?_
    exact mul_le_mul_of_nonneg_right (mul_rpow_self_le hx1 hCC2 hC0) hLg

end GlobalTheory.NLink
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_parameters_family_const : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, 1 ≤ C ∧ ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ParametersPolynomiallyBounded (Fm.L x i) C (Fm.params x hx i) := by
  atlas_forward_decl GlobalTheory.NLink.admissible_parameters_design_family
end
