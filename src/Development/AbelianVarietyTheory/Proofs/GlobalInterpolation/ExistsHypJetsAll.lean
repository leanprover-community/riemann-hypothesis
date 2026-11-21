import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JetsAllOfColIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColInJetsIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardDvdCardGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHFrameDtPackPre

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

namespace GlobalTheory.KerT

namespace JetsInhab

open GlobalTheory.Mem GlobalTheory.Mem.Col2

theorem exists_pre_sized : ∃ P : Pre, StagesInhab.HasLetters P ∧ Nonempty (PreX P) ∧
    (letI := P.host.cmStar; DiagSpaces P.sp) ∧ ∀ u, (P.duStar u : ℝ) = duStarOf P.host (P.hcW u) := by
  obtain ⟨P, ⟨X⟩, -, -, ⟨hD, -⟩, Del, letter, h1, -, h3, h4⟩ := exists_pre_two_words
  obtain ⟨du, hdu, e⟩ := DuInt.duStarOf_nat _ P.host (P.hcW P.u₀) P.g_cond X.g_big
  have hT : (0 : ℝ) < P.T P.u₀ := Nat.cast_pos.2 (P.T_prime _).pos
  have hd : (0 : ℝ) < du := Nat.cast_pos.2 hdu
  have hG : 0 < P.GamP := zero_lt_one.trans P.one_lt_gammaP
  have hf : (0 : ℝ) < P.R.f := by
    have : 0 < P.R.f := by unfold Ranks.f Ranks.n; positivity
    exact_mod_cast this
  have hk : (0 : ℝ) < P.R.k := by
    have := P.R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < P.R.k)
  have hfk : (0 : ℝ) < (P.R.f : ℝ) * P.R.k := mul_pos hf hk
  have key : ((P.T P.u₀ : ℝ) ^ ((P.R.f : ℝ) * P.R.k) * P.GamP ^ (2 : ℝ) * du / du) ^ ((1 : ℝ) / (P.R.f * P.R.k)) *
      P.GamP ^ (-(2 : ℝ) / (P.R.f * P.R.k)) = P.T P.u₀ := by
    rw [mul_div_cancel_right₀ _ hd.ne', Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hT.le,
      ← Real.rpow_mul hG.le, mul_assoc, ← Real.rpow_add hG, mul_one_div_cancel hfk.ne', Real.rpow_one,
      show (2 : ℝ) * (1 / (P.R.f * P.R.k)) + -2 / (P.R.f * P.R.k) = 0 by ring, Real.rpow_zero, mul_one]
  let Q : Pre := { P with
    Word := Unit
    wordFin := inferInstance
    u₀ := ()
    hcW := fun _ => P.hcW P.u₀
    hcW_base := P.hcW_base
    hcW_v := fun _ => P.hcW_v _
    hcW_b := fun _ => P.hcW_b _
    hcW_e := fun _ => P.hcW_e _
    hcW_first := fun _ => P.hcW_first _
    hcW_last := fun _ => P.hcW_last _
    T := fun _ => P.T P.u₀
    T_level := fun _ => P.T_level _
    T_norm := fun _ => P.T_norm _
    sp_T := P.sp_T
    cOf := fun _ => P.cOf P.u₀
    cOf_ne := fun _ => P.cOf_ne _
    cOf_eq := fun _ => P.cOf_eq _
    T_ne_pde := fun _ => P.T_ne_pde _
    duStar := fun _ => du
    duStar_pos := fun _ => hdu
    Dstar := (P.T P.u₀ : ℝ) ^ ((P.R.f : ℝ) * P.R.k) * P.GamP ^ (2 : ℝ) * du
    Dstar_pos := by positivity
    T_win := fun _ => by
      rw [key]
      exact ⟨le_rfl, le_mul_of_one_le_left hT.le (le_add_of_nonneg_right (by positivity))⟩ }
  refine ⟨Q, ⟨Del, fun _ => letter P.u₀, h1, fun _ _ _ => rfl, fun _ => h3 _, fun _ => h4 _⟩, ⟨{ X with
    piT := fun _ => X.piT P.u₀
    piT_K := fun _ => X.piT_K _
    piT_norm := fun _ => X.piT_norm _
    piT_cong := fun _ => X.piT_cong _
    hcW_inj := fun _ _ _ => rfl
    T_gt := fun _ => X.T_gt _
    spread_le := fun _ => X.spread_le _ }⟩, hD, fun _ => e⟩


end JetsInhab

end GlobalTheory.KerT
