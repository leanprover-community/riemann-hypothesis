import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaPrimeAllPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterLargeAllPointsBoundStatement

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift
variable {D : D7}

theorem U_sub_c_eq_w (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < (Vc D j).rank) :
    ((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ =
      (((lamL j τ).w ⟨a, ha⟩ : ℤ) : ℝ) + ((Vc D j).rank : ℝ) / 2 - a := by
  have h1 := lamT_of_lt j τ a ha
  have h2 := congrArg (Int.cast : ℤ → ℝ) h1
  push_cast at h2
  show ((Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) a : ℤ) : ℝ) - cT j τ = _
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN cT
  push_cast
  rw [h2]
  ring

theorem valsAt_of_isLamPrime : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau),
    Formalism.IndefR.Bridge.IsLamPrime (GlobalTheory.ExpTie.Lift.lamL j τ) ((j : ℕ) + 1) τ → GlobalTheory.ExpTie.Lift.ValsAt L j τ := by
  intro D L j τ h
  obtain ⟨hj, W, hk, hm, ht, hJ, he, hv, hb, hw⟩ := h
  obtain ⟨k, m, t, J, e, v, b⟩ := W
  simp only at hk hm ht hJ he hv hb
  subst hk hm ht hJ
  have hN := rank_eq j
  have hK := D.R.m_add_three_le_k
  have ht0 := D.R.t_odd.pos
  have hjm := j.2
  have hrk : ((Vc D j).rank : ℚ) = (D.R.k : ℚ) + D.R.m + D.R.t - 1 := by
    rw [hN, Nat.cast_add, Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
  have hmj : ((D.R.m - ((j : ℕ) + 1) : ℕ) : ℚ) = (D.R.m : ℚ) - j - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hk1 : ((D.R.k - 1 : ℕ) : ℚ) = (D.R.k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hr1 : D.R.k + D.R.m - 1 + D.R.t = (Vc D j).rank := by omega
  have hp : D.R.k + ((j : ℕ) + 1) - 1 = D.R.k + j := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    have hal : a < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ a hal]
    have hq := hw ⟨a, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    rw [hr1, hp, hmj] at hq
    have hv' : ((v (a + 1 + 1) : ℤ) : ℚ) = (D.hc τ).v ⟨a, ha⟩ := hv ⟨a, ha⟩
    have hQ : (((lamL j τ).w ⟨a, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - a = (D.hc τ).v ⟨a, ha⟩ := by
      rw [hq, ← hv']; push_cast; ring
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this
    exact this
  · intro i hi
    have hal : D.R.k - 1 + i < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ _ hal]
    have hq := hw ⟨_, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    rw [hr1, hp, hmj, show D.R.k - 1 + (i : ℕ) + 1 - (D.R.k - 1) = (i : ℕ) + 1 by omega,
      show D.R.k - 1 + (i : ℕ) + 1 = D.R.k + i by omega] at hq
    have hb' := hb i
    have hQ : (((lamL j τ).w ⟨_, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - ((D.R.k - 1 + i : ℕ) : ℚ) = -(D.hc τ).b i := by
      rw [Nat.cast_add, hk1]
      push_cast at hq
      linarith
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this ⊢
    exact this
  · intro s hs
    have hal : D.R.k + j + s < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ _ hal]
    have hq := hw ⟨_, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    have c3 : D.R.k + ↑j + s + 1 ≤ D.R.k + ((j : ℕ) + 1) - 1 + D.R.t := by omega
    simp only [c3, if_true] at hq
    rw [hp, hmj] at hq
    have hQ : (((lamL j τ).w ⟨_, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - ((D.R.k + j + s : ℕ) : ℚ) =
        -(D.hc τ).e ⟨(j : ℕ) + 1 - 1, hj.2⟩ + ((D.R.t : ℚ) - 1) / 2 - s := by
      push_cast at hq he ⊢
      linarith
    have hwj : wj D ((j : ℕ) + 1) τ = (((D.hc τ).e ⟨(j : ℕ) + 1 - 1, hj.2⟩ : ℚ) : ℝ) := by
      unfold wj; rw [dif_pos hj.2]
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    rw [hwj]
    push_cast at this ⊢
    linarith
  · intro i hi
    have hal : D.R.k - 1 + i + D.R.t < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ _ hal]
    have hq := hw ⟨_, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    have c3 : ¬ (D.R.k - 1 + (i : ℕ) + D.R.t + 1 ≤ D.R.k + ((j : ℕ) + 1) - 1 + D.R.t) := by omega
    simp only [c3, if_false] at hq
    rw [show D.R.m - ((j : ℕ) + 1) + 1 - (D.R.m - ((j : ℕ) + 1) + 1 - (D.R.k - 1 + (i : ℕ) + D.R.t + 1 - (D.R.k + ((j : ℕ) + 1) - 1) - D.R.t))
        = (i : ℕ) - j by omega] at hq
    rw [show (j : ℕ) + 1 + ((i : ℕ) - j) = (i : ℕ) + 1 by omega, hp, hmj] at hq
    have hij : (((i : ℕ) - (j : ℕ) : ℕ) : ℚ) = (i : ℚ) - j := by
      rw [Nat.cast_sub (by omega)]
    have hb' := hb i
    have hQ : (((lamL j τ).w ⟨_, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - ((D.R.k - 1 + i + D.R.t : ℕ) : ℚ) = -(D.hc τ).b i := by
      rw [Nat.cast_add, Nat.cast_add, hk1]
      rw [hij] at hq
      push_cast at hq
      linarith
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this ⊢
    exact this

end GlobalTheory.ExpTie.Lift

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftWeightRho_entryValues : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), Formalism.IndefR.Bridge.IsLamPrime (GlobalTheory.ExpTie.Lift.lamL j τ) ((j : ℕ) + 1) τ → GlobalTheory.ExpTie.Lift.ValsAt L j τ := by
  atlas_forward_decl GlobalTheory.ExpTie.Lift.valsAt_of_isLamPrime
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift

theorem block_centre : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → (∀ a, Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ ≤ a → a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t → (GlobalTheory.ExpTie.Lift.wts L j).lam τ a = (GlobalTheory.ExpTie.Lift.wts L j).lam τ (Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ)) ∧ (((GlobalTheory.ExpTie.Lift.wts L j).bot (GlobalTheory.ExpTie.parOf L j) τ : ℝ) + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2 - (GlobalTheory.ExpTie.Lift.wts L j).c τ = -(GlobalTheory.ExpTie.Lift.wts L j).e τ) := by
  intro D L j τ hv
  have hk := D.R.m_add_three_le_k
  have ht0 := D.R.t_odd.pos
  have hkc : Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ = D.R.k + (j : ℕ) := by
    simp only [Formalism.CohomologicalDescent.ShortWeightBounds.kc, parOf, wts]; omega
  have htt : (parOf L j).t = D.R.t := rfl
  have he : (wts L j).e τ = wj D ((j : ℕ) + 1) τ := rfl
  constructor
  · intro a ha1 ha2
    rw [hkc] at ha1 ⊢
    rw [hkc, htt] at ha2
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ha1
    have h1 := hv.2.2.1 s (by omega)
    have h0 := hv.2.2.1 0 ht0
    simp only [add_zero, Nat.cast_zero, sub_zero] at h0
    have hU : ((wts L j).U (parOf L j) τ (D.R.k + j + s) : ℝ) = (((wts L j).U (parOf L j) τ (D.R.k + j) - s : ℤ) : ℝ) := by
      push_cast; linarith
    have hU' := Int.cast_injective (α := ℝ) hU
    change Formalism.CohomologicalDescent.UnitNormBounds.UN _ _ _ = Formalism.CohomologicalDescent.UnitNormBounds.UN _ _ _ - _ at hU'
    unfold Formalism.CohomologicalDescent.UnitNormBounds.UN at hU'
    push_cast at hU'
    omega
  · have hrow : Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ + (parOf L j).t - 1 = D.R.k + (j : ℕ) + (D.R.t - 1) := by
      rw [hkc, htt]; omega
    have h := hv.2.2.1 (D.R.t - 1) (by omega)
    have hts : ((D.R.t - 1 : ℕ) : ℝ) = (D.R.t : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hts] at h
    rw [Formalism.CohomologicalDescent.ShortWeightBounds.Wts.bot, hrow, htt, he]
    linarith

end GlobalTheory.ExpTie.Lift

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftWeightRho_block_constant_centred : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → (∀ a, Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ ≤ a → a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t → (GlobalTheory.ExpTie.Lift.wts L j).lam τ a = (GlobalTheory.ExpTie.Lift.wts L j).lam τ (Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ)) ∧ (((GlobalTheory.ExpTie.Lift.wts L j).bot (GlobalTheory.ExpTie.parOf L j) τ : ℝ) + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2 - (GlobalTheory.ExpTie.Lift.wts L j).c τ = -(GlobalTheory.ExpTie.Lift.wts L j).e τ) := by
  atlas_forward_decl GlobalTheory.ExpTie.Lift.block_centre
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem GlobalTheory.ExpTie.Lift.window_cloud : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ((GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).xm τ : ℝ) ∧ (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ ∧ ((GlobalTheory.ExpTie.Lift.wts L j).xp τ : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.parOf L j).S) ∧ ∀ a, a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) → (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ := by
  intro D L j τ hv
  have hS : (GlobalTheory.ExpTie.parOf L j).S = L.Sc := rfl
  have hkc : Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) = D.R.k - 1 := rfl
  have hxm : (GlobalTheory.ExpTie.Lift.wts L j).xm τ = ⌈(GlobalTheory.ExpTie.Lift.wts L j).c τ⌉ := rfl
  have hxp : (GlobalTheory.ExpTie.Lift.wts L j).xp τ = ⌊(GlobalTheory.ExpTie.Lift.wts L j).c τ + L.Sc⌋ := rfl

  have hrow : ∀ a, a < D.R.k - 1 →
      (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧
        (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ := by
    intro a ha
    have h1 := hv.1 a ha
    have h2 := L.cloud_v τ ⟨a, ha⟩
    have hlo : (GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) := by
      have : (0 : ℝ) ≤ (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ) := by exact_mod_cast h2.1
      linarith
    have hhi : ((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + L.Sc := by
      have : (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ) ≤ L.Sc := by exact_mod_cast h2.2
      linarith
    rw [hxm, hxp]
    exact ⟨Int.ceil_le.2 hlo, Int.le_floor.2 hhi⟩
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have h0 := hrow 0 (by omega)
  refine ⟨⟨?_, le_trans h0.1 h0.2, ?_⟩, ?_⟩
  · rw [hxm]; exact Int.le_ceil _
  · rw [hxp, hS]; exact Int.floor_le _
  · intro a ha
    rw [hkc] at ha
    exact hrow a ha
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftWeightRho_window_contains_cloud : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ((GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).xm τ : ℝ) ∧ (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ ∧ ((GlobalTheory.ExpTie.Lift.wts L j).xp τ : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.parOf L j).S) ∧ ∀ a, a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) → (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ := by
  atlas_forward_decl GlobalTheory.ExpTie.Lift.window_cloud
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

theorem low_dist : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ∀ a, a < (GlobalTheory.ExpTie.parOf L j).Nr → ((Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) ≤ a ∧ a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ) ∨ Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t ≤ a) → 2 * (GlobalTheory.ExpTie.parOf L j).b / (GlobalTheory.ExpTie.parOf L j).lstar + ((GlobalTheory.ExpTie.parOf L j).t : ℝ) / 2 + 3 ≤ |((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) - (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.Lift.wts L j).e τ| ∧ |((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) - (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.Lift.wts L j).e τ| ≤ (GlobalTheory.ExpTie.parOf L j).η := by
  intro D L P5 j τ hv a ha hcase
  have hn := rank_eq j
  have hk := D.R.m_add_three_le_k
  have hjm := j.2
  change a < (Vc D j).rank at ha
  change (D.R.k - 1 ≤ a ∧ a < D.R.k - 1 + ((j : ℕ) + 1)) ∨ D.R.k - 1 + ((j : ℕ) + 1) + D.R.t ≤ a at hcase
  obtain ⟨i, hval⟩ : ∃ i : Fin D.R.m,
      ((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ = -(((D.hc τ).b i : ℚ) : ℝ) := by
    rcases hcase with ⟨h1, h2⟩ | h1
    · refine ⟨⟨a - (D.R.k - 1), by omega⟩, ?_⟩
      have h := hv.2.1 ⟨a - (D.R.k - 1), by omega⟩ (by simp only [Fin.le_def]; omega)
      have ha' : D.R.k - 1 + (a - (D.R.k - 1)) = a := by omega
      simp only [ha'] at h
      exact h
    · refine ⟨⟨a - (D.R.k - 1) - D.R.t, by omega⟩, ?_⟩
      have h := hv.2.2.2 ⟨a - (D.R.k - 1) - D.R.t, by omega⟩ (by simp only [Fin.lt_def]; omega)
      have ha' : D.R.k - 1 + (a - (D.R.k - 1) - D.R.t) + D.R.t = a := by omega
      simp only [ha'] at h
      exact h
  have he : (wts L j).e τ = (((D.hc τ).e j : ℚ) : ℝ) := by
    show wj D ((j : ℕ) + 1) τ = _
    unfold wj
    rw [dif_pos (by omega)]
    congr 3
  have habs : |((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ + (wts L j).e τ| =
      |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| := by
    rw [hval, he, ← abs_neg]
    push_cast
    ring_nf
  rw [habs]
  refine ⟨?_, L.be_close τ i j⟩
  have hN : ((D.R.N D.R.m : ℕ) : ℝ) = (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by
    unfold Ranks.N
    push_cast
    ring
  have hls : (parOf L j).lstar = LevelStarExponents.lStar L := by
    unfold Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.lstar LevelStarExponents.lStar
    rw [hN]
    rfl
  have hb : (parOf L j).b = L.sc.b := rfl
  rw [hls, hb]
  exact P5.lows_far τ i j

end GlobalTheory.ExpTie.Lift

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftWeightRho_lows_distance_bounds : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ∀ a, a < (GlobalTheory.ExpTie.parOf L j).Nr → ((Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) ≤ a ∧ a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ) ∨ Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t ≤ a) → 2 * (GlobalTheory.ExpTie.parOf L j).b / (GlobalTheory.ExpTie.parOf L j).lstar + ((GlobalTheory.ExpTie.parOf L j).t : ℝ) / 2 + 3 ≤ |((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) - (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.Lift.wts L j).e τ| ∧ |((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) - (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.Lift.wts L j).e τ| ≤ (GlobalTheory.ExpTie.parOf L j).η := by
  atlas_forward_decl GlobalTheory.ExpTie.Lift.low_dist
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift

variable {D : D7}

theorem thick_of_mem (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (hv : ValsAt L j τ)
    (hτ : τ ∈ (wts L j).T2) :
    (parOf L j).Thick ((wts L j).e τ) ∧ ((wts L j).xp τ : ℝ) ≤ (parOf L j).h := by
  have hmem : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces := by
    simpa [wts] using hτ
  have hm2 := D.R.two_le_m
  have hj := j.2
  have h1 := L.win_thick ((j : ℕ) + 1) (by omega) (by omega) τ hmem
  have h2 := L.win_thick D.R.m (by omega) le_rfl τ hmem
  have hc := c_le L j τ hv
  have hb : (parOf L j).b = L.sc.b := rfl
  refine ⟨?_, ?_⟩
  · show (parOf L j).b ≤ wj D ((j : ℕ) + 1) τ ∧ wj D ((j : ℕ) + 1) τ ≤ (parOf L j).b + L.etaSz + 1
    rw [hb]; exact h1
  · have hfl : ((wts L j).xp τ : ℝ) ≤ cT j τ + L.Sc := by
      show ((⌊cT j τ + L.Sc⌋ : ℤ) : ℝ) ≤ cT j τ + L.Sc
      exact Int.floor_le _
    have hc' : cT j τ ≤ wj D D.R.m τ + ((D.R.t : ℝ) - 1) / 2 := hc
    have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    show ((wts L j).xp τ : ℝ) ≤ (parOf L j).b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1
    rw [hb]
    linarith [h2.2]

end GlobalTheory.ExpTie.Lift

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftWeightRho_thickPlace_centre_window : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → τ ∈ (GlobalTheory.ExpTie.Lift.wts L j).T2 → (GlobalTheory.ExpTie.parOf L j).Thick ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).xp τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).h := by
  atlas_forward_decl GlobalTheory.ExpTie.Lift.thick_of_mem
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

variable {D : Formalism.BasicNotions.D7}

theorem other_of_not_thick (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau)
    (hv : GlobalTheory.ExpTie.Lift.ValsAt L j τ) (hT : τ ∉ (GlobalTheory.ExpTie.Lift.wts L j).T2) :
    ((GlobalTheory.ExpTie.parOf L j).Top ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).b' * (1 + 1 / (GlobalTheory.ExpTie.parOf L j).x + 1 / (GlobalTheory.ExpTie.parOf L j).x ^ 2) + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) ∨ ((GlobalTheory.ExpTie.parOf L j).Thin ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).w'' + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) := by
  classical
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m

  have hw : ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ L.Sc + (GlobalTheory.ExpTie.Lift.wts L j).c τ := by
    have hU := U_last L j τ
    have h0 := hv.1 0 (by omega)
    have hcv := (L.cloud_v τ ⟨0, by omega⟩).2
    have hwd : (GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ = (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ 0 := by
      show (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ 0 - (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ ((Vc D j).rank - 1) = _
      rw [hU, sub_zero]
    rw [hwd]
    linarith
  have hc := c_le L j τ hv
  have hnt : (D.eTau τ : D.R.GG) ∉ D.host.thickPlaces := by
    intro h
    apply hT
    simp only [wts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  have he : (GlobalTheory.ExpTie.Lift.wts L j).e τ = wj D ((j : ℕ) + 1) τ := rfl
  by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · left
    obtain ⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by
      unfold Host.topPlaces at htop
      simpa using htop
    have x1 := L.sc.one_lt_alt
    have x0 : 0 < L.sc.x := by linarith
    have hb0 : 0 < L.sc.b' := by
      have hX : 0 < L.sc.X' := by unfold Scale.X'; positivity
      have hb : 0 < L.sc.b := by unfold Scale.b; positivity
      unfold Scale.b' Scale.a
      positivity
    have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
    have hLa : 0 < L.LaG := by
      have h1 := P5.S_le
      have h2 := L.Sc_pos
      by_contra hn
      push_neg at hn
      have : L.LaG * L.sc.b' / D.R.k ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn hb0.le) hk0.le
      linarith
    have hbT : ((L.bT ⟨t, ht1⟩ : ℝ)) ≤ L.sc.b' * (1 + 1 / L.sc.x ^ 2) := by
      have h1 := P5.bT_le ⟨t, ht1⟩
      have h2 := P5.rho_le
      have h4 : 0 ≤ P5.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
        have := P5.Crho_pos; have := Real.log_nonneg x1.le; positivity
      have hx2 : L.sc.x ^ (-2 : ℝ) = 1 / L.sc.x ^ 2 := by
        rw [Real.rpow_neg x0.le, one_div]; norm_cast
      unfold LevelStarExponents.rhoP at h2
      rw [hx2] at h2
      have hq : 0 ≤ 1 / L.sc.x ^ 2 := by positivity
      have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / L.sc.x ^ 2 := by
        have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
        linarith
      have : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
        (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
      have h6 := mul_le_mul_of_nonneg_right h5 hb0.le
      nlinarith
    have a := L.bT_ge ⟨t, ht1⟩
    have wj1 := L.win_top ((j : ℕ) + 1) (by omega) (by omega) τ ⟨t, ht1⟩ ht2.symm
    have wjm := L.win_top D.R.m (by omega) le_rfl τ ⟨t, ht1⟩ ht2.symm
    refine ⟨⟨(L.bT ⟨t, ht1⟩ : ℝ), a, hbT, ?_, ?_⟩, ?_⟩
    · rw [he]; exact wj1.1
    · rw [he]; exact wj1.2
    · show _ ≤ L.Sc + L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) + L.etaSz + ((D.R.t : ℝ) - 1) / 2
      have : L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) = L.sc.b' * (1 + 1 / L.sc.x ^ 2) + L.sc.b' / L.sc.x := by ring
      linarith [wjm.2]
  · right
    have hthin : D.host.IsThin (D.eTau τ : D.R.GG) := ⟨(D.eTau τ).2, htop, hnt⟩
    have wj1 := L.win_thin ((j : ℕ) + 1) (by omega) (by omega) τ hthin
    have wjm := L.win_thin D.R.m (by omega) le_rfl τ hthin
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [he]; exact wj1.1
    · rw [he]; exact wj1.2
    · show _ ≤ L.Sc + L.sc.w'' D.R.n + L.etaSz + ((D.R.t : ℝ) - 1) / 2
      linarith [wjm.2]

end GlobalTheory.ExpTie.Lift
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftWeightRho_nonThickPlace_centre_width : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → τ ∉ (GlobalTheory.ExpTie.Lift.wts L j).T2 → ((GlobalTheory.ExpTie.parOf L j).Top ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).b' * (1 + 1 / (GlobalTheory.ExpTie.parOf L j).x + 1 / (GlobalTheory.ExpTie.parOf L j).x ^ 2) + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) ∨ ((GlobalTheory.ExpTie.parOf L j).Thin ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).w'' + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) := by
  atlas_forward_decl GlobalTheory.ExpTie.Lift.other_of_not_thick
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

theorem wts_U_le_h0_of_large : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), (GlobalTheory.ExpTie.parOf L j).Large → GlobalTheory.ExpTie.Lift.ValsAt L j τ → ∀ a, a < (GlobalTheory.ExpTie.parOf L j).Nr → (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (Formalism.CohomologicalDescent.ShortWeightBounds.h0 (GlobalTheory.ExpTie.parOf L j) : ℤ) := by
  intro D L P5 j τ hL hv a ha
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have ht1 : (1 : ℝ) ≤ D.R.t := L.t_win.1
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hS := L.Sc_pos
  have hη := L.etaSz_pos
  have x1 := L.sc.one_lt_alt
  have x0 : 0 < L.sc.x := by linarith
  have hb0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    exact div_pos (mul_pos x0 (Real.exp_pos _)) (Real.exp_pos _)
  have hn : (1 : ℝ) ≤ D.R.n := by unfold Ranks.n; exact_mod_cast (Nat.succ_le_of_lt (Formalism.HC.Frame.ord_pos _) : 1 ≤ _)
  have hU0 := U_nonneg L j τ 0 (by have := rank_eq j; omega)
  have hUa := liftWeightCombinatorialData_U_le_U_zero L j τ a ha
  have hv0 := hv.1 0 (by omega)
  have hcl := L.cloud_v τ ⟨0, by omega⟩
  have hc := c_le L j τ hv

  have ePb : (parOf L j).b = L.sc.b := rfl
  have eh : (parOf L j).h = L.sc.b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1 := rfl
  have hbb' := hL.bb'
  have htop := hL.top_le
  simp only [parOf] at hbb' htop
  change 12 * (D.R.k : ℝ) * (D.R.t : ℝ) * L.sc.b' < L.sc.b at hbb'

  have hm1 : 1 ≤ D.R.m := by omega
  have key : wj D D.R.m τ ≤ L.sc.b + L.etaSz + 1 ∨
      wj D D.R.m τ ≤ L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) + L.etaSz := by
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      obtain ⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by
        unfold Host.topPlaces at h1
        simpa using h1
      have hw := (L.win_top D.R.m hm1 le_rfl τ ⟨t, ht1⟩ ht2.symm).2
      have hbt := P5.bT_le ⟨t, ht1⟩
      have hr := P5.rho_le
      unfold LevelStarExponents.rhoP at hr
      have hLa : 0 < L.LaG := by
        have h := P5.S_le
        by_contra hc'
        push_neg at hc'
        have : L.LaG * L.sc.b' / D.R.k ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc' hb0.le) (by positivity)
        linarith
      have hNs : 0 ≤ LevelStarExponents.Nstar L := by
        unfold LevelStarExponents.Nstar Scale.delta1; positivity
      have hx2 : L.sc.x ^ (-2 : ℝ) = 1 / L.sc.x ^ 2 := by
        rw [Real.rpow_neg x0.le, one_div]; norm_cast
      have h4 : 0 ≤ P5.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
        have := P5.Crho_pos; have := Real.log_nonneg x1.le; positivity
      have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / L.sc.x ^ 2 := by
        have h6 : 0 ≤ LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k := by positivity
        have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
        rw [hx2] at hr
        linarith
      have h7 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
          (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
      have h8 : (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' ≤ 1 / L.sc.x ^ 2 * L.sc.b' :=
        mul_le_mul_of_nonneg_right h5 hb0.le
      right
      have : L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) = L.sc.b' + L.sc.b' / L.sc.x + 1 / L.sc.x ^ 2 * L.sc.b' := by ring
      rw [this]
      linarith
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · exact Or.inl (L.win_thick D.R.m hm1 le_rfl τ h2).2
      · have hw := (L.win_thin D.R.m hm1 le_rfl τ ⟨(D.eTau τ).2, h1, h2⟩).2
        right
        have hw1 : L.sc.w'' D.R.n ≤ L.sc.b' := by
          unfold Scale.w''
          rw [div_le_iff₀ (by positivity)]
          have hxn : 1 ≤ L.sc.x * (D.R.n : ℝ) := by nlinarith
          have := mul_le_mul_of_nonneg_left hxn hb0.le
          linarith
        have hpos : 0 ≤ L.sc.b' * (1 / L.sc.x + 1 / L.sc.x ^ 2) := by positivity
        nlinarith
  have hU0h : ((wts L j).U (parOf L j) τ 0 : ℝ) ≤ (parOf L j).h := by
    rw [eh]
    rcases key with h | h
    · nlinarith
    · have h2b : 2 * L.sc.b' < L.sc.b := by
        have : 2 * L.sc.b' ≤ 12 * (D.R.k : ℝ) * (D.R.t : ℝ) * L.sc.b' := by
          have : (1 : ℝ) ≤ (D.R.k : ℝ) * (D.R.t : ℝ) := by nlinarith
          nlinarith
        linarith
      linarith
  have hfl : ((wts L j).U (parOf L j) τ 0).toNat ≤ Formalism.CohomologicalDescent.ShortWeightBounds.h0 (parOf L j) := by
    unfold Formalism.CohomologicalDescent.ShortWeightBounds.h0
    apply Nat.le_floor
    have : (((wts L j).U (parOf L j) τ 0).toNat : ℝ) = ((wts L j).U (parOf L j) τ 0 : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hU0
    rw [this]; exact hU0h
  omega

end GlobalTheory.ExpTie.Lift
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftWeightRho_entries_le_floor_height : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), (GlobalTheory.ExpTie.parOf L j).Large → GlobalTheory.ExpTie.Lift.ValsAt L j τ → ∀ a, a < (GlobalTheory.ExpTie.parOf L j).Nr → (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (Formalism.CohomologicalDescent.ShortWeightBounds.h0 (GlobalTheory.ExpTie.parOf L j) : ℤ) := by
  atlas_forward_decl GlobalTheory.ExpTie.Lift.wts_U_le_h0_of_large
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

namespace GlobalTheory.ExpTie.Lift

open Formalism.IndefR.Bridge

theorem wts_ok : GlobalTheory.BigOn.AtPts fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, ∃ W : Formalism.CohomologicalDescent.ShortWeightBounds.Wts (Fm.D x i).what₂.Tau, W.Ok (GlobalTheory.ExpTie.parOf (Fm.L x i) j) ∧
    (∀ τ, ∃ c : ℤ, ∀ a : Fin (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank,
      (W.lam τ a : ℤ) = (Formalism.IndefR.Bridge.lamLdef (D := Fm.D x i) (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank ((j : ℕ) + 1) τ).w a + c) ∧
    (∀ τ a, a < (GlobalTheory.ExpTie.parOf (Fm.L x i) j).Nr → 0 ≤ W.U (GlobalTheory.ExpTie.parOf (Fm.L x i) j) τ a ∧ W.U (GlobalTheory.ExpTie.parOf (Fm.L x i) j) τ a ≤ (Formalism.CohomologicalDescent.ShortWeightBounds.h0 (GlobalTheory.ExpTie.parOf (Fm.L x i) j) : ℤ)) ∧
    W.T2.card ≤ (Fm.D x i).host.T2.card ∧ W.Sp = Formalism.MainNotions.JumpSetsAlt.excSet (Fm.D x i) := by
  refine GlobalTheory.ExpTie.atPts_imp (GlobalTheory.ExpTie.atPts_and GlobalTheory.T.lambda_prime_all_points GlobalTheory.T.parameter_large_all_points_bound) ?_
  intro eps Fm x hx i p hp j
  obtain ⟨hF, hLg⟩ := hp
  have hv : ∀ τ, ValsAt (Fm.L x i) j τ := fun τ => GlobalTheory.T.liftWeightRho_entryValues (Fm.L x i) j τ (hF j τ)
  refine ⟨wts (Fm.L x i) j, ⟨anti _ j, what₂ _ j, fun τ => (GlobalTheory.T.liftWeightRho_block_constant_centred (Fm.L x i) j τ (hv τ)).1, fun τ => (GlobalTheory.T.liftWeightRho_block_constant_centred (Fm.L x i) j τ (hv τ)).2,
    fun τ => (GlobalTheory.T.liftWeightRho_window_contains_cloud (Fm.L x i) j τ (hv τ)).1, fun τ => (GlobalTheory.T.liftWeightRho_window_contains_cloud (Fm.L x i) j τ (hv τ)).2,
    fun τ => GlobalTheory.T.liftWeightRho_lows_distance_bounds (Fm.L x i) (Fm.params x hx i) j τ (hv τ), fun τ h => GlobalTheory.T.liftWeightRho_thickPlace_centre_window (Fm.L x i) j τ (hv τ) h,
    fun τ h => GlobalTheory.T.liftWeightRho_nonThickPlace_centre_width (Fm.L x i) (Fm.params x hx i) j τ (hv τ) h⟩, fun τ => ⟨-(lamL j τ).detShift, fun a => ?_⟩,
    fun τ a ha => ⟨U_nonneg _ j τ a ha, GlobalTheory.T.liftWeightRho_entries_le_floor_height (Fm.L x i) (Fm.params x hx i) j τ (hLg j) (hv τ) a ha⟩, T2_card _ j, rfl⟩
  have := lamT_of_lt j τ a a.2
  show (lamT j τ a : ℤ) = _
  rw [this]
  ring

end GlobalTheory.ExpTie.Lift

end
end
