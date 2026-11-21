import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEvaluationSubstCompatibleThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueSubMemPdIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.QLog

theorem dIn_top_formalLog_map : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q]
    (σ : Type) (g : MvPowerSeries σ B), constantCoeff g = 1 →
      DIn (⊤ : Ideal B) (formalLog (map (algebraMap B Q) g)) := by
  intro B Q _ _ _ _ σ g hg α i
  classical
  obtain ⟨u, hu⟩ : IsUnit g := isUnit_iff_constantCoeff.mpr (by rw [hg]; exact isUnit_one)
  set φ := algebraMap B Q
  have hG : constantCoeff (map φ g) = 1 := by simp [hg]
  have hd : pderiv Q i (formalLog (map φ g)) = map φ ((↑u⁻¹ : MvPowerSeries σ B) * pderiv B i g) := by
    have h1 := mul_pderiv_formalLog hG i
    rw [pderiv_map] at h1
    have h2 : map φ (↑u⁻¹ : MvPowerSeries σ B) * map φ g = 1 := by
      rw [← map_mul, ← hu, Units.inv_mul, map_one]
    calc pderiv Q i (formalLog (map φ g))
        = (map φ (↑u⁻¹ : MvPowerSeries σ B) * map φ g) * pderiv Q i (formalLog (map φ g)) := by
          rw [h2, one_mul]
      _ = map φ ((↑u⁻¹ : MvPowerSeries σ B) * pderiv B i g) := by
          rw [mul_assoc, h1, map_mul]
  by_cases hα : α i = 0
  · exact ⟨0, Submodule.mem_top, by simp [hα]⟩
  · refine ⟨coeff (α - Finsupp.single i 1) ((↑u⁻¹ : MvPowerSeries σ B) * pderiv B i g),
      Submodule.mem_top, ?_⟩
    rw [natCast_mul_coeff_of_pderiv_eq hd hα, coeff_map]

end GlobalTheory.QLog
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diffCoeffsInIdeal_top_formalLog_constOne : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (σ : Type) (g : MvPowerSeries σ B), constantCoeff g = 1 → DIn (⊤ : Ideal B) (formalLog (map (algebraMap B Q) g)) := by
  atlas_forward_decl GlobalTheory.QLog.dIn_top_formalLog_map
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

namespace GlobalTheory.QLog

theorem dIn_top_powerSeriesLog (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] :
    DIn (⊤ : Ideal B) (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  intro α i
  have hα : α = Finsupp.single () (α ()) := Finsupp.unique_single α
  have hc : coeff α (PowerSeries.log Q : MvPowerSeries Unit Q)
      = PowerSeries.coeff (α ()) (PowerSeries.log Q) := by
    conv_lhs => rw [hα]
    rfl
  rw [hc, PowerSeries.coeff_log]
  obtain rfl : i = () := rfl
  split_ifs with h
  · exact ⟨0, trivial, by simp⟩
  · refine ⟨(-1) ^ (α () + 1), trivial, ?_⟩
    have h' : ((α () : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h
    rw [← map_natCast (algebraMap ℚ Q), ← map_mul, mul_div_cancel₀ _ h']
    simp

theorem hasVal_log_of_hasVal_formalLog : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (g : MvPowerSeries σ B) (q : Q), constantCoeff g = 1 → HasVal p z (formalLog (map (algebraMap B Q) g)) q → HasVal p (fun _ : Unit => E g - 1) (PowerSeries.log Q : MvPowerSeries Unit Q) q := by
  intro p _ B O Q _ _ _ _ _ θ hF σ _ _ z hz E hE g q hg hq
  haveI := hF.complete
  have hu : ∀ j : Unit, constantCoeff ((fun _ : Unit => g - 1) j) = 0 := fun _ => by simp [hg]
  have hEu : E (g - 1) = E g - 1 := by rw [map_sub, map_one]
  have hnil : ∃ N : ℕ, (p : B) ∣ (E g - 1) ^ N :=
    hEu ▸ ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p B B σ z hz).2 E hE).2.1 (g - 1) (hu ())
  have hD := dIn_top_powerSeriesLog B Q
  obtain ⟨q', hq', -⟩ := GlobalTheory.T.existsUnique_hasPAdicPowerSeriesValue_of_diffCoeffs p B O Q θ hF Unit (fun _ => E g - 1) (fun _ => hnil) _ hD
  have h4 := GlobalTheory.T.pAdicEvaluation_subst_compatible_thickening p B O Q θ hF σ z hz E hE Unit (fun _ => g - 1) _ q' hu hD
    (by simpa only [hEu] using hq')
  have h5 : subst (up Q (fun _ : Unit => g - 1)) (PowerSeries.log Q : MvPowerSeries Unit Q)
      = formalLog (map (algebraMap B Q) g) := by
    unfold formalLog PowerSeries.subst up
    simp only [map_sub, map_one]
  rw [h5] at h4
  rwa [HasVal.unique hF hq h4]

end GlobalTheory.QLog
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasVal_log_eval_of_hasVal_formalLog : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (g : MvPowerSeries σ B) (q : Q), constantCoeff g = 1 → HasVal p z (formalLog (map (algebraMap B Q) g)) q → HasVal p (fun _ : Unit => E g - 1) (PowerSeries.log Q : MvPowerSeries Unit Q) q := by
  atlas_forward_decl GlobalTheory.QLog.hasVal_log_of_hasVal_formalLog
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogPeriod

theorem theta_eval_char : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (ε : PreTilt O p) (hε : IsPrimitiveSystem ε) (F : BFrame ε) (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (g : MvPowerSeries (Fin d) F.B), (∀ n, c.ev n (map F.θ g) = charElem χ n) → ∀ (t : G.Tate) (n : ℕ) (z : Fin d → F.B), (∀ i, F.θ (z i) = t.pt n (c.x n i)) → (∀ i, ∃ N : ℕ, (p : F.B) ∣ z i ^ N) → ∀ E : MvPowerSeries (Fin d) F.B →ₐ[F.B] F.B, IsEval p z E → F.θ (E g) = zeta ε n ^ GlobalTheory.PDiv.digit n (epsPairing hε G t χ) := by
  intro p _ O _ _ _ _ ε hε F G d c χ g hg t n z hz hnil E hE
  haveI := F.frame.complete
  let Ev : MvPowerSeries (Fin d) O →ₐ[O] O := (t.pt n).comp (c.ev n)
  have hEv : IsEval p (fun i => F.θ (z i)) Ev := by
    refine ⟨fun i => ?_, fun m => ?_⟩
    · change t.pt n (c.ev n (X i)) = F.θ (z i)
      rw [(c.isEval n).1 i, hz]
    · obtain ⟨N, hN⟩ := (c.isEval n).2 m
      refine ⟨N, fun g hg => ?_⟩
      obtain ⟨w, hw⟩ := hN g hg
      refine ⟨t.pt n w, ?_⟩
      change t.pt n (c.ev n g) = _
      rw [hw, map_mul, map_pow, map_natCast]
  have h1 : F.θ (E g) = Ev (map F.θ g) :=
    ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p F.B F.B (Fin d) z hnil).2 E hE).2.2 O O F.θ F.θ Ev (fun _ => rfl) hEv g
  have h2 : Ev (map F.θ g) = t.pt n (charElem χ n) := by
    change t.pt n (c.ev n (map F.θ g)) = _
    rw [hg n]
  rw [h1, h2, ← GlobalTheory.PDivGroup.muRoot_pairing, ← GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsPairing_smul hε,
    GlobalTheory.PDivGroup.muRoot_smul]
  unfold epsTate
  rw [GlobalTheory.PDivGroup.muRoot_muTate]

end GlobalTheory.QLogPeriod
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_eval_eq_zeta_pow_digit : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (ε : PreTilt O p) (hε : IsPrimitiveSystem ε) (F : BFrame ε) (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (g : MvPowerSeries (Fin d) F.B), (∀ n, c.ev n (map F.θ g) = charElem χ n) → ∀ (t : G.Tate) (n : ℕ) (z : Fin d → F.B), (∀ i, F.θ (z i) = t.pt n (c.x n i)) → (∀ i, ∃ N : ℕ, (p : F.B) ∣ z i ^ N) → ∀ E : MvPowerSeries (Fin d) F.B →ₐ[F.B] F.B, IsEval p z E → F.θ (E g) = zeta ε n ^ GlobalTheory.PDiv.digit n (epsPairing hε G t χ) := by
  atlas_forward_decl GlobalTheory.QLogPeriod.theta_eval_char
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.SqZero

theorem mvPolynomialEval_truncFinsupp_eq_sum_coeff_mul_prod {R σ : Type} [CommRing R] [Fintype σ] [DecidableEq σ] (w : σ → R)
    (n : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    MvPolynomial.eval w (trunc' R n f) = ∑ β ∈ Finset.Iic n, coeff β f * ∏ i ∈ β.support, w i ^ β i := by
  have hsub : (trunc' R n f).support ⊆ Finset.Iic n := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, coeff_trunc'] at hm
    split_ifs at hm with h
    · exact Finset.mem_Iic.mpr h
    · exact absurd rfl hm
  rw [MvPolynomial.eval_eq, Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [coeff_trunc', if_pos (Finset.mem_Iic.mp hm)]
  · intro m _ hm
    rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]

theorem hasVal_log_of_mul_self_eq_zero :
    ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (p : ℕ) (x : B), x * x = 0 → HasVal p (fun _ : Unit => x) (PowerSeries.log Q : MvPowerSeries Unit Q) (algebraMap B Q x) := by
  intro B Q _ _ _ _ p x hx
  set y : Q := algebraMap B Q x with hy
  have hyy : y * y = 0 := by rw [hy, ← map_mul, hx, map_zero]
  have hcoeff : ∀ β : Unit →₀ ℕ, coeff β (PowerSeries.log Q : MvPowerSeries Unit Q) =
      PowerSeries.coeff (β ()) (PowerSeries.log Q) := by
    intro β
    rw [PowerSeries.coeff_def (by rfl)]
  intro m
  refine ⟨1, fun N' hN' => ⟨0, ?_⟩⟩
  rw [mul_zero, map_zero, sub_eq_zero, mvPolynomialEval_truncFinsupp_eq_sum_coeff_mul_prod]
  rw [Finset.sum_eq_single (Finsupp.single () 1)]
  · rw [hcoeff]
    simp [PowerSeries.coeff_log, hy]
  · intro β _ hβ
    rw [hcoeff, PowerSeries.coeff_log]
    by_cases h0 : β () = 0
    · simp [h0]
    · have h1 : β () ≠ 1 := by
        intro h1; apply hβ; ext u; simp [h1]
      have hsupp : β.support = {()} := by
        ext u; simp [h0]
      rw [hsupp, Finset.prod_singleton]
      obtain ⟨k, hk⟩ : ∃ k, β () = k + 2 := ⟨β () - 2, by omega⟩
      have hp : (algebraMap B Q) ((fun _ : Unit => x) ()) ^ (k + 2) = 0 := by
        show y ^ (k + 2) = 0
        rw [pow_add, pow_two, hyy, mul_zero]
      rw [hk, hp, mul_zero]
  · intro h
    exfalso; apply h
    rw [Finset.mem_Iic]
    intro u
    simpa using hN'

end GlobalTheory.QLog.SqZero
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasVal_log_of_mul_self_eq_zero' : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (p : ℕ) (x : B), x * x = 0 → HasVal p (fun _ : Unit => x) (PowerSeries.log Q : MvPowerSeries Unit Q) (algebraMap B Q x) := by
  atlas_forward_decl GlobalTheory.QLog.SqZero.hasVal_log_of_mul_self_eq_zero
end

section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.QLog

namespace GlobalTheory.QLog.LogDiff

theorem dIn_log : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q],
    DIn (⊤ : Ideal B) (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  intro B Q _ _ _ _ α i
  have hc : MvPowerSeries.coeff α (PowerSeries.log Q : MvPowerSeries Unit Q) =
      PowerSeries.coeff (α i) (PowerSeries.log Q) := by
    rw [PowerSeries.coeff_def (s := α) (n := α i) rfl]
  rw [hc, PowerSeries.coeff_log]
  by_cases h : α i = 0
  · exact ⟨0, trivial, by simp [h]⟩
  · refine ⟨(-1) ^ (α i + 1), trivial, ?_⟩
    have h' : ((α i : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h
    rw [if_neg h, ← map_natCast (algebraMap ℚ Q), ← map_mul, mul_div_cancel₀ _ h']
    simp

end GlobalTheory.QLog.LogDiff
end

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diffCoeffsInIdeal_top_powerSeries_log : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q], DIn (⊤ : Ideal B) (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  atlas_forward_decl GlobalTheory.QLog.LogDiff.dIn_log
end

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul

theorem subst_pow_log (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (m : ℕ) :
    subst (up Q (fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit B)))
      (PowerSeries.log Q : MvPowerSeries Unit Q)
      = (m : Q) • (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  have h1 : up Q (fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit B))
      = fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit Q) := by
    funext j
    simp [up]
  have h2 : formalLog (1 + X () : MvPowerSeries Unit Q)
      = (PowerSeries.log Q : MvPowerSeries Unit Q) := by
    rw [formalLog, add_sub_cancel_left, PowerSeries.subst]
    exact congrFun MvPowerSeries.subst_self _
  have h3 := formalLog_pow m (g := (1 + X () : MvPowerSeries Unit Q)) (by simp)
  rw [h2] at h3
  rw [h1, Nat.cast_smul_eq_nsmul, ← h3]
  rfl

end GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul
end

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_one_add_X_pow_log_eq_nsmul : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (m : ℕ), subst (up Q (fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit B))) (PowerSeries.log Q : MvPowerSeries Unit Q) = (m : Q) • (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  atlas_forward_decl GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul.subst_pow_log
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc WittVector

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharPeriod

theorem pow_dvd_of_theta_pow_dvd : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (x : B) (N : ℕ), (p : O) ∣ θ x ^ N → ∃ M : ℕ, (p : B) ∣ x ^ M := by
  intro p _ B O Q _ _ _ _ θ hF x N ⟨o, ho⟩
  obtain ⟨b, rfl⟩ := hF.surj o
  have hj : θ (x ^ N - p * b) = 0 := by rw [map_sub, map_pow, ho, map_mul, map_natCast, sub_self]
  obtain ⟨y, -, hy⟩ := hF.pd _ hj
  refine ⟨N * p, ?_⟩
  have h1 : (x ^ N - (x ^ N - p * b)) ∣ (x ^ N) ^ p - (x ^ N - p * b) ^ p := sub_dvd_pow_sub_pow _ _ _
  rw [sub_sub_cancel] at h1
  rw [pow_mul]
  have h2 : (x ^ N) ^ p = ((x ^ N) ^ p - (x ^ N - p * b) ^ p) + p * y := by rw [hy]; ring
  rw [h2]
  exact dvd_add (dvd_trans (dvd_mul_right _ _) h1) (dvd_mul_right _ _)

theorem root_iterate_pow {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    (n : ℕ) (y : PreTilt O p) : (root^[n] y) ^ (p ^ n) = y := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih]
    exact (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply y

theorem one_add_pow_of_sq_zero {R : Type} [CommRing R] {x : R} (hx : x * x = 0) (k : ℕ) :
    (1 + x) ^ k = 1 + k * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (k : R) * hx

theorem pow_mul_logValue : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p), IsPrimitiveSystem ε → ∀ (F : BFrame ε) [Algebra ℚ F.Q] (n k : ℕ) (w : F.B) (q : F.Q), F.θ w = zeta ε n ^ k → HasVal p (fun _ : Unit => w - 1) (PowerSeries.log F.Q : MvPowerSeries Unit F.Q) q → ∃ b : F.B, (p : F.Q) ^ n * q = algebraMap F.B F.Q (k * F.a (Sandwich.mu ε) + p ^ n * b) := by
  intro p _ O _ _ _ ε hε F _ n k w q hw hq
  have hF := F.frame
  haveI := hF.complete
  set r : F.B := F.a (teichmuller p (root^[n] ε)) with hr
  have hθr : F.θ r = zeta ε n := by rw [hr, F.θ_a, fontaineTheta_teichmuller]; rfl
  have hrp : r ^ (p ^ n) = 1 + F.a (Sandwich.mu ε) := by
    rw [hr, ← map_pow, ← map_pow, root_iterate_pow, Sandwich.mu, map_sub, map_one]
    ring
  set x : F.B := (k : F.B) * F.a (Sandwich.mu ε) with hx
  have hxx : x * x = 0 := by
    have h : F.a (Sandwich.mu ε) * F.a (Sandwich.mu ε) = 0 := by
      rw [← F.p_τ]; linear_combination ((p : F.B) * p) * F.τ_sq
    linear_combination ((k : F.B) * k) * h
  set e : F.B := r ^ k with he
  have hθe : F.θ e = zeta ε n ^ k := by rw [he, map_pow, hθr]
  have hep : e ^ (p ^ n) = 1 + x := by
    have h : F.a (Sandwich.mu ε) * F.a (Sandwich.mu ε) = 0 := by
      rw [← F.p_τ]; linear_combination ((p : F.B) * p) * F.τ_sq
    rw [he, ← pow_mul, mul_comm, pow_mul, hrp, one_add_pow_of_sq_zero h]
  have hpe : (p : F.B) ∣ (e - 1) ^ (p ^ n) := by
    obtain ⟨s, hs⟩ := exists_add_pow_prime_pow_eq (Fact.out : p.Prime) (e - 1) 1 n
    rw [sub_add_cancel, one_pow, hep] at hs
    refine ⟨k * F.τ - (e - 1) * s, ?_⟩
    have : (p : F.B) * F.τ = F.a (Sandwich.mu ε) := F.p_τ
    linear_combination -hs + hx - (k : F.B) * this
  have hnile : ∀ i : Unit, ∃ N : ℕ, (p : F.B) ∣ (fun _ : Unit => e - 1) i ^ N := fun _ => ⟨_, hpe⟩
  have hnilw : ∀ i : Unit, ∃ N : ℕ, (p : F.B) ∣ (fun _ : Unit => w - 1) i ^ N := by
    intro _
    have h1 : F.θ (w - 1) = F.θ (e - 1) := by rw [map_sub, map_sub, hw, hθe]
    obtain ⟨s, hs⟩ := hpe
    exact pow_dvd_of_theta_pow_dvd p F.B O F.Q F.θ hF (w - 1) (p ^ n)
      ⟨F.θ s, by rw [h1, ← map_pow, hs, map_mul, map_natCast]⟩
  have hD := GlobalTheory.T.diffCoeffsInIdeal_top_powerSeries_log F.B F.Q
  obtain ⟨q₁, hq₁, -⟩ := GlobalTheory.T.existsUnique_hasPAdicPowerSeriesValue_of_diffCoeffs p F.B O F.Q F.θ hF Unit (fun _ => e - 1) hnile _ hD
  have hJ : ∀ y ∈ RingHom.ker F.θ, ∃ y' ∈ RingHom.ker F.θ, y ^ p = p * y' := by
    intro y hy
    obtain ⟨y', hy', h⟩ := hF.pd y hy
    exact ⟨y', hy', h⟩
  obtain ⟨j, -, b', hjb⟩ := GlobalTheory.T.hasPAdicPowerSeriesValue_sub_mem_pd_ideal p F.B O F.Q F.θ hF Unit (fun _ => w - 1) hnilw
    (RingHom.ker F.θ) hJ (fun _ => e - 1) _ q q₁
    (fun _ => by rw [RingHom.mem_ker, sub_sub_sub_cancel_right, map_sub, hw, hθe, sub_self]) hD hq hq₁ 0
  obtain ⟨Ev, hEv, -⟩ := (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p F.B F.B Unit (fun _ => e - 1) hnile).1
  set u : Unit → MvPowerSeries Unit F.B := fun _ => (1 + X ()) ^ (p ^ n) - 1 with hu
  have hu0 : ∀ j, constantCoeff (u j) = 0 := fun _ => by simp [hu]
  have hEu : (fun j => Ev (u j)) = fun _ : Unit => x := by
    funext j
    simp only [hu, map_sub, map_pow, map_add, map_one, hEv.1 ()]
    rw [add_sub_cancel, hep, add_sub_cancel_left]
  have h1 : HasVal p (fun j => Ev (u j)) (PowerSeries.log F.Q : MvPowerSeries Unit F.Q) (algebraMap F.B F.Q x) := by
    rw [hEu]; exact GlobalTheory.T.hasVal_log_of_mul_self_eq_zero' F.B F.Q p x hxx
  have h2 := GlobalTheory.T.pAdicEvaluation_subst_compatible_thickening p F.B O F.Q F.θ hF Unit (fun _ => e - 1) hnile Ev hEv Unit u _ _ hu0 hD h1
  rw [hu, GlobalTheory.T.subst_one_add_X_pow_log_eq_nsmul F.B F.Q (p ^ n)] at h2
  have h3 := (GlobalTheory.T.hasPAdicPowerSeriesValue_add_smul_map p F.B O F.Q F.θ hF Unit (fun _ => e - 1) _ 0 q₁ 0 hq₁).2.1 ((p ^ n : ℕ) : F.Q)
  have h4 := HasVal.unique hF h3 h2
  refine ⟨j + b', ?_⟩
  rw [pow_zero, one_mul] at hjb
  have h5 : q = q₁ + algebraMap F.B F.Q (j + b') := by rw [← hjb]; ring
  rw [h5, mul_add, ← Nat.cast_pow, h4]
  simp only [map_add, map_mul, map_natCast, map_pow]
  push_cast
  ring

theorem hasPeriod_formalLog_char : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε) (F : BFrame ε) [Algebra ℚ F.Q] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (g : MvPowerSeries (Fin d) F.B), constantCoeff g = 1 → (∀ n, c.ev n (map F.θ g) = charElem χ n) → ∀ t, c.HasPeriod F.θ t (formalLog (map (algebraMap F.B F.Q) g)) (F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F _ G d c χ g hg1 hgχ t
  have hF := F.frame
  haveI := hF.complete
  have hD : DIn (⊤ : Ideal F.B) (formalLog (map (algebraMap F.B F.Q) g)) := GlobalTheory.T.diffCoeffsInIdeal_top_formalLog_constOne F.B F.Q (Fin d) g hg1
  have hnil : ∀ n (z : Fin d → F.B), (∀ i, F.θ (z i) = t.pt n (c.x n i)) → ∀ i, ∃ N : ℕ, (p : F.B) ∣ z i ^ N := by
    intro n z hz i
    obtain ⟨N, w, hw⟩ := c.nil n i
    exact pow_dvd_of_theta_pow_dvd p F.B O F.Q F.θ hF (z i) N ⟨t.pt n w, by rw [hz, ← map_pow, hw, map_mul, map_natCast]⟩
  have hex : ∀ (n : ℕ) (z : Fin d → F.B), (∀ i, F.θ (z i) = t.pt n (c.x n i)) → ∃ q : F.Q, HasVal p z (formalLog (map (algebraMap F.B F.Q) g)) q :=
    fun n z hz => (GlobalTheory.T.existsUnique_hasPAdicPowerSeriesValue_of_diffCoeffs p F.B O F.Q F.θ hF (Fin d) z (hnil n z hz) _ hD).exists
  have hcong : ∀ (n : ℕ) (z : Fin d → F.B) (q : F.Q), (∀ i, F.θ (z i) = t.pt n (c.x n i)) → HasVal p z (formalLog (map (algebraMap F.B F.Q) g)) q → ∃ b : F.B, (p : F.Q) ^ n * q = algebraMap F.B F.Q (F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) + p ^ n * b) := by
    intro n z q hz hq
    obtain ⟨E, hE, -⟩ := (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p F.B F.B (Fin d) z (hnil n z hz)).1
    have hq1 := GlobalTheory.T.hasVal_log_eval_of_hasVal_formalLog p F.B O F.Q F.θ hF (Fin d) z (hnil n z hz) E hE g q hg1 hq
    have hθ := GlobalTheory.T.theta_eval_eq_zeta_pow_digit p O ε hε F G d c χ g hgχ t n z hz (hnil n z hz) E hE
    obtain ⟨b, hb⟩ := pow_mul_logValue p O ε hε F n _ (E g) q hθ hq1
    set a := epsPairing hε G t χ
    obtain ⟨e, he⟩ := GlobalTheory.PDiv.pow_dvd_sub_digit n a
    have hy : F.a (Sandwich.mu ε * ofPadic p O a) = (GlobalTheory.PDiv.digit n a : F.B) * F.a (Sandwich.mu ε) + p ^ n * F.a (Sandwich.mu ε * ofPadic p O e) := by
      have h2 : ofPadic p O a = ofPadic p O (GlobalTheory.PDiv.digit n a : ℤ_[p]) + ofPadic p O ((p : ℤ_[p]) ^ n * e) := by
        rw [← map_add, ← he, add_sub_cancel]
      rw [h2]
      simp only [map_add, map_mul, map_pow, map_natCast]
      ring
    refine ⟨b - F.a (Sandwich.mu ε * ofPadic p O e), ?_⟩
    rw [hb, hy]
    congr 1
    ring
  first
  | exact ⟨hex, hcong⟩
  | exact hcong

end GlobalTheory.CharPeriod
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_formalLog_lift_characterSeries : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε) (F : BFrame ε) [Algebra ℚ F.Q] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (g : MvPowerSeries (Fin d) F.B), constantCoeff g = 1 → (∀ n, c.ev n (map F.θ g) = charElem χ n) → ∀ t, c.HasPeriod F.θ t (formalLog (map (algebraMap F.B F.Q) g)) (F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ))) := by
  atlas_forward_decl GlobalTheory.CharPeriod.hasPeriod_formalLog_char
end
