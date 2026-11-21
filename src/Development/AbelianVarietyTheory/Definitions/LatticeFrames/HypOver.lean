import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RankConditionRankOneIffEqZero

noncomputable section

namespace GlobalTheory.Core.RkFamModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ GlobalTheory.Core.Rk NumberField Module





theorem xu_pos (D : D7) (u : D.what₂.Word) : 0 < (D.mem u).A.Xu := by
  have h1 := (D.mem u).A.Dstar_pos
  have h2 : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  unfold ColumnsAtT.Xu
  positivity

theorem fk_pos (R : Ranks) : (0 : ℝ) < (R.f : ℝ) * R.k := by
  have := R.m_add_three_le_k
  have h1 : 0 < R.k := by omega
  have h2 : 0 < R.f := Nat.mul_pos two_pos R.ord_pos
  positivity

theorem log_tstar (D : D7) (u : D.what₂.Word) : Real.log (D.mem u).A.Tstar =
    Real.log (D.mem u).A.Xu - 2 / ((D.R.f : ℝ) * D.R.k) * Real.log (D.mem u).A.GamP := by
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  unfold ColumnsAtT.Tstar
  rw [Real.log_mul (xu_pos D u).ne' (Real.rpow_pos_of_pos hG _).ne', Real.log_rpow hG]
  ring

theorem log_T_lt (D : D7) (u : D.what₂.Word) :
    Real.log ((D.mem u).A.T : ℝ) < Real.log (D.mem u).A.Xu + 1 / ((D.R.f : ℝ) * D.R.k) := by
  have hT : (0 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hf := fk_pos D.R
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hs : 0 < (D.mem u).A.Tstar := mul_pos (xu_pos D u) (Real.rpow_pos_of_pos hG _)
  have h1 := Real.log_le_log hT (D.T_win u).2
  rw [Real.log_mul (by positivity) hs.ne', log_tstar] at h1
  have h2 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((D.R.f : ℝ) * D.R.k))
  have h3 : 0 < 2 / ((D.R.f : ℝ) * D.R.k) * Real.log (D.mem u).A.GamP :=
    mul_pos (by positivity) (Real.log_pos (D.mem u).A.one_lt_gammaP)
  linarith


theorem sameTops_iff {D D' : D7} (L : SizeData₂ D) (L' : SizeData₂ D') (hk : D.R.k = D'.R.k) :
    SameTops D D' ↔ ∀ (t : D.host.TT) (t' : D'.host.TT),
      (t : D.R.A).val = (t' : D'.R.A).val → L.aT t = L'.aT t' ∧ L.bT t = L'.bT t' := by
  have h : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have h' : 0 < D'.R.k := by omega
  have hkr : (D.R.k : ℝ) = D'.R.k := by exact_mod_cast hk
  constructor
  · intro H t t' ht
    have e1 : (D.eTau (D.eTau.symm ⟨D.R.tau1 t, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩) : D.R.GG) = D.R.tau1 t := by
      rw [Equiv.apply_symm_apply]
    have e2 : (D'.eTau (D'.eTau.symm ⟨D'.R.tau1 t', (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩) : D'.R.GG) =
        D'.R.tau1 t' := by rw [Equiv.apply_symm_apply]
    obtain ⟨a, b⟩ := H _ _ t t' h h' e1 e2 ht
    obtain ⟨c1, c2⟩ := L.top_u _ t h e1
    obtain ⟨d1, d2⟩ := L'.top_u _ t' h' e2
    rw [a, d1] at c1
    rw [b, d2] at c2
    constructor
    · exact_mod_cast (by linarith : (L.aT t : ℝ) = L'.aT t')
    · exact_mod_cast (by linarith : (L.bT t : ℝ) = L'.bT t')
  · intro H τ τ' t t' h h' e1 e2 ht
    obtain ⟨a, b⟩ := H t t' ht
    obtain ⟨c1, c2⟩ := L.top_u _ t h e1
    obtain ⟨d1, d2⟩ := L'.top_u _ t' h' e2
    rw [a, hkr, ← d1] at c1
    rw [b, hkr, ← d2] at c2
    exact ⟨by exact_mod_cast c1, by exact_mod_cast c2⟩

def ptsOf {ε : ℝ} (F : FamCore ε) : Pts := Pts.ofFam F



abbrev Ht (t : R0.A) : Host R0 := { H0 with TT := Finset.univ, u0 := t }

def hcA (c : ℕ) : HCParam R0 :=
  { hc0 with
    u := fun i => hc0.u i + if i.1 = 0 then (c : ℚ) else 0
    u_gt_v := fun i => by
      have := hc0.u_gt_v i
      have h2 : (0 : ℚ) ≤ if i.1 = 0 then (c : ℚ) else 0 := by split_ifs <;> positivity
      dsimp only
      linarith
    v_gt_u := fun i => by simpa using hc0.v_gt_u i
    u_last_gt := fun h h' => by
      have := hc0.u_last_gt h h'
      have h2 : (0 : ℚ) ≤ if R0.k - 1 = 0 then (c : ℚ) else 0 := by split_ifs <;> positivity
      dsimp only
      linarith
    u_half := fun i => by
      obtain ⟨z, hz⟩ := hc0.u_half i
      by_cases h : i.1 = 0
      · exact ⟨z + c, by simp only [h, if_true, hz]; push_cast; ring⟩
      · exact ⟨z, by simp only [h, if_false, hz, add_zero]⟩ }

abbrev pkg (N : ℕ) : ClsPkg where
  cls := fun _ => Fin (N + 1)
  clsFin := fun _ => inferInstance
  stab := fun _ _ => Unit
  stabGrp := fun _ _ => inferInstance
  stabFin := fun _ _ => inferInstance
  DGam := 1
  DGam_pos := one_pos
  dvd := fun _ _ => by simp

def perS (N : ℕ) (s : ℂ) : FK (Fin (N + 1)) →ₗ[ℂ] En 1 →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun φ F => s * φ 0 () * F 0) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

theorem tH (t : R0.A) : THyp (Ht t) := ⟨exampleHost_typeHypothesis.cond, exampleHost_typeHypothesis.bb, exampleHost_typeHypothesis.jac⟩

def gap (t : R0.A) : LocalGap (Ht t) := LocalGap.localGapOfRecord GlobalTheory.Mem.nonempty_record_of_locStage.some _

def lbl (t : R0.A) : Lbl (Ht t) := (lbl_nonempty (Ht t) (tH t) 5 (by norm_num) (by decide) (by decide)).some

set_option maxHeartbeats 1600000 in

def recd (t : R0.A) (c N : ℕ) (s : ℂ) : D7 :=
  letI := (Ht t).cmStar
  hostLevelRecord (Ht t) (W := Unit) () (fun _ _ => hcA c) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) 1 one_pos (fun _ _ l h => exampleWeight_cloud_gap_four l h) (fun _ _ => false) (fun _ _ _ => rfl)
    (fun _ _ l h => by
      have := exampleWeight_middle_entries l h
      simp only [Bool.false_eq_true, if_false, sub_zero]
      simp only [hcA, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, add_zero]
      exact this)
    (fun _ _ => 1) (fun _ _ => one_pos) (fun _ => 1) (fun _ => one_pos) 0 (fun _ => 0) (fun _ => 1) (fun _ => one_pos)
    (fun _ => pkg N) (fun _ => T0) (dstarOf T0) (dstarOf_pos T0) (fun _ => 1) (fun _ => one_pos) 2 one_lt_two
    (fun _ => exampleLevel_near_lower Tau0 T0) exampleHost_type_primes_split (tH t) (fun _ => examplePrime_mem_levelPrimes) (fun _ => examplePrime_ne_split_primes) (fun _ => π0O)
    (fun _ => π0_mem_K) (fun _ => π0_norm) (fun _ => π0_cong)
    (fun _ i _ => ((hostSpacesOfNorm (Ht t) T0 (π0O : (Ht t).E) π0_norm).X i).L0)
    (fun _ i _ => ((hostSpacesOfNorm (Ht t) T0 (π0O : (Ht t).E) π0_norm).X i).standardTuple_isLattice)
    (gap t) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ => false) (fun _ => rfl) 1 1 1 le_rfl Unit (fun _ => ()) (fun _ => ())
    (lbl t) (fun _ => by norm_num [T0]) (fun _ _ => perS N s) (fun _ => ⊤)
    (localDataAtServedPlace' (Ht t) (fun _ _ => hcA c) (fun _ : Unit => pkg N) (fun _ => T0) (fun _ _ => 0) (fun _ => 0) (fun _ _ => ∅))
    (localData_rank_eq_classes (Ht t) (fun _ _ => hcA c) (fun _ : Unit => pkg N) (fun _ => T0) (fun _ _ => 0) (fun _ => 0) (fun _ _ => ∅))

section Rank

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (N : ℕ)

theorem colTo_one (j : ℕ) : colTo (chainN hc (pkg N)) j (fun _ _ => 1) = fun _ _ => ((N : ℂ) + 1) ^ j := by
  induction j with
  | zero => funext _ _; simp [colTo]
  | succ j ih =>
    show (chainN hc (pkg N)).K j (colTo (chainN hc (pkg N)) j (fun _ _ => 1)) = _
    rw [ih]
    funext c y
    have e : ∀ a : Fin (N + 1), (chainN hc (pkg N)).wt j a • (chainN hc (pkg N)).Kmap j a c (fun _ => ((N : ℂ) + 1) ^ j) =
        fun _ => ((N : ℂ) + 1) ^ j := fun a => by
      rw [chainN_Kmap hc (pkg N) j a c]
      simp [ColumnChain.wt]
    have e2 : (chainN hc (pkg N)).K j (fun _ _ => ((N : ℂ) + 1) ^ j) c = ∑ _a : Fin (N + 1), fun _ : Unit => ((N : ℂ) + 1) ^ j := by
      unfold ColumnChain.K Formalism.ThetaLiftIndependence.kerOpM
      rw [Finset.sum_congr rfl fun a _ => e a]
    refine (congrFun e2 y).trans ?_
    simp [pow_succ]
    ring

variable (T : ℕ) [Fact T.Prime] (Dst : ℝ) (hD : 0 < Dst) (hT : T ≠ 2) (s : ℂ)

theorem rk_le_one : rkC (chainN hc (pkg N)) (atTN hc (pkg N) T Dst hD 1 one_pos 2 one_lt_two)
    (periodN hc (pkg N) (En 1) (perS N s)) ≤ 1 := by
  unfold rkC
  refine (Submodule.finrank_le _).trans ?_
  show finrank ℂ (Module.Dual ℂ (En 1)) ≤ 1
  rw [Subspace.dual_finrank_eq]
  simp

theorem rk_zero : rkC (chainN hc (pkg N)) (atTN hc (pkg N) T Dst hD 1 one_pos 2 one_lt_two)
    (periodN hc (pkg N) (En 1) (perS N 0)) = 0 := by
  unfold rkC
  have : PhiC (chainN hc (pkg N)) (atTN hc (pkg N) T Dst hD 1 one_pos 2 one_lt_two)
      (periodN hc (pkg N) (En 1) (perS N 0)) = 0 := by
    ext φ F
    show (0 : ℂ) * _ * _ = 0
    simp
  rw [this, LinearMap.range_zero, finrank_bot]

include hT in
theorem rk_one : rkC (chainN hc (pkg N)) (atTN hc (pkg N) T Dst hD 1 one_pos 2 one_lt_two)
    (periodN hc (pkg N) (En 1) (perS N 1)) = 1 := by
  refine le_antisymm (rk_le_one hc N T Dst hD 1) ?_
  unfold rkC
  haveI : FiniteDimensional ℂ (periodN hc (pkg N) (En 1) (perS N 1)).Mt := inferInstanceAs (FiniteDimensional ℂ (En 1))
  rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  intro h
  have h1 := LinearMap.congr_fun (LinearMap.congr_fun h ⟨fun _ _ => 1, by rw [atTN_Mram _ _ _ _ _ _ _ _ _ hT]; trivial⟩)
    (WithLp.toLp 2 fun _ => (1 : ℂ))
  have h2 : (1 : ℂ) * colTo (chainN hc (pkg N)) R.m (fun _ _ => 1) (0 : Fin (N + 1)) () * 1 = 0 := h1
  rw [colTo_one] at h2
  have h3 : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  simp [h3] at h2

end Rank

theorem baseDegree_ne_two : T0 ≠ 2 := by norm_num [T0]

theorem recd_dU (t c N s u) : dU (recd t c N s) u = N + 1 :=
  (atTN_du (fun _ : Tau2 R0 => hcA c) (pkg N) T0 (dstarOf T0) (dstarOf_pos T0) 1 one_pos 2 one_lt_two baseDegree_ne_two).trans (by simp)

theorem columnRank_eq_one_of_rankOne (t c N u) : rkC ((recd t c N 1).mem u).C ((recd t c N 1).mem u).A ((recd t c N 1).mem u).P = 1 :=
  rk_one (fun _ : Tau2 R0 => hcA c) N T0 (dstarOf T0) (dstarOf_pos T0) baseDegree_ne_two

theorem columnRank_eq_zero_of_rankZero (t c N u) : rkC ((recd t c N 0).mem u).C ((recd t c N 0).mem u).A ((recd t c N 0).mem u).P = 0 :=
  rk_zero (fun _ : Tau2 R0 => hcA c) N T0 (dstarOf T0) (dstarOf_pos T0)

theorem rankCondition_rankOne_iff_eq_zero (t c N u) : RK (recd t c N 1) u ↔ N = 0 := by
  show dU _ u < 2 * _ ↔ _
  rw [recd_dU, columnRank_eq_one_of_rankOne]; omega

theorem not_rankCondition_rankZero (t c N u) : ¬ RK (recd t c N 0) u := by
  show ¬ dU _ u < 2 * _
  rw [recd_dU, columnRank_eq_zero_of_rankZero]; omega


theorem recd_sameTops (t c N s t' c' N' s') : SameTops (recd t c N s) (recd t' c' N' s') ↔ c = c' := by
  constructor
  · intro H
    have := (H ⟨R0.tau1 0, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩ ⟨R0.tau1 0, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩
      ⟨(0 : R0.A), Finset.mem_univ _⟩ ⟨(0 : R0.A), Finset.mem_univ _⟩
      (show 0 < R0.k by decide) (show 0 < R0.k by decide) rfl rfl rfl).1
    have h2 : hc0.u ⟨0, by decide⟩ + (c : ℚ) = hc0.u ⟨0, by decide⟩ + (c' : ℚ) := this
    exact_mod_cast add_left_cancel h2
  · rintro rfl τ τ' _ _ h h' _ _ _
    exact ⟨rfl, rfl⟩

theorem val_cast (u₀ : ℕ) (h : u₀ < R0.n) : (R0.ofNat u₀).val = u₀ := R0.val_ofNat_of_lt h


end GlobalTheory.Core.RkFamModel

namespace GlobalTheory.Core.RkOverModel

open Formalism.BasicNotions GlobalTheory.Core.Rk GlobalTheory.Core.Rk.FamInh








theorem log_T_le (D : D7) (u : D.what₂.Word) : Real.log ((D.mem u).A.T : ℝ) ≤ Real.log (D.mem u).A.Xu + 1 := by
  have hT : (0 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hf := f_mul_k_pos D.R
  have h1 := Real.log_le_log hT (T_lt_cap D u).le
  rw [Real.log_mul (by positivity) (Xu_pos D u).ne'] at h1
  have h2 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((D.R.f : ℝ) * D.R.k))
  have h3 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.k := by
    have := D.R.m_add_three_le_k
    have a : 0 < D.R.f * D.R.k := Nat.mul_pos (Nat.mul_pos two_pos D.R.ord_pos) (by omega)
    exact_mod_cast a
  have h4 : 1 / ((D.R.f : ℝ) * D.R.k) ≤ 1 := (div_le_one hf).2 h3
  linarith

def famQ (q : ℝ → LvP) : Pts :=
  ⟨fun _ => Formalism.BasicNotions.Examples₂.R0.A, fun x t => recd (q x) t 0 0 1, Pts.ne_of_forall fun _ => ⟨0⟩,
    fun _ _ _ => recd_sameHost ..⟩

theorem exists_big : ∃ q : ℝ → LvP, ∀ x, Real.exp x < (q x).T := by
  choose f hf using exists_lvP
  exact ⟨fun x => f ⌈Real.exp x⌉₊, fun x => lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hf _)⟩

theorem ev_lt (a b : ℝ) {δ : ℝ} (hδ : δ < 1) : ∃ x₁ : ℝ, ∀ x, x₁ ≤ x → a * x ^ δ + b < x := by
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop (by linarith : 0 < 1 - δ)).eventually_ge_atTop (2 * a)).and
      ((Filter.eventually_gt_atTop (0 : ℝ)).and (Filter.eventually_gt_atTop (2 * b))))
  refine ⟨x₁, fun x hx => ?_⟩
  obtain ⟨h1, h0, h2⟩ := hx₁ x hx
  have e : x ^ (1 - δ) * x ^ δ = x := by rw [← Real.rpow_add h0]; simp
  have h7 := mul_le_mul_of_nonneg_right h1 (Real.rpow_pos_of_pos h0 δ).le
  linarith




def famTwo (p : LvP) : Pts :=
  ⟨fun _ => Formalism.BasicNotions.Examples₂.R0.A × Fin 2, fun _ i => recd p i.1 i.2 0 0, Pts.ne_of_forall fun _ => ⟨(0, 0)⟩,
    fun _ _ _ => recd_sameHost ..⟩


def clsN (p : LvP) (N : ℝ → ℕ) : ℝ → D7 → Prop := fun x D => ∃ t, D = recd p t 0 (N x) 1




def famSome (p : LvP) : Pts :=
  ⟨fun _ => Formalism.BasicNotions.Examples₂.R0.A × Fin 2, fun _ i => recd p i.1 0 i.2 1, Pts.ne_of_forall fun _ => ⟨(0, 0)⟩,
    fun _ _ _ => recd_sameHost ..⟩



end GlobalTheory.Core.RkOverModel

end
