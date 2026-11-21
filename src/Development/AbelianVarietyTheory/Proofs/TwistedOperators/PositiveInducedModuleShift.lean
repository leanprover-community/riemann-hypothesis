import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
import BuildAid.ForwardExisting

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.ActUIso

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

theorem adjoint_comp_isometry (T : H' →ₗᵢ[ℂ] H) (v : H') :
    (ContinuousLinearMap.adjoint T.toContinuousLinearMap) (T v) = v := by
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp

theorem deriv_isometry_comp (T : H' →ₗᵢ[ℂ] H) (f : ℝ → H') (t : ℝ) :
    deriv (fun s => T (f s)) t = T (deriv f t) := by
  by_cases hf : DifferentiableAt ℝ f t
  · have := (T.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hf.hasDerivAt
    exact this.deriv
  · have hTf : ¬ DifferentiableAt ℝ (fun s => T (f s)) t := by
      intro h
      apply hf
      have h2 := ((ContinuousLinearMap.adjoint T.toContinuousLinearMap).restrictScalars ℝ).differentiableAt.comp t h
      have e : f = (⇑(ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.adjoint T.toContinuousLinearMap)) ∘ fun s ↦ T (f s)) := by
        funext s
        simp [adjoint_comp_isometry]
      rw [e]; exact h2
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hTf, map_zero]

end GlobalTheory.ActUIso

namespace GlobalTheory.ActUIso

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

theorem inG_smul_add_theta {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((1 / 2 : ℂ) • (Y + PI.DSInfCharCap.thetaJ ε Y)) := by
  have hJ := Jm_conjTranspose ε
  have hJJ := Jm_mul_self ε
  unfold inG PI.DSInfCharCap.thetaJ
  set J := Jm ε
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
  have : (Y + -(J * Yᴴ * J))ᴴ * J + J * (Y + -(J * Yᴴ * J)) = 0 := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, hJ,
      Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    abel
  rw [this, smul_zero]

theorem inG_smul_sub_theta {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((1 / (2 * Complex.I)) • (Y - PI.DSInfCharCap.thetaJ ε Y)) := by
  have hJ := Jm_conjTranspose ε
  have hJJ := Jm_mul_self ε
  unfold inG PI.DSInfCharCap.thetaJ
  set J := Jm ε
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp [Complex.conj_I]
  rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, neg_smul, neg_add_eq_sub, ← smul_sub]
  have : J * (Y - -(J * Yᴴ * J)) - (Y - -(J * Yᴴ * J))ᴴ * J = 0 := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, hJ,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    abel
  rw [this, smul_zero]

theorem dsig_intertwine {n : ℕ} (ε : Fin n → Bool)
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (T : H' →ₗᵢ[ℂ] H) (hT : ∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w))
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : inG ε X) (w : H') :
    PI.PhMeasCore.dsig ρ X (T w) = T (PI.PhMeasCore.dsig ρ' X w) := by
  unfold PI.PhMeasCore.dsig
  have e : (fun t : ℝ => ρ (NormedSpace.exp ((t : ℂ) • X)) (T w)) =
      fun t : ℝ => T (ρ' (NormedSpace.exp ((t : ℂ) • X)) w) := by
    funext t
    have h := hT (expG ε X t) w
    have h2 : uMat (expG ε X t) = NormedSpace.exp ((t : ℂ) • X) := toM_expG ε X t hX
    rw [h2] at h
    exact h.symm
  rw [e, deriv_isometry_comp]

theorem dsigC_intertwine {n : ℕ} (ε : Fin n → Bool)
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (T : H' →ₗᵢ[ℂ] H) (hT : ∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w))
    (Y : Matrix (Fin n) (Fin n) ℂ) (w : H') :
    PI.DSInfCharCap.dsigC ε ρ Y (T w) = T (PI.DSInfCharCap.dsigC ε ρ' Y w) := by
  unfold PI.DSInfCharCap.dsigC
  rw [dsig_intertwine ε ρ ρ' T hT _ (inG_smul_add_theta ε Y),
    dsig_intertwine ε ρ ρ' T hT _ (inG_smul_sub_theta ε Y), map_add, map_smul]

theorem dsigCW_intertwine {n : ℕ} (ε : Fin n → Bool)
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (T : H' →ₗᵢ[ℂ] H) (hT : ∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w))
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (w : H') :
    PI.DSInfCharCap.dsigCW ε ρ l (T w) = T (PI.DSInfCharCap.dsigCW ε ρ' l w) := by
  induction l with
  | nil => rfl
  | cons Y l ih =>
    simp only [PI.DSInfCharCap.dsigCW]
    rw [ih, dsigC_intertwine ε ρ ρ' T hT]

theorem actU_isometry : ∀ {n : ℕ} (ε : Fin n → Bool) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (T : H' →ₗᵢ[ℂ] H), (∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w)) → ∀ (p : FreeAlgebra ℂ (Fin n × Fin n)) (w : H'), actU ε ρ p (T w) = T (actU ε ρ' p w) := by
  intro n ε H H' _ _ _ _ _ _ ρ ρ' T hT p w
  unfold actU
  simp only [Finsupp.sum, map_sum, map_smul, dsigCW_intertwine ε ρ ρ' T hT]

end GlobalTheory.ActUIso
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_intertwines_enveloping : ∀ {n : ℕ} (ε : Fin n → Bool) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (T : H' →ₗᵢ[ℂ] H), (∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w)) → ∀ (p : FreeAlgebra ℂ (Fin n × Fin n)) (w : H'), actU ε ρ p (T w) = T (actU ε ρ' p w) := by
  atlas_forward_decl GlobalTheory.ActUIso.actU_isometry
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem exists_chain_between {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    ∀ (k : ℕ) (A B : Submodule K V), A ≤ B → Module.finrank K B = Module.finrank K A + k →
      ∃ c : ℕ → Submodule K V, Monotone c ∧ c 0 = A ∧ (∀ t, k ≤ t → c t = B) ∧
        ∀ t ≤ k, Module.finrank K (c t) = Module.finrank K A + t := by
  intro k
  induction k with
  | zero =>
    intro A B hAB h
    have hE : A = B := Submodule.eq_of_le_of_finrank_eq hAB (by omega)
    exact ⟨fun _ => A, fun _ _ _ => le_rfl, rfl, fun _ _ => hE, fun t ht => by
      have : t = 0 := by omega
      subst this; simp⟩
  | succ k ih =>
    intro A B hAB h
    have hne : A ≠ B := by
      rintro rfl; omega
    obtain ⟨v, hvB, hvA⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hAB hne)
    have hA' : Module.finrank K (A ⊔ Submodule.span K {v} : Submodule K V) = Module.finrank K A + 1 :=
      Submodule.finrank_sup_span_singleton hvA
    have hle : (A ⊔ Submodule.span K {v} : Submodule K V) ≤ B :=
      sup_le hAB ((Submodule.span_singleton_le_iff_mem v B).2 hvB)
    obtain ⟨c, hc, hc0, hcB, hcr⟩ := ih _ B hle (by omega)
    refine ⟨fun t => match t with | 0 => A | s + 1 => c s, ?_, rfl, ?_, ?_⟩
    · refine monotone_nat_of_le_succ fun t => ?_
      rcases t with _ | s
      · show A ≤ c 0
        rw [hc0]; exact le_sup_left
      · show c s ≤ c (s + 1)
        exact hc (Nat.le_succ s)
    · intro t ht
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      exact hcB s (by omega)
    · intro t ht
      rcases t with _ | s
      · simp
      · show Module.finrank K (c s) = _
        rw [hcr s (by omega), hA']
        omega

theorem exists_refine_nat {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Wn : ℕ → Submodule K V) (jn P : ℕ → ℕ) (h0 : Wn 0 = ⊥) (hm : Monotone Wn)
    (hs : ∀ k, Module.finrank K (Wn (k + 1)) = Module.finrank K (Wn k) + jn k)
    (hP0 : P 0 = 0) (hPs : ∀ i, P (i + 1) = P i + jn i) :
    ∀ a, ∃ W' : ℕ → Submodule K V, Monotone W' ∧ (∀ l ≤ P a, Module.finrank K (W' l) = l) ∧
      (∀ i ≤ a, W' (P i) = Wn i) ∧ ∀ l, P a ≤ l → W' l = Wn a := by
  have hr : ∀ i, Module.finrank K (Wn i) = P i := by
    intro i
    induction i with
    | zero => rw [h0, hP0]; simp
    | succ i ih => rw [hs, ih, hPs]
  intro a
  induction a with
  | zero =>
    refine ⟨fun _ => ⊥, fun _ _ _ => le_rfl, fun l hl => ?_, fun i hi => ?_, fun l _ => h0.symm⟩
    · rw [hP0] at hl
      have : l = 0 := by omega
      subst this; simp
    · have : i = 0 := by omega
      subst this; exact h0.symm
  | succ a ih =>
    obtain ⟨W', hW'm, hW'r, hW'p, hW'l⟩ := ih
    obtain ⟨c, hc, hc0, hcB, hcr⟩ := exists_chain_between (jn a) (Wn a) (Wn (a + 1))
      (hm (Nat.le_succ a)) (hs a)
    obtain ⟨W'', hW''⟩ : ∃ W'' : ℕ → Submodule K V, ∀ l, W'' l = if l ≤ P a then W' l else c (l - P a) :=
      ⟨_, fun _ => rfl⟩
    have hPa : W' (P a) = Wn a := hW'l _ le_rfl
    refine ⟨W'', ?_, ?_, ?_, ?_⟩
    · intro l m hlm
      rw [hW'' l, hW'' m]
      by_cases hl : l ≤ P a
      · by_cases hm' : m ≤ P a
        · rw [if_pos hl, if_pos hm']; exact hW'm hlm
        · rw [if_pos hl, if_neg hm']
          calc W' l ≤ W' (P a) := hW'm hl
            _ = c 0 := by rw [hPa, hc0]
            _ ≤ c (m - P a) := hc (Nat.zero_le _)
      · rw [if_neg hl, if_neg (by omega)]
        exact hc (by omega)
    · intro l hl
      rw [hW'' l]
      by_cases hl' : l ≤ P a
      · rw [if_pos hl']; exact hW'r l hl'
      · rw [if_neg hl', hcr _ (by rw [hPs] at hl; omega), hr]
        omega
    · intro i hi
      rw [hW'' (P i)]
      rcases Nat.lt_or_ge i (a + 1) with hia | hia
      · have hle : P i ≤ P a := by
          have key : ∀ d, P i ≤ P (i + d) := by
            intro d
            induction d with
            | zero => exact le_rfl
            | succ d ihd => rw [← Nat.add_assoc, hPs]; omega
          have := key (a - i)
          rwa [show i + (a - i) = a by omega] at this
        rw [if_pos hle]; exact hW'p i (by omega)
      · have hi' : i = a + 1 := by omega
        subst hi'
        by_cases hj : P (a + 1) ≤ P a
        · rw [if_pos hj]
          have hj0 : jn a = 0 := by rw [hPs] at hj; omega
          rw [show P (a + 1) = P a by rw [hPs, hj0, Nat.add_zero], hPa]
          exact hc0.symm.trans (hcB 0 (by omega))
        · rw [if_neg hj, hPs, Nat.add_sub_cancel_left]
          exact hcB _ le_rfl
    · intro l hl
      rw [hPs] at hl
      rw [hW'' l]
      by_cases hl' : l ≤ P a
      · rw [if_pos hl', hW'l l (by omega)]
        exact hc0.symm.trans (hcB 0 (by omega))
      · rw [if_neg hl']
        exact hcB _ (by omega)

theorem exists_refine_isIsoFlag : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}, IsIsoFlag ε j W → ∃ (b : ℕ) (W' : Flag n b) (β : Fin b → Fin a) (p : Fin (a + 1) → Fin (b + 1)), IsIsoFlag ε (fun _ => 1) W' ∧ (∀ i, W' (p i) = W i) ∧ W' (Fin.last b) = W (Fin.last a) ∧ (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) ∧ ∀ i, (p i : ℕ) = ∑ l ∈ univ.filter (fun l : Fin a => (l : ℕ) < (i : ℕ)), j l := by
  intro n a ε j W hW
  obtain ⟨h0, hmono, hstep, hiso⟩ := hW
  obtain ⟨jn, hjn⟩ : ∃ jn : ℕ → ℕ, ∀ k, jn k = if h : k < a then j ⟨k, h⟩ else 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨Wn, hWn⟩ : ∃ Wn : ℕ → Submodule ℂ (Fin n → ℂ), ∀ k, Wn k = W ⟨min k a, by omega⟩ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℕ, ∀ i, P i = ∑ k ∈ range i, jn k := ⟨_, fun _ => rfl⟩
  have hP0 : P 0 = 0 := by rw [hP]; simp
  have hPs : ∀ i, P (i + 1) = P i + jn i := fun i => by rw [hP, hP, Finset.sum_range_succ]
  have hPm : Monotone P := fun x y h => by
    rw [hP, hP]; exact Finset.sum_le_sum_of_subset (Finset.range_mono h)
  have hWi : ∀ i : Fin (a + 1), Wn i = W i := fun i => by
    rw [hWn]; congr 1; ext; simp; omega
  have hWn0 : Wn 0 = ⊥ := by
    rw [hWn, ← h0]; congr 1
  have hWnm : Monotone Wn := fun x y hxy => by
    rw [hWn, hWn]; exact hmono (Fin.mk_le_mk.2 (by omega))
  have hWns : ∀ k, Module.finrank ℂ (Wn (k + 1)) = Module.finrank ℂ (Wn k) + jn k := by
    intro k
    by_cases hk : k < a
    · have e1 : Wn (k + 1) = W (⟨k, hk⟩ : Fin a).succ := by
        rw [hWn]; congr 1; ext; simp; omega
      have e2 : Wn k = W (⟨k, hk⟩ : Fin a).castSucc := by
        rw [hWn]; congr 1; ext; simp; omega
      rw [e1, e2, hstep ⟨k, hk⟩, hjn, dif_pos hk]
    · have e : Wn (k + 1) = Wn k := by
        rw [hWn, hWn]; congr 1; ext; simp; omega
      rw [e, hjn, dif_neg hk, Nat.add_zero]
  obtain ⟨W', hW'm, hW'r, hW'p, hW'l⟩ := exists_refine_nat Wn jn P hWn0 hWnm hWns hP0 hPs a
  have hlast : W' (P a) = W (Fin.last a) := by
    rw [hW'l _ le_rfl, ← hWi (Fin.last a), Fin.val_last]
  have hβ : ∀ l : Fin (P a), ∃! i : Fin a, P i ≤ l ∧ (l : ℕ) < P (i + 1) := by
    intro l
    have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha; have := l.isLt; omega
      · exact ha
    have hla : (l : ℕ) < P (a - 1 + 1) := by rw [show a - 1 + 1 = a by omega]; exact l.isLt
    have hex : ∃ m, (l : ℕ) < P (m + 1) := ⟨a - 1, hla⟩
    have hma : Nat.find hex < a := by
      have hle : Nat.find hex ≤ a - 1 := Nat.find_min' hex hla
      omega
    refine ⟨⟨Nat.find hex, hma⟩, ⟨?_, Nat.find_spec hex⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · simp only [h, hP0]; exact Nat.zero_le _
      · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
        rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
        simpa using this
    · rintro i ⟨hi1, hi2⟩
      apply Fin.ext
      show (i : ℕ) = Nat.find hex
      rcases lt_trichotomy (i : ℕ) (Nat.find hex) with h | h | h
      · exact absurd hi2 (not_lt.2 ((hPm (by omega : (i : ℕ) + 1 ≤ Nat.find hex)).trans
          (by
            rcases Nat.eq_zero_or_pos (Nat.find hex) with h' | h'
            · omega
            · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
              rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
              omega)))
      · exact h
      · exact absurd (Nat.find_spec hex) (not_lt.2 ((hPm (by omega : Nat.find hex + 1 ≤ (i : ℕ))).trans hi1))
  have hPle : ∀ i : Fin (a + 1), P i < P a + 1 := fun i => Nat.lt_succ_of_le (hPm (Nat.le_of_lt_succ i.isLt))
  refine ⟨P a, fun l => W' l, fun l => Classical.choose (hβ l), fun i => ⟨P i, hPle i⟩, ⟨?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_⟩
  · show W' ((0 : Fin (P a + 1)) : ℕ) = ⊥
    rw [Fin.val_zero]
    exact Submodule.finrank_eq_zero.1 (hW'r 0 (Nat.zero_le _))
  · intro x y hxy
    exact hW'm (Fin.le_iff_val_le_val.1 hxy)
  · intro i
    show Module.finrank ℂ (W' ((i.succ : Fin (P a + 1)) : ℕ)) = Module.finrank ℂ (W' ((i.castSucc : Fin (P a + 1)) : ℕ)) + 1
    rw [Fin.val_succ, Fin.coe_castSucc, hW'r _ (by omega), hW'r _ (by omega)]
  · intro x hx y hy
    have e : W' ((Fin.last (P a) : Fin (P a + 1)) : ℕ) = W (Fin.last a) := by rw [Fin.val_last, hlast]
    exact hiso x (e ▸ hx) y (e ▸ hy)
  · intro i
    show W' (P i) = W i
    rw [hW'p i (Nat.le_of_lt_succ i.isLt), hWi]
  · show W' ((Fin.last (P a) : Fin (P a + 1)) : ℕ) = W (Fin.last a)
    rw [Fin.val_last, hlast]
  · intro l i
    have hs := Classical.choose_spec (hβ l)
    constructor
    · rintro rfl
      refine ⟨Fin.le_iff_val_le_val.2 ?_, Fin.lt_iff_val_lt_val.2 ?_⟩
      · simpa using hs.1.1
      · simpa using hs.1.2
    · rintro ⟨h1, h2⟩
      refine (hs.2 i ⟨?_, ?_⟩).symm
      · simpa using Fin.le_iff_val_le_val.1 h1
      · simpa using Fin.lt_iff_val_lt_val.1 h2
  · intro i
    show P i = _
    rw [hP, Finset.sum_filter]
    have e1 : ∀ l : Fin a, (if (l : ℕ) < (i : ℕ) then j l else 0) =
        (fun k => if k < (i : ℕ) then jn k else 0) (l : ℕ) := by
      intro l; simp [hjn, l.isLt]
    rw [Finset.sum_congr rfl (fun l _ => e1 l), Fin.sum_univ_eq_sum_range (fun k => if k < (i : ℕ) then jn k else 0) a,
      ← Finset.sum_filter]
    congr 1
    ext k; simp; omega

end GlobalTheory.RealInd.Stages
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refine_isotropic_flag : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}, IsIsoFlag ε j W → ∃ (b : ℕ) (W' : Flag n b) (β : Fin b → Fin a) (p : Fin (a + 1) → Fin (b + 1)), IsIsoFlag ε (fun _ => 1) W' ∧ (∀ i, W' (p i) = W i) ∧ W' (Fin.last b) = W (Fin.last a) ∧ (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) ∧ ∀ i, (p i : ℕ) = ∑ l ∈ univ.filter (fun l : Fin a => (l : ℕ) < (i : ℕ)), j l := by
  atlas_forward_decl GlobalTheory.RealInd.Stages.exists_refine_isIsoFlag
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem keeps_of_refine {n a b : ℕ} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a}
    {p : Fin (a + 1) → Fin (b + 1)} (hW' : Monotone W') (hp : ∀ i, W' (p i) = W i)
    (hl : W' (Fin.last b) = W (Fin.last a))
    (hβ : ∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ)
    {g : Matrix (Fin n) (Fin n) ℂ} {c : Fin a → ℂ}
    (hstep : ∀ i : Fin a, ∀ y ∈ W i.succ, g *ᵥ y - c i • y ∈ W i.castSucc)
    (hlast : ∀ y ∈ W (Fin.last a), g *ᵥ y ∈ W (Fin.last a)) :
    ∀ l, ∀ y ∈ W' l, g *ᵥ y ∈ W' l := by
  intro l
  induction l using Fin.lastCases with
  | last => rw [hl]; exact hlast
  | cast l =>
    intro y hy
    obtain ⟨h1, h2⟩ := (hβ l (β l)).1 rfl
    have hy' : y ∈ W (β l).succ := by
      rw [← hp]; exact hW' h2.le hy
    have hs : g *ᵥ y - c (β l) • y ∈ W' l.castSucc := hW' h1 ((hp _).symm ▸ hstep _ y hy')
    have := (W' _).add_mem hs ((W' _).smul_mem (c (β l)) hy)
    rwa [sub_add_cancel] at this

theorem isSplit_of_refine {n a b : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} {W' : Flag n b}
    {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)} (hW : IsIsoFlag ε j W)
    (hW' : IsIsoFlag ε (fun _ => 1) W') (hp : ∀ i, W' (p i) = W i) (hl : W' (Fin.last b) = W (Fin.last a))
    (hβ : ∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) {x : Fin a → ℝ} {t : UJ ε}
    (ht : IsSplit ε W x t) : IsSplit ε W' (x ∘ β) t := by
  have k1 := keeps_of_refine hW'.2.1 hp hl hβ ht.2.1 (fun y hy => (ht.1 _ y hy).1)
  have ht' := ht.opp hW
  have hoM : Monotone (opp ε W') := fun _ _ h => Submodule.map_mono (hW'.2.1 h)
  have k2 := keeps_of_refine (W := opp ε W) (W' := opp ε W') hoM
    (fun i => congrArg (fun V => V.map (Jm ε).mulVecLin) (hp i))
    (congrArg (fun V => V.map (Jm ε).mulVecLin) hl) hβ ht'.2.1 (fun y hy => (ht'.1 _ y hy).1)
  refine ⟨fun l y hy => ⟨k1 l y hy, ?_⟩, fun l y hy => ?_, ?_⟩
  · have hJ : (uMat t)ᴴ = Jm ε * uMat t⁻¹ * Jm ε := by
      rw [mul_assoc, inv_mul_Jm, ← mul_assoc, Jm_mul_self, one_mul]
    have hi := GlobalTheory.FlagLeviGroup.inv_keeps (GlobalTheory.FlagLeviGroup.uMat_inv_mul t) _ (k2 l)
    obtain ⟨z, hz, e⟩ := hi _ ⟨y, hy, rfl⟩
    rw [mulVecLin_apply, mulVecLin_apply] at e
    rw [hJ, ← mulVec_mulVec, ← mulVec_mulVec, ← e, mulVec_mulVec, Jm_mul_self, one_mulVec]
    exact hz
  · obtain ⟨h1, h2⟩ := (hβ l (β l)).1 rfl
    have hy' : y ∈ W (β l).succ := by
      rw [← hp]; exact hW'.2.1 (Fin.castSucc_lt_iff_succ_le.1 h2) hy
    have hs := ht.2.1 (β l) y hy'
    rw [← hp] at hs
    exact hW'.2.1 h1 hs
  · rw [hl]; exact ht.2.2

end GlobalTheory.RealInd.Stages
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_torus_refined_flag : ∀ {n a b : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)}, IsIsoFlag ε j W → IsIsoFlag ε (fun _ => 1) W' → (∀ i, W' (p i) = W i) → W' (Fin.last b) = W (Fin.last a) → (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) → ∀ {x : Fin a → ℝ} {t : UJ ε}, IsSplit ε W x t → IsSplit ε W' (x ∘ β) t := by
  atlas_forward_decl GlobalTheory.RealInd.Stages.isSplit_of_refine
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd

theorem isSplit_commute_flagM : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}, IsIsoFlag ε j W →
    ∀ {x : Fin a → ℝ} {t : UJ ε}, IsSplit ε W x t → ∀ m ∈ flagM ε W, m * t = t * m := by
  intro n a ε j W hW x t ht m hm
  have hmi : m⁻¹ ∈ flagM ε W := (GlobalTheory.FlagLeviGroup.leviSub ε W).inv_mem hm
  have hmul : ∀ g h : UJ ε, uMat (g * h) = uMat g * uMat h := fun _ _ => rfl
  have hmm : uMat m * uMat m⁻¹ = 1 := by rw [← hmul, mul_inv_cancel]; rfl
  have hJ : (uMat m)ᴴ * Jm ε = Jm ε * uMat m⁻¹ := by
    have hg : (uMat m)ᴴ * Jm ε * uMat m = Jm ε := m.2
    calc (uMat m)ᴴ * Jm ε = (uMat m)ᴴ * Jm ε * (uMat m * uMat m⁻¹) := by rw [hmm, Matrix.mul_one]
      _ = Jm ε * uMat m⁻¹ := by rw [← Matrix.mul_assoc, hg]
  have hmy : ∀ y, uMat m *ᵥ (uMat m⁻¹ *ᵥ y) = y := fun y => by rw [mulVec_mulVec, hmm, one_mulVec]
  have key : ∀ y, uMat (m * t * m⁻¹) *ᵥ y = uMat m *ᵥ (uMat t *ᵥ (uMat m⁻¹ *ᵥ y)) := fun y => by
    rw [hmul, hmul, mulVec_mulVec, mulVec_mulVec]
  have hs : IsSplit ε W x (m * t * m⁻¹) := by
    refine ⟨(GlobalTheory.FlagLeviGroup.leviSub ε W).mul_mem ((GlobalTheory.FlagLeviGroup.leviSub ε W).mul_mem hm ht.1) hmi,
      fun i y hy => ?_, fun y hy => ?_⟩
    · have h1 := ht.2.1 i _ (hmi _ y hy).1
      have h2 := (hm _ _ h1).1
      convert h2 using 1
      rw [key, mulVec_sub, mulVec_smul, hmy]
    · have hy' : ∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ (uMat m⁻¹ *ᵥ y)) = 0 := fun z hz => by
        rw [mulVec_mulVec, ← hJ, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
        exact hy _ (hm _ z hz).1
      have h2 := (hm _ _ (ht.2.2 _ hy')).1
      convert h2 using 1
      rw [key, mulVec_sub, hmy]
  have := (existsUnique_isSplit hW x).unique hs ht
  calc m * t = m * t * m⁻¹ * m := by group
    _ = t * m := by rw [this]

end GlobalTheory.RealInd
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_commutes_split_torus : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}, IsIsoFlag ε j W → ∀ {x : Fin a → ℝ} {t : UJ ε}, IsSplit ε W x t → ∀ m ∈ flagM ε W, m * t = t * m := by
  atlas_forward_decl GlobalTheory.RealInd.isSplit_commute_flagM
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.BlockSum

theorem detOn_prefix {n b : ℕ} {ε : Fin n → Bool} {W' : Flag n b}
    (hW : IsIsoFlag ε (fun _ => 1) W') {x : Fin b → ℝ} {t : UJ ε} (ht : IsSplit ε W' x t) (m : Fin (b + 1)) :
    detOn (uMat t) (W' m) = Real.exp (∑ l with l.castSucc < m, x l) := by
  induction m using Fin.induction with
  | zero => simp [hW.1, detOn_bot, Fin.not_lt_zero]
  | succ m ih =>
    rw [ht.detOn_succ hW m, ih, ← Real.exp_add]
    congr 1
    have e1 : (Finset.univ.filter fun l : Fin b => l.castSucc < m.succ) = Iic m := by
      ext l; simp [Fin.castSucc_lt_succ_iff]
    have e2 : (Finset.univ.filter fun l : Fin b => l.castSucc < m.castSucc) = Iio m := by
      ext l; simp
    rw [e1, e2, ← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    simp [add_comm]

theorem blockSum_eq_zero : ∀ {n a b : ℕ} {ε : Fin n → Bool} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a}
    {p : Fin (a + 1) → Fin (b + 1)}, IsIsoFlag ε (fun _ => 1) W' → (∀ i, W' (p i) = W i) →
    (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) →
    ∀ {x : Fin b → ℝ} {t : UJ ε}, IsSplit ε W' x t → t ∈ leviOne ε W → ∀ i, ∑ l with β l = i, x l = 0 := by
  intro n a b ε W W' β p hW hp hβ x t ht hl i
  have hS : ∀ k : Fin (a + 1), ∑ l with l.castSucc < p k, x l = 0 := fun k => by
    have h1 := hl.2 k
    rw [← hp k, detOn_prefix hW ht] at h1
    exact Real.exp_eq_one_iff _ |>.1 h1
  set A := p i.castSucc
  set B := p i.succ
  have hblk : (Finset.univ.filter fun l : Fin b => β l = i) =
      ((Finset.univ.filter fun l : Fin b => l.castSucc < B).filter fun l => ¬ l.castSucc < A) := by
    ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hβ, not_lt]; tauto
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter fun l : Fin b => l.castSucc < B) (fun l => l.castSucc < A) x
  rw [hS i.succ, ← hblk] at hsplit
  have h0 : ∑ l ∈ (Finset.univ.filter fun l : Fin b => l.castSucc < B).filter (fun l => l.castSucc < A), x l = 0 := by
    rw [Finset.filter_filter]
    rcases le_total A B with h | h
    · have : (Finset.univ.filter fun l : Fin b => l.castSucc < B ∧ l.castSucc < A) =
          Finset.univ.filter fun l : Fin b => l.castSucc < A := by
        ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h' => h'.2, fun h' => ⟨lt_of_lt_of_le h' h, h'⟩⟩
      rw [this]; exact hS i.castSucc
    · have : (Finset.univ.filter fun l : Fin b => l.castSucc < B ∧ l.castSucc < A) =
          Finset.univ.filter fun l : Fin b => l.castSucc < B := by
        ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h' => h'.1, fun h' => ⟨h', lt_of_lt_of_le h' h⟩⟩
      rw [this]; exact hS i.succ
  linarith

end GlobalTheory.RealInd.BlockSum
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_torus_levi_sum_vanishes : ∀ {n a b : ℕ} {ε : Fin n → Bool} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)}, IsIsoFlag ε (fun _ => 1) W' → (∀ i, W' (p i) = W i) → (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) → ∀ {x : Fin b → ℝ} {t : UJ ε}, IsSplit ε W' x t → t ∈ leviOne ε W → ∀ i, ∑ l with β l = i, x l = 0 := by
  atlas_forward_decl GlobalTheory.RealInd.BlockSum.blockSum_eq_zero
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages.UnipConj

variable {n : ℕ} {ε : Fin n → Bool}

private lemma unitaryMatrix_mul_inv_eq_one (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← show uMat (g * g⁻¹) = uMat g * uMat g⁻¹ from rfl, mul_inv_cancel]
  rfl

private lemma unitaryMatrix_inv_eq_conj_transpose (g : Formalism.REAL.UJ ε) :
    uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
  have hf : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : (Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε) * uMat g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat g)ᴴ, hf,
      Formalism.REAL.Jm_mul_self]
  calc uMat g⁻¹
      = ((Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε) * uMat g) * uMat g⁻¹ := by
        rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, unitaryMatrix_mul_inv_eq_one, Matrix.mul_one]

theorem conj_mem_flagN {a : ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (m : Formalism.REAL.UJ ε) (hm : m ∈ flagM ε W) (u : Formalism.REAL.UJ ε) (hu : u ∈ flagN ε W) :
    m * u * m⁻¹ ∈ flagN ε W := by
  have hmk : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i := fun i y hy => (hm i y hy).1
  have hmik : ∀ i, ∀ y ∈ W i, uMat m⁻¹ *ᵥ y ∈ W i := fun i =>
    UnipRad.inv_keeps m (W i) (hmk i)
  have key : ∀ y : Fin n → ℂ, uMat (m * u * m⁻¹) *ᵥ y - y =
      uMat m *ᵥ (uMat u *ᵥ (uMat m⁻¹ *ᵥ y) - uMat m⁻¹ *ᵥ y) := by
    intro y
    have e := unitaryMatrix_mul_inv_eq_one m
    rw [show uMat (m * u * m⁻¹) = uMat m * uMat u * uMat m⁻¹ from rfl]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, e, Matrix.one_mulVec, Matrix.mul_assoc]
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · rw [key]
    exact hmk _ _ (hu.1 i _ (hmik _ _ hy))
  · rw [key]
    refine hmk _ _ (hu.2 _ fun x hx => ?_)
    have hx' := hmk _ x hx
    have h0 := hy _ hx'
    rw [unitaryMatrix_inv_eq_conj_transpose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec _ (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε),
      Formalism.REAL.Jm_mul_self, Matrix.one_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    exact h0

theorem flagN_le_refine {a b : ℕ} {W : Flag n a} {W' : Flag n b} (hW' : Monotone W')
    {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)} (hp : ∀ i, W' (p i) = W i)
    (hlast : W' (Fin.last b) = W (Fin.last a))
    (hβ : ∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ)
    (g : Formalism.REAL.UJ ε) (hg : g ∈ flagN ε W) : g ∈ flagN ε W' := by
  refine ⟨fun l y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨h1, h2⟩ := (hβ l (β l)).1 rfl
    have hs : l.succ ≤ p (β l).succ := by
      rw [Fin.le_def]; rw [Fin.lt_def] at h2; simp only [Fin.val_succ, Fin.coe_castSucc] at h2 ⊢; omega
    have hy' : y ∈ W (β l).succ := by rw [← hp]; exact hW' hs hy
    have := hg.1 (β l) y hy'
    rw [← hp] at this
    exact hW' h1 this
  · rw [hlast] at hy ⊢
    exact hg.2 y hy

end GlobalTheory.RealInd.Stages.UnipConj

theorem GlobalTheory.RealInd.Stages.unip_conj_refine : ∀ {n a b : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)}, IsIsoFlag ε j W → IsIsoFlag ε (fun _ => 1) W' → (∀ i, W' (p i) = W i) → W' (Fin.last b) = W (Fin.last a) → (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) → ∀ m ∈ flagM ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W' := by
  intro n a b ε j W W' β p hW hW' hp hlast hβ m hm u hu
  exact GlobalTheory.RealInd.Stages.UnipConj.flagN_le_refine hW'.2.1 hp hlast hβ _
    (GlobalTheory.RealInd.Stages.UnipConj.conj_mem_flagN m hm u hu)
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_conjugates_unipotent_refined : ∀ {n a b : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)}, IsIsoFlag ε j W → IsIsoFlag ε (fun _ => 1) W' → (∀ i, W' (p i) = W i) → W' (Fin.last b) = W (Fin.last a) → (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) → ∀ m ∈ flagM ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W' := by
  atlas_forward_decl GlobalTheory.RealInd.Stages.unip_conj_refine
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RhoSum

theorem rho_one_eq {b : ℕ} (n : ℕ) (l : Fin b) :
    rho n (fun _ => 1) l = (n : ℂ) - 2 * (l : ℕ) - 1 := by
  simp [rho, Fin.card_Iio]

theorem sum_range_aff (n P j : ℕ) :
    ∑ m ∈ range j, ((n : ℂ) - 2 * ((P + m : ℕ) : ℂ) - 1) = (j : ℂ) * ((n : ℂ) - 2 * P - j) := by
  induction j with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

theorem filter_lt_eq_Iio {a : ℕ} (i : Fin a) :
    univ.filter (fun l : Fin a => (l : ℕ) < (i.castSucc : ℕ)) = Iio i := by
  ext l
  rw [mem_filter, mem_Iio, Fin.coe_castSucc, Fin.lt_iff_val_lt_val]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

theorem filter_lt_succ {a : ℕ} (i : Fin a) :
    univ.filter (fun l : Fin a => (l : ℕ) < (i.succ : ℕ)) = insert i (Iio i) := by
  ext l
  rw [mem_filter, mem_insert, mem_Iio, Fin.val_succ, Fin.lt_iff_val_lt_val, Fin.ext_iff]
  constructor
  · rintro ⟨-, h⟩; omega
  · intro h; exact ⟨mem_univ _, by omega⟩

theorem card_and_rho_sum : ∀ {a b : ℕ} (n : ℕ) (j : Fin a → ℕ) {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)}, (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) → (∀ i, (p i : ℕ) = ∑ l ∈ univ.filter (fun l : Fin a => (l : ℕ) < (i : ℕ)), j l) → ∀ i, #{l | β l = i} = j i ∧ ∑ l with β l = i, rho n (fun _ => 1) l = (j i : ℂ) * rho n j i := by
  intro a b n j β p hβ hp i
  set P : ℕ := (p i.castSucc : ℕ) with hP
  set Q : ℕ := (p i.succ : ℕ) with hQ
  have hPsum : (P : ℂ) = ∑ l ∈ Iio i, (j l : ℂ) := by
    rw [hP, hp, filter_lt_eq_Iio]; push_cast; rfl
  have hQP : Q = P + j i := by
    rw [hQ, hP, hp, hp, filter_lt_succ, filter_lt_eq_Iio, sum_insert (by simp), add_comm]
  have hQb : Q ≤ b := Nat.lt_succ_iff.mp (p i.succ).isLt
  have hmap : (univ.filter (fun l => β l = i)).map Fin.valEmbedding = Ico P (P + j i) := by
    ext x
    rw [mem_map, mem_Ico]
    constructor
    · rintro ⟨l, hl, rfl⟩
      rw [mem_filter, hβ, Fin.le_iff_val_le_val, Fin.lt_iff_val_lt_val, Fin.coe_castSucc] at hl
      simp only [Fin.valEmbedding_apply]
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x, by omega⟩, ?_, rfl⟩
      rw [mem_filter, hβ, Fin.le_iff_val_le_val, Fin.lt_iff_val_lt_val, Fin.coe_castSucc]
      exact ⟨mem_univ _, by simp only; omega, by simp only; omega⟩
  constructor
  · rw [← card_map Fin.valEmbedding, hmap, Nat.card_Ico]; omega
  · have : ∑ l with β l = i, rho n (fun _ => 1) l
        = ∑ x ∈ (univ.filter (fun l => β l = i)).map Fin.valEmbedding, ((n : ℂ) - 2 * (x : ℂ) - 1) := by
      rw [sum_map]; exact sum_congr rfl fun l _ => rho_one_eq n l
    rw [this, hmap, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, sum_range_aff, rho, hPsum]
end GlobalTheory.RhoSum
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refined_flag_half_sum_of_roots : ∀ {a b : ℕ} (n : ℕ) (j : Fin a → ℕ) {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)}, (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) → (∀ i, (p i : ℕ) = ∑ l ∈ univ.filter (fun l : Fin a => (l : ℕ) < (i : ℕ)), j l) → ∀ i, #{l | β l = i} = j i ∧ ∑ l with β l = i, rho n (fun _ => 1) l = (j i : ℂ) * rho n j i := by
  atlas_forward_decl GlobalTheory.RhoSum.card_and_rho_sum
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem restr_mem_indFun_stage : ∀ {n a b : ℕ} {ε : Fin n → Bool} {W : Flag n a} {W' : Flag n b} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (s' : Fin b → ℂ) (y : Fin b → ℝ), (∀ x t, IsSplit ε W' x t → t ∈ leviOne ε W → pairing (fun _ => 1) s' x = pairing (fun _ => 1) (fun l => Complex.I * y l) x) → ∀ {F : UJ ε → U}, F ∈ indFun ⊤ (fun _ => 1) W' τ s' → ∀ g, restr (leviOne ε W) F g ∈ indFun (leviOne ε W) (fun _ => 1) W' τ (fun l => Complex.I * y l) := by
  intro n a b ε W W' U _ _ τ s' y hs F hF g
  rw [mem_indFun_top] at hF
  obtain ⟨hc, hlaw⟩ := hF
  refine ⟨?_, fun g' hg' => restr_of_not_mem F g hg', ?_⟩
  · exact ((hc.comp (continuous_mul_const g)).continuousOn).congr fun m hm => restr_of_mem F g hm
  · intro u hu m hm x t ht h1 h2 h3 g' hg'
    have hM : u * m * t * g' ∈ leviOne ε W :=
      (leviOne ε W).mul_mem ((leviOne ε W).mul_mem ((leviOne ε W).mul_mem h1 h2) h3) hg'
    rw [restr_of_mem F g hM, restr_of_mem F g hg', mul_assoc (u * m * t) g' g, hlaw u hu m hm x t ht]
    congr 2
    have e : ∀ s r : Fin b → ℂ, pairing (fun _ => 1) (s + r) x =
        pairing (fun _ => 1) s x + pairing (fun _ => 1) r x := by
      intro s r
      simp only [pairing, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    rw [e, e, hs x t ht h3]

end GlobalTheory.RealInd.Stages
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induction_in_stages_restriction : ∀ {n a b : ℕ} {ε : Fin n → Bool} {W : Flag n a} {W' : Flag n b} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (s' : Fin b → ℂ) (y : Fin b → ℝ), (∀ x t, IsSplit ε W' x t → t ∈ leviOne ε W → pairing (fun _ => 1) s' x = pairing (fun _ => 1) (fun l => Complex.I * y l) x) → ∀ {F : UJ ε → U}, F ∈ indFun ⊤ (fun _ => 1) W' τ s' → ∀ g, restr (leviOne ε W) F g ∈ indFun (leviOne ε W) (fun _ => 1) W' τ (fun l => Complex.I * y l) := by
  atlas_forward_decl GlobalTheory.RealInd.Stages.restr_mem_indFun_stage
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem stageFun_continuous : ∀ {n : ℕ} {ε : Fin n → Bool} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (M : Subgroup (UJ ε)) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V) (μ : Measure ↥(KG ε ⊓ M)) [IsProbabilityMeasure μ], (∀ f : Fsp, ‖ι f‖ ^ 2 = ∫ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ∂μ) → ∀ {F : UJ ε → U}, Continuous F → (∀ g, restr M F g ∈ Fsp) → Continuous (stageFun M Fsp ι F) := by
  intro n ε U V _ _ _ _ M Fsp ι μ _ hnorm F hF hmem

  let Φ : C(UJ ε, C(KG ε, U)) :=
    ContinuousMap.curry ⟨fun p : UJ ε × KG ε => F ((p.2 : UJ ε) * p.1), by fun_prop⟩
  have hΦ : ∀ g (k : KG ε), Φ g k = F ((k : UJ ε) * g) := fun g k => rfl
  have key : ∀ g g₀, ‖stageFun M Fsp ι F g - stageFun M Fsp ι F g₀‖ ≤ ‖Φ g - Φ g₀‖ := by
    intro g g₀
    rw [stageFun_of_mem ι (hmem g), stageFun_of_mem ι (hmem g₀), ← map_sub]
    set f : Fsp := (⟨_, hmem g⟩ - ⟨_, hmem g₀⟩ : Fsp) with hf
    set C := ‖Φ g - Φ g₀‖
    have hC : 0 ≤ C := norm_nonneg _
    have hpt : ∀ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ≤ C ^ 2 := by
      intro k
      have hkM : (k : UJ ε) ∈ M := (Subgroup.mem_inf.1 k.2).2
      have hkK : (k : UJ ε) ∈ KG ε := (Subgroup.mem_inf.1 k.2).1
      have : f.1 k = (Φ g - Φ g₀) ⟨k, hkK⟩ := by
        simp only [hf, Submodule.coe_sub, Pi.sub_apply, ContinuousMap.sub_apply, hΦ,
          restr_of_mem _ _ hkM]
      rw [this]
      exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousMap.norm_coe_le_norm _ _) 2
    have hint : ∫ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ∂μ ≤ C ^ 2 := by
      have h1 := norm_integral_le_of_norm_le_const (μ := μ) (f := fun k => ‖f.1 k‖ ^ 2) (C := C ^ 2)
        (Filter.Eventually.of_forall fun k => by
          rw [Real.norm_of_nonneg (by positivity)]; exact hpt k)
      simp at h1
      exact (le_abs_self _).trans h1
    have h3 : ‖ι f‖ ^ 2 ≤ C ^ 2 := (hnorm f).symm ▸ hint
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hC two_ne_zero).1 h3
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun g => key g g₀) ?_
  have : Filter.Tendsto (fun g => Φ g - Φ g₀) (nhds g₀) (nhds 0) := by
    simpa using ((Φ.continuous.tendsto g₀).sub_const (Φ g₀))
  simpa using this.norm

end GlobalTheory.RealInd.Stages
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stage_function_continuous : ∀ {n : ℕ} {ε : Fin n → Bool} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (M : Subgroup (UJ ε)) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V) (μ : Measure ↥(KG ε ⊓ M)) [IsProbabilityMeasure μ], (∀ f : Fsp, ‖ι f‖ ^ 2 = ∫ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ∂μ) → ∀ {F : UJ ε → U}, Continuous F → (∀ g, restr M F g ∈ Fsp) → Continuous (stageFun M Fsp ι F) := by
  atlas_forward_decl GlobalTheory.RealInd.Stages.stageFun_continuous
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem stageFun_law : ∀ {n a b : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (s : Fin a → ℂ) (s' : Fin b → ℂ) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V), (∀ m ∈ leviOne ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W') → (∀ x t, IsSplit ε W x t → IsSplit ε W' (x ∘ β) t ∧ ∀ m ∈ leviOne ε W, m * t = t * m) → (∀ v, τ 1 v = v) → (∀ x : Fin a → ℝ, pairing (fun _ => 1) (s' + rho n fun _ => 1) (x ∘ β) = pairing j (s + rho n j) x) → (∀ y ∈ leviOne ε W, ∀ f f' : Fsp, (∀ g, f'.1 g = f.1 (g * y)) → σ (uMat y) (ι f) = ι f') → ∀ {F : UJ ε → U}, F ∈ indFun ⊤ (fun _ => 1) W' τ s' → (∀ g, restr (leviOne ε W) F g ∈ Fsp) → ∀ u ∈ flagN ε W, ∀ m ∈ leviOne ε W, ∀ x t, IsSplit ε W x t → ∀ g, stageFun (leviOne ε W) Fsp ι F (u * m * t * g) = Complex.exp (pairing j (s + rho n j) x) • σ (uMat m) (stageFun (leviOne ε W) Fsp ι F g) := by
  intro n a b ε j W W' β U V _ _ _ _ τ σ s s' Fsp ι hconj hsplit hτ hpair htrans F hF hmem u hu m hm x t ht g
  set M := leviOne ε W with hM
  have uMat_one : uMat (1 : UJ ε) = 1 := rfl
  have hlaw := (mem_indFun_top.1 hF).2
  have h1N : (1 : UJ ε) ∈ flagN ε W' := ⟨fun i y _ => by simp [uMat_one], fun y _ => by simp [uMat_one]⟩

  have hN : ∀ u' ∈ flagN ε W', ∀ h, F (u' * h) = F h := fun u' hu' h => by
    have := hlaw u' hu' 1 (leviOne ε W').one_mem 0 1 isSplit_one h
    simpa [uMat_one, hτ, pairing] using this
  obtain ⟨ht', hcomm⟩ := hsplit x t ht
  have hA : ∀ h, F (t * h) = Complex.exp (pairing j (s + rho n j) x) • F h := fun h => by
    have := hlaw 1 h1N 1 (leviOne ε W').one_mem (x ∘ β) t ht' h
    simpa [uMat_one, hτ, hpair] using this
  have hr : restr M F (u * m * t * g) = Complex.exp (pairing j (s + rho n j) x) • restr M F (m * g) := by
    funext m'
    by_cases hm' : m' ∈ M
    · rw [Pi.smul_apply, restr_of_mem _ _ hm', restr_of_mem _ _ hm']
      have e1 : m' * (u * m * t * g) = (m' * u * m'⁻¹) * (t * ((m' * m) * g)) := by
        rw [← mul_assoc t, ← hcomm _ (M.mul_mem hm' hm)]; group
      rw [e1, hN _ (hconj m' hm' u hu), hA, mul_assoc]
    · rw [Pi.smul_apply, restr_of_not_mem _ _ hm', restr_of_not_mem _ _ hm', smul_zero]
  have hr2 : ∀ h, restr M F (m * g) h = restr M F g (h * m) := fun h => by
    by_cases hh : h ∈ M
    · rw [restr_of_mem _ _ hh, restr_of_mem _ _ (M.mul_mem hh hm), mul_assoc]
    · rw [restr_of_not_mem _ _ hh, restr_of_not_mem _ _ (fun e => hh (by simpa using M.mul_mem e (M.inv_mem hm)))]
  rw [stageFun_of_mem ι (hmem g), stageFun_of_mem ι (hmem _)]
  have e2 : (⟨restr M F (u * m * t * g), hmem _⟩ : Fsp) = Complex.exp (pairing j (s + rho n j) x) • ⟨restr M F (m * g), hmem _⟩ :=
    Subtype.ext hr
  rw [e2, map_smul, htrans m hm ⟨_, hmem g⟩ ⟨_, hmem (m * g)⟩ hr2]

end GlobalTheory.RealInd.Stages
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induction_in_stages_intertwining : ∀ {n a b : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (s : Fin a → ℂ) (s' : Fin b → ℂ) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V), (∀ m ∈ leviOne ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W') → (∀ x t, IsSplit ε W x t → IsSplit ε W' (x ∘ β) t ∧ ∀ m ∈ leviOne ε W, m * t = t * m) → (∀ v, τ 1 v = v) → (∀ x : Fin a → ℝ, pairing (fun _ => 1) (s' + rho n fun _ => 1) (x ∘ β) = pairing j (s + rho n j) x) → (∀ y ∈ leviOne ε W, ∀ f f' : Fsp, (∀ g, f'.1 g = f.1 (g * y)) → σ (uMat y) (ι f) = ι f') → ∀ {F : UJ ε → U}, F ∈ indFun ⊤ (fun _ => 1) W' τ s' → (∀ g, restr (leviOne ε W) F g ∈ Fsp) → ∀ u ∈ flagN ε W, ∀ m ∈ leviOne ε W, ∀ x t, IsSplit ε W x t → ∀ g, stageFun (leviOne ε W) Fsp ι F (u * m * t * g) = Complex.exp (pairing j (s + rho n j) x) • σ (uMat m) (stageFun (leviOne ε W) Fsp ι F g) := by
  atlas_forward_decl GlobalTheory.RealInd.Stages.stageFun_law
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem stageFun_normSq_integral : ∀ {n : ℕ} {ε : Fin n → Bool} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (M : Subgroup (UJ ε)) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V) (μ : Measure ↥(KG ε ⊓ M)) [IsProbabilityMeasure μ], (∀ f : Fsp, ‖ι f‖ ^ 2 = ∫ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ∂μ) → ∀ {F : UJ ε → U}, Continuous F → (∀ g, restr M F g ∈ Fsp) → ∫ k : KG ε, ‖stageFun M Fsp ι F k‖ ^ 2 ∂muK ε = ∫ k : KG ε, ‖F k‖ ^ 2 ∂muK ε := by
  intro n ε U V _ _ _ _ M Fsp ι μ _ hnorm F hFc hF

  have h1 : ∀ k : KG ε, ‖stageFun M Fsp ι F k‖ ^ 2 = ∫ c : ↥(KG ε ⊓ M), ‖F ((c : UJ ε) * (k : UJ ε))‖ ^ 2 ∂μ := by
    intro k
    rw [stageFun_of_mem ι (hF k), hnorm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only
    rw [restr_of_mem F (k : UJ ε) (Subgroup.mem_inf.1 c.2).2]
  simp_rw [h1]

  have hKc : Continuous fun k : KG ε => F (k : UJ ε) := hFc.comp continuous_subtype_val
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hKc.continuousOn
  have hint : Integrable (Function.uncurry fun (k : KG ε) (c : ↥(KG ε ⊓ M)) => ‖F ((c : UJ ε) * (k : UJ ε))‖ ^ 2)
      ((muK ε).prod μ) := by
    refine Integrable.of_bound (C := C ^ 2) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      refine (continuous_norm.comp (hFc.comp ?_)).pow 2
      exact (continuous_subtype_val.comp continuous_snd).mul (continuous_subtype_val.comp continuous_fst)
    · refine Filter.Eventually.of_forall fun p => ?_
      have hp : (p.2 : UJ ε) * (p.1 : UJ ε) ∈ KG ε := mul_mem (Subgroup.mem_inf.1 p.2.2).1 p.1.2
      have hb := hC (⟨_, hp⟩ : KG ε) (Set.mem_univ _)
      simp only [Function.uncurry, Real.norm_eq_abs, abs_pow, abs_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [integral_integral_swap hint]
  have h3 : ∀ c : ↥(KG ε ⊓ M), ∫ k : KG ε, ‖F ((c : UJ ε) * (k : UJ ε))‖ ^ 2 ∂muK ε =
      ∫ k : KG ε, ‖F k‖ ^ 2 ∂muK ε := by
    intro c
    exact integral_mul_left_eq_self (μ := muK ε) (fun k : KG ε => ‖F (k : UJ ε)‖ ^ 2)
      (⟨c, (Subgroup.mem_inf.1 c.2).1⟩ : KG ε)
  simp_rw [h3]
  simp

end GlobalTheory.RealInd.Stages
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stage_function_norm_integral : ∀ {n : ℕ} {ε : Fin n → Bool} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (M : Subgroup (UJ ε)) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V) (μ : Measure ↥(KG ε ⊓ M)) [IsProbabilityMeasure μ], (∀ f : Fsp, ‖ι f‖ ^ 2 = ∫ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ∂μ) → ∀ {F : UJ ε → U}, Continuous F → (∀ g, restr M F g ∈ Fsp) → ∫ k : KG ε, ‖stageFun M Fsp ι F k‖ ^ 2 ∂muK ε = ∫ k : KG ε, ‖F k‖ ^ 2 ∂muK ε := by
  atlas_forward_decl GlobalTheory.RealInd.Stages.stageFun_normSq_integral
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem stageS_pairings : ∀ {a b : ℕ} (n : ℕ) (j : Fin a → ℕ) (β : Fin b → Fin a) (s : Fin a → ℂ) (y : Fin b → ℝ), (∀ i, 1 ≤ j i) → (∀ i, #{l | β l = i} = j i) → (∀ i, ∑ l with β l = i, rho n (fun _ => 1) l = (j i : ℂ) * rho n j i) → (∀ x : Fin a → ℝ, pairing (fun _ => 1) (stageS j β s y + rho n fun _ => 1) (x ∘ β) = pairing j (s + rho n j) x) ∧ ∀ x : Fin b → ℝ, (∀ i, ∑ l with β l = i, x l = 0) → pairing (fun _ => 1) (stageS j β s y) x = pairing (fun _ => 1) (fun l => Complex.I * y l) x := by
  intro a b n j β s y hj hcard hrho
  have hsum : ∀ i, ∑ l with β l = i, stageS j β s y l = (j i : ℂ) * s i := by
    intro i
    have hj0 : (j i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hj i; omega)
    have h1 : ∀ l ∈ ({l | β l = i} : Finset (Fin b)),
        stageS j β s y l = s i + Complex.I * ((y l - blockMean j β y i : ℝ) : ℂ) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp [stageS, hl]
    have h2 : ∑ l with β l = i, ((y l - blockMean j β y i : ℝ) : ℂ) = 0 := by
      rw [← Complex.ofReal_sum, Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, blockMean]
      rw [mul_div_cancel₀ _ hj0, sub_self, Complex.ofReal_zero]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, h2, Finset.sum_const, hcard,
      nsmul_eq_mul]
    ring
  constructor
  · intro x
    simp only [pairing, Nat.cast_one, one_mul, Pi.add_apply, Function.comp_apply]
    rw [← Finset.sum_fiberwise Finset.univ β]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h3 : ∀ l ∈ ({l | β l = i} : Finset (Fin b)),
        (stageS j β s y l + rho n (fun _ => 1) l) * (x (β l) : ℂ)
          = (stageS j β s y l + rho n (fun _ => 1) l) * (x i : ℂ) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      rw [hl]
    rw [Finset.sum_congr rfl h3, ← Finset.sum_mul, Finset.sum_add_distrib, hsum, hrho]
    ring
  · intro x hx
    simp only [pairing, Nat.cast_one, one_mul]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← Finset.sum_fiberwise Finset.univ β]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h4 : ∀ l ∈ ({l | β l = i} : Finset (Fin b)),
        stageS j β s y l * (x l : ℂ) - Complex.I * (y l : ℂ) * (x l : ℂ)
          = (s i - Complex.I * (blockMean j β y i : ℂ)) * (x l : ℂ) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp only [stageS, hl]
      push_cast
      ring
    rw [Finset.sum_congr rfl h4, ← Finset.mul_sum, ← Complex.ofReal_sum, hx i]
    simp

end GlobalTheory.RealInd.Stages
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stage_parameter_pairing_shift : ∀ {a b : ℕ} (n : ℕ) (j : Fin a → ℕ) (β : Fin b → Fin a) (s : Fin a → ℂ) (y : Fin b → ℝ), (∀ i, 1 ≤ j i) → (∀ i, #{l | β l = i} = j i) → (∀ i, ∑ l with β l = i, rho n (fun _ => 1) l = (j i : ℂ) * rho n j i) → (∀ x : Fin a → ℝ, pairing (fun _ => 1) (stageS j β s y + rho n fun _ => 1) (x ∘ β) = pairing j (s + rho n j) x) ∧ ∀ x : Fin b → ℝ, (∀ i, ∑ l with β l = i, x l = 0) → pairing (fun _ => 1) (stageS j β s y) x = pairing (fun _ => 1) (fun l => Complex.I * y l) x := by
  atlas_forward_decl GlobalTheory.RealInd.Stages.stageS_pairings
end

section
section
noncomputable section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem isKFin_map {n : ℕ} (ε : Fin n → Bool) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (T : H' →ₗᵢ[ℂ] H)
    (hT : ∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w)) {v : H'} (hv : IsKFin ε ρ' v) :
    IsKFin ε ρ (T v) := by
  obtain ⟨S, hS, hvS, hK⟩ := hv
  refine ⟨S.map T.toLinearMap, inferInstance, ⟨v, hvS, rfl⟩, ?_⟩
  rintro g hg _ ⟨w, hw, rfl⟩
  have hu : gᴴ * Jm ε * g = Jm ε := by
    rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.1 hg.1, Matrix.one_mul]
  obtain ⟨y, rfl, -⟩ := GlobalTheory.RealIwasawa.exists_uMat g hu
  exact ⟨_, hK _ hg w hw, hT y w⟩

end GlobalTheory.RealInd.Stages

namespace GlobalTheory.RealInd.Stages

theorem exists_stage {n : ℕ} {ε : Fin n → Bool} (I : IndModule ε) (h : 0 < I.a)
    (hTL : GlobalTheory.Published.Langlands.TemperedLevi) :
    ∃ (I' : IndModule ε) (h' : 0 < I'.a), I'.j ⟨0, h'⟩ = 1 ∧ (I'.s ⟨0, h'⟩).re = (I.s ⟨0, h⟩).re ∧
      ∃ T : I'.H →ₗᵢ[ℂ] I.H, ∀ (g : UJ ε) (w : I'.H), T (I'.ρ (uMat g) w) = I.ρ (uMat g) (T w) := by
  obtain ⟨b, W', β, p, hW', hp, hl, hβ, hpos⟩ := GlobalTheory.T.refine_isotropic_flag I.flag
  have h6 := GlobalTheory.T.refined_flag_half_sum_of_roots n I.j hβ hpos
  have hp0 : p 0 = 0 := Fin.ext (by rw [hpos]; simp)
  have hb : 0 < b := by
    have := (h6 ⟨0, h⟩).1
    have h1 := I.pos ⟨0, h⟩
    have h2 : #{l | β l = ⟨0, h⟩} ≤ b := (card_filter_le _ _).trans (by simp)
    omega
  have hβ0 : β ⟨0, hb⟩ = ⟨0, h⟩ := by
    refine (hβ _ _).2 ⟨?_, ?_⟩
    · rw [show (⟨0, h⟩ : Fin I.a).castSucc = 0 from rfl, hp0]; exact Fin.zero_le _
    · obtain ⟨l, hl0⟩ : (univ.filter (fun l => β l = ⟨0, h⟩)).Nonempty := by
        rw [← card_pos, (h6 ⟨0, h⟩).1]; exact I.pos _
      have := ((hβ l ⟨0, h⟩).1 (mem_filter.1 hl0).2).2
      rw [Fin.lt_iff_val_lt_val] at this ⊢
      simp only [Fin.coe_castSucc] at this ⊢
      omega
  obtain ⟨U, _, _, _, τ, y, hτ, hμ⟩ := hTL n ε I.toDatum b W' hW' (fun i => ⟨p i, hp i⟩) hl
  have hKM : IsCompact ((KG ε : Set (UJ ε)) ∩ (I.M : Set (UJ ε))) :=
    (isCompact_iff_compactSpace.2 (instCompactKG n ε)).inter_right (isClosed_leviOne I.flag I.pos)
  haveI : CompactSpace ↥(KG ε ⊓ I.M) := isCompact_iff_compactSpace.1 hKM
  let μ : Measure ↥(KG ε ⊓ I.M) := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  obtain ⟨ι, hι⟩ := hμ μ inferInstance inferInstance
  set s' := stageS I.j β I.s y with hs'def
  obtain ⟨H', _, _, _, ρ', ι', hm'⟩ := exists_isIndModel (σ := τ) hW' (fun _ => le_rfl)
    (fun m hm => hτ.2.2.1.2.1 _ ⟨m, hm, rfl⟩) s'
  let D' : Datum ε :=
    { a := b
      j := fun _ => 1
      W := W'
      flag := hW'
      pos := fun _ => le_rfl
      V := U
      σ := τ
      temp := hτ
      s := s' }
  let I' : IndModule ε := { D' with H := H', ρ := ρ', ι := ι', model := hm' }
  have h9 := GlobalTheory.T.stage_parameter_pairing_shift n I.j β I.s y I.pos (fun i => (h6 i).1) (fun i => (h6 i).2)
  have hs : ∀ x t, IsSplit ε W' x t → t ∈ leviOne ε I.W →
      pairing (fun _ => 1) s' x = pairing (fun _ => 1) (fun l => Complex.I * y l) x :=
    fun x t ht hm => h9.2 x (GlobalTheory.T.split_torus_levi_sum_vanishes hW' hp hβ ht hm)
  have h1 : ∀ v, τ 1 v = v := fun v => by
    rw [hτ.2.2.1.1.1]; rfl
  have hmem : ∀ F ∈ I'.fns, ∀ g, restr I.M F g ∈ indFun I.M (fun _ => 1) W' τ (fun l => Complex.I * y l) := fun F hF g => GlobalTheory.T.induction_in_stages_restriction τ s' y hs hF g
  have hcont : ∀ F ∈ I'.fns, Continuous F := fun F hF => (mem_indFun_top.1 hF).1
  have hΦ : ∀ F ∈ I'.fns, stageFun I.M _ ι F ∈ I.fns := fun F hF => mem_indFun_top.2
    ⟨GlobalTheory.T.stage_function_continuous I.M _ ι μ hι.norm_sq (hcont F hF) (hmem F hF),
     GlobalTheory.T.induction_in_stages_intertwining τ I.σ I.s s' _ ι (fun m hm u hu => GlobalTheory.T.levi_conjugates_unipotent_refined I.flag hW' hp hl hβ m hm.1 u hu)
      (fun x t ht => ⟨GlobalTheory.T.split_torus_refined_flag I.flag hW' hp hl hβ ht, fun m hm => GlobalTheory.T.levi_commutes_split_torus I.flag ht m hm.1⟩) h1 h9.1 hι.transl hF
      (hmem F hF)⟩
  let Φ : I'.fns →ₗ[ℂ] I.fns :=
    { toFun := fun F => ⟨stageFun I.M _ ι F.1, hΦ F.1 F.2⟩
      map_add' := fun F G => Subtype.ext (funext fun g => by
        change stageFun I.M _ ι (F.1 + G.1) g = stageFun I.M _ ι F.1 g + stageFun I.M _ ι G.1 g
        rw [stageFun_of_mem ι (hmem _ (I'.fns.add_mem F.2 G.2) g), stageFun_of_mem ι (hmem _ F.2 g),
          stageFun_of_mem ι (hmem _ G.2 g), ← map_add]
        exact congrArg ι (Subtype.ext (funext fun m => by
          by_cases hm : m ∈ I.M <;> simp [restr, hm])))
      map_smul' := fun c F => Subtype.ext (funext fun g => by
        change stageFun I.M _ ι (c • F.1) g = c • stageFun I.M _ ι F.1 g
        rw [stageFun_of_mem ι (hmem _ (I'.fns.smul_mem c F.2) g), stageFun_of_mem ι (hmem _ F.2 g), ← map_smul]
        exact congrArg ι (Subtype.ext (funext fun m => by
          by_cases hm : m ∈ I.M <;> simp [restr, hm]))) }
  have hnorm : ∀ F : I'.fns, ‖I.ι (Φ F)‖ = ‖ι' F‖ := fun F =>
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by
      rw [I.model.norm_sq, hm'.norm_sq]
      exact GlobalTheory.T.stage_function_norm_integral I.M _ ι μ hι.norm_sq (hcont _ F.2) (hmem _ F.2))
  have hΦtr : ∀ (F : I'.fns) (g : UJ ε),
      (Φ ⟨fun g' => F.1 (g' * g), indFun_mul_right F.2 trivial⟩).1 = fun g' => (Φ F).1 (g' * g) := fun F g =>
    funext fun g' => by
      change stageFun I.M _ ι (fun g' => F.1 (g' * g)) g' = stageFun I.M _ ι F.1 (g' * g)
      have : restr I.M (fun g' => F.1 (g' * g)) g' = restr I.M F.1 (g' * g) := funext fun m => by
        simp only [restr, mul_assoc]
      unfold stageFun
      rw [this]
  have hbd : ∃ C, ∀ F, ‖(I.ι ∘ₗ Φ) F‖ ≤ C * ‖ι' F‖ := ⟨1, fun F => by rw [one_mul]; exact (hnorm F).le⟩
  let T₀ := (I.ι ∘ₗ Φ).extendOfNorm ι'
  have hT₀ : ∀ F, T₀ (ι' F) = I.ι (Φ F) := LinearMap.extendOfNorm_eq hm'.dense hbd
  have hiso : ∀ v, ‖T₀ v‖ = ‖v‖ := fun v =>
    hm'.dense.induction_on v (isClosed_eq (by fun_prop) (by fun_prop)) fun F => by rw [hT₀]; exact hnorm F
  refine ⟨I', hb, rfl, ?_, ⟨T₀.toLinearMap, hiso⟩, fun g w => ?_⟩
  · change (s' ⟨0, hb⟩).re = _
    simp [hs'def, stageS, hβ0]
  · change T₀ (ρ' (uMat g) w) = I.ρ (uMat g) (T₀ w)
    refine hm'.dense.induction_on w (isClosed_eq (by fun_prop) (by fun_prop)) fun F => ?_
    rw [hm'.transl g trivial F ⟨_, indFun_mul_right F.2 trivial⟩ (fun _ => rfl), hT₀, hT₀]
    exact (I.model.transl g trivial (Φ F) _ (fun g' => congrFun (hΦtr F g) g')).symm

end GlobalTheory.RealInd.Stages

namespace GlobalTheory.RealInd.Stages

theorem exists_first_step_one : GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a) (χ : Fin n → ℂ), (∀ (k : ℕ) v, IsKFin ε I.ρ v → ∃ N : ℕ, actU ε I.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) → ∃ (I' : IndModule ε) (h' : 0 < I'.a), I'.j ⟨0, h'⟩ = 1 ∧ (I'.s ⟨0, h'⟩).re = (I.s ⟨0, h⟩).re ∧ (∀ (k : ℕ) v, IsKFin ε I'.ρ v → ∃ N : ℕ, actU ε I'.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) := by
  intro hLC n ε I h χ hI
  obtain ⟨I', h', hj, hre, T, hT⟩ := exists_stage I h hLC.2.2.2.2.2.2
  refine ⟨I', h', hj, hre, fun k v hv => ?_⟩
  obtain ⟨N, hN⟩ := hI k (T v) (isKFin_map ε _ _ T hT hv)
  exact ⟨N, T.injective (by rw [← GlobalTheory.T.isometry_intertwines_enveloping ε _ _ T hT, hN, map_zero])⟩

end GlobalTheory.RealInd.Stages

end
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_induced_module_shift : GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a) (χ : Fin n → ℂ), (∀ (k : ℕ) v, IsKFin ε I.ρ v → ∃ N : ℕ, actU ε I.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) → ∃ (I' : IndModule ε) (h' : 0 < I'.a), I'.j ⟨0, h'⟩ = 1 ∧ (I'.s ⟨0, h'⟩).re = (I.s ⟨0, h⟩).re ∧ (∀ (k : ℕ) v, IsKFin ε I'.ρ v → ∃ N : ℕ, actU ε I'.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) := by
  atlas_forward_decl GlobalTheory.RealInd.Stages.exists_first_step_one
end
