import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatPowDvdPerPowMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTower
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtaleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MittagLefflerImageBreuilKisinModPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentCoefficientsAinfModPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisOfEtaleInvariantBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescendRightInverseStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeApproximationMittagLefflerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosed

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.TransLim

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), IsUnit T0 → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∃ Y : ∀ n, Matrix (Fin (tw.d' n)) (Fin (tw.d' (n + 1))) bk.S, ∀ n i j, (l : WCb l) ^ n ∣ (R n * (Y n).map bk.evW - R (n + 1)) i j := by
  intro l _ K bk τ hτ d N ρ tw F T0 R hT0 hR
  have key : ∀ n, ∃ Y : Matrix (Fin (tw.d' n)) (Fin (tw.d' (n + 1))) bk.S,
      (F n).T * Y.map bk.evW = zW (tw.f n) * (F (n + 1)).T := fun n =>
    GlobalTheory.T.exists_equivariantMap_breuilKisinMatrix l K bk τ hτ N N (tw.d' (n + 1)) (tw.d' n) (fun g => (tw.ρ' (n + 1) g).val)
      (fun g => (tw.ρ' n g).val) (F (n + 1)) (F n) (tw.f n) (tw.f_equi n)
  choose Y hY using key
  refine ⟨Y, fun n => ?_⟩
  let π : WCb l →+* WCb l ⧸ Ideal.span {(l : WCb l) ^ n} := Ideal.Quotient.mk _
  have hz : ∀ {a b : ℕ} (M M' : Matrix (Fin a) (Fin b) (WCb l)),
      (∀ i j, (l : WCb l) ^ n ∣ (M - M') i j) ↔ M.map π = M'.map π := by
    intro a b M M'
    constructor
    · intro h
      ext i j
      simp only [Matrix.map_apply]
      rw [← sub_eq_zero, ← map_sub]
      exact (Ideal.Quotient.eq_zero_iff_dvd _ _).2 (by simpa [Matrix.sub_apply] using h i j)
    · intro h i j
      rw [Matrix.sub_apply]
      refine (Ideal.Quotient.eq_zero_iff_dvd _ _).1 ?_
      rw [map_sub, sub_eq_zero]
      exact congrFun (congrFun h i) j
  have hA : (zW (tw.Pi n)).map π * (F n).T.map π = T0.map π * (R n).map π := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]; exact (hz _ _).1 (hR n)
  have hD : (zW (tw.Pi (n + 1))).map π * (F (n + 1)).T.map π = T0.map π * (R (n + 1)).map π := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    refine (hz _ _).1 fun i j => ?_
    exact dvd_trans (pow_dvd_pow _ (Nat.le_succ n)) (hR (n + 1) i j)
  have hB : (F n).T.map π * ((Y n).map bk.evW).map π = (zW (tw.f n)).map π * (F (n + 1)).T.map π := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hY n]
  have hC : (zW (tw.Pi n)).map π * (zW (tw.f n)).map π = (zW (tw.Pi (n + 1))).map π := by
    rw [← Matrix.map_mul]
    refine (hz _ _).1 fun i j => ?_
    have h1 := map_dvd (algebraMap ℤ_[l] (WCb l)) (tw.f_Pi n i j)
    simp only [map_pow, map_natCast] at h1
    convert h1 using 1
    simp [zW, Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, map_sum, map_mul]
  obtain ⟨u, hu⟩ := hT0
  have hinv : ((u⁻¹ : (Matrix (Fin d) (Fin d) (WCb l))ˣ) : Matrix (Fin d) (Fin d) (WCb l)).map π * T0.map π = 1 := by
    rw [← Matrix.map_mul, ← hu, Units.inv_mul, Matrix.map_one _ (map_zero π) (map_one π)]
  have hE : T0.map π * ((R n).map π * ((Y n).map bk.evW).map π) = T0.map π * (R (n + 1)).map π := by
    rw [← Matrix.mul_assoc, ← hA, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hC, hD]
  have hF : (R n).map π * ((Y n).map bk.evW).map π = (R (n + 1)).map π := by
    have := congrArg (fun M => ((u⁻¹ : (Matrix (Fin d) (Fin d) (WCb l))ˣ) : Matrix (Fin d) (Fin d) (WCb l)).map π * M) hE
    simpa only [← Matrix.mul_assoc, hinv, Matrix.one_mul] using this
  rw [← Matrix.map_mul] at hF
  exact (hz _ _).2 hF

end GlobalTheory.BKLim.TransLim
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approximatingLattices_transitionMatrix_modPow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), IsUnit T0 → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∃ Y : ∀ n, Matrix (Fin (tw.d' n)) (Fin (tw.d' (n + 1))) bk.S, ∀ n i j, (l : WCb l) ^ n ∣ (R n * (Y n).map bk.evW - R (n + 1)) i j := by
  atlas_forward_decl GlobalTheory.BKLim.TransLim.main
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.BKLim.limvec_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, R n i j ∈ bk.OE) → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v) := by
  intro l _ K bk τ hτ d N ρ tw F T0 R hR hF v hv
  have hcl := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  have hevW : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  have key : ∀ (k : ℕ) (z : WCb l), (l : WCb l) ^ k ∣ z ↔
      Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ k}) z = 0 := fun k z => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨fun i => ?_, ?_⟩
  · apply hcl.2.1
    intro n
    obtain ⟨s', hs'⟩ := hv n
    refine ⟨(R n *ᵥ fun j => bk.evW (s' j)) i, ?_, hs' i⟩
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hR n i j) (hevW _)
  · have hinc : ∀ x : ℤ_[l], inclW l (algebraMap ℤ_[l] (Ainf l) x) = algebraMap ℤ_[l] (WCb l) x :=
      fun x => (inclWA l).commutes x
    have hx : ∀ i k, ∃ a : Ainf l, (l : WCb l) ^ k ∣
        (l : WCb l) ^ 0 * (inclW l τ ^ N • (T0 *ᵥ v)) i - inclW l (1 * a) := by
      intro i k
      obtain ⟨s', hs'⟩ := hv k
      obtain ⟨Y, Y', hY, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N (tw.d' k) (fun g => (tw.ρ' k g).val) (F k)
      refine ⟨(((tw.Pi k).map (algebraMap ℤ_[l] (Ainf l)) * Y) *ᵥ fun j => bk.ev (s' j)) i, ?_⟩
      set q := Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ k}) with hq
      rw [key, pow_zero, one_mul, one_mul, map_sub, sub_eq_zero]
      have h1 : (fun i => q (v i)) = fun i => q ((R k *ᵥ fun j => bk.evW (s' j)) i) := funext fun i => by
        have := (key k _).1 (hs' i); rwa [Pi.sub_apply, map_sub, sub_eq_zero] at this
      have h2 : (zW (tw.Pi k) * (F k).T).map q = (T0 * R k).map q := by
        ext i j; have := (key k _).1 (hF k i j); rwa [Matrix.sub_apply, map_sub, sub_eq_zero] at this
      have e1 : inclW l ((((tw.Pi k).map (algebraMap ℤ_[l] (Ainf l)) * Y) *ᵥ fun j => bk.ev (s' j)) i) =
          (inclW l τ ^ N • ((zW (tw.Pi k) * (F k).T) *ᵥ fun j => bk.evW (s' j))) i := by
        rw [RingHom.map_mulVec, Matrix.map_mul, hY, Matrix.map_map]
        have : (tw.Pi k).map ((inclW l) ∘ (algebraMap ℤ_[l] (Ainf l))) = zW (tw.Pi k) := by
          ext a b; simp [zW, hinc]
        rw [this, Matrix.mul_smul, Matrix.smul_mulVec]
        rfl
      rw [e1, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
        RingHom.map_mulVec, RingHom.map_mulVec, h2, Matrix.map_mul, ← Matrix.mulVec_mulVec]
      have h1' : (⇑q ∘ v) = (R k).map q *ᵥ (⇑q ∘ fun j => bk.evW (s' j)) := funext fun j => by
        rw [Function.comp_apply, ← RingHom.map_mulVec]; exact congrFun h1 j
      rw [h1']
    refine ⟨fun i => Classical.choose (GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) 0 _ (hx i)), funext fun i => ?_⟩
    have := Classical.choose_spec (GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) 0 _ (hx i))
    rw [one_mul] at this
    exact this.symm
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitVector_mem_OE_and_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, R n i j ∈ bk.OE) → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v) := by
  first | (exact @GlobalTheory.BKLim.limvec_mem) | (exact GlobalTheory.BKLim.limvec_mem) | (intros; apply GlobalTheory.BKLim.limvec_mem  <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 4000000 in
theorem GlobalTheory.LimVec.invertible_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)), (∀ n, ∃ R' : Matrix (Fin (d' n)) (Fin d) (WCb l), (∀ i j, R' i j ∈ bk.OE) ∧ ∀ i j, (l : WCb l) ^ n ∣ (R n * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ n i j, R n i j ∈ bk.OE) → ∃ V V' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, V i j ∈ bk.OE) ∧ (∀ i j, V' i j ∈ bk.OE) ∧ V * V' = 1 ∧ ∀ j k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ ((fun i => V i j) - R k *ᵥ fun a => bk.evW (s' a)) i := by
  intro l _ K bk d d' R h1 h2 h3
  have lnu : ¬ IsUnit ((l : ℕ) : WCb l) := by
    intro h
    obtain ⟨u, hu⟩ := h
    have h1 := congrArg (fun x : WCb l => x.coeff 0) u.mul_inv
    simp only [WittVector.mul_coeff_zero, WittVector.one_coeff_zero] at h1
    rw [hu, WittVector.coeff_p_zero, zero_mul] at h1
    exact zero_ne_one h1
  have evW_mem : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  obtain ⟨hOEsat, ⟨wX, -, hwX⟩, -, hOEdec, -⟩ := GlobalTheory.T.integral_elements_unit_factorization l K bk
  obtain ⟨-, hOEcl, -⟩ := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  have cU : IsUnit (bk.evW X) := ⟨⟨_, wX, hwX, by rw [mul_comm]; exact hwX⟩, rfl⟩
  set π := Ideal.Quotient.mk (Ideal.span {((l : ℕ) : WCb l)}) with hπ
  have hdvd : ∀ x : WCb l, ((l : ℕ) : WCb l) ∣ x ↔ π x = 0 := fun x => by
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have πl : π ((l : ℕ) : WCb l) = 0 := (hdvd _).1 dvd_rfl
  have hdvd' : ∀ x y : WCb l, ((l : ℕ) : WCb l) ∣ x - y → π x = π y := fun x y h => by
    rw [← sub_eq_zero, ← map_sub]; exact (hdvd _).1 h
  obtain ⟨m, hm1, hm⟩ := h2 1
  obtain ⟨R', hR'OE, hRR'⟩ := h1 m
  choose k s y hk using fun a j => hR'OE a j 1
  set N := Finset.univ.sup (fun p : Fin (d' m) × Fin d => k p.1 p.2) with hN
  have hkN : ∀ a j, k a j ≤ N := fun a j =>
    Finset.le_sup (f := fun p : Fin (d' m) × Fin d => k p.1 p.2) (Finset.mem_univ (a, j))
  let σ : Fin (d' m) → Fin d → bk.S := fun a j => X ^ (N - k a j) * s a j
  have hσ : ∀ a j, π (bk.evW (σ a j)) = π (bk.evW X ^ N * R' a j) := by
    intro a j
    have e : bk.evW X ^ N * R' a j = bk.evW (σ a j) + (l : WCb l) * (bk.evW X ^ (N - k a j) * y a j) := by
      have hk' := hk a j
      rw [pow_one] at hk'
      have hp : bk.evW X ^ N = bk.evW X ^ (N - k a j) * bk.evW X ^ k a j := by
        rw [← pow_add, Nat.sub_add_cancel (hkN a j)]
      simp only [σ, map_mul, map_pow]
      rw [hp, mul_assoc, hk']
      ring
    rw [e, map_add, (hdvd _).1 (dvd_mul_right _ _), add_zero]
  choose v hv1 hvlim using fun j => hm (fun a => σ a j)
  let V : Matrix (Fin d) (Fin d) (WCb l) := Matrix.of fun i j => v j i
  have hVmem : ∀ i j, V i j ∈ bk.OE := by
    intro i j
    apply hOEcl
    intro n
    obtain ⟨s', hs'⟩ := hvlim j n
    refine ⟨(R n *ᵥ fun a => bk.evW (s' a)) i, ?_, hs' i⟩
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun a _ => Subring.mul_mem _ (h3 n i a) (evW_mem _)
  have hπV : π.mapMatrix V = π (bk.evW X ^ N) • (1 : Matrix (Fin d) (Fin d) (WCb l ⧸ Ideal.span {((l : ℕ) : WCb l)})) := by
    ext i j
    have e1 := hdvd' _ _ (by simpa [pow_one] using hv1 j i)
    have e2 : π ((R m * R') i j) = π ((1 : Matrix (Fin d) (Fin d) (WCb l)) i j) :=
      hdvd' _ _ (dvd_trans (dvd_pow_self ((l : ℕ) : WCb l) (show m ≠ 0 by omega)) (by simpa [Matrix.sub_apply] using hRR' i j))
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, V, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [e1]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hσ]
    rw [Matrix.mul_apply] at e2
    rw [map_sum] at e2
    simp only [map_mul] at e2
    calc ∑ x, π (R m i x) * (π (bk.evW X ^ N) * π (R' x j)) = π (bk.evW X ^ N) * ∑ x, π (R m i x) * π (R' x j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      _ = _ := by
          rw [e2]
          by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hdet : π V.det = π ((bk.evW X ^ N) ^ d) := by
    rw [RingHom.map_det, hπV, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    simp only [map_pow]
  have ndvd : ¬ ((l : ℕ) : WCb l) ∣ V.det := by
    intro h
    rw [hdvd, hdet, ← hdvd] at h
    obtain ⟨a, ha⟩ := h
    exact lnu (isUnit_of_mul_isUnit_left (ha ▸ (cU.pow N).pow d))
  let V0 : Matrix (Fin d) (Fin d) ↥bk.OE := Matrix.of fun i j => ⟨V i j, hVmem i j⟩
  have hV0 : bk.OE.subtype.mapMatrix V0 = V := by ext i j; rfl
  have hdetmem : V.det ∈ bk.OE := by
    rw [← hV0, ← RingHom.map_det]; exact (V0.det).2
  have hadj : ∀ i j, V.adjugate i j ∈ bk.OE := by
    intro i j
    rw [← hV0, ← RingHom.map_adjugate]; exact (V0.adjugate i j).2
  have hne : V.det ≠ 0 := fun h => ndvd (h ▸ dvd_zero _)
  obtain ⟨e, u, u', hu, hu', huu', hdec⟩ := hOEdec _ hdetmem hne
  have he : e = 0 := by
    by_contra he
    apply ndvd
    rw [hdec]
    obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
    exact Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero _)) _
  rw [he, pow_zero, one_mul] at hdec
  refine ⟨V, u' • V.adjugate, hVmem, fun i j => ?_, ?_, fun j k' => hvlim j k'⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]; exact Subring.mul_mem _ hu' (hadj i j)
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, hdec, smul_smul, mul_comm, huu', one_smul]
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitVectors_invertible_basis_over_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)), (∀ n, ∃ R' : Matrix (Fin (d' n)) (Fin d) (WCb l), (∀ i j, R' i j ∈ bk.OE) ∧ ∀ i j, (l : WCb l) ^ n ∣ (R n * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ n i j, R n i j ∈ bk.OE) → ∃ V V' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, V i j ∈ bk.OE) ∧ (∀ i j, V' i j ∈ bk.OE) ∧ V * V' = 1 ∧ ∀ j k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ ((fun i => V i j) - R k *ᵥ fun a => bk.evW (s' a)) i := by
  first | (exact @GlobalTheory.LimVec.invertible_basis) | (exact GlobalTheory.LimVec.invertible_basis) | (intros; apply GlobalTheory.LimVec.invertible_basis  <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000

namespace GlobalTheory.BKLim.SatLat

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (T0 V V' : Matrix (Fin d) (Fin d) (WCb l)) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit T0 → (∀ i j, V i j ∈ bk.OE) → (∀ i j, V' i j ∈ bk.OE) → V * V' = 1 → Y1.map (inclW l) = inclW l τ ^ N • (T0 * V) → ∃ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Wm Wm' : Matrix (Fin d) (Fin d) (WCb l)), IsUnit (Y.map (inclW l)) ∧ (∀ i j, Wm i j ∈ bk.OE) ∧ (∀ i j, Wm' i j ∈ bk.OE) ∧ Wm * Wm' = 1 ∧ Y.map (inclW l) = inclW l τ ^ N • (T0 * Wm) ∧ ∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a) := by
  intro l _ K bk τ hτ d N T0 V V' Y1 hT0 hV hV' hVV' hY1
  classical
  obtain ⟨htu, -, -, -⟩ := GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ
  have hOEcl := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) (WCb l), M = inclW l τ ^ N • T0 := ⟨_, rfl⟩
  have hMu : IsUnit M.det := by
    rw [hM, Matrix.det_smul]
    exact ((htu.pow N).pow _).mul ((Matrix.isUnit_iff_isUnit_det T0).1 hT0)
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMu
  have hMM' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hMu
  have hVu : IsUnit V.det := by
    have h : V.det * V'.det = 1 := by rw [← Matrix.det_mul, hVV', Matrix.det_one]
    exact ⟨⟨V.det, V'.det, h, by rw [mul_comm]; exact h⟩, rfl⟩
  let ι : (Fin d → Ainf l) → (Fin d → WCb l) := fun y a => inclW l (y a)
  have hιmul : ∀ (A : Matrix (Fin d) (Fin d) (Ainf l)) (v : Fin d → Ainf l),
      ι (A *ᵥ v) = A.map (inclW l) *ᵥ ι v := by
    intro A v; funext i; simp [ι, Matrix.mulVec, dotProduct, map_sum]
  have hevW : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  have hevWι : ∀ c : Fin d → bk.S, ι (fun a => bk.ev (c a)) = fun a => bk.evW (c a) := fun c => rfl
  let mem : (Fin d → Ainf l) → Prop := fun y => ∀ i, (M⁻¹ *ᵥ ι y) i ∈ bk.OE
  have hY1M : Y1.map (inclW l) = M * V := by rw [hY1, hM, Matrix.smul_mul]
  have hmemV : ∀ c : Fin d → bk.S, mem (Y1 *ᵥ fun a => bk.ev (c a)) := by
    intro c i
    show (M⁻¹ *ᵥ ι (Y1 *ᵥ fun a => bk.ev (c a))) i ∈ bk.OE
    rw [hιmul, hevWι, hY1M, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hMM', Matrix.one_mul]
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hV i j) (hevW _)
  obtain ⟨Y, hYu, hYmem⟩ := GlobalTheory.T.ainf_closed_membership_limit l K bk d mem
    (fun i => by
      show (M⁻¹ *ᵥ ι 0) i ∈ bk.OE
      have : ι 0 = 0 := by funext a; simp [ι]
      rw [this, Matrix.mulVec_zero]; exact Subring.zero_mem _)
    (fun y z hy hz i => by
      show (M⁻¹ *ᵥ ι (y + z)) i ∈ bk.OE
      have : ι (y + z) = ι y + ι z := by funext a; simp [ι]
      rw [this, Matrix.mulVec_add]; exact Subring.add_mem _ (hy i) (hz i))
    (fun c y hy i => by
      show (M⁻¹ *ᵥ ι (fun a => bk.ev c * y a)) i ∈ bk.OE
      have : ι (fun a => bk.ev c * y a) = bk.evW c • ι y := by funext a; simp [ι, BK.evW]
      rw [this, Matrix.mulVec_smul]; exact Subring.mul_mem _ (hevW c) (hy i))
    (fun y hy i => by
      have h : (M⁻¹ *ᵥ ι (fun a => (l : Ainf l) * y a)) i ∈ bk.OE := hy i
      have : ι (fun a => (l : Ainf l) * y a) = ((l : ℕ) : WCb l) • ι y := by funext a; simp [ι]
      rw [this, Matrix.mulVec_smul] at h
      exact hOEcl.1 _ h)
    (fun y hy _ z hz i => by
      refine hOEcl.2.1 _ fun n => ⟨_, hy n i, ?_⟩
      rw [← Pi.sub_apply, ← Matrix.mulVec_sub]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.dvd_sum fun j _ => Dvd.dvd.mul_left ?_ _
      have := map_dvd (inclW l) (hz n j)
      simpa [ι, map_sub, map_pow, map_natCast] using this)
    Y1 M (by rw [hY1M, Matrix.det_mul]; exact (hMu.mul hVu).ne_zero)
    ((Matrix.isUnit_iff_isUnit_det M).2 hMu) hmemV
    (fun y hy => by
      refine ⟨M⁻¹ *ᵥ ι y, hy, ?_⟩
      show ι y = M *ᵥ (M⁻¹ *ᵥ ι y)
      rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec])
  obtain ⟨Wm, hWm⟩ : ∃ Wm : Matrix (Fin d) (Fin d) (WCb l), Wm = M⁻¹ * Y.map (inclW l) := ⟨_, rfl⟩
  have hYWm : Y.map (inclW l) = M * Wm := by rw [hWm, ← Matrix.mul_assoc, hMM, Matrix.one_mul]
  have hcol : ∀ (A : Matrix (Fin d) (Fin d) (Ainf l)) (j : Fin d),
      (A *ᵥ fun a => bk.ev ((Pi.single j (1 : bk.S) : Fin d → bk.S) a)) = fun i => A i j := by
    intro A j; funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hWmOE : ∀ i j, Wm i j ∈ bk.OE := by
    intro i j
    have h : (M⁻¹ *ᵥ ι (fun a => Y a j)) i ∈ bk.OE := (hYmem (fun a => Y a j)).2 ⟨Pi.single j (1 : bk.S), (hcol Y j).symm⟩ i
    rw [hWm]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, ι] using h
  have hC : ∀ j, ∃ c : Fin d → bk.S, (fun i => Y1 i j) = Y *ᵥ fun a => bk.ev (c a) := fun j =>
    (hYmem _).1 (by rw [← hcol Y1 j]; exact hmemV _)
  choose c hc using hC
  obtain ⟨Cw, hCw⟩ : ∃ Cw : Matrix (Fin d) (Fin d) (WCb l), Cw = Matrix.of fun a j => bk.evW (c j a) := ⟨_, rfl⟩
  have hVW : V = Wm * Cw := by
    have h1 : Y1.map (inclW l) = Y.map (inclW l) * Cw := by
      refine Matrix.ext fun i j => ?_
      have := congrArg (fun v => inclW l (v i)) (hc j)
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hCw, BK.evW, map_sum] using this
    rw [hY1M, hYWm, Matrix.mul_assoc] at h1
    have h2 := congrArg (HMul.hMul M⁻¹) h1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMM', Matrix.one_mul, Matrix.one_mul] at h2
    exact h2
  refine ⟨Y, Wm, Cw * V', hYu, hWmOE, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [Matrix.mul_apply, hCw, Matrix.of_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hevW _) (hV' k j)
  · rw [← Matrix.mul_assoc, ← hVW, hVV']
  · rw [hYWm, hM, Matrix.smul_mul]
  · rintro y ⟨w, hw, hyw⟩
    refine (hYmem y).1 ?_
    intro i
    have : ι y = M *ᵥ w := by
      rw [hM]; refine hyw.trans ?_; funext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    show (M⁻¹ *ᵥ ι y) i ∈ bk.OE
    rw [this, Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec]; exact hw i

end GlobalTheory.BKLim.SatLat
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.saturatedAinfLattice_free_over_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (T0 V V' : Matrix (Fin d) (Fin d) (WCb l)) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit T0 → (∀ i j, V i j ∈ bk.OE) → (∀ i j, V' i j ∈ bk.OE) → V * V' = 1 → Y1.map (inclW l) = inclW l τ ^ N • (T0 * V) → ∃ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Wm Wm' : Matrix (Fin d) (Fin d) (WCb l)), IsUnit (Y.map (inclW l)) ∧ (∀ i j, Wm i j ∈ bk.OE) ∧ (∀ i j, Wm' i j ∈ bk.OE) ∧ Wm * Wm' = 1 ∧ Y.map (inclW l) = inclW l τ ^ N • (T0 * Wm) ∧ ∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a) := by
  first | (exact @GlobalTheory.BKLim.SatLat.main) | (exact GlobalTheory.BKLim.SatLat.main) | (intros; apply GlobalTheory.BKLim.SatLat.main  <;> assumption)
end

section
universe u_1 u_2 u_3

namespace GlobalTheory.DvdSubMapMk

theorem dvd_sub_iff_map_mk_eq {R : Type u_1} [inst : CommRing R] {p : Type u_2} {q : Type u_3}
    (a : R) (A B : Matrix p q R) :
    (∀ (i : p) (j : q), a ∣ (A - B) i j) ↔
      Matrix.map A (⇑(Ideal.Quotient.mk (Ideal.span {a})) : R → R ⧸ Ideal.span {a}) =
        Matrix.map B (⇑(Ideal.Quotient.mk (Ideal.span {a})) : R → R ⧸ Ideal.span {a}) := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton,
    Matrix.sub_apply]

end GlobalTheory.DvdSubMapMk
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.LimLink

theorem dvd_iff_map_eq {R : Type*} [CommRing R] {p q : Type*} (a : R) (A B : Matrix p q R) :
    (∀ i j, a ∣ (A - B) i j) ↔
      A.map (Ideal.Quotient.mk (Ideal.span {a})) = B.map (Ideal.Quotient.mk (Ideal.span {a})) := by
  first
  | exact @_root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq
  | exact _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq
  | (apply _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq ..)

theorem map_smul_ringHom {R S : Type*} [CommRing R] [CommRing S] {p q : Type*} (f : R →+* S) (r : R)
    (A : Matrix p q R) : (r • A).map f = f r • A.map f := by
  ext i j; simp

end GlobalTheory.BKLim.LimLink

open GlobalTheory.BKLim.LimLink in
theorem GlobalTheory.BKLim.limit_basis_link_mod : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (tw.d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v)) → ∀ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (T : Matrix (Fin d) (Fin d) (WCb l)), Y.map (inclW l) = inclW l τ ^ N • T → (∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∀ n, ∃ m, n ≤ m ∧ ∃ (Rn : Matrix (Fin d) (Fin (tw.d' m)) bk.S) (Q : Matrix (Fin (tw.d' m)) (Fin d) (Ainf l)), (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi m) * (F m).T - T * Rn.map bk.evW) i j) ∧ ∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * (Rn.map bk.ev * Q).map (inclW l) - inclW l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j := by
  intro l _ K bk τ hτ d N ρ tw F T0 R H1 H2 H3 Y T hY H5 n
  obtain ⟨hu, -, -, -⟩ := GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ
  have huN : IsUnit (inclW l τ ^ N) := hu.pow N
  obtain ⟨π, key, key'⟩ : ∃ π : WCb l →+* (WCb l ⧸ Ideal.span {(l : WCb l) ^ n}),
      (∀ {p q : ℕ} (A B : Matrix (Fin p) (Fin q) (WCb l)),
        (∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) → A.map π = B.map π) ∧
      (∀ {p q : ℕ} (A B : Matrix (Fin p) (Fin q) (WCb l)),
        A.map π = B.map π → ∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) :=
    ⟨_, fun A B => (dvd_iff_map_eq _ A B).1, fun A B => (dvd_iff_map_eq _ A B).2⟩
  obtain ⟨m, hnm, hm⟩ := H2 n
  have hcol : ∀ j : Fin (tw.d' m), ∃ (v : Fin d → WCb l) (c : Fin d → bk.S),
      (∀ i, (l : WCb l) ^ n ∣ v i - R m i j) ∧ T0 *ᵥ v = T *ᵥ fun a => bk.evW (c a) := by
    intro j
    obtain ⟨v, hv1, hv2⟩ := hm (Pi.single j 1)
    obtain ⟨hOE, y, hy⟩ := H3 v hv2
    obtain ⟨c, hc⟩ := H5 y ⟨v, hOE, hy⟩
    refine ⟨v, c, ?_, ?_⟩
    · intro i
      have hs : (fun a => bk.evW ((Pi.single j (1 : bk.S) : Fin (tw.d' m) → bk.S) a))
          = Pi.single j 1 := by
        funext a; by_cases h : a = j
        · subst h; simp
        · simp [Pi.single_apply, h]
      have := hv1 i
      rw [hs] at this
      simpa [Matrix.mulVec_single_one] using this
    · have h1 : (fun i => inclW l (y i)) = inclW l τ ^ N • (T *ᵥ fun a => bk.evW (c a)) := by
        rw [hc]; funext i
        rw [RingHom.map_mulVec, hY, Matrix.smul_mulVec]
        rfl
      rw [hy] at h1
      exact huN.smul_left_cancel.1 h1
  choose V C hV hVC using hcol
  let Rn : Matrix (Fin d) (Fin (tw.d' m)) bk.S := Matrix.of fun i j => C j i
  have hTR : T * Rn.map bk.evW = T0 * Matrix.of (fun i j => V j i) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hVC j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Rn]
    exact this.symm
  have hfirst : (zW (tw.Pi m) * (F m).T).map π = (T * Rn.map bk.evW).map π := by
    have e1 : (zW (tw.Pi m) * (F m).T).map π = (T0 * R m).map π :=
      key _ _ (fun i j => (pow_dvd_pow _ hnm).trans (H1 m i j))
    have e2 : (R m).map π = (Matrix.of fun i j => V j i).map π :=
      key _ _ (fun i j => by
        have := hV j i
        rw [← dvd_neg]; simpa [neg_sub] using this)
    rw [e1, hTR, Matrix.map_mul, Matrix.map_mul, e2]
  obtain ⟨Ym, Y'm, hYm, hYY⟩ :=
    GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N (tw.d' m) (fun g => (tw.ρ' m g).val) (F m)
  obtain ⟨Sm, hSm⟩ := (tw.onto m).surj
  refine ⟨m, hnm, Rn, Y'm * Sm.map (algebraMap ℤ_[l] (Ainf l)), key' _ _ hfirst, ?_⟩
  have hinc : ∀ x : ℤ_[l], inclW l (algebraMap ℤ_[l] (Ainf l) x) = algebraMap ℤ_[l] (WCb l) x :=
    fun x => (inclWA l).commutes x
  have hFY : (F m).T * Y'm.map (inclW l) = inclW l τ ^ N • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (WCb l)) := by
    apply huN.smul_left_cancel.1
    rw [← Matrix.smul_mul, ← hYm, ← Matrix.map_mul, hYY, map_smul_ringHom,
      Matrix.map_one _ (map_zero _) (map_one _), smul_smul, map_pow, ← pow_add, two_mul]
  have hQ : ((Rn.map bk.ev) * (Y'm * Sm.map (algebraMap ℤ_[l] (Ainf l)))).map (inclW l)
      = Rn.map bk.evW * (Y'm.map (inclW l) * zW Sm) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map]
    congr 2
    ext i j
    simp [hinc]
  have hS1 : (zW (tw.Pi m * Sm)).map π = (1 : Matrix (Fin d) (Fin d) (WCb l)).map π := by
    apply key
    intro i j
    have e : (zW (tw.Pi m * Sm) - 1) i j = algebraMap ℤ_[l] (WCb l) ((tw.Pi m * Sm - 1 : Matrix (Fin d) (Fin d) ℤ_[l]) i j) := by
      simp only [zW, Matrix.sub_apply, Matrix.map_apply, map_sub]
      congr 1
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [e]
    refine (pow_dvd_pow _ hnm).trans ?_
    have := map_dvd (algebraMap ℤ_[l] (WCb l)) (hSm i j)
    simpa using this
  have hE : inclW l τ ^ N • (zW (tw.Pi m) * (F m).T * (Y'm.map (inclW l) * zW Sm))
      = inclW l τ ^ (2 * N) • zW (tw.Pi m * Sm) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (F m).T, hFY, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_smul,
      ← pow_add, ← two_mul]
    simp only [zW, Matrix.map_mul]
  apply key'
  calc (Y.map (inclW l) * (Rn.map bk.ev * (Y'm * Sm.map (algebraMap ℤ_[l] (Ainf l)))).map (inclW l)).map π
      = (inclW l τ ^ N • ((T * Rn.map bk.evW) * (Y'm.map (inclW l) * zW Sm))).map π := by
        rw [hQ, hY, Matrix.smul_mul, ← Matrix.mul_assoc]
    _ = (inclW l τ ^ N • ((zW (tw.Pi m) * (F m).T) * (Y'm.map (inclW l) * zW Sm))).map π := by
        rw [map_smul_ringHom, map_smul_ringHom, Matrix.map_mul, Matrix.map_mul (L := zW (tw.Pi m) * (F m).T), hfirst]
    _ = (inclW l τ ^ (2 * N) • zW (tw.Pi m * Sm)).map π := by rw [hE]
    _ = (inclW l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l))).map π := by
        rw [map_smul_ringHom, map_smul_ringHom, hS1]
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_matrix_congruence_lift_sequence : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (tw.d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v)) → ∀ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (T : Matrix (Fin d) (Fin d) (WCb l)), Y.map (inclW l) = inclW l τ ^ N • T → (∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∀ n, ∃ m, n ≤ m ∧ ∃ (Rn : Matrix (Fin d) (Fin (tw.d' m)) bk.S) (Q : Matrix (Fin (tw.d' m)) (Fin d) (Ainf l)), (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi m) * (F m).T - T * Rn.map bk.evW) i j) ∧ ∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * (Rn.map bk.ev * Q).map (inclW l) - inclW l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j := by
  first | (exact @GlobalTheory.BKLim.limit_basis_link_mod) | (exact GlobalTheory.BKLim.limit_basis_link_mod) | (intros; apply GlobalTheory.BKLim.limit_basis_link_mod  <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfInvLim

theorem dvd_mul_entry {R : Type} [CommRing R] {d : ℕ} (c : R) (A B : Matrix (Fin d) (Fin d) R)
    (h : ∀ i j, c ∣ B i j) (i j : Fin d) : c ∣ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (h k j) _

theorem exists_mul_eq_smul_one : ∀ (l : ℕ) [Fact l.Prime] (d M : ℕ) (τ : Ainf l)
    (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) →
    (∀ n, ∃ Q : Matrix (Fin d) (Fin d) (Ainf l), ∀ i j, (l : WCb l) ^ n ∣
      (Y.map (inclW l) * Q.map (inclW l) - inclW l τ ^ M • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) →
    ∃ Y' : Matrix (Fin d) (Fin d) (Ainf l), Y * Y' = τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  intro l _ d M τ Y hY hQ
  have hinj : Function.Injective (inclW l) :=
    WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))
  set A := Y.map (inclW l) with hA
  set c := inclW l τ ^ M with hc
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hY)
  have hinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).1 hY)
  set Z := c • A⁻¹ with hZ
  have hZent : ∀ i j, ∃ a : Ainf l, Z i j = inclW l (1 * a) := by
    intro i j
    refine GlobalTheory.AinfSat.mem_ideal_of_saturated l 1 (by rw [map_one]; exact isUnit_one) 0 (Z i j) fun n => ?_
    obtain ⟨Q, hQn⟩ := hQ n
    have h1 := dvd_mul_entry _ A⁻¹ _ hQn i j
    have h2 : A⁻¹ * (A * Q.map (inclW l) - c • (1 : Matrix (Fin d) (Fin d) (WCb l))) =
        Q.map (inclW l) - Z := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hinvA, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    rw [h2] at h1
    refine ⟨Q i j, ?_⟩
    rw [pow_zero, one_mul, one_mul, dvd_sub_comm]
    simpa [Matrix.sub_apply] using h1
  choose Y' hY' using hZent
  refine ⟨Matrix.of fun i j => Y' i j, ?_⟩
  have hmap : (Matrix.of fun i j => Y' i j).map (inclW l) = Z := by
    ext i j; simp [hY' i j]
  have key : (Y * Matrix.of fun i j => Y' i j).map (inclW l) =
      (τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))).map (inclW l) := by
    rw [Matrix.map_mul, hmap, hZ, Matrix.mul_smul, ← hA, hAinv]
    ext i j
    simp [Matrix.one_apply, hc, Matrix.smul_apply]
    split_ifs <;> simp
  refine Matrix.ext fun i j => hinj ?_
  exact congrFun (congrFun (congrArg Matrix.of.symm key) i) j

end GlobalTheory.AinfInvLim
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_exists_mul_eq_pow_smul_of_mod_lPow : ∀ (l : ℕ) [Fact l.Prime] (d M : ℕ) (τ : Ainf l) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → (∀ n, ∃ Q : Matrix (Fin d) (Fin d) (Ainf l), ∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * Q.map (inclW l) - inclW l τ ^ M • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → ∃ Y' : Matrix (Fin d) (Fin d) (Ainf l), Y * Y' = τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  atlas_forward_decl GlobalTheory.AinfInvLim.exists_mul_eq_smul_one
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfRinv

theorem rinv_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (d d' n M : ℕ) (τ : Ainf l) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d') (Ainf l)) (Q : Matrix (Fin d') (Fin d) (Ainf l)), IsUnit (inclW l τ) → IsUnit (Y.map (inclW l)) → Y * Y' = τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * (A * Q).map (inclW l) - inclW l τ ^ M • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → ∀ i j, (l : Ainf l) ^ n ∣ (A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j := by
  intro l _ d d' n M τ Y Y' A Q hτ hY hYY' hdiv
  set f : Ainf l →+* WCb l := inclW l with hf
  let I : Ideal (WCb l) := Ideal.span {((l : WCb l)) ^ n}
  let π : WCb l →+* WCb l ⧸ I := Ideal.Quotient.mk I
  let fW := (f.mapMatrix : Matrix (Fin d) (Fin d) (Ainf l) →+* Matrix (Fin d) (Fin d) (WCb l))
  let πM := (π.mapMatrix : Matrix (Fin d) (Fin d) (WCb l) →+* Matrix (Fin d) (Fin d) (WCb l ⧸ I))
  have hsm : ∀ {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (c : R),
      (φ.mapMatrix : Matrix (Fin d) (Fin d) R →+* Matrix (Fin d) (Fin d) S) (c • 1) = φ c • 1 := by
    intro R S _ _ φ c; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  set t : WCb l := f τ ^ M with ht
  have hfτ : fW (τ ^ M • 1) = t • 1 := by rw [hsm, map_pow]

  have h1 : fW Y * fW Y' = t • 1 := by rw [← map_mul, hYY', hfτ]
  obtain ⟨u, hu⟩ := hY
  have hYw : fW Y = (u : Matrix (Fin d) (Fin d) (WCb l)) := hu.symm
  have h2 : fW Y' * fW Y = t • 1 := by
    have e : fW Y' = (↑u⁻¹ : Matrix (Fin d) (Fin d) (WCb l)) * (fW Y * fW Y') := by
      rw [← Matrix.mul_assoc, hYw, Units.inv_mul, Matrix.one_mul]
    rw [e, h1, hYw, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul]

  set s : WCb l ⧸ I := π t with hs
  have hsu : IsUnit s := (hτ.pow M).map π
  have hmod : πM (fW Y * fW (A * Q) - t • 1) = 0 := by
    ext i j
    simp only [πM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hdiv i j))
  rw [map_sub, map_mul, hsm] at hmod
  have hYZ := sub_eq_zero.mp hmod
  have h2b : πM (fW Y') * πM (fW Y) = s • 1 := by rw [← map_mul, h2, hsm]
  have hZ : πM (fW (A * Q)) = πM (fW Y') := by
    have : s • πM (fW (A * Q)) = s • πM (fW Y') := by
      calc s • πM (fW (A * Q)) = (πM (fW Y') * πM (fW Y)) * πM (fW (A * Q)) := by
              rw [h2b, Matrix.smul_mul, Matrix.one_mul]
        _ = πM (fW Y') * (s • 1) := by rw [Matrix.mul_assoc, hYZ]
        _ = s • πM (fW Y') := by rw [Matrix.mul_smul, Matrix.mul_one]
    exact (hsu.smul_left_cancel).mp this
  have hfin : πM (fW (A * (Q * Y) - τ ^ M • 1)) = 0 := by
    rw [← Matrix.mul_assoc, map_sub, map_sub, map_mul, map_mul, hZ, h2b, hfτ, hsm, sub_self]
  intro i j
  have hij : π (f ((A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j)) = 0 := by
    have := congrFun (congrFun hfin i) j
    simpa [πM, fW, RingHom.mapMatrix_apply, Matrix.map_apply] using this
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hij)
  obtain ⟨a, ha⟩ := GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) n w (fun _ => ⟨(A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j, by rw [one_mul, ← hw, sub_self]; exact dvd_zero _⟩)
  refine ⟨a, GlobalTheory.Prism.inclW_injective ?_⟩
  rw [one_mul] at ha
  rw [map_mul, map_pow, map_natCast, ← ha]
  exact hw

end GlobalTheory.AinfRinv
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_rightInverse_up_to_pow_mod_lPow : ∀ (l : ℕ) [Fact l.Prime] (d d' n M : ℕ) (τ : Ainf l) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d') (Ainf l)) (Q : Matrix (Fin d') (Fin d) (Ainf l)), IsUnit (inclW l τ) → IsUnit (Y.map (inclW l)) → Y * Y' = τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * (A * Q).map (inclW l) - inclW l τ ^ M • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → ∀ i j, (l : Ainf l) ^ n ∣ (A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j := by
  atlas_forward_decl GlobalTheory.AinfRinv.rinv_mod_pow
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.ChangeEtaleBasis.main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (T0 Wm Wm' A0 A0' : Matrix (Fin d) (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T0.map (galW l (g : GQ l)) = T0) → (∀ i j, A0 i j ∈ bk.OE) → (∀ i j, A0' i j ∈ bk.OE) → T0.map (frobW l) = T0 * A0 → A0 * A0' = 1 → (∀ i j, Wm i j ∈ bk.OE) → (∀ i j, Wm' i j ∈ bk.OE) → Wm * Wm' = 1 → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * (T0 * Wm).map (galW l (g : GQ l)) = T0 * Wm) ∧ ∃ A1 A1' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A1 i j ∈ bk.OE) ∧ (∀ i j, A1' i j ∈ bk.OE) ∧ (T0 * Wm).map (frobW l) = (T0 * Wm) * A1 ∧ A1 * A1' = 1 := by
  intro l _ K bk d ρ T0 Wm Wm' A0 A0' hT0 hA0 hA0' hfr hAA hW hW' hWW
  have hO := GlobalTheory.T.integral_elements_unit_factorization l K bk
  have hgal : ∀ g : ↥(GK K), bk.FixFlat g → Wm.map (galW l (g : GQ l)) = Wm := by
    intro g hg
    exact Matrix.ext fun i j => by
      simp only [Matrix.map_apply]
      exact hO.2.2.2.2.2.1 g hg _ (hW i j)
  have hfrob : ∀ M : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, M i j ∈ bk.OE) → ∀ i j, M.map (frobW l) i j ∈ bk.OE := by
    intro M hM i j
    exact hO.2.2.2.2.2.2 _ (hM i j)
  have hmul : ∀ M N : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, M i j ∈ bk.OE) → (∀ i j, N i j ∈ bk.OE) → ∀ i j, (M * N) i j ∈ bk.OE := by
    intro M N hM hN i j
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ (fun k _ => Subring.mul_mem _ (hM i k) (hN k j))
  have hW'W : Wm' * Wm = 1 := mul_eq_one_comm.mp hWW
  refine ⟨?_, Wm' * A0 * Wm.map (frobW l), Wm'.map (frobW l) * A0' * Wm, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have hmap : (T0 * Wm).map (galW l (g : GQ l)) = T0.map (galW l (g : GQ l)) * Wm.map (galW l (g : GQ l)) :=
      Matrix.map_mul (f := ((galW l (g : GQ l)) : WCb l →+* WCb l))
    rw [hmap, hgal g hg, ← Matrix.mul_assoc, hT0 g hg]
  · exact hmul _ _ (hmul _ _ hW' hA0) (hfrob _ hW)
  · exact hmul _ _ (hmul _ _ (hfrob _ hW') hA0') hW
  · have hmap : (T0 * Wm).map (frobW l) = T0.map (frobW l) * Wm.map (frobW l) :=
      Matrix.map_mul (f := ((frobW l) : WCb l →+* WCb l))
    rw [hmap, hfr]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wm Wm', hWW, Matrix.one_mul]
  · have hφ : Wm.map (frobW l) * Wm'.map (frobW l) = 1 := by
      have e : (Wm * Wm').map (frobW l) = Wm.map (frobW l) * Wm'.map (frobW l) :=
        Matrix.map_mul (f := ((frobW l) : WCb l →+* WCb l))
      rw [← e, hWW]; exact Matrix.map_one _ (map_zero _) (map_one _)
    calc Wm' * A0 * Wm.map (frobW l) * (Wm'.map (frobW l) * A0' * Wm)
        = Wm' * A0 * (Wm.map (frobW l) * Wm'.map (frobW l)) * A0' * Wm := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hφ, Matrix.mul_one, Matrix.mul_assoc Wm', hAA, Matrix.mul_one, hW'W]
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantEtaleBasis_change_by_OE_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (T0 Wm Wm' A0 A0' : Matrix (Fin d) (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T0.map (galW l (g : GQ l)) = T0) → (∀ i j, A0 i j ∈ bk.OE) → (∀ i j, A0' i j ∈ bk.OE) → T0.map (frobW l) = T0 * A0 → A0 * A0' = 1 → (∀ i j, Wm i j ∈ bk.OE) → (∀ i j, Wm' i j ∈ bk.OE) → Wm * Wm' = 1 → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * (T0 * Wm).map (galW l (g : GQ l)) = T0 * Wm) ∧ ∃ A1 A1' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A1 i j ∈ bk.OE) ∧ (∀ i j, A1' i j ∈ bk.OE) ∧ (T0 * Wm).map (frobW l) = (T0 * Wm) * A1 ∧ A1 * A1' = 1 := by
  first | (exact @GlobalTheory.ChangeEtaleBasis.main) | (exact GlobalTheory.ChangeEtaleBasis.main) | (intros; apply GlobalTheory.ChangeEtaleBasis.main  <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem limit_pre_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val), ∃ (P : Pre bk N d fun g => (ρ g).val) (r : ℕ), ∀ n, ∃ m, n ≤ m ∧ Link bk P.T (F m).T (tw.Pi m) n r := by
  intro l _ K bk τ hτ d N ρ tw F
  obtain ⟨T0, hT0, hT0R⟩ := GlobalTheory.T.exists_etale_basis_limit_lattice_tower l K bk τ hτ d N ρ tw F
  obtain ⟨hfix0, A0, A0', hA0, hA0', hφ0, hAA0⟩ := GlobalTheory.T.limit_breuilKisin_basis_invariant_etale l K bk τ hτ d N ρ tw F T0 hT0 hT0R
  choose R R' hRO hR'O hR hRR' using hT0R
  obtain ⟨Yt, hYt⟩ := GlobalTheory.T.approximatingLattices_transitionMatrix_modPow l K bk τ hτ d N ρ tw F T0 R hT0 hR
  have hc := GlobalTheory.T.latticeApproximation_mittagLeffler l K bk τ hτ d N ρ tw F T0 R hT0 hRO hR
  have hlim := GlobalTheory.T.mittagLeffler_image_breuilKisin_modPow l K bk d tw.d' R Yt hYt hc
  have hL3 := GlobalTheory.T.limitVector_mem_OE_and_ainf l K bk τ hτ d N ρ tw F T0 R hRO hR
  obtain ⟨V, V', hVO, hV'O, hVV, hVlim⟩ := GlobalTheory.T.limitVectors_invertible_basis_over_OE l K bk d tw.d' R (fun n => ⟨R' n, hR'O n, hRR' n⟩) hlim hRO
  choose y1 hy1 using fun j => (hL3 _ (hVlim j)).2
  have hY1 : (Matrix.of fun i j => y1 j i).map (inclW l) = inclW l τ ^ N • (T0 * V) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hy1 j) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  obtain ⟨Y, Wm, Wm', hYu, hWO, hW'O, hWW, hYW, hmem⟩ := GlobalTheory.T.saturatedAinfLattice_free_over_breuilKisin l K bk τ hτ d N T0 V V' _ hT0 hVO hV'O hVV hY1
  have hlink := GlobalTheory.T.twisted_matrix_congruence_lift_sequence l K bk τ hτ d N ρ tw F T0 R hR hlim hL3 Y (T0 * Wm) hYW hmem
  obtain ⟨Y', hYY'⟩ := GlobalTheory.T.ainf_exists_mul_eq_pow_smul_of_mod_lPow l d (2 * N) τ Y hYu (fun n => by
    obtain ⟨m, _, Rn, Q, _, h⟩ := hlink n
    exact ⟨Rn.map bk.ev * Q, h⟩)
  obtain ⟨hfixT, A1, A1', hA1, hA1', hφ1, hAA1⟩ := GlobalTheory.T.invariantEtaleBasis_change_by_OE_unit l K bk d (fun g => (ρ g).val) T0 Wm Wm' A0 A0' hfix0 hA0 hA0' hφ0 hAA0 hWO hW'O hWW
  have hTu : IsUnit (T0 * Wm) := hT0.mul ⟨⟨Wm, Wm', hWW, mul_eq_one_comm.1 hWW⟩, rfl⟩
  obtain ⟨P, hP⟩ := GlobalTheory.T.breuilKisin_basis_of_etale_invariant_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) (T0 * Wm) A1 A1' Y Y' hTu hA1 hA1' hφ1 hAA1 hfixT hYW hYY'
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_right_inverse_mod_pow_of_ev l K bk τ hτ (2 * N)
  refine ⟨P, r, fun n => ?_⟩
  obtain ⟨m, hnm, Rn, Q, h1, h2⟩ := hlink n
  have h3 := GlobalTheory.T.ainf_rightInverse_up_to_pow_mod_lPow l d (tw.d' m) n (2 * N) τ Y Y' (Rn.map bk.ev) Q (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).1 hYu hYY' h2
  obtain ⟨G, hG⟩ := hr d (tw.d' m) n Rn (Q * Y) h3
  exact ⟨m, hnm, Rn, G, by rw [hP]; exact h1, hG⟩

end GlobalTheory.BKLim
end
