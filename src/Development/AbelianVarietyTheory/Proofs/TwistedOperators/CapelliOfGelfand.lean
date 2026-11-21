import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracedQminorComatrixTruncatedInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonicStatement
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import BuildAid.ForwardExisting

section
section
open Formalism.REAL Finset Polynomial

namespace GlobalTheory.ScalarNewton

open Matrix

theorem sum_adjugate_eq {R : Type*} [CommRing R] [IsDomain R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (h : M.det ≠ 0) :
    ∑ a, ∑ b, M.adjugate a b = (M + Matrix.of fun _ _ => (1 : R)).det - M.det := by
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  have hinj : Function.Injective φ := IsFractionRing.injective R K
  apply hinj
  have hdet : φ M.det = (M.map φ).det := RingHom.map_det φ M
  have hd0 : (M.map φ).det ≠ 0 := by
    rw [← hdet]; exact (map_ne_zero_iff φ hinj).2 h
  have hd : IsUnit (M.map φ).det := hd0.isUnit
  have hJ : (M + Matrix.of fun _ _ => (1 : R)).map φ =
      M.map φ + replicateCol Unit (fun _ : ι => (1 : K)) * replicateRow Unit (fun _ : ι => (1 : K)) := by
    ext i j; simp [replicateCol, replicateRow, Matrix.mul_apply]
  have hadj : ∀ a b, φ (M.adjugate a b) = (M.map φ).adjugate a b := by
    intro a b
    have := congrFun (congrFun (RingHom.map_adjugate φ M) a) b
    simpa using this
  have key := det_add_replicateCol_mul_replicateRow (ι := Unit) hd (fun _ => (1 : K)) (fun _ => 1)
  rw [map_sub, RingHom.map_det φ, RingHom.map_det φ, map_sum]
  simp only [map_sum, hadj]
  change _ = ((M + Matrix.of fun _ _ => (1 : R)).map φ).det - (M.map φ).det
  rw [hJ, key, det_unique (n := Unit), Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply, replicateCol_apply,
    Matrix.smul_apply, smul_eq_mul, one_mul, mul_one, Finset.univ_unique, Finset.sum_singleton]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hd0]
  ring

end GlobalTheory.ScalarNewton

namespace GlobalTheory.ScalarNewton

open Matrix

variable (m : ℕ) (χ : Fin (m + 1) → ℂ)

noncomputable def amat : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)

theorem gelfVal_eq (k : ℕ) : GlobalTheory.Dec.gelfVal χ k = ∑ a, ∑ b, (amat m χ ^ k) a b := rfl

noncomputable def pmat : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X] :=
  (X : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).map C + (amat m χ - (m : ℂ) • 1).map C

theorem pmat_apply (a b : Fin (m + 1)) : pmat m χ a b =
    if a = b then X + C (χ a - (m : ℂ) / 2) else if a < b then -1 else 0 := by
  by_cases h1 : a = b
  · subst h1
    simp [pmat, amat, Formalism.REAL.Amat]
    rw [show ((m : ℂ[X])) = C (m : ℂ) from (map_natCast C m).symm, ← C_add, ← C_sub, ← C_sub]
    congr 1
    ring
  · by_cases h2 : a < b
    · simp [pmat, amat, Formalism.REAL.Amat, h1, h2, Matrix.one_apply]
    · simp [pmat, amat, Formalism.REAL.Amat, h1, h2, Matrix.one_apply]

theorem pmat_eq : pmat m χ = (X - C (m : ℂ)) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X]) + (amat m χ).map C := by
  refine Matrix.ext fun a b => ?_
  by_cases h1 : a = b
  · subst h1
    simp [pmat]
    ring
  · simp [pmat, h1, Matrix.one_apply]

theorem det_pmat : (pmat m χ).det = ∏ s, (X + C (χ s - (m : ℂ) / 2)) := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_congr rfl fun s _ => by rw [pmat_apply]; simp
  · intro i j h
    have h' : j < i := h
    rw [pmat_apply, if_neg (ne_of_gt h'), if_neg (not_lt_of_gt h')]

theorem det_pmat_add : (pmat m χ + Matrix.of fun _ _ => (1 : ℂ[X])).det =
    ∏ s, (X + C (χ s - (m : ℂ) / 2 + 1)) := by
  rw [Matrix.det_of_lowerTriangular]
  · exact Finset.prod_congr rfl fun s _ => by rw [Matrix.add_apply, pmat_apply]; simp; ring
  · intro i j h
    have h' : i < j := h
    rw [Matrix.add_apply, pmat_apply, if_neg (ne_of_lt h'), if_pos h']
    simp

theorem det_pmat_ne_zero : (pmat m χ).det ≠ 0 := by
  rw [det_pmat]
  exact Finset.prod_ne_zero_iff.2 fun s _ => X_add_C_ne_zero _

end GlobalTheory.ScalarNewton

namespace GlobalTheory.ScalarNewton

open Matrix

theorem sumEnt_smul {n : ℕ} (c : ℂ[X]) (W : Matrix (Fin n) (Fin n) ℂ[X]) :
    ∑ a, ∑ b, (c • W) a b = c * ∑ a, ∑ b, W a b := by
  simp [Finset.mul_sum]

theorem sumEnt_sub {n : ℕ} (V W : Matrix (Fin n) (Fin n) ℂ[X]) :
    ∑ a, ∑ b, (V - W) a b = ∑ a, ∑ b, V a b - ∑ a, ∑ b, W a b := by
  simp [Finset.sum_sub_distrib]

theorem sumEnt_sum {n : ℕ} (s : Finset ℕ) (W : ℕ → Matrix (Fin n) (Fin n) ℂ[X]) :
    ∑ a, ∑ b, (∑ i ∈ s, W i : Matrix (Fin n) (Fin n) ℂ[X]) a b = ∑ i ∈ s, ∑ a, ∑ b, W i a b := by
  simp only [Matrix.sum_apply]
  calc _ = ∑ a, ∑ i ∈ s, ∑ b, W i a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem poly_identity (m N : ℕ) (χ : Fin (m + 1) → ℂ) :
    (X - C (m : ℂ)) ^ (N + 1) * ((pmat m χ + Matrix.of fun _ _ => (1 : ℂ[X])).det - (pmat m χ).det) -
      (pmat m χ).det * ∑ k ∈ range (N + 1), (-1) ^ k * (X - C (m : ℂ)) ^ (N - k) * C (GlobalTheory.Dec.gelfVal χ k) =
    (-1) ^ (N + 1) * ∑ a, ∑ b, ((pmat m χ).adjugate * ((amat m χ).map C) ^ (N + 1)) a b := by
  set x : ℂ[X] := X - C (m : ℂ)
  set Bm : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X] := (amat m χ).map C
  set Mx := pmat m χ
  have hnp : ∀ i : ℕ, (-Bm) ^ i = ((-1 : ℂ[X]) ^ i) • Bm ^ i := by
    intro i; rw [← neg_one_smul ℂ[X] Bm, _root_.smul_pow]
  have hxp : ∀ i : ℕ, (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])) ^ i = x ^ i • 1 := by
    intro i; rw [_root_.smul_pow, one_pow]
  have hBp : ∀ i : ℕ, ∑ a, ∑ b, (Bm ^ i) a b = C (GlobalTheory.Dec.gelfVal χ i) := by
    intro i
    rw [gelfVal_eq, map_sum]
    simp only [map_sum]
    have : Bm ^ i = (amat m χ ^ i).map C := by
      rw [Matrix.map_pow]
    rw [this]
    simp
  have hcomm : Commute (-Bm) (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])) :=
    (Commute.one_right _).smul_right x
  have hgeom := hcomm.mul_geom_sum₂ (N + 1)
  set P := ∑ i ∈ range (N + 1), (-Bm) ^ i * (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])) ^ (N + 1 - 1 - i)
  have hMP : Mx * P = x ^ (N + 1) • 1 - (-1 : ℂ[X]) ^ (N + 1) • Bm ^ (N + 1) := by
    have : Mx = -(-Bm - x • 1) := by rw [show Mx = pmat m χ from rfl, pmat_eq]; abel
    rw [this, neg_mul, hgeom, hnp, hxp]
    abel
  have hSP : ∑ a, ∑ b, P a b = ∑ k ∈ range (N + 1), (-1) ^ k * x ^ (N - k) * C (GlobalTheory.Dec.gelfVal χ k) := by
    rw [sumEnt_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hnp, hxp, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, sumEnt_smul, hBp]
    simp only [Nat.add_sub_cancel]
  have hadj : Mx.adjugate * Mx = Mx.det • 1 := Matrix.adjugate_mul Mx
  have hdP : Mx.det • P = Mx.adjugate * (Mx * P) := by
    rw [← Matrix.mul_assoc, hadj, Matrix.smul_mul, Matrix.one_mul]
  have hS := congrArg (fun W => ∑ a, ∑ b, W a b) hdP
  rw [sumEnt_smul, hSP, hMP, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, sumEnt_sub,
    sumEnt_smul, sumEnt_smul, sum_adjugate_eq Mx (det_pmat_ne_zero m χ)] at hS
  rw [hS]
  ring

end GlobalTheory.ScalarNewton

namespace GlobalTheory.ScalarNewton

open Matrix

theorem natDegree_adjugate_pmat_le (m : ℕ) (χ : Fin (m + 1) → ℂ) (i j : Fin (m + 1)) :
    ((pmat m χ).adjugate i j).natDegree ≤ m := by
  rw [adjugate_fin_succ_eq_det_submatrix]
  have h1 : ((-1 : ℂ[X]) ^ ((j : ℕ) + i)) = C ((-1) ^ ((j : ℕ) + i)) := by simp
  rw [h1]
  refine (natDegree_C_mul_le _ _).trans ?_
  have e : (pmat m χ).submatrix j.succAbove i.succAbove =
      (X : ℂ[X]) • ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix j.succAbove i.succAbove).map C +
      ((amat m χ - (m : ℂ) • 1).submatrix j.succAbove i.succAbove).map C := rfl
  rw [e]
  simpa using natDegree_det_X_add_C_le
    ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix j.succAbove i.succAbove)
    ((amat m χ - (m : ℂ) • 1).submatrix j.succAbove i.succAbove)

theorem scalar_newton : ∀ (m N : ℕ) (χ : Fin (m + 1) → ℂ), ∃ r : ℂ[X], r.natDegree ≤ m ∧ ∀ u : ℂ,
    (u - m) ^ (N + 1) * (∏ s, (u + 1 - (m : ℂ) / 2 + χ s) - ∏ s, (u - (m : ℂ) / 2 + χ s)) -
      (∏ s, (u - (m : ℂ) / 2 + χ s)) * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * GlobalTheory.Dec.gelfVal χ k =
      r.eval u := by
  intro m N χ
  refine ⟨(-1) ^ (N + 1) * ∑ a, ∑ b, ((pmat m χ).adjugate * ((amat m χ).map C) ^ (N + 1)) a b, ?_, ?_⟩
  · have hc : ((-1 : ℂ[X]) ^ (N + 1)) = C ((-1) ^ (N + 1)) := by simp
    rw [hc]
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_sum_le_of_forall_le _ _ fun a _ => natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
    rw [Matrix.mul_apply]
    refine natDegree_sum_le_of_forall_le _ _ fun c _ => ?_
    rw [← Matrix.map_pow, Matrix.map_apply]
    exact (natDegree_mul_C_le _ _).trans (natDegree_adjugate_pmat_le m χ a c)
  · intro u
    rw [← poly_identity, det_pmat, det_pmat_add]
    simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_prod, eval_add, eval_finset_sum, eval_neg,
      eval_one]
    have e1 : ∏ s, (u + (χ s - (m : ℂ) / 2 + 1)) = ∏ s, (u + 1 - (m : ℂ) / 2 + χ s) :=
      Finset.prod_congr rfl fun _ _ => by ring
    have e0 : ∏ s, (u + (χ s - (m : ℂ) / 2)) = ∏ s, (u - (m : ℂ) / 2 + χ s) :=
      Finset.prod_congr rfl fun _ _ => by ring
    rw [e1, e0]

end GlobalTheory.ScalarNewton
end

open Formalism.REAL Finset Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_capelli_truncated_perelomov_popov : ∀ (m N : ℕ) (χ : Fin (m + 1) → ℂ), ∃ r : ℂ[X], r.natDegree ≤ m ∧ ∀ u : ℂ, (u - m) ^ (N + 1) * (∏ s, (u + 1 - (m : ℂ) / 2 + χ s) - ∏ s, (u - (m : ℂ) / 2 + χ s)) - (∏ s, (u - (m : ℂ) / 2 + χ s)) * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * GlobalTheory.Dec.gelfVal χ k = r.eval u := by
  atlas_forward_decl GlobalTheory.ScalarNewton.scalar_newton
end

section
section
open Finset Polynomial

namespace GlobalTheory

lemma shiftDiffPoly_coeff_comp (f : ℂ[X]) (n : ℕ) :
    (f.comp (X + 1)).coeff n = ∑ i ∈ range (f.natDegree + 1), f.coeff i * (i.choose n : ℂ) := by
  rw [comp, eval₂_eq_sum_range]
  simp [finset_sum_coeff, coeff_C_mul, coeff_X_add_one_pow]

lemma shiftDiffPoly_coeff_top (f : ℂ[X]) (n : ℕ) (hn : f.natDegree ≤ n) :
    (f.comp (X + 1) - f).coeff n = 0 := by
  rw [coeff_sub, shiftDiffPoly_coeff_comp, Finset.sum_eq_single n]
  · simp
  · intro b hb hbn
    have : b < n := by simp at hb; omega
    simp [Nat.choose_eq_zero_of_lt this]
  · intro hn'
    have : f.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by simp at hn'; omega)
    simp [this]

lemma shiftDiffPoly_coeff_sub (f : ℂ[X]) (e : ℕ) (he : f.natDegree = e + 1) :
    (f.comp (X + 1) - f).coeff e = ((e : ℂ) + 1) * f.coeff (e + 1) := by
  rw [coeff_sub, shiftDiffPoly_coeff_comp, he, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero]
  · simp [Nat.choose_succ_self_right]; ring
  · intro i hi
    simp at hi
    simp [Nat.choose_eq_zero_of_lt hi]

theorem newton_recursion_poly_unique : ∀ (m N : ℕ) (p : ℕ → ℂ) (f r : ℂ[X]), m < N → p 0 = (m : ℂ) + 1 → f.natDegree ≤ m → r.natDegree ≤ m → (∀ u : ℂ, (u - m) ^ (N + 1) * (f.eval (u + 1) - f.eval u) - f.eval u * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * p k = r.eval u) → f = 0 := by
  intro m N p f r hmN hp0 hf hr hid
  have hlead : ∀ k : ℕ, ((X - C (m:ℂ)) ^ k).coeff k = 1 := fun k => by
    have h := ((monic_X_sub_C (m:ℂ)).pow k).coeff_natDegree
    rwa [natDegree_pow, natDegree_X_sub_C, mul_one] at h
  set Pi : ℂ[X] := ∑ k ∈ range (N + 1), C ((-1) ^ k * p k) * (X - C (m:ℂ)) ^ (N - k) with hPi
  set g : ℂ[X] := f.comp (X + 1) - f with hg
  have hpoly : (X - C (m:ℂ)) ^ (N + 1) * g - f * Pi = r := by
    apply Polynomial.funext
    intro u
    simp only [hg, hPi, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_comp, eval_add,
      eval_one, eval_finset_sum]
    rw [← hid u]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hPiN : Pi.coeff N = (m : ℂ) + 1 := by
    rw [hPi, finset_sum_coeff, Finset.sum_range_succ', Finset.sum_eq_zero]
    · simp only [pow_zero, one_mul, Nat.sub_zero, coeff_C_mul, hlead, hp0, mul_one, zero_add]
    · intro k hk
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
      rw [natDegree_pow, natDegree_X_sub_C]
      simp at hk
      omega
  have hPideg : Pi.natDegree ≤ N := by
    rw [hPi]
    apply natDegree_sum_le_of_forall_le
    intro k _
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_pow, natDegree_X_sub_C]
    omega
  set d := f.natDegree with hd
  have hcoef : ((X - C (m:ℂ)) ^ (N + 1) * g - f * Pi).coeff (d + N) = r.coeff (d + N) := by rw [hpoly]
  rw [coeff_sub] at hcoef
  have hr0 : r.coeff (d + N) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have h2 : (f * Pi).coeff (d + N) = f.coeff d * Pi.coeff N :=
    coeff_mul_add_eq_of_natDegree_le le_rfl hPideg
  have h1 : ((X - C (m:ℂ)) ^ (N + 1) * g).coeff (d + N) = d * f.coeff d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · have hg0 : g = 0 := by
        ext n
        rw [coeff_zero]
        exact shiftDiffPoly_coeff_top f n (by omega)
      rw [hg0, mul_zero, coeff_zero, h0]
      simp
    · obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      have hgdeg : g.natDegree ≤ e := by
        rw [natDegree_le_iff_coeff_eq_zero]
        intro n hn
        exact shiftDiffPoly_coeff_top f n (by omega)
      have hidx : d + N = (N + 1) + e := by omega
      rw [hidx, coeff_mul_add_eq_of_natDegree_le (by rw [natDegree_pow, natDegree_X_sub_C, mul_one]) hgdeg,
        hlead, one_mul, shiftDiffPoly_coeff_sub f e he, he]
      push_cast
      ring
  rw [h1, h2, hPiN, hr0] at hcoef
  have hne : (d : ℂ) - ((m : ℂ) + 1) ≠ 0 := by
    intro h
    have h' : (d : ℂ) = ((m + 1 : ℕ) : ℂ) := by push_cast; linear_combination h
    have := Nat.cast_injective h'
    omega
  have hc : f.coeff d = 0 := by
    have : f.coeff d * ((d : ℂ) - ((m : ℂ) + 1)) = 0 := by linear_combination hcoef
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hne
  exact leadingCoeff_eq_zero.mp hc

end GlobalTheory
end

open Finset Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poly_eq_zero_of_newton_recursion : ∀ (m N : ℕ) (p : ℕ → ℂ) (f r : ℂ[X]), m < N → p 0 = (m : ℂ) + 1 → f.natDegree ≤ m → r.natDegree ≤ m → (∀ u : ℂ, (u - m) ^ (N + 1) * (f.eval (u + 1) - f.eval u) - f.eval u * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * p k = r.eval u) → f = 0 := by
  atlas_forward_decl GlobalTheory.newton_recursion_poly_unique
end

section
open Formalism.REAL Finset Polynomial

open GlobalTheory.Dec (gelfVal)

namespace GlobalTheory.CapelliNewton

theorem gelfVal_zero (m : ℕ) (χ : Fin (m+1) → ℂ) : gelfVal χ 0 = (m:ℂ) + 1 := by
  simp [gelfVal, Matrix.one_apply]

theorem etr_apply_all {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ)
    (E : Fin (m+1) → Fin (m+1) → Module.End ℂ V) (χ : Fin (m+1) → ℂ)
    (hetr : ∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) (k : ℕ) (w : V) :
    etr E k w = gelfVal χ k • w := by
  cases k with
  | zero => rw [gelfVal_zero]; simp [etr, epow, add_smul]; rw [Nat.cast_smul_eq_nsmul]
  | succ k => exact hetr k w

noncomputable def polyOf {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) : ℂ[X] :=
  ∑ i ∈ range (d + 1), C (φ (c i v)) * X ^ i

theorem polyOf_eval {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) (u : ℂ) :
    (polyOf d c φ v).eval u = φ ((∑ i ∈ range (d + 1), u ^ i • c i) v) := by
  unfold polyOf
  rw [eval_finset_sum, LinearMap.sum_apply, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, LinearMap.smul_apply, map_smul, smul_eq_mul, mul_comm]

theorem polyOf_natDegree {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) : (polyOf d c φ v).natDegree ≤ d := by
  unfold polyOf
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.lt_succ_iff.mp (mem_range.mp hi)

theorem polyOf_coeff {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) : (polyOf d c φ v).coeff d = φ (c d v) := by
  unfold polyOf
  rw [finset_sum_coeff, sum_eq_single d]
  · simp
  · intro b _ hb; simp [coeff_C_mul_X_pow, hb.symm]
  · intro h; exact absurd (self_mem_range_succ d) h

noncomputable def capQ (m : ℕ) (χ : Fin (m+1) → ℂ) : ℂ[X] := ∏ s, (X + C (χ s - (m : ℂ) / 2))

theorem capQ_eval (m : ℕ) (χ : Fin (m+1) → ℂ) (u : ℂ) :
    (capQ m χ).eval u = ∏ s, (u - (m : ℂ) / 2 + χ s) := by
  simp [capQ, eval_prod]; refine prod_congr rfl fun s _ => by ring

theorem capQ_monic (m : ℕ) (χ : Fin (m+1) → ℂ) : (capQ m χ).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_add_C _

theorem capQ_natDegree (m : ℕ) (χ : Fin (m+1) → ℂ) : (capQ m χ).natDegree = m + 1 := by
  unfold capQ
  rw [natDegree_prod_of_monic _ _ fun s _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem main_succ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ)
    (E : Fin (m+1) → Fin (m+1) → Module.End ℂ V) (χ : Fin (m+1) → ℂ) (hE : GlRel E)
    (hetr : ∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) (u : ℂ) (v : V) :
    qdet E u v = (∏ s, (u - (m : ℂ) / 2 + χ s)) • v := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet (Module.End ℂ V) (m + 1) E
  set P := polyOf (m + 1) c φ v with hPdef
  have hP : ∀ w : ℂ, φ (qdet E w v) = P.eval w := fun w => by rw [polyOf_eval, hc]

  have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → Module.End ℂ V, ∀ w : ℂ,
      qminor E (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
    intro i j
    obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap (Module.End ℂ V) (m + 1) m E (Fin.succAbove j) (Fin.succAbove i) 0
    exact ⟨c', fun w => by simpa using hc' w⟩
  choose cm hcm using hmin
  let N := m + 1
  let Rc : ℕ → Module.End ℂ V := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * cm i j d * epow E (N + 1) j i
  have hR : ∀ w : ℂ, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * qminor E (Fin.succAbove j) (Fin.succAbove i) w * epow E (N + 1) j i
      = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
    intro w
    simp only [Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
    conv_lhs => enter [2, x]; rw [sum_comm]
    rw [sum_comm]
  set Rp := polyOf m Rc φ v
  have hrec : ∀ w : ℂ, (w - m) ^ (N + 1) * (P.eval (w + 1) - P.eval w) - P.eval w * ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * gelfVal χ k = (C (-(-1) ^ N) * Rp).eval w := by
    intro w
    have h1 := congrArg (fun T : Module.End ℂ V => φ (T v)) (GlobalTheory.T.traced_qminor_comatrix_truncated_inverse (Module.End ℂ V) m E hE w N)
    rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor', hR] at h1
    have h2 : (qdet E w * ∑ k ∈ range (N + 1), algebraMap ℂ (Module.End ℂ V) ((-1) ^ k * (w - m) ^ (N - k)) * etr E k) v
        = (∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * gelfVal χ k) • qdet E w v := by
      rw [Module.End.mul_apply, LinearMap.sum_apply]
      simp only [Module.End.mul_apply, Module.algebraMap_end_apply, etr_apply_all m E χ hetr, smul_smul]
      rw [← sum_smul, map_smul]
    rw [h2] at h1
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_add, map_smul, LinearMap.sub_apply, map_sub, smul_eq_mul] at h1
    rw [← polyOf_eval] at h1
    simp only [hP] at h1
    simp only [eval_mul, eval_neg, eval_pow, eval_C]
    linear_combination h1
  obtain ⟨rs, hrs, hrsE⟩ := GlobalTheory.T.scalar_capelli_truncated_perelomov_popov m N χ
  have hf := GlobalTheory.T.poly_eq_zero_of_newton_recursion m N (gelfVal χ) (P - C (φ v) * capQ m χ) (C (-(-1) ^ N) * Rp - C (φ v) * rs)
    (Nat.lt_succ_self m) (gelfVal_zero m χ) ?_ ?_ ?_
  · have := congrArg (eval u) hf
    simp only [eval_sub, eval_mul, eval_C, eval_zero, capQ_eval] at this
    rw [map_sub, map_smul, hP, smul_eq_mul]; linear_combination this
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_sub, coeff_C_mul]
    rcases Nat.lt_or_ge (m + 1) k with h | h
    · rw [coeff_eq_zero_of_natDegree_lt ((polyOf_natDegree _ _ _ _).trans_lt h),
        coeff_eq_zero_of_natDegree_lt (by rw [capQ_natDegree]; exact h)]; simp
    · have hk' : k = m + 1 := le_antisymm h hk
      subst hk'
      have := (capQ_monic m χ).coeff_natDegree
      rw [capQ_natDegree] at this
      rw [this, polyOf_coeff, hc1]; simp
  · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_C_mul_le _ _ |>.trans (polyOf_natDegree _ _ _ _)
    · exact natDegree_C_mul_le _ _ |>.trans hrs
  · intro w
    have h1 := hrec w
    have h2 := hrsE w
    rw [← capQ_eval m χ (w + 1), ← capQ_eval m χ w] at h2
    simp only [eval_sub, eval_mul, eval_C] at h1 h2 ⊢
    linear_combination h1 - φ v * h2

end GlobalTheory.CapelliNewton

namespace GlobalTheory.CapelliNewton

theorem capelli_of_gelfand : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ), GlRel E → (∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) → ∀ (Y : ℂ) (v : V), qdet E (Y + ((n : ℂ) - 1) / 2) v = (∏ s, (Y + χ s)) • v := by
  intro V _ _ n E χ hE hetr Y v
  cases n with
  | zero => simp [qdet, qminor]
  | succ m =>
    rw [main_succ V m E χ hE hetr]
    congr 1
    refine prod_congr rfl fun s _ => ?_
    push_cast; ring

end GlobalTheory.CapelliNewton
end
