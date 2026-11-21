import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfUnitBoundedTeichmullerFlatDenominators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_unit_bounded_teichmullerFlat_denominators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l), IsUnit (inclW l a) → ∀ n : ℕ, ∃ (m : ℕ) (t : Ainf l), (l : Ainf l) ^ n ∣ t * a - bk.ev X ^ m := by
  first | exact @GlobalTheory.BSP.BddDen.main | exact GlobalTheory.BSP.BddDen.main | (intros; apply GlobalTheory.BSP.BddDen.main <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP.BK

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem X_pow_natDegree_mem_lE (bk : BK K) : (X : bk.S) ^ bk.Ep.natDegree ∈ bk.J := by
  have hdvd : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]; exact bk.dvd_coeff i h
    · subst h; rw [if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h, sub_zero]; exact dvd_zero _
  obtain ⟨q, hq⟩ := hdvd
  have h1 := congrArg (fun p : Polynomial (Wq l bk.a) => (p : bk.S)) hq
  simp only [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul,
    Polynomial.coe_C] at h1
  rw [map_natCast] at h1
  have h2 : (X : bk.S) ^ bk.Ep.natDegree = bk.E - (l : bk.S) * (q : bk.S) := by
    linear_combination -h1
  rw [h2]
  exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

theorem E_mem_span_l_X (bk : BK K) : bk.E ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} := by
  obtain ⟨w, hw⟩ := bk.coeff_zero
  have hc : constantCoeff bk.E = (l : Wq l bk.a) * w := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hw]
  rw [eq_shift_mul_X_add_const bk.E, hc, map_mul, map_natCast]
  exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

end GlobalTheory.BSP.BK

theorem GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N : ℕ),
    ∃ n : ℕ, ∀ m : ℕ, ∃ n' : ℕ, ∀ s : bk.S,
      (X : bk.S) ^ m * s ∈ bk.J ^ n' ⊔ Ideal.span {(l : bk.S) ^ n} → s ∈ bk.J ^ N := by
  intro l _ K bk N
  refine ⟨N, fun m => ⟨N + (m + bk.Ep.natDegree * N), fun s hs => ?_⟩⟩
  have hJ : bk.J ≤ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} :=
    sup_le le_sup_left (Ideal.span_singleton_le_iff_mem _ |>.2 (BK.E_mem_span_l_X bk))
  have h1 : bk.J ^ (N + (m + bk.Ep.natDegree * N)) ≤
      Ideal.span {(l : bk.S) ^ N} ⊔ Ideal.span {(X : bk.S) ^ (m + bk.Ep.natDegree * N)} := by
    refine (Ideal.pow_right_mono hJ _).trans ?_
    have := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(l : bk.S)}) (J := Ideal.span {(X : bk.S)})
      (n := N) (m := m + bk.Ep.natDegree * N)
    rwa [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at this
  have hs' := (sup_le h1 le_sup_left : _ ≤ Ideal.span {(l : bk.S) ^ N} ⊔
      Ideal.span {(X : bk.S) ^ (m + bk.Ep.natDegree * N)}) hs
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hs'
  obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  set t := s - (X : bk.S) ^ (bk.Ep.natDegree * N) * g with ht
  have htm : (X : bk.S) ^ m * t = C ((l : Wq l bk.a) ^ N) * h := by
    rw [ht, map_pow, map_natCast, mul_sub, ← hyz]; ring
  have ht' : t = C ((l : Wq l bk.a) ^ N) * PowerSeries.mk (fun k => coeff (k + m) h) := by
    ext k
    have := congrArg (coeff (k + m)) htm
    rw [coeff_X_pow_mul', if_pos (Nat.le_add_left m k), Nat.add_sub_cancel, coeff_C_mul] at this
    rw [this, coeff_C_mul, coeff_mk]
  have hs2 : s = ((X : bk.S) ^ bk.Ep.natDegree) ^ N * g + (l : bk.S) ^ N * PowerSeries.mk (fun k => coeff (k + m) h) := by
    have : s = t + (X : bk.S) ^ (bk.Ep.natDegree * N) * g := by rw [ht]; ring
    rw [this, ht', map_pow, map_natCast, ← pow_mul]; ring
  rw [hs2]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (BK.X_pow_natDegree_mem_lE bk) N))
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) N))
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_mem_ideal_pow_of_X_pow_mul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N : ℕ), ∃ n : ℕ, ∀ m : ℕ, ∃ n' : ℕ, ∀ s : bk.S, (X : bk.S) ^ m * s ∈ bk.J ^ n' ⊔ Ideal.span {(l : bk.S) ^ n} → s ∈ bk.J ^ N := by
  atlas_forward_decl GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.NullOverS

theorem topBasis_c_mem_map {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (TB : TopBasis s I ι) (i : ι) (n : ℕ) {x : A} (hx : x ∈ (I ^ n).map s) : TB.c i x ∈ I ^ n := by
  have key : ∀ r : A, TB.c i (r * x) ∈ I ^ n := by
    refine Submodule.span_induction (p := fun x _ => ∀ r : A, TB.c i (r * x) ∈ I ^ n) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, hj, rfl⟩ r
      rw [mul_comm, TB.c_mul]
      exact Ideal.mul_mem_right _ _ hj
    · intro r; simp
    · intro y z _ _ hy hz r
      rw [mul_add, map_add]; exact Ideal.add_mem _ (hy r) (hz r)
    · intro a y _ hy r
      rw [smul_eq_mul, ← mul_assoc]; exact hy _
  simpa using key 1

theorem topBasis_c_i₀ {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (TB : TopBasis s I ι) (a : S) : TB.c TB.i₀ (s a) = a := by
  have h := TB.c_mul TB.i₀ a 1
  rw [mul_one, ← TB.b_i₀, TB.c_self, mul_one] at h
  exact h

end GlobalTheory.NullOverS

theorem GlobalTheory.NullOverS.null_of_mul_null : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type)
    (TB : TopBasis bk.ev bk.J ι) (d : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) →
    ∀ (σ : ι → Matrix (Fin d) (Fin d) bk.S),
    (∀ (n : ℕ) (a b : Fin d), {i | (Y * (σ i).map bk.ev) a b ∉ (bk.J ^ n).map bk.ev}.Finite) →
    ∀ (n : ℕ) (a b : Fin d), {i | σ i a b ∉ bk.J ^ n}.Finite := by
  intro l _ K bk ι TB d Y hY σ hσ N a b
  obtain ⟨n, hn⟩ := GlobalTheory.T.breuilKisin_mem_ideal_pow_of_X_pow_mul_mem l K bk N
  have hdet : IsUnit (inclW l Y.det) := by
    rw [RingHom.map_det]; exact (Matrix.isUnit_iff_isUnit_det _).1 hY
  obtain ⟨m, t, q, hq⟩ := GlobalTheory.T.ainf_unit_bounded_teichmullerFlat_denominators l K bk Y.det hdet n
  obtain ⟨n', hn'⟩ := hn m
  refine (Set.finite_iUnion fun c : Fin d => hσ n' c b).subset ?_
  intro i hi
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hi ⊢
  by_contra hc
  push_neg at hc
  apply hi
  apply hn'
  have h1 : (t • adjugate Y * (Y * (σ i).map bk.ev)) a b = t * Y.det * bk.ev (σ i a b) := by
    rw [← Matrix.mul_assoc, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
  have h2 : bk.ev (X ^ m * σ i a b) = (t • adjugate Y * (Y * (σ i).map bk.ev)) a b -
      bk.ev ((l : bk.S) ^ n) * (q * bk.ev (σ i a b)) := by
    rw [h1, map_mul, map_pow, map_pow, map_natCast]
    linear_combination (-(bk.ev (σ i a b))) * hq
  rw [← GlobalTheory.NullOverS.topBasis_c_i₀ TB (X ^ m * σ i a b), h2, map_sub]
  refine Ideal.sub_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
  · refine GlobalTheory.NullOverS.topBasis_c_mem_map TB _ _ ?_
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (hc c)
  · rw [TB.c_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.null_powerSeries_of_null_ainf_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type) (TB : TopBasis bk.ev bk.J ι) (d : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → ∀ (σ : ι → Matrix (Fin d) (Fin d) bk.S), (∀ (n : ℕ) (a b : Fin d), {i | (Y * (σ i).map bk.ev) a b ∉ (bk.J ^ n).map bk.ev}.Finite) → ∀ (n : ℕ) (a b : Fin d), {i | σ i a b ∉ bk.J ^ n}.Finite := by
  atlas_forward_decl GlobalTheory.NullOverS.null_of_mul_null
end
