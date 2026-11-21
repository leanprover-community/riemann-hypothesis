import Mathlib

section
namespace GlobalTheory.AevalTotalDegreeLinear

open MvPolynomial

theorem totalDegree_aeval_le_of_linear {κ : Type} (f : κ → MvPolynomial κ ℂ)
    (hf : ∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) (P : MvPolynomial κ ℂ) :
    MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P)
      ≤ MvPolynomial.totalDegree P := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (totalDegree_finset_sum _ _).trans ?_
  refine Finset.sup_le fun s hs => ?_
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  have hprod : totalDegree (s.prod fun i k => f i ^ k) ≤ s.sum fun _ k => k := by
    rw [Finsupp.prod, Finsupp.sum]
    refine (totalDegree_finset_prod _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine (totalDegree_pow _ _).trans ?_
    calc s i * totalDegree (f i) ≤ s i * 1 := Nat.mul_le_mul_left _ (hf i)
      _ = s i := mul_one _
  refine hprod.trans ?_
  exact Finset.le_sup (f := fun s : κ →₀ ℕ => s.sum fun _ e => e) hs

theorem main : ∀ {κ : Type} (f : κ → MvPolynomial κ ℂ), (∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial κ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P) ≤ MvPolynomial.totalDegree P :=
  fun f hf P => totalDegree_aeval_le_of_linear f hf P

end GlobalTheory.AevalTotalDegreeLinear
end

section
noncomputable section

open MvPolynomial

namespace GlobalTheory.CompactHowe

variable {ι : Type} {N n : ℕ}

def subst2 (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (Fin N × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin N × Fin n) ℂ :=
  aeval fun p => ∑ k, ∑ l, C (h k p.1 * g l p.2) * X (k, l)

def substF (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin N × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin N × Fin n) ℂ :=
  aeval fun p => ∑ k, ∑ l, C (h p.1 k p.2.1 * g p.1 l p.2.2) * X (p.1, k, l)

theorem subst2_X (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ) (p : Fin N × Fin n) :
    subst2 h g (X p) = ∑ k, ∑ l, C (h k p.1 * g l p.2) * X (k, l) := aeval_X _ _

theorem substF_X (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (p : ι × Fin N × Fin n) :
    substF h g (X p) = ∑ k, ∑ l, C (h p.1 k p.2.1 * g p.1 l p.2.2) * X (p.1, k, l) := aeval_X _ _

theorem totalDegree_aeval_le {κ : Type} (f : κ → MvPolynomial κ ℂ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (P : MvPolynomial κ ℂ) : (aeval f P).totalDegree ≤ P.totalDegree := by
  first
  | exact @_root_.GlobalTheory.AevalTotalDegreeLinear.main
  | exact _root_.GlobalTheory.AevalTotalDegreeLinear.main
  | (apply _root_.GlobalTheory.AevalTotalDegreeLinear.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AevalTotalDegreeLinear.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AevalTotalDegreeLinear.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AevalTotalDegreeLinear.main ..)

theorem totalDegree_substF_le (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) : (substF h g P).totalDegree ≤ P.totalDegree :=
  totalDegree_aeval_le _ (fun _ => totalDegree_finsetSum_le fun _ _ => totalDegree_finsetSum_le fun _ _ =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])) P

theorem subst2_mul (h h' : Matrix (Fin N) (Fin N) ℂ) (g g' : Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (Fin N × Fin n) ℂ) : subst2 h g (subst2 h' g' P) = subst2 (h * h') (g * g') P := by
  have key : (subst2 h g).comp (subst2 h' g') = subst2 (h * h') (g * g') := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, subst2_X, subst2_X]
    simp only [map_sum, map_mul, subst2_X, algHom_C, algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun _ => Finset.univ) (t' := Finset.univ) (s' := fun _ => Finset.univ) (by simp)]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun x => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  exact congrArg (fun f => f P) key

theorem subst2_one (P : MvPolynomial (Fin N × Fin n) ℂ) : subst2 1 1 P = P := by
  have key : subst2 (1 : Matrix (Fin N) (Fin N) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) = AlgHom.id ℂ _ := by
    refine algHom_ext fun p => ?_
    rw [subst2_X, Finset.sum_eq_single p.1, Finset.sum_eq_single p.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  rw [key]; rfl

end GlobalTheory.CompactHowe

end
end
