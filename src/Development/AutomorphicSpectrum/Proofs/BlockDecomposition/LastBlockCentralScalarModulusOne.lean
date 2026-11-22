module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.ZjScalar

theorem sum_card_mul_modExp {h : ℕ} (d : Fin h → ℕ) :
    ∑ a, (d a : ℤ) * modExp (fun a => Fin (d a)) a = 0 := by
  simp only [modExp, Fintype.card_fin, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : b < a
  · simp [hab, mul_comm]
  · simp [hab]

theorem prod_zpow_eq {ι : Type} (s : Finset ι) (x : ℝ) (hx : x ≠ 0) (f : ι → ℤ) :
    ∏ a ∈ s, x ^ f a = x ^ ∑ a ∈ s, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem zj_last {h : ℕ} (d : Fin h → ℕ) (t : kˣ) (j : Fin h) (hj : j.val + 1 = h) (a : Fin h) :
    Zl.JC.zj d t j a = Matrix.GeneralLinearGroup.scalar (Fin (d a)) t := by
  have : a ≤ j := by
    have := a.2
    exact Fin.le_def.2 (by omega)
  simp [Zl.JC.zj, this]

theorem nabs_det_zj_last {h : ℕ} (d : Fin h → ℕ) (t : kˣ) (j : Fin h) (hj : j.val + 1 = h) (a : Fin h) :
    nabs k (Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a)) = nabs k t ^ (d a) := by
  rw [zj_last d t j hj a]
  have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = t ^ (d a) := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
  rw [this]
  simp [nabs]

end GlobalTheory.CompanionTheory.ZjScalar
