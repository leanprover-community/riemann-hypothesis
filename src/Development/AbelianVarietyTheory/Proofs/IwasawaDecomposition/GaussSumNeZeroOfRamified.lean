module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist

@[expose] public section

noncomputable section

open ValuativeRel
open scoped Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.LocLanglands

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_le_iff_ord {x y : kˣ} : valuation k (x : k) ≤ valuation k (y : k) ↔ ord k y ≤ ord k x := by
  rw [ord, ord, neg_le_neg_iff, WithZero.log_le_log (by simp) (by simp)]
  exact (map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k)).symm

variable (k) in
theorem exists_unit_pow (a : ℕ) : ∃ p : kˣ, valuation k (p : k) = uniformizer k ^ a ∧ ord k p = a := by
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (uniformizer k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact uniformizer_ne_zero (R := k) (by simpa using hy.symm)
  have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hy
  refine ⟨Units.mk0 y hy0 ^ a, by simp [hy], ?_⟩
  induction a with
  | zero => simpa using ord_eq_zero (k := k) (x := 1) (by simp)
  | succ n ih => rw [pow_succ, ord_mul, ih, h1]; simp

variable {ψ : AddChar k Circle} {χ : kˣ →* ℂˣ} {c : kˣ} {a : ℕ} {R R' : Finset kˣ}

end GlobalTheory.LocLanglands
