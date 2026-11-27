module

public import TauCeti.Analysis.AbsoluteValue.Action
public import TauCeti.Analysis.AbsoluteValue.ValuationSubring
public import Lib.ClassField.Places.AbsoluteValues
import Mathlib.RingTheory.Valuation.Algebraic

/-!
# Stabilizers of nonarchimedean absolute values on algebraic extensions

Let a group act on an algebraic extension `L/K` by automorphisms fixing `K`. For every
nonarchimedean absolute value `w` on `L`, its stabilizer is the decomposition group of its closed
unit ball. This applies to the algebraic closure of `ℚ` with any scaling of the absolute value.
We obtain criteria for Frobenius and inertia using the action on `w` itself.

More generally, if two absolute values agree on `K`, then `smul_valuationSubring_eq_iff`
identifies the automorphisms carrying one unit ball to the other with those carrying one
absolute value to the other. In particular, it transfers the conjugacy in
`New.IsPlaceOver.exists_smul` to absolute values above a finite prime.
-/

@[expose] public section

open scoped Pointwise

namespace New

variable {K L Γ : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {w : AbsoluteValue L ℝ}

/-- Equivalent absolute values on an algebraic extension agree if one is nonarchimedean
and they agree on the base field. -/
private theorem eq_of_isEquiv_of_under_eq {v : AbsoluteValue L ℝ} (hw : IsNonarchimedean w)
    (h : w.IsEquiv v) (hK : w.under K = v.under K) : w = v := by
  ext x
  -- Some positive power of the value of `x` is the value of a base-field element.
  obtain ⟨n, r, hn, -, hr⟩ := (w.toValuation hw).exists_map_pow_eq_map_algebraMap_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic (R := K) x)
  have hx : w (x ^ n) = w (algebraMap K L r) := by
    simpa [map_pow] using congrArg ((↑) : NNReal → ℝ) hr
  apply (pow_left_inj₀ (w.nonneg x) (v.nonneg x) hn.ne').mp
  rw [← map_pow, ← map_pow, hx, h.eq_iff_eq.mp hx]
  exact DFunLike.congr_fun hK r

variable [Group Γ] [MulSemiringAction Γ L] [SMulCommClass Γ K L]

/-- For two nonarchimedean absolute values with the same restriction to the base field,
an automorphism carries one closed unit ball to the other exactly when it carries one
absolute value to the other. -/
theorem smul_valuationSubring_eq_iff {v : AbsoluteValue L ℝ}
    (hw : IsNonarchimedean w) (hv : IsNonarchimedean v) (hK : w.under K = v.under K) (σ : Γ) :
    σ • w.valuationSubring hw = v.valuationSubring hv ↔ σ • w = v := by
  rw [SetLike.ext_iff]
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    AbsoluteValue.mem_valuationSubring_iff, ← AbsoluteValue.smul_apply]
  refine ⟨fun h ↦ ?_, fun h x ↦ by rw [h]⟩
  have hequiv : v.IsEquiv (σ • w) := isEquiv_of_forall_le_one_iff fun x ↦ (h x).symm
  exact (eq_of_isEquiv_of_under_eq (K := K) hv hequiv (by simpa using hK.symm)).symm

include K in
/-- The decomposition group of the closed unit ball of any nonarchimedean absolute value on
an algebraic extension is the stabilizer of the absolute value. -/
theorem decompGroup_valuationSubring_eq_stabilizer (hw : IsNonarchimedean w) :
    decompGroup Γ (w.valuationSubring hw) = MulAction.stabilizer Γ w := by
  ext σ
  exact smul_valuationSubring_eq_iff (K := K) hw hw rfl σ

include K in
/-- Frobenius at the closed unit ball fixes the absolute value and acts by the given power
modulo its open unit ball. -/
theorem isFrob_valuationSubring_iff (hw : IsNonarchimedean w) {q : ℕ} {σ : Γ} :
    IsFrob (w.valuationSubring hw) q σ ↔
      σ ∈ MulAction.stabilizer Γ w ∧ ∀ x, w x ≤ 1 → w (σ • x - x ^ q) < 1 := by
  rw [IsFrob, decompGroup_valuationSubring_eq_stabilizer (K := K) hw]
  simp only [ValuationSubring.valuation_le_one_iff, AbsoluteValue.mem_valuationSubring_iff,
    ← ValuationSubring.mem_nonunits_iff, AbsoluteValue.mem_nonunits_valuationSubring_iff]

include K in
/-- Inertia at the closed unit ball fixes the absolute value and acts trivially modulo its
open unit ball. -/
theorem mem_inertiaGroup_valuationSubring_iff (hw : IsNonarchimedean w) {σ : Γ} :
    σ ∈ inertiaGroup Γ (w.valuationSubring hw) ↔
      σ ∈ MulAction.stabilizer Γ w ∧ ∀ x, w x ≤ 1 → w (σ • x - x) < 1 := by
  simp only [mem_inertiaGroup_iff, isFrob_valuationSubring_iff (K := K) hw, pow_one]

end New
