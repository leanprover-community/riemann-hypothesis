module

public import TauCeti.Analysis.AbsoluteValue.Equivalence
public import Lib.Adelic.Adeles.Basic
public import Lib.ClassField.Places.GaloisDefs
import Lib.ClassField.Places.ValuationSubrings

/-!
# Places as valuation subrings and as absolute values

In this library a place of `Ω` is a valuation subring `A`. This file compares the notions built on
`A` with the same notions for an absolute value `w` on `Ω` whose closed unit ball is `A`, that is,
`x ∈ A ↔ w x ≤ 1`. If `w` restricts to the real or a `p`-adic absolute value on `ℚ`, an element of
`Γ` stabilises `A` exactly when it preserves `w`, so decomposition groups, Frobenius elements and
inertia groups can be read off from `w`. Over a number field `K`, `A` lies over the prime `v` of
`𝓞 K` exactly when the restriction of `w` to `K` is equivalent to the `v`-adic absolute value.

## Main results

* `New.isEquiv_of_forall_le_one_iff`: two absolute values on a field with the same closed unit ball
  are equivalent.
* `New.valuation_lt_one_iff_of_forall_mem_iff`: the maximal ideal of `A` is the open unit ball of
  `w`.
* `New.mem_decompGroup_iff_of_forall_mem_iff`: `σ` stabilises `A` iff `w (σ • x) = w x` for all `x`.
* `New.isFrob_iff_of_forall_mem_iff`, `New.mem_inertiaGroup_iff_of_forall_mem_iff`: Frobenius
  elements and the inertia group of `A` in terms of `w`.
* `New.isPlaceOver_iff_isEquiv_adicAbv`: `A` lies over `v` iff `w.under K` is equivalent to the
  `v`-adic absolute value `NumberField.HeightOneSpectrum.adicAbv K v`.

Notions from other files:
* `Rat.AbsoluteValue.IsStandard` (Tau Ceti): an absolute value on `ℚ` is the real one or a `p`-adic
  one.
* `AbsoluteValue.under` (Mathlib): the restriction of an absolute value to a subfield.

## Relation to the literature

Known; see Neukirch, *Algebraic Number Theory*, Ch. II, §§3 and 9.
-/

@[expose] public section

open NumberField NumberField.HeightOneSpectrum

namespace New

section Field

variable {F : Type*} [Field F] {v w : AbsoluteValue F ℝ}

/-- `w x < 1` says that `x` is zero or that `w x⁻¹ ≤ 1` fails. -/
private lemma apply_lt_one_iff_or {x : F} : w x < 1 ↔ x = 0 ∨ ¬w x⁻¹ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [map_inv₀, inv_le_one₀ (w.pos hx)]
    simp [hx]

/-- Two absolute values on a field with the same closed unit ball are equivalent. -/
theorem isEquiv_of_forall_le_one_iff (h : ∀ x, v x ≤ 1 ↔ w x ≤ 1) : v.IsEquiv w :=
  AbsoluteValue.isEquiv_iff_lt_one_iff.mpr fun _ ↦ by simp only [apply_lt_one_iff_or, h]

end Field

variable {Ω Γ : Type*} [Field Ω] [Group Γ] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω}
  {w : AbsoluteValue Ω ℝ}

/-- If `A` is the closed unit ball of `w`, then `A.valuation x ≤ 1` iff `w x ≤ 1`. -/
theorem valuation_le_one_iff_of_forall_mem_iff (hA : ∀ x, x ∈ A ↔ w x ≤ 1) {x : Ω} :
    A.valuation x ≤ 1 ↔ w x ≤ 1 :=
  (A.valuation_le_one_iff x).trans (hA x)

/-- If `A` is the closed unit ball of `w`, the maximal ideal of `A` is the open unit ball of `w`. -/
theorem valuation_lt_one_iff_of_forall_mem_iff (hA : ∀ x, x ∈ A ↔ w x ≤ 1) {x : Ω} :
    A.valuation x < 1 ↔ w x < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or, hA,
    apply_lt_one_iff_or]

variable {K : Type*} [Field K] [NumberField K] [Algebra K Ω] {v : FinPlace K}

/-- If `A` is the closed unit ball of `w`, then `A` lies over the prime `v` of `𝓞 K` exactly when
the restriction of `w` to `K` is equivalent to the `v`-adic absolute value. -/
theorem isPlaceOver_iff_isEquiv_adicAbv (hA : ∀ x, x ∈ A ↔ w x ≤ 1) :
    IsPlaceOver A v ↔ (w.under K).IsEquiv (adicAbv K v) := by
  have h_adic (x : K) : adicAbv K v x < 1 ↔ v.valuation K x < 1 := by
    rw [adicAbv_def, NNReal.coe_lt_one,
      WithZeroMulInt.toNNReal_lt_one_iff (one_lt_absNorm_nnreal v)]
  refine ⟨fun h ↦ AbsoluteValue.isEquiv_iff_lt_one_iff.mpr fun x ↦ ?_, fun h x ↦ ?_⟩
  · rw [AbsoluteValue.under_apply, ← valuation_lt_one_iff_of_forall_mem_iff hA, h_adic]
    exact h.isEquiv.lt_one_iff_lt_one
  · rw [valuation_lt_one_iff_of_forall_mem_iff hA, ← AbsoluteValue.under_apply, h.lt_one_iff,
      h_adic]
    exact v.valuation_lt_one_iff_mem x

variable [CharZero Ω]

/-- Let `A` be the closed unit ball of `w`, and let `w` restrict to the real or a `p`-adic absolute
value on `ℚ`. Then `σ` stabilises `A` exactly when it preserves `w`. -/
theorem mem_decompGroup_iff_of_forall_mem_iff (hA : ∀ x, x ∈ A ↔ w x ≤ 1)
    (hw : Rat.AbsoluteValue.IsStandard (w.under ℚ)) {σ : Γ} :
    σ ∈ decompGroup Γ A ↔ ∀ x, w (σ • x) = w x := by
  rw [mem_decompGroup_iff]
  refine ⟨fun h ↦ ?_, fun h x ↦ by rw [hA, hA, h]⟩
  -- `x ↦ w (σ • x)` also has closed unit ball `A`, and it agrees with `w` on `ℚ`, so it is `w`.
  let f := MulSemiringAction.toRingHom Γ Ω σ
  have h_equiv : (w.comp (f := f) f.injective).IsEquiv w :=
    isEquiv_of_forall_le_one_iff fun x ↦ (hA _).symm.trans ((h x).trans (hA x))
  have h_nat (n : ℕ) : w (f n) = w.under ℚ n := by
    rw [map_natCast f, AbsoluteValue.under_apply, map_natCast (algebraMap ℚ Ω)]
  have h_eq : w.comp (f := f) f.injective = w :=
    h_equiv.eq_of_isStandard hw hw h_nat fun n ↦ by
      rw [AbsoluteValue.under_apply, map_natCast (algebraMap ℚ Ω)]
  exact fun x ↦ DFunLike.congr_fun h_eq x

/-- Let `A` be the closed unit ball of `w`, and let `w` restrict to the real or a `p`-adic absolute
value on `ℚ`. Then `σ` is a Frobenius element for `q` at `A` exactly when it preserves `w` and
`w (σ • x - x ^ q) < 1` whenever `w x ≤ 1`. -/
theorem isFrob_iff_of_forall_mem_iff (hA : ∀ x, x ∈ A ↔ w x ≤ 1)
    (hw : Rat.AbsoluteValue.IsStandard (w.under ℚ)) {q : ℕ} {σ : Γ} :
    IsFrob A q σ ↔ (∀ x, w (σ • x) = w x) ∧ ∀ x, w x ≤ 1 → w (σ • x - x ^ q) < 1 := by
  rw [IsFrob, mem_decompGroup_iff_of_forall_mem_iff hA hw]
  simp only [valuation_le_one_iff_of_forall_mem_iff hA, valuation_lt_one_iff_of_forall_mem_iff hA]

/-- Let `A` be the closed unit ball of `w`, and let `w` restrict to the real or a `p`-adic absolute
value on `ℚ`. Then `σ` lies in the inertia group of `A` exactly when it preserves `w` and
`w (σ • x - x) < 1` whenever `w x ≤ 1`. -/
theorem mem_inertiaGroup_iff_of_forall_mem_iff (hA : ∀ x, x ∈ A ↔ w x ≤ 1)
    (hw : Rat.AbsoluteValue.IsStandard (w.under ℚ)) {σ : Γ} :
    σ ∈ inertiaGroup Γ A ↔ (∀ x, w (σ • x) = w x) ∧ ∀ x, w x ≤ 1 → w (σ • x - x) < 1 := by
  simp only [mem_inertiaGroup_iff, isFrob_iff_of_forall_mem_iff hA hw, pow_one]

end New
