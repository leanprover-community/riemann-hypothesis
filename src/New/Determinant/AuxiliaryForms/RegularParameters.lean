module

import TauCeti.RepresentationTheory.DiscreteSeries.RegularParameter
import Mathlib.Algebra.Order.Star.Int
public import Lib.GLn.SchurModule.SchurOrthogonality
public import Lib.Weil.Construction.ThetaJets
import New.UpperBound.Kernels.JetConjugatesAndBounds

/-!
# Weights of regular parameters and bounds on boxes

A weight is a pair `(κ, e)`: `κ w h` is the number of columns of height `h` at the place `w`, and
`e w` is the power of the determinant. `New.IsHCParam κ e l` says that `l w` lists twice the
Harish-Chandra parameter of `(κ, e)` in some order. This file finds a weight for each regular
parameter `l = 2λ` (`New.HCParam.HasGap`) using
`TauCeti.RepresentationTheory.DiscreteSeries.RegularParameter` at each place. It also bounds a
weight by its parameter: the number of boxes and the power of the determinant.

## Main definitions and results

* `New.Exchange.boxes_le_card_mul_of_isHCParam`, `New.Exchange.natAbs_le_of_isHCParam`: a bound `β`
  on the entries of `l` bounds the number of boxes and, for nonempty `n`, the determinant power.
* `New.Exchange.exists_isHCParam_of_hasGap`: every regular parameter comes from a weight;
  `New.Exchange.exists_isHCParam_of_le` adds control of the determinant power from below.

Notions from other files:
* `New.boxes κ N`: the number of boxes in the columns of height below `N`, over all places.
-/

@[expose] public section

noncomputable section

section WeightsOfParameters

open Finset Fintype

namespace New.Exchange

variable {Φ n : Type} [Fintype Φ] [Fintype n]

private lemma isHCParam_iff {κ : Φ → ℕ → ℕ} {e : Φ → ℤ} {l : Φ → n → ℤ} :
    IsHCParam κ e l ↔ ∀ w, TauCeti.IsDoubledHCParameter (κ w) (e w) (l w) := by
  simp only [IsHCParam, TauCeti.isDoubledHCParameter_iff, TauCeti.doubledHCParameter_eq,
    hcParameter, diagramWeight_apply, Nat.cast_sum]

/-- If `l` lists twice the Harish-Chandra parameter of the weight `(κ, e)` (`IsHCParam`), where
`κ w h` is the number of columns of height `h` at the place `w : Φ`, and `|l w i| ≤ β` for all `w`
and `i`, then `κ` has at most `card Φ * card n * β` boxes in columns of height below `card n`. -/
lemma boxes_le_card_mul_of_isHCParam {κ : Φ → ℕ → ℕ} {e : Φ → ℤ} {l : Φ → n → ℤ}
    (hl : IsHCParam κ e l) {β : ℕ} (hβ : ∀ (w : Φ) (i : n), |l w i| ≤ β) :
    boxes κ (Fintype.card n) ≤ Fintype.card Φ * Fintype.card n * β := by
  simpa only [TauCeti.boxesBelow_def] using
    TauCeti.sum_boxesBelow_le (isHCParam_iff.mp hl) hβ

/-- Let `n` be nonempty. If `l` is twice the Harish-Chandra parameter of the weight `(κ, e)` and
`|l w i| ≤ β` for all `i`, then the power of the determinant at `w` satisfies `|e w| ≤ β`. -/
lemma natAbs_le_of_isHCParam [Nonempty n] {κ : Φ → ℕ → ℕ} {e : Φ → ℤ} {l : Φ → n → ℤ}
    (hl : IsHCParam κ e l) {β : ℕ} {w : Φ} (hβ : ∀ i : n, |l w i| ≤ β) : (e w).natAbs ≤ β := by
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
  exact (isHCParam_iff.mp hl w).abs_le hβ

/-- Let each `l w` be a parameter of gap `c` for the signs `s`, and let
`e w ≤ l w i / 2 + card n / 2` for all `i` (integer divisions). Then `l` is twice the Harish-Chandra
parameter of a weight with column multiplicities `f` and determinant power `e w + f w (card n)`. The
parameter sees only the columns of height below `card n` and the determinant power, so above that
height `f` can be prescribed, as `κ`. -/
lemma exists_isHCParam_of_le {s : n → ℤˣ} (κ : Φ → ℕ → ℕ) {e : Φ → ℤ} {c : ℕ} {l : Φ → n → ℤ}
    (hc : ∀ w : Φ, (toHCParam s (l w)).HasGap c)
    (he_le : ∀ (w : Φ) (i : n), e w ≤ l w i / 2 + Fintype.card n / 2) :
    ∃ f : Φ → ℕ → ℕ,
      IsHCParam f (fun w : Φ ↦ e w + f w (Fintype.card n)) l ∧
      ∀ w : Φ, ∀ k > Fintype.card n, f w k = κ w k := by
  have he (w : Φ) (i : n) : 2 * e w + 1 - Fintype.card n ≤ l w i := by
    have := he_le w i
    have : (l w i + Fintype.card n - 1) % 2 = 0 := Int.even_iff.mp ((hc w).parity i)
    omega
  choose f h_high hf using fun w ↦
    TauCeti.exists_isDoubledHCParameter_of_le (hc w).injective (hc w).parity (he w) (κ w)
  exact ⟨f, isHCParam_iff.mpr hf, h_high⟩

/-- If every `l w` is a parameter of gap `c` for the signs `s` (in particular, its entries are
distinct and have the parity of `card n - 1`), then `l` is twice the Harish-Chandra parameter of
some weight `(κ, e)`. -/
lemma exists_isHCParam_of_hasGap {s : n → ℤˣ} {c : ℕ} {l : Φ → n → ℤ}
    (hc : ∀ w : Φ, (toHCParam s (l w)).HasGap c) :
    ∃ (κ : Φ → ℕ → ℕ) (e : Φ → ℤ), IsHCParam κ e l := by
  choose κ e he using fun w ↦ TauCeti.exists_isDoubledHCParameter (hc w).injective (hc w).parity
  exact ⟨κ, e, isHCParam_iff.mpr he⟩

end New.Exchange

end WeightsOfParameters

end
