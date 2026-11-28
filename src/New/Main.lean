module

public import New.Reduction.OneSidedBound
import TauCeti.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis

/-!
# From non-vanishing in Re s > 1/2 to zeros on the critical line

In the open critical strip the functional equation sends a zero at `s` for `χ` to a zero at `1 - s`
for `χ⁻¹`. Complex conjugation gives a zero at `1 - conj s` for `χ` itself.
Thus the half-plane bound `DirichletLNonvanishingRightOfHalf`
rules out zeros to the left of the critical line as well.

* `New.zeros_on_line`: the zeros of `L(s, χ)` in `0 < re s < 1` have `re s = 1 / 2`.
* `New.zeta_zeros_on_line`: the character modulo `1` supplies the half-plane bound for `ζ`, so its
  nontrivial zeros lie on the critical line.

## Relation to the literature

Known result: the passage from the half-plane to the critical line by the functional equation. The
non-vanishing itself is `New.grh`.
-/

@[expose] public section

open Complex DirichletCharacter

variable (h : DirichletLNonvanishingRightOfHalf)

include h

/-- Assume `DirichletLNonvanishingRightOfHalf` (hypothesis `h`): Dirichlet L-functions do not vanish
for Re s > 1/2, the pole excepted. Then `DirichletLZerosOnLine` holds: every zero s of a Dirichlet
L-function with 0 < Re s < 1 has Re s = 1/2. -/
lemma New.zeros_on_line : DirichletLZerosOnLine := by
  refine fun N _ χ ↦ χ.zeroFreeRightOf_one_half_LFunction_iff_re_eq_one_half.mp ?_
  refine TauCeti.zeroFreeRightOf_iff.mpr fun s hs ↦ ?_
  rw [← not_lt, χ.meromorphicOrderAt_LFunction_pos_iff]
  exact fun ⟨hz, hpole⟩ ↦ h N χ s hs hpole.symm hz

/-- Assume `DirichletLNonvanishingRightOfHalf` (hypothesis `h`): Dirichlet L-functions do not vanish
for Re s > 1/2, the pole excepted. Then `RiemannZetaZerosOnLine` holds: every zero s of ζ outside
{1, −2, −4, …} has Re s = 1/2. -/
lemma New.zeta_zeros_on_line : RiemannZetaZerosOnLine := by
  apply TauCeti.riemannHypothesis_iff_riemannZeta_ne_zero.mpr
  intro s hs
  obtain rfl | hs₁ := eq_or_ne s 1
  · exact riemannZeta_one_ne_zero
  · simpa only [LFunction_modOne_eq] using h 1 1 s hs (Or.inr hs₁)
