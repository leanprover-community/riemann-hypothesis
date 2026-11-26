module

public import New.Reduction.OneSidedBound

/-!
# From non-vanishing in Re s > 1/2 to zeros on the critical line

The last step: the usual forms of the hypothesis follow from `DirichletLNonvanishingRightOfHalf`,
the non-vanishing of all Dirichlet L-functions in `re s > 1 / 2`, by the symmetry `s ↦ 1 - s` of the
zeros.

* `New.zeros_on_line`: the zeros of `L(s, χ)` in `0 < re s < 1` have `re s = 1 / 2`.
* `New.zeta_zeros_on_line`: the nontrivial zeros of `ζ` have `re s = 1 / 2`.

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
lemma New.zeta_zeros_on_line : RiemannZetaZerosOnLine := fun s ↦ by
  obtain _ := h 1 1 s, h 1 1 (1 - s), @Nat.or_exists_add_one, riemannZeta_zero
  simp_all
  grind [riemannZeta_def_of_ne_zero, completedRiemannZeta_one_sub, Complex.Gammaℝ_eq_zero_iff]
