module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormB

@[expose] public section

set_option linter.style.haveILetI false

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HDiscOmL

open IsDedekindDomain IsLocalRing Module

variable {R F : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)]

omit [IsDomain R] [UniqueFactorizationMonoid R] [IsFractionRing R F] in
theorem prod_zpow {κ G : Type*} [CommGroupWithZero G] {x : G} (hx : x ≠ 0) (s : Finset κ)
    (f : κ → ℤ) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hx]

end HDiscOmL

end ReciprocityTheory.ChartRestriction.G.T0
