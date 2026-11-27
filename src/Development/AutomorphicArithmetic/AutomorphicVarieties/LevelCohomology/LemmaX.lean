module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliSharperConductor

/-! # The Bernoulli-unit lemma with the halved dyadic conductor bound -/

@[expose] public section

namespace UpperTheory.V.X

/-- The first generalized Bernoulli number of the product character is an ℓ-adic unit
under the conductor, parity and order conditions in `XData`. -/
theorem lemmaX : LemmaX := by
  intro ℓ _ d f n φ ξ h
  exact norm_genB_prodX_of_halved_conductor h.d_pos h.four h.f_odd h.big φ ξ h.ord h.prim2 h.odd

end UpperTheory.V.X
