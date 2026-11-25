module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightExponentStrictlyAntitone

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

theorem _root_.GlobalTheory.T.weight_exponent_strictly_antitone : ∀ (n : ℕ) (l : Fin (n / 2) → ℤ), Cone l → StrictAnti (wexp n l) ∧ ∀ i, wexp n l (Fin.rev i) = -wexp n l i := by
  first | exact @GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev
