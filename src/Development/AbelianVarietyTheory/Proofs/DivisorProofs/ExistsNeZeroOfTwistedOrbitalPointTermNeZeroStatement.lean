module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwistedOrbitalPointTermNeZero

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct


theorem _root_.GlobalTheory.T.exists_ne_zero_of_twistedOrbitalPointTerm_ne_zero : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G), GlobalTheory.EulerAbs.twTerm θ K δ f y ≠ 0 → ∃ k ∈ K, f ((y * k)⁻¹ * δ * θ (y * k)) ≠ 0 := by
  first | exact @GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero
