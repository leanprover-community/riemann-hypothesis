module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev quadField (H : Host E) : IntermediateField ℚ E := IntermediateField.adjoin ℚ {((H.rt : 𝓞 E) : E)}

instance (H : Host E) : Fact H.d.Prime := ⟨H.d_prime⟩

def TameAtRamified (H : Host E) : Prop :=
  ∀ (l : ℕ) (w : Ideal (𝓞 E)), l.Prime → (l : ℤ) ∣ discr E → w.IsMaximal → (l : 𝓞 E) ∈ w →
    w.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ w ∧
    (l ≠ H.d → ∃ a ∈ Algebra.adjoin ℤ {H.w0}, a ∈ w ∧ H.bar a ∉ w) ∧
    (l = H.d → (l : 𝓞 E) ∉ w ^ 3)

section Degree

variable (k : Type) [Field k] [NumberField k]

end Degree

section Lie

variable {H : Host E} {k : Type} [Field k] [NumberField k]

end Lie

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification
