module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ChiK
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr

@[expose] public section

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def unTw {l : ℕ} [Fact l.Prime] (W : R2 Ω l) (e : ℕ) (χ : G ℚ Ω →* (Qbar l)ˣ) : R2 Ω l :=
  tw W (cycBar ℚ Ω l ^ e * χ⁻¹)

end GlobalTheory.K4
