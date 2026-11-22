module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
public import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeterminantCharacterIdentity

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight MvPolynomial
open scoped nonZeroDivisors Classical

section Minors

variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (R : Type) [CommRing R]

end Minors

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def conjId (H : Host E) (𝔞 : Ideal (𝓞 E)) : Ideal (𝓞 E) := 𝔞.map (H.bar : 𝓞 E →+* 𝓞 E)

end Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

section Coeff

variable {n : ℕ} {T : Type} [AddCommGroup T] [Module c.F T] [Module (𝓞 c.F) T] [IsScalarTower (𝓞 c.F) c.F T]

end Coeff

end GlobalTheory.IndefiniteRowSideFullHecke.DeterminantCharacterIdentity
