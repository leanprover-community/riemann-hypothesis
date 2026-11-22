module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.EmbeddingHermitianPairs

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

variable (X : Data E r) (x : Frame X.Ψ r)

end Frame

section Torus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x : Frame X.Ψ r}

end Torus

section Relab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ)

end Relab

section Letters

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

end Letters

section Map

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

end Map

section Pin1

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

end Pin1

end ReciprocityTheory.ChartRestriction.G.PullbackSections
