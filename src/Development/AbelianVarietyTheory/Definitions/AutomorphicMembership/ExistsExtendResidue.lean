module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackAbVarModel

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField TopologicalSpace IsLocalRing
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.ShFam GlobalTheory.TotalFrame GlobalTheory.FlagPts Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts
open Formalism.MainNotions.DIV.Cons (SCF intO)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

variable {P : ∀ B : Mdl Y i₀, Lat B → Prop}

end Family

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

section Reduction

end Reduction

section Point

variable {Z : ct.Mdl} (y : ct.Pt Z)

end Point

end At

end GlobalTheory.LocM
