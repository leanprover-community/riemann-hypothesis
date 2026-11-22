module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData

@[expose] public section

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

end Free

variable {D : D7} {A : Amb D} {N j : ℕ}

variable {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (a : At S κ p)

namespace GIso

variable {a} {Z : a.Mdl} {F₁ F₂ F₃ : a.Sh Z}

end GIso

end At

attribute [instance] FrmSt.lvAdd FrmSt.lvMod

attribute [instance] BdySt.iRr BdySt.iRd BdySt.iRl BdySt.iRn BdySt.iRi BdySt.iRc BdySt.iYa BdySt.iYm BdySt.iXa BdySt.iXm BdySt.iSg BdySt.iSk BdySt.iSm BdySt.iSt

attribute [instance] ThgSt.atAdd ThgSt.atFin ThgSt.thGrp ThgSt.snAdd ThgSt.snMod

attribute [instance] JetSt.jAdd JetSt.jMod JetSt.fbAdd JetSt.fbMod

attribute [instance] EvlSt.lgAdd EvlSt.lbAdd EvlSt.ltAdd

attribute [instance] HTpSt.tpAdd HTpSt.omAdd HTpSt.omMod HTpSt.tcAdd HTpSt.tcMod

attribute [instance] HTmSt.obAdd HTmSt.obMod

namespace Stages

variable {ct : At S κ p} (st : Stages ct)

end Stages

end GlobalTheory.LocM
