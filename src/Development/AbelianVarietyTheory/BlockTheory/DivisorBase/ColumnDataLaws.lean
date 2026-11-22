module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

end Theta

section Frame

variable {D : D7}

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}

variable {U : Unf Xo c σ r} (W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r)
  (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)

end Frame

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RowDat

variable {T : CoreJ D} {i : Fin D.R.m} (Y : RowDat T G i)

variable (R : RealDat D A Ks)

end RowDat

end Row

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws
