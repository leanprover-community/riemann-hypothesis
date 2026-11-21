import Formalism.LocalToGlobal.CharacterGerms.RowTieMemCFin
import Formalism.LocalToGlobal.CharacterGerms.ValuationEqSelfOfUnitGerm
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelfCuts
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStabSelf
import Formalism.LocalToGlobal.CharacterGerms.UncurryLogConstantCoeff
import Formalism.SharpRestriction.GrowthBounds.ExponentialPartialDerivatives
import Formalism.LocalToGlobal.CharacterGerms.RowTieMain
import Formalism.LocalToGlobal.CharacterGerms.CoefficientIdentitySelfConjugate
import Formalism.SharpRestriction.GrowthBounds.ProofRowTieVals
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelfU
import Formalism.SharpRestriction.GrowthBounds.CoeffIdentitySelfConjHolds

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField Formalism.L2.FormalSeriesBounds.RF
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def UnitSelfAllSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (d : ℕ) [NeZero d]
    (Orb : Type) [Fintype Orb] (I0 : Orb → Type) [∀ o, Fintype (I0 o)]
    (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)), UnitSelfSt Y p

def GermLiftSelfAllSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (d : ℕ) [NeZero d]
    (Orb : Type) [Fintype Orb] (I0 : Orb → Type) [∀ o, Fintype (I0 o)]
    (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V), GermLiftSelfSt Y p H

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

structure GeoInS : Prop where
  lab : LabSGeoCoreSt Xo c
  ndg : NondegenerateCharts Xo c

  ch : CharacterHypothesisSelfUnramified Xo c

variable {Xo c}
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb]



end Formalism.L2.FormalSeriesBounds
