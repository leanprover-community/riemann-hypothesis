module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionCompatibleAtReadIdentificationsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionPairingRationalOnRationalPointsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace GlobalTheory.Fc.DivLinked

section Read

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Matrix Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}



theorem divisionRows_pairing_vanishes_of_rational_pairing_law
    (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧
      GlobalTheory.Published.CuspRapidDecay) (x : GlobalTheory.Mem.R3.TwIn ex) (hH : Holds x.R x.F) (hB : Rw.BkLaw D)
    (hV : CxData.BtVanish (fc := x.F.fc) (x.R.toCx3 x.F)) : GlobalTheory.Cp.DivRows3G (GlobalTheory.Mem.R3.divisionPairOfAdelicFormsFaceColumnsData x) := by
  have hRational := GlobalTheory.T.divisionPairing_rational_on_rationalPoints'
    hC D x.G x.Pl0 x.I0 x.T x.A3 _ x.R x.F x.cG ex.p0 x.Y x.Z x.C x.pins hH
  have hRows := (GlobalTheory.T.divisionCompatible_at_readIdentifications
    hC D x.G x.Pl0 x.I0 x.T x.A3 _ x.R x.F x.cG ex.p0 x.Y x.Z x.C x.sEE Yd x.JM x.pins hH
    (fun _ _ => x.div.grp)).2 x.mjH ex.idx (hB hRational) hV
  exact {
    sharpRR := hRows.sharpRR
    baseRR := hRows.baseRR
    divisionRows_rationalLift := fun i t _ => hRows.divisionRows_rationalLift i t
    thTheta := fun i t _ v => hRows.thTheta i t v
    num := ⟨fun i t _ w => hRows.num.Ij i t w, fun i t _ w => hRows.num.jw i t w, hRows.num.etaJ⟩
    colsBk := hRows.colsBk }

end Read

end GlobalTheory.Fc.DivLinked

end
