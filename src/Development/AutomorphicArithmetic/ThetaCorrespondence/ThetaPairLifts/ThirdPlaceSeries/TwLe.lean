module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistUpperBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefStStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatStHoldsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesStStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStAltBisStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceStStatement
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct


open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp.TupLe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem twLe_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.TwistUpperBound₂ := by
  intro _ _ _ hA hX
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA hX) fun Fm x hx i p hr hm w hw j ⟨a, c⟩ ρ hρ ν rd hf hc => ?_
  have hL := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have h0 := baseOf_of_pin (cG := p.cG) p.charW.base.lev hρ hf.pin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  obtain ⟨c1, c2⟩ := c ρ hρ hf.adapted
  obtain ⟨-, e, h1, h2⟩ := hf.adapted
  exact _root_.GlobalTheory.BigOn.Exp.TupLe.realTw_le_alt _root_.GlobalTheory.T.seesaw_places_statement _root_.GlobalTheory.T.tuple_flat_estimate _root_.GlobalTheory.T.tupLe_traceSt _root_.GlobalTheory.T.tuple_coef_le _root_.GlobalTheory.T.small_tuple_statement_alt hr hm hL hw a.1 hρ hf.pin hf.level
    { h0 with } e h1 h2 c1 c2 hf.norm hf.rat hc
end GlobalTheory.BigOn.Exp.TupLe
end
end
