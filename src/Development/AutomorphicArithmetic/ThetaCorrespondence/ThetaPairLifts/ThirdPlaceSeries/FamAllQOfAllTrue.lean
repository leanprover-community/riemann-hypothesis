module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColSideStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreDataOfPointStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricDatumOfFamilyStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LawsLinksOfGeoRowsColsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkOntoOfOntoAllStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkZeroOfChartZeroStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneCentralPinStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedOfTrueStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowChExistsStatement
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MiTop
theorem famAllQ_of_allTrue_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → 1 ≤ B.R.rS → GlobalTheory.ChainOnto.OntoAll (I.rec7 l Z) → _root_.GlobalTheory.MiTop.FamilyAllConditions W := by
  intro hCD hDS hHC hSA B X I l Z L hT Gi Gl Kc Yd cX ex W hA hr ho
  have hpk := hA.pk
  obtain ⟨z, hzC, hzZ, hz⟩ := _root_.GlobalTheory.T.exists_botDat_of_placedP_framed W hpk hr
  refine ⟨z, hzC, hzZ, fun u => ?_⟩
  obtain ⟨a, haI, haT, haO, haF⟩ := _root_.GlobalTheory.T.all_true_family_datum_alt hDS hHC hSA W hA u
  obtain ⟨row, hrI, hrS⟩ := _root_.GlobalTheory.T.exists_pairwise_same_choices_at_geo hCD W u hpk a.g
  have hcol := fun k => _root_.GlobalTheory.T.true_geometry_family_invariance_alt hDS hHC W hA u a haI haT haO k row hrI hrS
  obtain ⟨col, hOK, hLaws, hCZ, hTail, hComm, hRat⟩ :=
    _root_.GlobalTheory.T.true_geometry_family_column_data_alt hDS hHC hSA W hA u a haI haT row hrI hrS hcol
  have hc : (a.fam row col).c.Is := (_root_.GlobalTheory.T.famCh_is_and_tuples_is_of_colOK hDS hHC W u hpk (a.fam row col) hOK).1
  have hPl := _root_.GlobalTheory.T.placed_p_of_true_geometry W hA u a haI haT row col hc
  obtain ⟨d, hdB, hdb, hdz⟩ := hz u (a.fam row col) a.d.B hPl haF
  refine ⟨a.fam row col, d, hdz, hLaws, ?_, hTail, _root_.GlobalTheory.T.linkDown_of_famCh W u hpk _ hOK, _root_.GlobalTheory.T.linkOnto_of_ontoAll' W u hpk ho _ hOK, hComm, hRat⟩
  refine _root_.GlobalTheory.T.linkZero_of_chartZero' W u (a.fam row col) d hCZ (fun h₀ => ?_) hdb
  rw [hdB]
  exact haI.bot.1 h₀
end GlobalTheory.MiTop
end
