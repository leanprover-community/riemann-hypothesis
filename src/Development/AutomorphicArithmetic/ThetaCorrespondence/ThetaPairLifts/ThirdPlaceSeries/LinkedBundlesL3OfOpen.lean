module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowOfCovolumeOntoGrid
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWPRowsOfRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventualL3OfCovolume
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedTiesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupAllUsedPart
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Glob.CovolRow
theorem linked_bundles_l3_of_open_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.NT.RayField → _root_.GlobalTheory.CovTop.CovolumeBoundOfX → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.S0.CovolumeBoundThirdPlaceSeries := by
  intro hDS hHC hCR hCW hRay hCov hL N S Γ hN o
  have hA := _root_.GlobalTheory.T.class_sum_divisor_all_alt hRay hL N S Γ hN o.hDivG
  obtain ⟨R, hR, h⟩ := RowL.and (RowL.and (RowL.and (RowL.and o.hPA o.hDivG) o.good) o.geo) hA
  refine ⟨R, hR, h.imp fun 𝒜 σ hsel H => ?_⟩
  obtain ⟨⟨⟨⟨hpa, hdv⟩, hgd⟩, hgeo⟩, hall⟩ := H
  choose τ hτ using fun {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) x hx i => hgeo Fm hc x hx i
  let τ' : _root_.GlobalTheory.Fc.CompatibleSelection σ := fun Fm hc x hx i => τ Fm hc x hx i
  have hduty : ∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm := fun _ Fm hc =>
    let ⟨_, _, h7, _⟩ := hsel Fm hc
    (DQ.familyClass_sevenDuties_and_stableLattices _ Fm h7).1
  have hrows : Ind.EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := _root_.GlobalTheory.Fc.Ind.evW_pRows_of_rows_alt hDS hHC hCR hCW 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') (fun Fm hc x hx i => hpa Fm hc x hx i)
    (fun Fm hc x hx i => _root_.GlobalTheory.Fc.FourBoundsAtBundles.p_div_of_div3g _ (hdv Fm hc x hx i)) hgd
    (fun Fm hc x hx i => ⟨(hτ Fm hc x hx i).2.1, (hτ Fm hc x hx i).2.2.1⟩)
  exact _root_.GlobalTheory.Fc.Ind.eventual_L3_of_covolume_alt hCov 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') hduty hrows
    (GlobalTheory.Fc.FourBoundsAtBundles.evW_of_atAll fun Fm hc x hx i => (hall Fm hc x hx i (τ Fm hc x hx i)).2.2.2.1)
end GlobalTheory.Glob.CovolRow
end
