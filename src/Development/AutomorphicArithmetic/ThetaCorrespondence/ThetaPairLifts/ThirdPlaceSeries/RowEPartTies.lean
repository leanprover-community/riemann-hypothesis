module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeParametersNumericaStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MoreOfTiesB
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PathCoreConditionsOfParametersFreeConditionsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowETiesB
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



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PlugPt
theorem rowE_part_ties_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (Q : V4.Slot),
    CoreSlot 𝒮 → RowE (Bd := _root_.GlobalTheory.Fc.Ind.PointSummands) (sAnd Q RayPosition) (linkOf fun K p c b => _root_.GlobalTheory.PlugPt.pinnedPointOfReading ν K p c b.pt)
      fun _ D O c b => TiesB D O c b.pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧ More b.pt := by
  intro hR hL 𝒮 ν Q hC
  refine (EvP.and (_root_.GlobalTheory.PlugPt.rowE_tiesB_alt hR hL 𝒮 ν Q hC) GlobalTheory.T.eventually_constructedPoint_hostSize_numerical).mono ?_
  intro κ K _ H β hq c b hl
  obtain ⟨p, b', hpin, heq⟩ := hl
  have hl' : linkOf (_root_.GlobalTheory.PlugPt.pinnedPointOfReading ν) K β c b.pt :=
    ⟨p, b'.pt, hpin, congrArg (fun y : (Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.Ind.PointSummands D O c) =>
      (⟨y.1, y.2.1, y.2.2.pt⟩ : Σ (D : D7) (O : Obj D), BdPt D O c)) heq⟩
  have ht : TiesB β.D β.O c b.pt := H.1 β hq c b.pt hl'
  have hs : FieldSmall β.D β.O.L := ((H.2 β).2 _ ht.1.tied.field).2.2
  have hw : SingleIndexPlacesAreTwisted b.pt := fun w hw => ((b.muDef 0 0).2.2.2 w).2 hw
  exact ⟨ht, ⟨hs, (GlobalTheory.T.pathCoreConditions_of_intrinsicConditions β.D β.O c b.pt ht hs).2.2.1⟩, GlobalTheory.PlugPt.more_of_tiesB β.D β.O c b.pt ht hs hw⟩
end GlobalTheory.PlugPt
end
