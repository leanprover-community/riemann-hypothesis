module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideOf
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RayClassFieldsInCoefficientFieldConstructedPointStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SeriesUpdatePreservesParametersFreeConditionsRayFielStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RaysOfRayRecStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideWTiesStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PlugPt
theorem rowE_tiesB_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (Q : V4.Slot),
    CoreSlot 𝒮 → RowE (sAnd Q RayPosition) (linkOf (_root_.GlobalTheory.PlugPt.pinnedPointOfReading ν)) fun _ => TiesB := by
  intro hR hL 𝒮 ν Q hC
  refine RowE.of_all ?_
  intro κ K β c b _ hq hl
  have hray : RayRec β.D β.O.ex.nch := GlobalTheory.T.rayClassFieldsInCoefficientField_constructedPoint K β hq.2
  obtain ⟨p, b', ⟨kap, lam, err, hs⟩, heq⟩ := hl
  let F : (Σ (D : D7) (O : Obj D), BdPt D O c) → Prop := fun x => RayRec x.1 x.2.1.ex.nch → TiesB x.1 x.2.1 c x.2.2
  have hp : F ⟨p.w.D p.Z, p.O, b'⟩ := by
    intro hr
    have hu := GlobalTheory.T.seriesUpdate_preserves_parameterFreeConditions_rayFields _ _ (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p) p.O.ex.errX p.O.ex.xd kap lam err
    show (sidePt b').Ties p.O.ex.errX p.O.ex.xd ∧ (sidePt b').Rays
    rw [hs]
    exact ⟨hu.1 (_root_.GlobalTheory.T.side_weight_ties_err_of_ray_field_core_slot hR hL 𝒮 ν hC K p), hu.2 (_root_.GlobalTheory.T.side_weight_rays_of_ray_rec' hL 𝒮 ν K p hr)⟩
  have hb : F ⟨β.D, β.O, b⟩ := (congrArg F heq).mpr hp
  exact hb hray
end GlobalTheory.PlugPt
end
