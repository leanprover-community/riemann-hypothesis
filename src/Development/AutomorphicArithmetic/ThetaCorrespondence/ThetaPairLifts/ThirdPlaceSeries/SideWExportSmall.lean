module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideOf
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmallFrameAtColumnStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WPtFrame
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

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem sideW_export_small_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), Nonempty (GlobalTheory.SeriesTie.ExportTie (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).YS (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).v₀) ∧ LevelIs (p.w.D p.Z).nexp ((_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).R.eG.trans (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cG) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).P0 (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).ψ0⁻¹ ∧ AllData (p.w.D p.Z).nexp p.O.ex.xd.xd0 ∧ SmallHas (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf := by
  intro hR hL 𝒮 ν K p
  have hE : (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).Export p.O.ex.xd := (ν.rd _ _ _ _ _ _ _ _ _ _ _ _ p.x.nx).2.1.down
  have hcf : (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf = Fr.at (p.w.st p.Z) p.f := (GlobalTheory.Plug.wPt_frame 𝒮 K p).2.1
  refine ⟨hE.1, hE.2.1, hE.2.2, ?_⟩
  rw [hcf]
  exact GlobalTheory.T.small_frame_at_column hR p.B p.f p.T p.w p.Z
end GlobalTheory
end
