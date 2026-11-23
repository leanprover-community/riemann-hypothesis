module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideOf
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreFrameCompatibleConstructedPointStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WPtFrame
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideWChrStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideWExportSmallStatement
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
theorem GlobalTheory.PlugPt.side_weight_ties_of_ray_field : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮), CoreSlot 𝒮 → ∀ (K : Ctx) (p : WPt 𝒮 K), (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).Ties p.O.ex.errX p.O.ex.xd := by
  intro hR hL 𝒮 ν hC K p
  obtain ⟨hRC, hTC, -⟩ := GlobalTheory.Plug.wPt_frame 𝒮 K p
  have ht := GlobalTheory.T.coreFrameCompatible_constructed_point hR 𝒮 hC K p
  obtain ⟨hpsi, hval, htame⟩ := _root_.GlobalTheory.T.side_weight_psi_choice_tame_tie hL 𝒮 ν K p
  obtain ⟨hser, hlev, hdat, hsmall⟩ := _root_.GlobalTheory.T.side_weight_export_all_data_small_has hR hL 𝒮 ν K p
  refine ⟨?_, ?_, hser, hlev, hdat, hpsi, hval, hsmall, htame⟩
  · show p.x.what₂.r.z.R.C = GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z
    rw [hRC, hTC]
  · show Tied p.O.ex.errX p.x.what₂.r.z.core (GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z)
    rw [hTC]
    exact ht
end
