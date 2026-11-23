module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoreSlotConstructionMonoFewerCoresBothPasses
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsOfStrongerNExt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Glob
theorem open_and_linked_of_stronger_extension_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N N' : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N' K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c)) → (∀ H : ∀ 𝒜 : FamClass, RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜 → Prop, _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L H) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ) (fun Q L => Row Q L H)) ∧ (_root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) → _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ)) := by
  intro hL N N' S Γ hN
  obtain ⟨hB, hG, hLk, -⟩ := _root_.GlobalTheory.HeightCounting.Up.rows_of_stronger_nExt_alt hL N N' S Γ hN
  have m : ∀ H : ∀ 𝒜 : FamClass, RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜 → Prop, _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L H) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ) (fun Q L => Row Q L H) :=
    fun H h => GlobalTheory.HeightCounting.Up.eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => GlobalTheory.HeightCounting.Up.row_mono_id hS hLk h) h
  exact ⟨m, fun o => ⟨m _ o.hPA, m _ o.hLamP, m _ o.hDivG, m _ o.hDcPtG, m _ o.selJ, m _ o.tie, m _ o.lab, m _ o.good, m _ o.geo, m _ o.mi, m _ o.kap, m _ o.df⟩⟩
end GlobalTheory.Glob
end
