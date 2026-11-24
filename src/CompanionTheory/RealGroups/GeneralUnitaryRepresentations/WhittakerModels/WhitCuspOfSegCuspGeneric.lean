module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.WhittakerModels.RankDual
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.WhittakerModels.UnipBEqUnipotent
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.WhittakerModels.WhitLeOneOfDict
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace CompanionTheory.rg.gu.whit

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem whitLeOne : GlobalTheory.BZMir.Whit.WhitLeOne k :=
  whitLeOne_of_dict k (unipB_eq_unipotent k) (whitChar_eq_psiN k)
    (fun ρ N θ => rank_twJacquet_le_one_iff ρ N θ) (fun ρ => isAdmissible_iff ρ)

theorem whitRankIrr : GlobalTheory.BZSeg.WhitRankIrr k :=
  fun ψ hψc hψ1 N V _ _ π hs hirr => whitLeOne k N ψ V π hs hirr hψc hψ1

end CompanionTheory.rg.gu.whit
