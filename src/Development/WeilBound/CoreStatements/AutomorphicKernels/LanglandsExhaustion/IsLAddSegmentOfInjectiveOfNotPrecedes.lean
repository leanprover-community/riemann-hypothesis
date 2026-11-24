module

import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.IsLAddSegmentOfInjectiveOfNotPrecedes
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.CuspEmbP
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PeelDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOrderedFormSnoc
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc GlobalTheory.CompanionTheory.ExhGood

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isL_add_segment_of_injective_of_not_precedes [CharZero k] (HS : GlobalTheory.Published.StandardCosocleGL) (HL : LSocleGL k) (x : IrrGL (k := k))
    (y : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (y a).1 = x.1) (s : Segment k) (𝔫 : Multiset (Segment k))
    (hs : IsLSeg s (y 0).rep) (hn : IsL 𝔫 (y 1).rep)
    (hf : ∃ f : x.rep.IntertwiningMap (prodIrr y hd), Function.Injective f)
    (hp : ∀ Δ ∈ 𝔫, ¬ Δ.Precedes s) :
    IsL (𝔫 + {s}) x.rep := by
  apply CompanionTheory.Exh.isL_add_segment_of_injective_of_not_precedes <;> assumption

theorem peelGoodP (h1 : GlobalTheory.Published.StandardCosocleGL) (h2 : Zc.LSocleGL k) (_h3 : RefineP k) [CharZero k] :
    Zc.PeelGoodP k := by
  intro x y hd Δ 𝔫 hs hn hf hp
  exact isL_add_segment_of_injective_of_not_precedes h1 h2 x y hd Δ 𝔫 hs hn hf hp

end PositivityTheory.Exh

end
