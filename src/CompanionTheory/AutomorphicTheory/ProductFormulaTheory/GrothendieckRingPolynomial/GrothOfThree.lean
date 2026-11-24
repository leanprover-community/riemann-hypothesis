module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.CuspEmbP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothOfCls
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.PeelGood
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

namespace CompanionTheory.Groth

theorem groth_of_three (hZ : GlobalTheory.Published.SegmentRepresentation)
    (hI : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.Cos.LUnlinkedIrr k)
    (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      CompanionTheory.Exh.MidP k ∧ CompanionTheory.Exh.RefineP k ∧ CompanionTheory.Exh.SwapP k) : GlobalTheory.Published.GrothendieckRingPolynomial :=
  groth_of_cls fun k _ _ _ _ => cls_of hZ k (hI k) (H k)

end CompanionTheory.Groth
