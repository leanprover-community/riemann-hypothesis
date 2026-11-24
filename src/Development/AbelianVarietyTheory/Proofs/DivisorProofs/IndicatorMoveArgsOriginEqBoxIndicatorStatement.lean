module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorUniformizerExponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorMoveArgsOriginEqBoxIndicator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem _root_.GlobalTheory.T.indicator_moveArgs_origin_eq_box_indicator : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (a a' : ℤ) (g : G.VertexGroup), (∀ j, g (G.m, j) = colDiag G ϖ a a' j) → ∀ e : Vars G, Set.indicator {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} (1 : G.Args → ℂ) (G.moveArgs .one g (fill hs 0 0 e)) = (box G ϖ a a').indicator (1 : Vars G → ℂ) e := by
  first | exact @GlobalTheory.OriginBox.indicator_moveArgs_origin | exact GlobalTheory.OriginBox.indicator_moveArgs_origin | (intros; apply GlobalTheory.OriginBox.indicator_moveArgs_origin <;> assumption)
