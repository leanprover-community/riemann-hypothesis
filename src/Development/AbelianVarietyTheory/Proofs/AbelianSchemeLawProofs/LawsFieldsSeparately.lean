module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory


open CategoryTheory AlgebraicGeometry in
theorem _root_.GlobalTheory.lawsFieldsSeparately :
    _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalSectionsRankAlgClosed ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.AmpleSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.KerPowSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.MulPullSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.MulNSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.CubeSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.SquareSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.RigiditySt ∧
      _root_.ReciprocityTheory.ChartRestriction.G.Out.WeilSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.WeilNondegSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.SymLiftSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.IrredSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.GoodPtSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.SerreSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.PolBaseChangeSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.QuotientSt ∧
      _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.CharPairSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.SmoothDenseSt := by
  obtain ⟨h₁, h₂, -⟩ := _root_.GlobalTheory.allSixLaws
  exact ⟨h₁.globalSectionsRank, h₁.secBaseChange, h₁.ample, h₁.kerPow, h₁.mulPull, h₁.mulN, h₁.cube,
    h₁.square, h₁.rigidity, h₁.weil, h₁.weilNondeg, h₁.symLift, h₁.irred, h₁.goodPt, h₁.serre,
    h₁.globalFns, h₁.polBaseChange, h₁.quotient, h₂.secBaseChangeAny, h₂.secTwist, h₂.charPair,
    h₂.smoothDense⟩

end GlobalTheory
