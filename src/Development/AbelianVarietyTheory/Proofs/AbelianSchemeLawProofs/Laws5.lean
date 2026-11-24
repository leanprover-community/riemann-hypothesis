module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRingActionOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLinearOfIsPullUniformisation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TraceFormTwistIsoOfPullback
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
theorem _root_.GlobalTheory.laws5 (hG : _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) (hS : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt) : _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws5 := by
  refine ⟨?_, _root_.GlobalTheory.qkToAk_baseChange hG hS, _root_.GlobalTheory.psiOnExists⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.OLinBaseChangeSt
  intro R R' _ _ _ _ I I' hI hI' φ D A G _ _ U G' _ _ bc hbc A' D' hD U' hU O _ _ _ ιD ιA ιG
    hlin ιG' hG' ιA' hA'
  obtain ⟨x, ιD', h1, h2⟩ :=
    _root_.GlobalTheory.exists_oAct_of_isPullDeg hG R R' φ D.toPre D'.toPre hD O ιD
  letI := x
  refine ⟨x, ιD', h1, h2, ?_, ?_⟩
  · apply _root_.GlobalTheory.PullLinear.oLinear_of_isPullUnif R R' I I' φ D D' hD A A' G G' bc hbc U U' hU O
      ιD ιD' ιA ιA' ιG ιG'
    all_goals assumption
  · exact _root_.GlobalTheory.traceFormTwistIso_of_overPullback R R' φ D.toPre D'.toPre hD O ιD ιD' h1 h2

end GlobalTheory
