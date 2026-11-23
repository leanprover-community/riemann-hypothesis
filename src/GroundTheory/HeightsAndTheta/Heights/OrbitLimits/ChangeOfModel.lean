module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem genFibreExists : GenFibreExistsStatement := by
  intro K _ ι _ K' _ ι' _ κ v P' d' _ hP'
  exact Inter.GenericPointExists.proof K ι K' ι' v P' hP'.2.1.1

theorem existsUniqueAll : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)], ExistsUniqueStatement F ι := by
  intro F _ K _ ι _
  exact ExistsUnique.full F ι

theorem ChangeOfModel.of_found (hAI3 : Inter.PushforwardArithIntersection.Statement) (hGr : GraphStatement)
    (hIso : HilbertSamuel.IsomInvariance.Statement) (hGI : HilbertSamuel.GraphIsometric.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement :=
  HilbertSamuel.ChangeOfModel.proof hAI3 hGr genFibreExists existsUniqueAll hIso hGI

end GroundTheory.Heights₂.Heights.Targets
