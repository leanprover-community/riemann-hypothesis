module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivSupport
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumRatSection
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem Multilin.of_found
    (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u})
    (hEx : FieldNumbers.ExistsForm.Statement.{u})
    (hDiv : FieldNumbers.DivCycleSupport.Statement.{u})
    (hAdd : FieldNumbers.IntNumAdd.Statement.{u})
    {K : Type} [Fintype K] (F : Type u) [Field F] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.MultilinStatement F ι := by
  classical
  intro I hI V n L j a b hV
  have e : ∀ L' : Fin n → K → ℤ, I V n L' = intNum F V L' := fun L' =>
    Numbers.agree_of hBase hCut hEx hDiv I hI V n L' hV
  have hP : NumbersDVR.IsMultiProjPrime V := (Objects.isMultiProjPrime_iff V).mpr hV.1
  rw [e, e, e]
  exact hAdd F K ι V hP.multiHomog hP.relevant n (relDim_eq_of_ringKrullDim V n hV.2) L j a b

theorem Multilin.full {K : Type} [Fintype K] (F : Type u) [Field F] (ι : K → Type)
    [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.AI.I1.MultilinStatement F ι :=
  Multilin.of_found FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
    FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full FieldNumbers.IntNumAdd.full F ι

end GroundTheory.Heights₂.Heights.Targets
