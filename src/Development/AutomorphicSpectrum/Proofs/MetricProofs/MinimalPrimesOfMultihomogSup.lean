module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.MinHom

open MvPolynomial ReciprocityTheory.AnForm.R

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomogIdeal_of_mem_minimalPrimes_sup :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)),
      IsMultiHomogIdeal P → IsMultiHomogIdeal D →
        ∀ Q ∈ (P ⊔ D).minimalPrimes, IsMultiHomogIdeal Q := by
  intro K _ ι _ P D hP hD Q hQ
  classical
  have toGeo : ∀ I : Ideal (MvPolynomial (Σ k, ι k) ℂ), IsMultiHomogIdeal I →
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := ℂ) (ι := ι) I := fun I h => h
  have hQ' : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := ℂ) (ι := ι) Q :=
    ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_isHomogeneous fun k =>
      ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_mem_minimalPrimes _
        ((ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_isMultiHomogIdeal (toGeo P hP) k).sup
          (ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_isMultiHomogIdeal (toGeo D hD) k)) hQ
  exact hQ'

end GlobalTheory.CompanionTheory.Ar.Cmp.MinHom
