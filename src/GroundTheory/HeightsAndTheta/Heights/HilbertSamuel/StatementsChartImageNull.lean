module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
public import Mathlib.RingTheory.Nullstellensatz
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ChartDimLt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ)
    (p : (k : K) → ι k),
    IsMultiHomogIdeal J →
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) < ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ ReciprocityTheory.AnForm.R.chartIdeal J p) < (e : WithBot ℕ∞)

def ChartRatioImageNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) < (e : WithBot ℕ∞) →
      volume {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ J, Ψ (segre z) 0 ≠ 0 ∧
        (Fin.cons 1 y : Fin (e + 1) → ℂ) = (Ψ (segre z) 0)⁻¹ • Ψ (segre z)} = 0

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
