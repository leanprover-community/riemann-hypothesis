module

public import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Metric Formalism.MainNotions.S Formalism.MainNotions.S.Gauge
open scoped Classical

def expR {n : ℕ} (ε : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) : Formalism.REAL.UJ ε :=
  if h : Formalism.REAL.inUJ ε (NormedSpace.exp (unrealify x)) then ⟨(Matrix.isUnit_exp (unrealify x)).unit, h⟩ else 1

def ExpProdU : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))),
    m ⊔ h = gLie ε → (∀ x ∈ m, ∀ y ∈ h, inner ℝ x y = 0) →
    ∀ (ι η : Type) [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h),
    GaugeDens ε → ∃ r : ℝ, 0 < r ∧ ∃ D : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ,
      ContinuousAt D 0 ∧ D 0 = gaugeU ε ∧ Measurable D ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r, MeasurableSet A →
        Formalism.REAL.muG ε ((fun p => expR ε (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) *
          expR ε (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' A) =
        ∫⁻ p in A, ENNReal.ofReal (D p)

end PI.AprimeInfW
