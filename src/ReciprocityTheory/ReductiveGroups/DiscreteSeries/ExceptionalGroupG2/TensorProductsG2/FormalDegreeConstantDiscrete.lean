module

public import Formalism.PeriodIntegrals.ZuckTensor
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Transported
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdCons
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Consumer

@[expose] public section

noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

theorem zuckerman_tensor_exists :
    ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
      PI.UpqRep.IsHCParam μ → PI.UpqRep.IsDS ε μ σ → ∀ h : ℝ, PI.ZuckTensor.GapAtLeast ε μ h → thrS ε + 1 < h →
        ∃ X : PI.ZuckTensor.TensorDS n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ + Pi.single s 1) :=
  zuckG

theorem zuckerman_dual_tensor_exists :
    ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
      PI.UpqRep.IsHCParam μ → PI.UpqRep.IsDS ε μ σ → ∀ h : ℝ, PI.ZuckTensor.GapAtLeast ε μ h → thrS ε + 1 < h →
        ∃ X : PI.ZuckTensor.TensorDSd n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ - Pi.single s 1) :=
  zuckDualG

variable {n : ℕ}

section FdCons

open ReciprocityTheory.ChartRestriction.DS.S7

theorem formal_degree_constant_measure (n : ℕ) (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H),
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      thrS ε + 1 < h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      (∀ μ : Fin n → ℝ, IsHCParam μ → GapAtLeast ε μ h →
        ∃ (T : KType ε (lowK ε μ)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε μ T Ψ) →
      v ≠ 0 → Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) σ v = c * Formalism.QuantumDeterminants.fdegHC lam :=
  fdCons_muG n ε

end FdCons

end ReciprocityTheory.ChartRestriction.DS.G2
