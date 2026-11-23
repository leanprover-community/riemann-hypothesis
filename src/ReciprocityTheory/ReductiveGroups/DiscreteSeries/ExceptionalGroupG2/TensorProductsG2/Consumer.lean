module

public import Formalism.PeriodIntegrals.ZuckTensor
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ConsumerB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ConsumerD

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

open MeasureTheory

def ZuckG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    PI.UpqRep.IsHCParam μ → PI.UpqRep.IsDS ε μ σ → ∀ h : ℝ, PI.ZuckTensor.GapAtLeast ε μ h → thrS ε + 1 < h →
      ∃ X : PI.ZuckTensor.TensorDS n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ + Pi.single s 1)

def ZuckDualG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    PI.UpqRep.IsHCParam μ → PI.UpqRep.IsDS ε μ σ → ∀ h : ℝ, PI.ZuckTensor.GapAtLeast ε μ h → thrS ε + 1 < h →
      ∃ X : PI.ZuckTensor.TensorDSd n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ - Pi.single s 1)

theorem zuckG : ZuckG := by
  intro n ε μ H _ _ _ σ hμ hd h hG hth
  by_cases hq : 1 ≤ S7.q0 ε
  · exact cns_zuck_nc hq hμ hd hG hth
  · have h0 : S7.q0 ε = 0 := by omega
    have hpq : pOf ε = 0 ∨ qOf ε = 0 := by
      simp only [S7.q0] at h0
      omega
    exact cns_zuck_cpt hpq hμ hd

theorem zuckDualG : ZuckDualG := by
  intro n ε μ H _ _ _ σ hμ hd h hG hth
  by_cases hq : 1 ≤ S7.q0 ε
  · exact cns_zuckd_nc hq hμ hd hG hth
  · have h0 : S7.q0 ε = 0 := by omega
    have hpq : pOf ε = 0 ∨ qOf ε = 0 := by
      simp only [S7.q0] at h0
      omega
    exact cns_zuckd_cpt hpq hμ hd

end ReciprocityTheory.ChartRestriction.DS.G2
