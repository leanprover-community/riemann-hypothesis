module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoSignedLatticeSumProductSubFactors
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

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.tendsto_signedLatticeSum_product_sub_factors : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O), B₁.LieReg → B₂.LieReg → (B₁.P * B₂.P).Separable → K.Small a → IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → Tendsto (fun k : ℕ => (((HH (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 - (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (HH B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 * HH B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1) : ℚ) : ℝ) / ((B₁.rho (algebraMap K.O B₁.A a ^ k) : ℝ) * (B₂.rho (algebraMap K.O B₂.A a ^ k) : ℝ)))) atTop (𝓝 0) := by
  first | exact @GlobalTheory.UnitLemma.Desc.hh_prod_tendsto | exact GlobalTheory.UnitLemma.Desc.hh_prod_tendsto | (intros; apply GlobalTheory.UnitLemma.Desc.hh_prod_tendsto <;> assumption)
