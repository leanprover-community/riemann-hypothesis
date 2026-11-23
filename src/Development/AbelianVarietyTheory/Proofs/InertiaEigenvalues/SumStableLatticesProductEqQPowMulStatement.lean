module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumStableLatticesProductEqQPowMul
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.sum_stableLattices_product_eq_q_pow_mul : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → (B₁.P * B₂.P).Separable → ∀ (φ₁ : Submodule K.O B₁.A → ℚ) (φ₂ : Submodule K.O B₂.A → ℚ), {M ∈ B₁.Lin | φ₁ M ≠ 0}.Finite → {M ∈ B₂.Lin | φ₂ M ≠ 0}.Finite → {M ∈ (B₁.prod B₂).Lin | φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) = (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) := by
  first | exact @GlobalTheory.UnitLemma.FibSum.fibsum | exact GlobalTheory.UnitLemma.FibSum.fibsum | (intros; apply GlobalTheory.UnitLemma.FibSum.fibsum <;> assumption)
