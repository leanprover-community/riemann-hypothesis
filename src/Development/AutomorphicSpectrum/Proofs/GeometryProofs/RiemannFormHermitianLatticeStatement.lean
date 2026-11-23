module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RiemannFormHermitianLattice
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

open Filter Topology Matrix

theorem _root_.GlobalTheory.T.riemann_form_hermitian_lattice : ∀ (g : ℕ) (Bs : Matrix (Fin g) (Fin g) ℤ) (τ G : Matrix (Fin g) (Fin g) ℂ) (c : ℝ), 0 < c → (Bs.map (fun x : ℤ => (x : ℝ))).PosSemidef → τᵀ = τ → (∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((τ.map Complex.im) *ᵥ v)) → G.IsHermitian → (∀ u u' v v' : Fin g → ℤ, Bs *ᵥ v = 0 → Bs *ᵥ v' = 0 → (((fun k => (u k : ℂ)) + τ *ᵥ (fun k => (v k : ℂ))) ⬝ᵥ G *ᵥ star ((fun k => (u' k : ℂ)) + τ *ᵥ (fun k => (v' k : ℂ)))).im = ((v ⬝ᵥ u' - u ⬝ᵥ v' : ℤ) : ℝ)) → (∀ u : Fin g → ℤ, (∀ v : Fin g → ℤ, Bs *ᵥ v = 0 → u ⬝ᵥ v = 0) → G *ᵥ (fun k => (u k : ℂ)) = 0) → ∀ y : Fin g → ℂ, 0 ≤ (y ⬝ᵥ G *ᵥ star y).re ∧ (y ⬝ᵥ G *ᵥ star y).re ≤ c⁻¹ * ∑ i, ‖y i‖ ^ 2 ∧ ((y ⬝ᵥ G *ᵥ star y).re = 0 → y ∈ Submodule.span ℂ {p : Fin g → ℂ | ∃ u : Fin g → ℤ, (∀ v : Fin g → ℤ, Bs *ᵥ v = 0 → u ⬝ᵥ v = 0) ∧ p = fun k => (u k : ℂ)}) := by
  first | exact @GlobalTheory.CompanionTheory.RiemannForm.form_bounds | exact GlobalTheory.CompanionTheory.RiemannForm.form_bounds | (intros; apply GlobalTheory.CompanionTheory.RiemannForm.form_bounds <;> assumption)
