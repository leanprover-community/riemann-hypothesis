module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedSiegelBasisBalancedForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_adapted_siegel_basis_balanced_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B₀ ∈ realForms H.bar X → IsPosDef B₀ → ∀ n : ℕ, Module.finrank ℤ X = n → ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (b : Module.Basis (Fin n) ℤ X) (d d' : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ B' ∈ realForms H.bar X ∧ (∀ i j, B (b i) (b j) = gram d u i j) ∧ ∀ i j, B' (b i) (b j) = gram d' u i j := by
  first | exact @GlobalTheory.RedTh.exists_adapted_siegel_basis | exact GlobalTheory.RedTh.exists_adapted_siegel_basis | (intros; apply GlobalTheory.RedTh.exists_adapted_siegel_basis <;> assumption)
