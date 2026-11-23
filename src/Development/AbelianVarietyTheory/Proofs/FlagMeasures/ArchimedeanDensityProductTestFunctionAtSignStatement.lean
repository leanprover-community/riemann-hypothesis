module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ArchimedeanDensityProductTestFunctionAtSign
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.archimedean_density_product_testFunction_at_sign : ∀ (I : AutInst) (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)), (∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) → ∀ (lamv : InfinitePlace I.F → ℝ) (χ : Ainf I.F → ℂ), (∀ v, lamv v ≠ 0) → (∀ x, χ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ v, lamv v * (θ v (x ⊗ₜ[I.F] (1 : I.E))).re : ℝ) : ℂ))) → ∀ (μi : Measure (Fin 1 → Fin I.n → Ainf I.F ⊗[I.F] I.E)) (νi : Measure (Ainf I.F)), SelfDual μi (fun X Y => χ (BR (Ainf I.F) I.cm.sig I.J X Y)) → SelfDual νi (fun s t => χ (s * t)) → ∀ (φ : InfinitePlace I.F → (Fin I.n → ℂ) → ℝ) (D : InfinitePlace I.F → ℝ → ℝ), (∀ v, Continuous (φ v) ∧ HasCompactSupport (φ v) ∧ IsDens (I.ε v) (φ v) (D v)) → ∀ Fi : Ainf I.F → ℂ, IsContDensityOn μi (fun X => qR (Ainf I.F) I.cm.sig I.J (X 0)) id νi {c | IsUnit c} (fun X => ((∏ v, φ v ((I.P v)⁻¹ *ᵥ fun i => θ v (X 0 i)) : ℝ) : ℂ)) Fi → ∀ s : Bool, Fi (sgn (Ainf I.F) s) = ((∏ v, 2 ^ I.n * |lamv v| ^ ((I.n : ℝ) - 1 / 2) * D v (sgn ℝ s) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.GaussMean.RealDensityCc.density_at_sign | exact GlobalTheory.GaussMean.RealDensityCc.density_at_sign | (intros; apply GlobalTheory.GaussMean.RealDensityCc.density_at_sign <;> assumption)
