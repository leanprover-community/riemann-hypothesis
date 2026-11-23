module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantBoxApproximation
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

theorem _root_.GlobalTheory.T.locally_constant_box_approximation : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (ι : Type) [Fintype ι] (ψ : (ι → Fv F v) → ℝ), Continuous ψ → HasCompactSupport ψ → ∃ B : ℝ, 0 ≤ B ∧ ∀ δ : ℝ, 0 < δ → ∃ (k : ℕ) (C : Finset (ι → Fv F v)), (∀ y, |ψ y - ∑ c ∈ C, ψ c * boxInd v k c y| ≤ δ * ∑ c ∈ C, boxInd v k c y) ∧ (C.card : ℝ) * (((Ideal.absNorm v.asIdeal : ℝ) ^ k) ^ Fintype.card ι)⁻¹ ≤ B ∧ |(∫ y, ψ y ∂(Measure.pi fun _ => lam)) - ∑ c ∈ C, ψ c * (((Ideal.absNorm v.asIdeal : ℝ) ^ k) ^ Fintype.card ι)⁻¹| ≤ δ * B := by
  first | exact @GlobalTheory.CompanionTheory.Equi.LocApprox.loc_approx | exact GlobalTheory.CompanionTheory.Equi.LocApprox.loc_approx | (intros; apply GlobalTheory.CompanionTheory.Equi.LocApprox.loc_approx <;> assumption)
