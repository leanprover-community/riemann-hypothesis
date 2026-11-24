module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.adelic_character_frequencies_and_conductor_product : ∀ (I : AutInst) (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)), (∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) → ∀ ψ : AddChar (AF I.F) ℂ, IsCharAF I.F ψ → ∃ (lamv : InfinitePlace I.F → ℝ) (m : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F) → ℤ), (∀ v, lamv v ≠ 0) ∧ (∀ x, psiInf I.F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ v, lamv v * (θ v (x ⊗ₜ[I.F] (1 : I.E))).re : ℝ) : ℂ))) ∧ (Function.support m).Finite ∧ (∀ u (t : Fv I.F u), (∀ s ∈ u.adicCompletionIntegers I.F, psiV I.F ψ u (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp (m u)) ∧ ∏ᶠ u, (Ideal.absNorm u.asIdeal : ℝ) ^ m u = |(discr I.F : ℝ)| * ∏ v, |lamv v| := by
  first | exact @GlobalTheory.AdeleCharConductor.real_part_and_conductors | exact GlobalTheory.AdeleCharConductor.real_part_and_conductors | (intros; apply GlobalTheory.AdeleCharConductor.real_part_and_conductors <;> assumption)
