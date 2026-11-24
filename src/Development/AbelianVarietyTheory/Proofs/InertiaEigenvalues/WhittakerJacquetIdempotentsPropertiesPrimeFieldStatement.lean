module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeField
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField : ∀ (g : ℕ) [Fact g.Prime] (N k s : ℕ) (ψ : AddChar (ZMod g) ℂ), eU g N ψ * eU g N ψ = eU g N ψ ∧ (eU g N ψ).coeff 1 = ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹ ∧ (N = k + 2 * s + 1 → eJ g N k s ψ * eJ g N k s ψ = eJ g N k s ψ ∧ (eJ g N k s ψ).coeff 1 = (g : ℂ) ^ k * ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹) ∧ (k < N → eJ' g N k ψ * eJ' g N k ψ = eJ' g N k ψ ∧ (eJ' g N k ψ).coeff 1 = (g : ℂ) ^ k * ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹) := by
  first | exact @GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField | exact GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField | (intros; apply GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField <;> assumption)
