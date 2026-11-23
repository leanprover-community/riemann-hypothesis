module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LinearIndependentCoordinatesDenominator
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
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice

@[expose] public section

open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors

theorem _root_.GlobalTheory.T.linear_independent_coordinates_denominator : ∀ (L : Type) [Field L] [NumberField L] (M : Type) [AddCommGroup M] [Module (𝓞 L) M] [Module.Finite (𝓞 L) M] [Module.IsTorsionFree (𝓞 L) M] (i : ℕ) (f : Fin i → M), LinearIndependent (𝓞 L) f → i = Module.finrank (𝓞 L) M → ∃ c : M →ₗ[𝓞 L] (Fin i → L), Function.Injective c ∧ (∀ j, c (f j) = Pi.single j 1) ∧ ∀ x, ∃ (D : 𝓞 L) (a : Fin i → 𝓞 L), D ≠ 0 ∧ D • x = ∑ j, a j • f j ∧ ∀ j, (D : L) * c x j = a j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.Coords.coordinates_of_maximal_independent | exact GlobalTheory.CompanionTheory.Ar.Lines.Coords.coordinates_of_maximal_independent | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.Coords.coordinates_of_maximal_independent <;> assumption)
