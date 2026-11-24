module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternal
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.eigenspace_decomposition_internal : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (E : Type) [AddCommGroup E] [Module Ω E] (F : Type) [Field F] [NumberField F] (ρ : NumberField.RingOfIntegers F →+* Module.End Ω E) (I : Type) [Fintype I] [DecidableEq I] (σ : I → (NumberField.RingOfIntegers F →+* Ω)), Function.Injective σ → Fintype.card I = Module.finrank ℚ F → DirectSum.IsInternal fun s => eigSp ρ (σ s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isInternal_eigSp | exact GlobalTheory.CompanionTheory.Ar.isInternal_eigSp | (intros; apply GlobalTheory.CompanionTheory.Ar.isInternal_eigSp <;> assumption)
