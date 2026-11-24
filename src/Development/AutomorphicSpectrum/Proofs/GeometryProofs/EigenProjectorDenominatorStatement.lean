module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenProjectorDenominator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

open NumberField GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.eigen_projector_denominator : ∀ (E : Type) [Field E] [NumberField E], ∃ D : ℕ, 0 < D ∧ ∀ (Ω : Type) [Field Ω] [CharZero Ω] (V : Type) [AddCommGroup V] [Module Ω V] (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω), ∃ T ∈ Sandwich.opRing ρ σ, (∀ v, T v ∈ eigSp ρ σ) ∧ ∀ v ∈ eigSp ρ σ, T v = (D : Ω) • v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sandwich.exists_eigen_op_uniform | exact GlobalTheory.CompanionTheory.Ar.Sandwich.exists_eigen_op_uniform | (intros; apply GlobalTheory.CompanionTheory.Ar.Sandwich.exists_eigen_op_uniform <;> assumption)
