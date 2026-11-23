module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportClassMinimisersAlongLinearEquiv
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

open GlobalTheory.PolFan GlobalTheory.LocM

theorem _root_.GlobalTheory.T.transport_classMinimisers_along_linearEquiv : ∀ (O : Type) [CommRing O] (X Y : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (n N : ℕ) [NeZero N] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ)) (ebY : Y ≃ₗ[ℤ] (Fin n → ℤ)) (f : X ≃ₗ[O] Y) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((ebY (μ cl) i : ℤ) : ZMod N) = cl i) → ∃ σ : Equiv.Perm (Fin n → ZMod N), (∀ cl i, ((ebX (f.symm (μ (σ cl))) i : ℤ) : ZMod N) = cl i) ∧ ∀ b : LinearMap.BilinForm ℤ Y, (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → pull f.toLinearMap b (f.symm (μ (σ cl))) (f.symm (μ (σ cl))) ≤ pull f.toLinearMap b α α := by
  first | exact @GlobalTheory.transport_minimisers | exact GlobalTheory.transport_minimisers | (intros; apply GlobalTheory.transport_minimisers <;> assumption)
