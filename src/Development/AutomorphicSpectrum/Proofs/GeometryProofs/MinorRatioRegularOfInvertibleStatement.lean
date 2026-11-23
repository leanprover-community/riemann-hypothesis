module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MinorRatioRegularOfInvertible
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.minor_ratio_regular_of_invertible : ∀ (K : Type) [Field K] (R : Subring K) (n r : ℕ) (A : Matrix (Fin n) (Fin r) K) (B : Matrix (Fin r) (Fin n) K) (G : Matrix (Fin r) (Fin r) K) (a : K) (k : Fin r) (J : Fin ((k : ℕ) + 1) → Fin n), (∀ j l, A j l ∈ R) → (∀ l j, B l j ∈ R) → B * A = 1 → a ≠ 0 → ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ≠ 0 → (∀ l j, ((a • (A * G)).submatrix (Function.update J l j) (Fin.castLE k.2)).det / ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ∈ R) → ∃ D Ee : Fin ((k : ℕ) + 1) → Fin r → K, (∀ l i, D l i ∈ R) ∧ (∀ l i, Ee l i ∈ R) ∧ (∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) ∧ ∀ l, D l ∈ flagStep K (fun c i => G i c) ((k : ℕ) + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.split_of_regular_ratios | exact GlobalTheory.CompanionTheory.Ar.FlagBun.split_of_regular_ratios | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.split_of_regular_ratios <;> assumption)
