module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Data.Matrix.Mul
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar

@[expose] public section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.WittOrbit

section

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {A : Subring E}

theorem int_mul {l m n : Type} [Fintype m] {X : Matrix l m E} {Y : Matrix m n E} (hX : ∀ i j, X i j ∈ A)
    (hY : ∀ i j, Y i j ∈ A) : ∀ i j, (X * Y) i j ∈ A := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)

theorem int_map {m n : Type} {X : Matrix m n E} (hs : ∀ z ∈ A, c z ∈ A) (hX : ∀ i j, X i j ∈ A) :
    ∀ i j, (X.map c) i j ∈ A := by
  intro i j
  rw [Matrix.map_apply]
  exact hs _ (hX i j)

theorem map_map_eq {m n : Type} (hc : ∀ z, c (c z) = z) (X : Matrix m n E) : (X.map c).map c = X := by
  ext i j; simp [hc]

theorem map_mul' {l m n : Type} [Fintype m] (X : Matrix l m E) (Y : Matrix m n E) :
    (X * Y).map c = X.map c * Y.map c :=
  Matrix.map_mul

end

end GlobalTheory.CompanionTheory.WittOrbit
