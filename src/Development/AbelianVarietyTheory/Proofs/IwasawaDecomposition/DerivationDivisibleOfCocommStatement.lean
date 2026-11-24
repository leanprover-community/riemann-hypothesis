module

public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivationDivisibleOfCocomm
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
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

open Formalism.MainNotions.DIV.Cons (intO)

theorem _root_.GlobalTheory.T.derivation_divisible_of_cocomm : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (A : Type) [CommRing A] [Bialgebra ↥(intO C) A] [Coalgebra.IsCocomm ↥(intO C) A] [Module.Finite ↥(intO C) A] [Module.Free ↥(intO C) A] (q : ↥(intO C)), q ≠ 0 → ∀ D : A →ₗ[↥(intO C)] ↥(intO C), (∀ a b : A, q ∣ D (a * b) - Coalgebra.counit (R := ↥(intO C)) a * D b - Coalgebra.counit (R := ↥(intO C)) b * D a) → (∀ u : A, IsGroupLikeElem ↥(intO C) u → q ∣ D u) → ∀ c : ↥(intO C), ‖(c : C)‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → ∀ a : A, q ∣ c * D a := by
  first | exact @GlobalTheory.GroupLikeDerivation.dvd_mul_of_groupLike | exact GlobalTheory.GroupLikeDerivation.dvd_mul_of_groupLike | (intros; apply GlobalTheory.GroupLikeDerivation.dvd_mul_of_groupLike <;> assumption)
