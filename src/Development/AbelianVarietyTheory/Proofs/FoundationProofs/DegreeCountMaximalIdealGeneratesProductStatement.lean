module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DegreeCountMaximalIdealGeneratesProduct
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

open Polynomial

theorem _root_.GlobalTheory.T.degree_count_maximalIdeal_generates_product : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (D P₀ P : Ideal A) (Q Q' : I → Ideal A) (f₀ f : A), P₀.IsMaximal → P.IsMaximal → (∀ i, (Q i).IsMaximal) → (∀ i, (Q' i).IsMaximal) → Function.Injective Q' → (∀ i, Q' i ≠ P) → (∀ i, ¬ D ≤ Q' i) → ¬ D ≤ P →
 f₀ ≠ 0 → f ≠ 0 → Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N → f ∈ D → f ∈ P → (∀ i, f ∈ Q' i ^ N) → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀}) →
 Ideal.span {f} = P * D * ∏ i, Q' i ^ N := by
  first | exact @GlobalTheory.degree_count_generates | exact GlobalTheory.degree_count_generates | (intros; apply GlobalTheory.degree_count_generates <;> assumption)
