module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingProductIntegral
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

open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.alternating_product_integral : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (A : Subring K) (L : Set V) (s : Finset ι), (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) → (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) → ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), (∀ k, v k ∈ L) → t ⊆ s → ∀ q, q + t.card = a + 1 → alt f h a v t ∈ forms (A : Set K) L q := by
  first | exact @_root_.GlobalTheory.DI.alt_mem_forms | exact _root_.GlobalTheory.DI.alt_mem_forms | (intros; apply _root_.GlobalTheory.DI.alt_mem_forms <;> assumption)
