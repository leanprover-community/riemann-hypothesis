module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SplittingIntegralFormsBound
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
theorem _root_.GlobalTheory.T.splitting_integral_forms_bound : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (A : Subring K) (B : Set K) (L : Set V) (s : Finset ι), IsPhi p f h Φ → (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) → (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) → ∀ (a q : ℕ) (t : Finset ι), t ⊆ s → q + t.card = a + 1 → ∀ x ∈ forms B L a, Φ x t ∈ forms {z | ∃ c ∈ B, ∃ b ∈ A, z = c ^ p * b} L q := by
  first | exact @_root_.GlobalTheory.DI.phi_mem_forms | exact _root_.GlobalTheory.DI.phi_mem_forms | (intros; apply _root_.GlobalTheory.DI.phi_mem_forms <;> assumption)
