module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Order.Filter.Cofinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetEqFinprodLocalSums
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

open Filter
open scoped Classical

theorem _root_.GlobalTheory.T.finsum_doubleCoset_eq_finprod_local_sums : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (T K : Subgroup G) (TH KH : ∀ i, Subgroup (H i)) (s : G → ℂ) (s' : ∀ i, H i → ℂ), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ i, ∀ t ∈ TH i, ∀ k ∈ KH i, ∀ x, s' i (t * x * k) = s' i x) → (∀ i, {q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)) | s' i (Quotient.out q) ≠ 0}.Finite) → (∀ᶠ i in cofinite, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0) → (∀ g, s g = ∏ᶠ i, s' i (p i g)) → ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K : Set G), s (Quotient.out q) = ∏ᶠ i, ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q) := by
  first | exact @GlobalTheory.DoubleCosetEuler.finsum_doubleCoset_eq_finprod_local | exact GlobalTheory.DoubleCosetEuler.finsum_doubleCoset_eq_finprod_local | (intros; apply GlobalTheory.DoubleCosetEuler.finsum_doubleCoset_eq_finprod_local <;> assumption)
