module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationSpanEqIdOnIrreducible
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

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_augmentationSpan_eq_id_on_irreducible : ∀ {K : Type} [Field K] [IsAlgClosed K] {Γ : Type} [Group Γ] {m : ℕ} (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)), (∀ g, ∀ v ∈ P, S g *ᵥ v ∈ P) → (∀ Q : Submodule K (Fin m → K), Q ≤ P → (∀ g, ∀ v ∈ Q, S g *ᵥ v ∈ Q) → Q = ⊥ ∨ Q = P) → (∃ g, ∃ v ∈ P, S g *ᵥ v ≠ v) → ∃ T ∈ Submodule.span K (Set.range fun g => S g - 1), ∀ v ∈ P, T *ᵥ v = v := by
  first | exact @GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on | exact GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on | (intros; apply GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on <;> assumption)
