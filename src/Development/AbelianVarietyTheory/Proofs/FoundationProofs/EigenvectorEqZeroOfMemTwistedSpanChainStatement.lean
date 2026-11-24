module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigenvectorEqZeroOfMemTwistedSpanChain
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.eigenvector_eq_zero_of_mem_twistedSpan_chain : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J : Set G) (N : ℕ → Set G) (θ : G → ℂ) (z : G), Datum J θ → (∀ m, Datum (N m) (fun _ => 1)) → Monotone N → (∀ y ∈ N 0, y ∈ J ∧ θ y = 1) → (∀ m y, y ∈ N (m + 1) ↔ z * y * z⁻¹ ∈ N m) → (∀ y ∈ N 1, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) → (∀ j ∈ J, ∃ y ∈ N 0, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ (m : ℕ) (u : V), u ∈ aug π (N m) (fun _ => 1) → IsEig π J θ u → u = 0 := by
  first | exact @GlobalTheory.PsType.eig_eq_zero_of_mem_aug_chain | exact GlobalTheory.PsType.eig_eq_zero_of_mem_aug_chain | (intros; apply GlobalTheory.PsType.eig_eq_zero_of_mem_aug_chain <;> assumption)
