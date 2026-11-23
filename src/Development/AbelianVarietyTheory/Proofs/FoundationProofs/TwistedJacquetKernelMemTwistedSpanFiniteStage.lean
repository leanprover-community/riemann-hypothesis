module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Order.CompletePartialOrder
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

namespace GlobalTheory.PsType

theorem twKer_one_mem_aug_stage : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (U : Subgroup G) (N : ℕ → Set G), Monotone N →
    (∀ y ∈ U, ∃ m, y ∈ N m) → ∀ v ∈ twKer π U 1, ∃ m, v ∈ aug π (N m) (fun _ => 1) := by
  intro G V _ _ _ π U N hN hU v hv
  have mono : ∀ {a b : ℕ}, a ≤ b → aug π (N a) (fun _ => 1) ≤ aug π (N b) (fun _ => 1) := by
    intro a b h
    refine Submodule.span_mono ?_
    rintro x ⟨g, hg, w, rfl⟩
    exact ⟨g, hN h hg, w, rfl⟩
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, w, rfl⟩ := hx
    obtain ⟨m, hm⟩ := hU n n.2
    exact ⟨m, Submodule.subset_span ⟨n, hm, w, by simp⟩⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, add_mem (mono (le_max_left _ _) ha) (mono (le_max_right _ _) hb)⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, Submodule.smul_mem _ c ha⟩

end GlobalTheory.PsType
