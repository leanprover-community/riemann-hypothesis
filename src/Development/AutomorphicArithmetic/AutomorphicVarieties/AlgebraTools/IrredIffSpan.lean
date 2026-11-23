module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleOfSpanningMatrices
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanMapRingHomEqTop
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

@[expose] public section

open Polynomial Matrix IsLocalRing TensorProduct

private theorem irreducible_of_span_eq_top {K G ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    (f : G → Matrix ι ι K) (h : Submodule.span K (Set.range f) = ⊤) (N : Submodule K (ι → K))
    (hN : ∀ g, ∀ v ∈ N, (f g).mulVec v ∈ N) : N = ⊥ ∨ N = ⊤ :=
  _root_.UpperTheory.Reformulated.B.IrreducibleOfSpanningMatrices.irreducible_of_span_eq_top f h N hN

private theorem span_map_ringHom_eq_top {k K G ι : Type} [Field k] [Field K] [Fintype ι] [DecidableEq ι]
    (φ : k →+* K) (f : G → Matrix ι ι k) (h : Submodule.span k (Set.range f) = ⊤) :
    Submodule.span K (Set.range fun g => (f g).map φ) = ⊤ :=
  _root_.UpperTheory.Reformulated.B.Qe1.span_map_ringHom_eq_top φ f h

theorem UpperTheory.V.AlgebraTools.irred_iff_span :
    ∀ {k K G : Type} [Field k] [IsAlgClosed k] [Field K] [Group G] {ι : Type} [Fintype ι] [DecidableEq ι] (φ : k →+* K) (ρ : G →* Matrix ι ι k), ((∀ N : Submodule k (ι → k), (∀ g, ∀ v ∈ N, (ρ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) ↔ Submodule.span k (Set.range ρ) = ⊤) ∧ (Submodule.span k (Set.range ρ) = ⊤ ↔ Submodule.span K (Set.range fun g => (ρ g).map φ) = ⊤) ∧ (Submodule.span K (Set.range fun g => (ρ g).map φ) = ⊤ → ∀ N : Submodule K (ι → K), (∀ g, ∀ v ∈ N, ((ρ g).map φ).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) := by
  intro k K G _ _ _ _ ι _ _ φ ρ
  refine ⟨⟨KStar.Schema.span_eq_top_of_irreducible ρ, fun h N hN => irreducible_of_span_eq_top ρ h N hN⟩,
    ⟨span_map_ringHom_eq_top φ ρ, fun h => ?_⟩, fun h N hN => irreducible_of_span_eq_top _ h N hN⟩
  refine KStar.Schema.span_eq_top_of_residue φ ?_ _ ?_
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ).mp φ.injective
  · rw [← Set.range_comp]
    exact h
