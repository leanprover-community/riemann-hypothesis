module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentTerms
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Extension
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem exists_isReps_of_fg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι] (ϖ : 𝒪[k])
    (hϖ : Irreducible ϖ) (M : Submodule 𝒪[k] (ι → k)) (hM : M.FG) :
    ∃ T : Finset (ι → k), IsReps ϖ M T := by
  classical
  have h1 : Finite (𝒪[k] ⧸ Ideal.span {ϖ}) := by
    rw [← hϖ.maximalIdeal_eq]
    exact (inferInstance : Finite 𝓀[k])
  have hfin : Module.Finite 𝒪[k] M := Module.Finite.iff_fg.mpr hM
  set N : Submodule 𝒪[k] M := Ideal.span {ϖ} • ⊤ with hN
  have h2 : Finite (M ⧸ N) := by
    have : Finite (M ⧸ (⊤ : Submodule 𝒪[k] M)) := by
      have : Subsingleton (M ⧸ (⊤ : Submodule 𝒪[k] M)) :=
        Submodule.Quotient.subsingleton_iff.mpr rfl
      infer_instance
    exact Submodule.finite_quotient_smul _ Module.Finite.fg_top
  have hmem : ∀ x : M, x ∈ N ↔ (x : ι → k) ∈ ϖ • M := by
    intro x
    rw [hN, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨b, -, rfl⟩
      exact ⟨b, b.2, rfl⟩
    · rintro ⟨b, hb, h⟩
      exact ⟨⟨b, hb⟩, trivial, Subtype.ext h⟩
  have := Fintype.ofFinite (M ⧸ N)
  choose s hs using Submodule.Quotient.mk_surjective N
  refine ⟨Finset.univ.image fun q => (s q : ι → k), ?_, ?_⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    exact (s q).2
  · intro v hv
    have key : ∀ q, v - (s q : ι → k) ∈ ϖ • M ↔ Submodule.Quotient.mk (⟨v, hv⟩ : M) = q := by
      intro q
      conv_rhs => rw [← hs q, Submodule.Quotient.eq, hmem]
      rfl
    refine ⟨s (Submodule.Quotient.mk ⟨v, hv⟩), ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩,
      (key _).mpr rfl⟩, ?_⟩
    rintro t ⟨ht, h⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    rw [(key q).mp h]

end GlobalTheory.RootEx.UnfoldShape
