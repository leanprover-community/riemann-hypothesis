module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.CosetReps

theorem exists_fin_coset_reps (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (J H A : Subgroup G) (hJ : IsCompact (J : Set G)) (hH : IsOpen (H : Set G))
    (_hHJ : H ≤ J) (_hAJ : A ≤ J) (hcov : ∀ y ∈ J, ∃ a ∈ A, a⁻¹ * y ∈ H) :
    ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G, (∀ i, x i ∈ A) ∧
      ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H := by
  classical
  obtain ⟨t, ht⟩ := hJ.elim_finite_subcover
    (fun a : A => (fun y : G => (a : G)⁻¹ * y) ⁻¹' (H : Set G))
    (fun a => hH.preimage (continuous_const.mul continuous_id))
    (fun y hy => by
      obtain ⟨a, ha, hay⟩ := hcov y hy
      exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, hay⟩)
  let T : Finset (G ⧸ H) := t.image (fun a : A => ((a : G) : G ⧸ H))
  have rep : ∀ q : T, ∃ a : A, ((a : G) : G ⧸ H) = q := by
    rintro ⟨q, hq⟩
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨a, rfl⟩
  choose f hf using rep
  have key : ∀ y ∈ J, ((y : G) : G ⧸ H) ∈ T := by
    intro y hy
    obtain ⟨a, hat, hay⟩ := Set.mem_iUnion₂.1 (ht hy)
    exact Finset.mem_image.2 ⟨a, hat, QuotientGroup.eq.2 hay⟩
  let e : T ≃ Fin T.card := T.equivFin
  have main : ∀ y ∈ J, ∃! i, ((f (e.symm i) : A) : G)⁻¹ * y ∈ H := by
    intro y hy
    refine ⟨e ⟨_, key y hy⟩, ?_, ?_⟩
    · refine QuotientGroup.eq.1 ?_
      rw [Equiv.symm_apply_apply, hf]
    · intro i hi
      have h1 : (((f (e.symm i) : A) : G) : G ⧸ H) = ((y : G) : G ⧸ H) := QuotientGroup.eq.2 hi
      rw [hf] at h1
      rw [← Equiv.symm_apply_eq]
      exact Subtype.ext h1
  obtain ⟨i₀, -⟩ := main 1 J.one_mem
  exact ⟨T.card, i₀.pos, fun i => ((f (e.symm i) : A) : G), fun i => (f (e.symm i)).2, main⟩

end GlobalTheory.CompanionTheory.CosetReps
