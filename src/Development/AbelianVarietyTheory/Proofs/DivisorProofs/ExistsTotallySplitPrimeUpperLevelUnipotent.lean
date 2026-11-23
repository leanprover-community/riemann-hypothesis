module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfA

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.LevelSplit

theorem primesOver_eq (E : Type) [Field E] [NumberField E] {g : ℕ} (hg : g.Prime) :
    (Ideal.span {(g : ℤ)}).primesOver (𝓞 E) = {P : Ideal (𝓞 E) | P.IsPrime ∧ (g : 𝓞 E) ∈ P} := by
  ext P
  simp only [Ideal.primesOver, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP, hL⟩
    refine ⟨hP, ?_⟩
    have h1 : (g : ℤ) ∈ Ideal.span {(g : ℤ)} := Ideal.mem_span_singleton_self _
    rw [hL.over] at h1
    simpa using (Ideal.mem_comap.mp h1)
  · rintro ⟨hP, hgP⟩
    refine ⟨hP, ⟨?_⟩⟩
    have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hg).irreducible
    refine hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simpa using hgP

end GlobalTheory.LevelSplit

theorem GlobalTheory.levelHyp_totallySplit_unipotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C), LevelHyp M → ∃ g : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g ∧ 3 * r < g ∧ ∀ c, ∀ β ∈ M.upper c, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver (M.comp c).L' g β := by
  intro E _ _ _ r U C _ _ M hM
  obtain ⟨g, ⟨hg, hcard⟩, hgr, hU⟩ := hM
  have hset := GlobalTheory.LevelSplit.primesOver_eq E hg
  refine ⟨g, ⟨hg, ?_⟩, hgr, ?_⟩
  · rw [hset]; exact hcard
  · intro c β hβ P hP
    rw [hset] at hP
    exact ⟨r, fun v hv => hU c β hβ P hP.1 hP.2 v hv⟩
