module

public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ReciprocityTheory.Gal
open Formalism.NG
namespace GlobalTheory

theorem hcLC_exists_pow_smul_eq_zero : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O),
    (∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0) → ∀ x ∈ ReciprocityTheory.ChartRestriction.T2.HcLC ρ, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  intro O _ G _ _ _ M _ _ ρ ϖ hM x hx
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hx
  have hlc : IsLocallyConstant (c : G → M) := hc
  classical
  let f : M → ℕ := fun m => Classical.choose (hM m)
  have hf : ∀ m, ϖ ^ f m • m = 0 := fun m => Classical.choose_spec (hM m)
  have hfin : (Set.range (c : G → M)).Finite := hlc.range_finite
  obtain ⟨N, hN⟩ := (hfin.image f).bddAbove
  refine ⟨N, ?_⟩
  have hc0 : ϖ ^ N • c = 0 := by
    apply Subtype.ext
    funext g
    have hk : f ((c : G → M) g) ≤ N := hN ⟨_, ⟨g, rfl⟩, rfl⟩
    show ϖ ^ N • (c : G → M) g = 0
    rw [← Nat.sub_add_cancel hk, pow_add, mul_smul, hf, smul_zero]
  rw [← LinearMap.map_smul, hc0, map_zero]

end GlobalTheory
