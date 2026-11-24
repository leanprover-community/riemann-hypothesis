module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
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

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem permCoef_shortExact : ∀ (k G : Type) [CommRing k] [Group G] (X : Type) [MulAction G X] (S : ShortComplex (Rep k G)), S.ShortExact → ∃ h : permCoef X S.f ≫ permCoef X S.g = 0, (ShortComplex.mk (permCoef X S.f) (permCoef X S.g) h).ShortExact := by
  intro k G _ _ X _ S hS
  have hf : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have hex : LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap :=
    (hS.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  have hfg : ∀ a, S.g.hom (S.f.hom a) = 0 := fun a => by
    have := congrArg (fun φ => Rep.Hom.hom φ a) S.zero
    exact this
  have hz : permCoef X S.f ≫ permCoef X S.g = 0 := by
    ext x a y
    change S.g.hom (S.f.hom (Finsupp.single x a y)) = 0
    exact hfg _
  refine ⟨hz, ?_⟩
  have hm : Mono (permCoef X S.f) := by
    rw [Rep.mono_iff_injective]
    exact Finsupp.mapRange_injective _ (map_zero _) hf
  have he : Epi (permCoef X S.g) := by
    rw [Rep.epi_iff_surjective]
    exact Finsupp.mapRange_surjective _ (map_zero _) hg
  refine { exact := ?_ }
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change (Finsupp.mapRange.linearMap S.f.hom.toLinearMap : (X →₀ S.X₁) →ₗ[k] (X →₀ S.X₂)).range =
    (Finsupp.mapRange.linearMap S.g.hom.toLinearMap : (X →₀ S.X₂) →ₗ[k] (X →₀ S.X₃)).ker
  rw [Finsupp.ker_mapRange, Finsupp.range_mapRange_linearMap _ (LinearMap.ker_eq_bot.2 hf), hex]

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.permCoef_preserves_shortExact : ∀ (k G : Type) [CommRing k] [Group G] (X : Type) [MulAction G X] (S : ShortComplex (Rep k G)), S.ShortExact → ∃ h : permCoef X S.f ≫ permCoef X S.g = 0, (ShortComplex.mk (permCoef X S.f) (permCoef X S.g) h).ShortExact := by
  first
  | exact @GlobalTheory.HomStab.permCoef_shortExact
end
