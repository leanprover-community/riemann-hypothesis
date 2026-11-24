module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransferOfRelationGenericFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecKRatioTraitDescendsToFractionFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionsSameFamilyProportionalStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_ratio_of_exp_one_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ (G : IntFam (maximalIdeal R) D.toPre k) (S Ψ : SecK C.P.L.L C.α k), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u Ψ G) → ∀ (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsLocalRing W₀] (T₀ : Trait C W₀) (a₀ b₀ : W₀), a₀ ≠ 0 → b₀ ≠ 0 → T₀.Exp a₀ b₀ S G → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp (T.φ t) (T.φ r * u) S G := by
  intro R _ _ _ hB D C k hk G S Ψ hΨ W₀ _ _ _ T₀ a₀ b₀ ha hb hS
  obtain ⟨u₀, hu₀⟩ := hΨ W₀ T₀
  have hp := GlobalTheory.T.traitExpansions_same_family_proportional R hB D C W₀ T₀ k hk G S Ψ a₀ b₀ 1 (u₀ : W₀) hS hu₀
  obtain ⟨r, t, hr, ht, hrt⟩ := GlobalTheory.T.secK_ratio_trait_descends_to_fractionField R hB D C W₀ T₀ k S Ψ ((u₀ : W₀) * a₀) (b₀ * 1)
    (mul_ne_zero u₀.ne_zero ha) (by rw [_root_.mul_one]; exact hb) hp
  refine ⟨r, t, hr, ht, fun W _ _ _ T => ?_⟩
  obtain ⟨u, hu⟩ := hΨ W T
  exact ⟨u, GlobalTheory.T.expansion_transfer_of_relation_genericFibre R D C W T k G S Ψ r t (u : W) hrt hu⟩

end GlobalTheory.Mum
