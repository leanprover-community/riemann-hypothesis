module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLocalExtResidueFieldSeparableStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionWithRangeInOpenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparablePointSmoothLocalRingOpenStatement
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

theorem exists_finEtale_section_of_smooth : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (U : Over (Sp R)), Smooth U.hom → ∀ O : U.left.Opens, (∃ u ∈ O, U.hom u = closedPoint R) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (a : Sp R' ⟶ U.left), FinExt ρ ∧ ρ.Etale ∧ a ≫ U.hom = spMap ρ ∧ Set.range a ⊆ O := by
  intro R _ _ _ hR U hU O hO
  obtain ⟨k', _, _, _, _, x, hx, hxO⟩ := GlobalTheory.T.exists_separable_point_smooth_localRing_open R U hU O hO
  obtain ⟨R', _, _, _, ρ, σ, hF, hE, hσ⟩ := GlobalTheory.T.exists_finiteEtale_local_ext_residueField_separable R hR k'
  have hN : IsNoetherianRing R' := hF.1.1
  have hc : IsAdicComplete (maximalIdeal R') R' := hF.1.2.2.2
  have hx₀ : (spMap σ ≫ x) ≫ U.hom = spMap ((residue R').comp ρ) := by
    rw [Category.assoc, hx, ← hσ, ← Spec.map_comp]; rfl
  have hr : Set.range (spMap σ ≫ x) ⊆ O := by
    rintro _ ⟨p, rfl⟩; exact hxO ⟨_, rfl⟩
  obtain ⟨a, ha, haO⟩ := GlobalTheory.T.exists_lift_residueFieldPoint_smooth_completeLocal R R' hc ρ U hU (spMap σ ≫ x) hx₀ O hr
  exact ⟨R', _, inferInstance, inferInstance, ρ, a, hF, hE, ha, haO⟩

end GlobalTheory.Mum
