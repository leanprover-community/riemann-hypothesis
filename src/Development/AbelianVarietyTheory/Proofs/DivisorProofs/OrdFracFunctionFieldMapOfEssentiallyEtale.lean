module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open IsLocalRing

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EtaleKlt

theorem ord_functionFieldMap_of_formallyEtale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (E : DivOver p) (E' : DivOver (f ≫ p)) (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring), (∀ x, functionFieldMap f x ∈ E'.ring → x ∈ E.ring) → ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale → ((functionFieldMap f).restrict E.ring E'.ring h).EssFiniteType → ∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := by
  intro M W _ _ p f _ E E' h htr het hft g
  set φ := functionFieldMap f
  set ρ := φ.restrict E.ring E'.ring h
  letI := ρ.toAlgebra
  haveI : Algebra.FormallyEtale E.ring E'.ring := het
  haveI : Algebra.EssFiniteType E.ring E'.ring := hft
  haveI : IsLocalHom (algebraMap E.ring E'.ring) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    have e : φ (x : W.functionField) * (y : M.functionField) = 1 := congrArg Subtype.val hy
    have hx0 : (x : W.functionField) ≠ 0 := by
      rintro h0
      rw [h0, map_zero, zero_mul] at e
      exact zero_ne_one e
    have hinv : φ ((x : W.functionField)⁻¹) = y := by
      rw [map_inv₀]
      exact inv_eq_of_mul_eq_one_right e
    have hmem : (x : W.functionField)⁻¹ ∈ E.ring := htr _ (hinv ▸ y.2)
    exact IsUnit.of_mul_eq_one (b := (⟨_, hmem⟩ : E.ring)) (Subtype.ext (mul_inv_cancel₀ hx0))
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := E.ring) (S := E'.ring)
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  have ht' : Irreducible (ρ t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht, Ideal.map_span,
      Set.image_singleton]
    rfl
  obtain ⟨m, u, e⟩ := exists_eq_unit_mul_zpow (F := W.functionField) ht g.ne_zero
  have h1 := ordTop_vw_unit_mul_zpow (F := W.functionField) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := M.functionField) ht' (Units.map ρ.toMonoidHom u) m
  rw [← e, ordTop_vw_of_ne_zero _ g.ne_zero, WithTop.coe_inj] at h1
  have e2 : ((Units.map φ.toMonoidHom g : M.functionFieldˣ) : M.functionField) =
      algebraMap E'.ring M.functionField (Units.map ρ.toMonoidHom u) *
        algebraMap E'.ring M.functionField (ρ t) ^ m := by
    rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, e, map_mul, map_zpow₀]
    rfl
  rw [← e2, ordTop_vw_of_ne_zero _ (Units.ne_zero _), WithTop.coe_inj] at h2
  exact h2.trans h1.symm

end GlobalTheory.EtaleKlt
