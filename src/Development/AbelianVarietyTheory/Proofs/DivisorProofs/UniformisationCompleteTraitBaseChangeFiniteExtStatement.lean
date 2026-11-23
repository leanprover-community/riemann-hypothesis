module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationCompleteTraitBaseChangeFiniteExt
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

theorem _root_.GlobalTheory.T.uniformisation_completeTrait_baseChange_finite_ext : ∀ (R R₂ W W₂ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] (ρ : R →+* R₂) (φ : R →+* W) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂), Base R → GlobalTheory.LN.CDvr W → GlobalTheory.LN.CDvr W₂ → FinExt σ → IsLocalHom σ → φ₂.comp ρ = σ.comp φ → Function.Injective φ₂ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left), IsGrpPullback G₂ G (spMap ρ) β → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left), IsGrpPullback GW G (spMap φ) βW → ∀ (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), ∃ (GW' : Over (Sp W₂)) (_ : GrpObj GW') (_ : IsCommMonObj GW') (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' ∧ IsGrpPullback GW' GW (spMap σ) τ ∧ βW' ≫ β = τ ≫ βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' ∧ LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) := by
  first | exact @GlobalTheory.Mum.unif_trait_baseChange | exact GlobalTheory.Mum.unif_trait_baseChange | (intros; apply GlobalTheory.Mum.unif_trait_baseChange <;> assumption)
