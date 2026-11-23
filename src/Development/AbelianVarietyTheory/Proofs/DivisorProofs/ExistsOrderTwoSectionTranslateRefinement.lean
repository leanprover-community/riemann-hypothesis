module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointRefinementsCompareUnifStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionSectionLiftTorusExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegId
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TwistSec

theorem exists_sec_compare : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 ∧ ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ ∀ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D₂.toPre D'.toPre) → Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D'.toPre) := by
  intro R _ _ _ hR D₀ D A G _ _ hG U hS
  obtain ⟨g, h2, hc⟩ := GlobalTheory.T.exists_orderTwo_point_refinements_compare_unif R hR D₀ D A G hG U hS
  obtain ⟨a, ha, hl⟩ := GlobalTheory.T.exists_twoTorsion_section_lift_torusExtension R hR D A G hG U g h2
  refine ⟨a, ha, fun A₂ D₂ U₂ hL => ?_⟩
  obtain ⟨R', i1, i2, i3, ρ, D₁, D₂', hf, hloc, h0, h2', hid⟩ := hc a ha hl A₂ D₂ U₂ hL
  refine ⟨R', i1, i2, i3, ρ, D₁, hf, hloc, h0, fun D' hD' => ?_⟩
  have h3 := isPullDeg_unique_any R R' ρ D₂.toPre D₂'.toPre D'.toPre h2' hD'
  have h4 := nonempty_isPullDeg_comp_of_injective R' R' R' (RingHom.id R') (RingHom.id R') D₁.toPre D₂'.toPre
    D'.toPre Function.injective_id hid h3
  simpa using h4

end GlobalTheory.TwistSec
