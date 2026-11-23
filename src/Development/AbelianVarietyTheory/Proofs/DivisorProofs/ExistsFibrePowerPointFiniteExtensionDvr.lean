module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFamilyPointOfPrincipalObjectStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelLevelAfterFiniteExtensionDVRStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectFibrePowerAtSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackDivisionPointsPushEqStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LowChart

theorem exists_fibrePow_point_of_polAV : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (F : SFam PB.g n (zetaAway n)) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f₁ : V →+* V₁) (v : Sp V₁ ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = spMap (f₁.comp b)), IsCN V₁ ∧ IsDiscreteValuationRing V₁ ∧ Function.Injective f₁ ∧ f₁.Finite ∧ IsLocalHom f₁ ∧ ∃ (β₁ : (GlobalTheory.LowChart.siegAt F v _ hs).A.left ⟶ PB.A.left) (β₁₂ : (G2 (GlobalTheory.LowChart.siegAt F v _ hs).A).left ⟶ (G2 PB.A).left), IsGrpPullback (GlobalTheory.LowChart.siegAt F v _ hs).A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso (GlobalTheory.LowChart.siegAt F v _ hs).P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ a, (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ≫ β₁ = spMap f₁ ≫ (c a).left := by
  intro n hn hodd V _ _ _ hV hD b PB r c hc
  obtain ⟨V₁, _, _, _, f₁, s, β, β₂, d, h1, h2, h3, h4, h5, hP, hpb, hsq, hlb, hd⟩ :=
    GlobalTheory.T.exists_siegelLevel_after_finiteExtension_DVR n hn hodd V hV hD b PB r c
  have : CharZero V₁ := h1.2.2.2
  obtain ⟨F, x, hx, hpbF⟩ := GlobalTheory.T.exists_siegel_family_point_of_principal_object n hn hodd PB.g V₁ (f₁.comp b) s hP
  obtain ⟨v, hs, β₁, β₁₂, p1, p2, p3, p4⟩ :=
    GlobalTheory.T.exists_siegelObject_fibrePower_at_sections F (spMap f₁) (spMap (f₁.comp b)) x hx s hpbF PB.A (abelian₂ PB.A PB.L) β β₂ hpb hsq hlb r d
  refine ⟨F, V₁, inferInstance, inferInstance, inferInstance, f₁, v, hs, h1, h2, h3, h4, h5, β₁, β₁₂, p1, p2, p3,
    fun a => ?_⟩
  rw [p4]
  exact GlobalTheory.T.grpPullback_divisionPoints_push_eq (spMap f₁) s.A PB.A β hpb n r d c hc hd a

end GlobalTheory.LowChart
