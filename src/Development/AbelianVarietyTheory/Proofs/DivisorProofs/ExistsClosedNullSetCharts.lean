module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeImageComplPtsIn
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue GlobalTheory.Mean4O.CoverInt
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Points (PtsOver)

namespace GlobalTheory.Mean4O.CoverExc

section Model

variable {F : Type} [Field F] [NumberField F] {X G : Scheme.{0}} {p : X ⟶ Sp (𝓞 F)} {q : G ⟶ Sp F} {j : G ⟶ X}


end Model

section Fibre

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q)


include hπ in
theorem app_algX (U : X.Opens) (a : k) : algX q (π ⁻¹ᵁ U) a = (π.app U).hom (algX p U a) := by
  have hw : π ≫ p = q ≫ spMap (RingHom.id k) := by
    rw [hπ, show spMap (RingHom.id k) = 𝟙 _ from Spec.map_id _, Category.comp_id]
  have := RingHom.congr_fun (TopForm.appLE_comp_algX (p := p) (p' := q) (φ := π)
    (σ := RingHom.id k) hw (V := U) (W := π ⁻¹ᵁ U) le_rfl) a
  simpa [Scheme.Hom.app_eq_appLE] using this.symm


include hπ in
theorem etale_app {U : X.Opens} {e : ℕ} {x : Fin e → Γ(X, U)} (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale)
    (het : (π.app U).hom.Etale) :
    (MvPolynomial.eval₂Hom (algX q (π ⁻¹ᵁ U)) fun a => (π.app U).hom (x a)).Etale := by
  have hcx : (MvPolynomial.eval₂Hom (algX q (π ⁻¹ᵁ U)) fun a => (π.app U).hom (x a)) =
      (π.app U).hom.comp (MvPolynomial.eval₂Hom (algX p U) x) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_
    · simp [app_algX π hπ]
    · simp
  rw [hcx]
  exact RingHom.Etale.stableUnderComposition _ _ hx het

end Fibre

end GlobalTheory.Mean4O.CoverExc
