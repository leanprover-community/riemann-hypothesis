module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.ChartSmooth

theorem isStandardSmooth_C (k : Type) [CommRing k] (D : ℕ) :
    (algebraMap k (MvPolynomial (Fin D) k)).IsStandardSmoothOfRelativeDimension D := by
  let P₀ : Algebra.Presentation k (MvPolynomial (Fin D) k) (Fin D) Empty :=
    { __ := Algebra.Generators.mvPolynomial k (Fin D)
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation k (MvPolynomial (Fin D) k) (Fin D) Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation k (MvPolynomial (Fin D) k) (Fin D) Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).2
    (P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension]))

theorem isStandardSmooth_algX {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {D : ℕ}
    {U : X.Opens} (x : Fin D → Γ(X, U)) (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) :
    (algX p U).IsStandardSmoothOfRelativeDimension D := by
  have hC : (MvPolynomial.eval₂Hom (algX p U) x).comp (algebraMap k _) = algX p U :=
    RingHom.ext fun a => MvPolynomial.eval₂Hom_C _ _ a
  have h := (RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.1 hx).comp
    (isStandardSmooth_C k D)
  rwa [hC, zero_add] at h

theorem smooth_of_etale {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {D : ℕ}
    {U : X.Opens} (hU : IsAffineOpen U) (x : Fin D → Γ(X, U))
    (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) :
    SmoothOfRelativeDimension D (U.ι ≫ p) := by
  have hA : IsAffine U.toScheme := hU
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv (isStandardSmooth_algX p x hx)
  have h₂ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _
    U.topIso.symm.commRingCatIsoToRingEquiv h₁
  refine (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension D)).2
    (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_)
  have e : (U.ι ≫ p).appTop = (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (by simp) ≫ U.topIso.inv := by
    rw [Iso.hom_inv_id_assoc]
    simp only [Scheme.Hom.appTop, Scheme.Hom.appLE, Scheme.Hom.comp_app, Scheme.Opens.topIso_inv,
      Scheme.Opens.ι_app, Category.assoc]
    exact (congrArg (p.app ⊤ ≫ ·) (Eq.trans (congrArg X.presheaf.map (Subsingleton.elim _ _))
      (X.presheaf.map_comp _ _))).trans (Category.assoc _ _ _).symm
  rw [e]
  exact h₂

end GlobalTheory.ChartSmooth
