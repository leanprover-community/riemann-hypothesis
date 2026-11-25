module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.LocusEqTopOfDualPow
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoGrCechMapPolyToGamma
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GlobalTheory.Adelic

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Points GlobalTheory.Twist GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

theorem smoothOfRelativeDimension_pspace (R : Type) [CommRing R] (M : ℕ) :
    SmoothOfRelativeDimension M (PSpace.str R M) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} M)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension M))
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} M) (chartCover R M)
    fun (i : Fin (M + 1)) => ?_
  change SmoothOfRelativeDimension M (chartι R M i ≫ _)
  rw [chartι_str]
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension M)).2 ?_
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  have h := Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial R {j : Fin (M + 1) // j ≠ i}
  rw [show Nat.card {j : Fin (M + 1) // j ≠ i} = M by simp] at h
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap M).2 h

variable (k : Type) [Field k] (M : ℕ)

theorem geometricallyConnected_pspace : GeometricallyConnected (PSpace.str k M) :=
  ⟨geometrically_iff_of_commRing.2 fun K _ _ _ _ _ h =>
    have e := (isPullback_baseChange M (algebraMap k K)).isoIsPullback _ _ h
    e.hom.homeomorph.surjective.connectedSpace e.hom.continuous⟩

abbrev projSys : LinSys k where
  Y := PSpace k M
  str := PSpace.str k M
  D := M
  L := O1 k M
  isLB := O1_isLB k M
  N := M + 1
  b := coord k M

namespace projSys

theorem algebraΓ_eq : (projSys k M).algebraΓ = algebraSections k M ⊤ :=
  Algebra.algebra_ext _ _ fun _r => (LB.resG_self (X := PSpace k M) le_top _).symm

theorem form_eq {d : ℕ} {g : MvPolynomial (Fin (M + 1)) k} (hg : g.IsHomogeneous d) :
    (projSys k M).form hg = ProjSpace.formSec d g hg := by
  rw [ProjCoh.formSec_eq]
  exact congrArg (fun a : Algebra k Γ(PSpace k M, ⊤) =>
    letI := a; Twist.formSec (coord k M) (mem_polyGrading_natCast.2 hg)) (algebraΓ_eq k M)

theorem eq_of_sameImage {y y' : PSpace k M} (h : (projSys k M).SameImage y y') : y = y' := by
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.ext' fun d g hg => ?_)
  replace hg : g.IsHomogeneous d := hg
  have := h d g hg
  rw [form_eq, nonzeroLocus_formSec] at this
  exact not_iff_not.1 this

abbrev gen : PSpace k M := AmpleModel.genericPt k M

theorem gen_mem (i : Fin (M + 1)) : gen k M ∈ chart k M i := fun h => X_ne_zero (R := k) i h

theorem valR_resPt {Y : Scheme.{0}} (y : Y) (U : Y.Opens) (hy : y ∈ U) (f : Γ(Y, U)) :
    valR (resPt y) U f = Y.evaluation U y hy f := by
  have ht : ⊤ ≤ Y.fromSpecStalk y ⁻¹ᵁ U := (le_preimage_iff (C := Y.presheaf.stalk y) _ U).2 (by
    rw [show Y.fromSpecStalk y (IsLocalRing.closedPoint (Y.presheaf.stalk y)) = y from
      Scheme.fromSpecStalk_closedPoint]; exact hy)
  have e : valMap (C := Y.presheaf.stalk y) (Y.fromSpecStalk y) U ht = Y.presheaf.germ U y hy := by
    change (Y.fromSpecStalk y).appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom = _
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hy]
    simp only [Category.assoc]
    have e : (Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE (le_top : Y.fromSpecStalk y ⁻¹ᵁ U ≤ ⊤)).op ≫
        (Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  exact (valR_spMap_comp (Y.residue y).hom (Y.fromSpecStalk y) U ht f).trans (congrArg (Y.residue y).hom
    ((valR_eq (C := Y.presheaf.stalk y) _ _ ht f).trans (congrArg (fun q => q.hom f) e)))

end projSys
end GlobalTheory.Adelic
