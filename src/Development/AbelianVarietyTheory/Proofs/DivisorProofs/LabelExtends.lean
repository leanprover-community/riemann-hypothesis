module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SectionLift
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LineNorm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped Classical

namespace GlobalTheory.LabelExt

section Gen

variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem lift_finite [IsIntegrallyClosed R] {X S : Scheme.{0}} (f : X ⟶ S) [IsFinite f] (y : Sp R ⟶ S) (w : Sp K ⟶ X)
    (h : w ≫ f = spMap (algebraMap R K) ≫ y) : ∃ v : Sp R ⟶ X, v ≫ f = y ∧ spMap (algebraMap R K) ≫ v = w :=
  _root_.UpperTheory.Reformulated.B.Yt7.lift_finite f y w h

theorem ext_frac {S : Scheme.{0}} {G : Over S} [IsSeparated G.hom] {y : Sp R ⟶ S} {u v : Over.mk y ⟶ G}
    (h : spMap (algebraMap R K) ≫ u.left = spMap (algebraMap R K) ≫ v.left) : u = v := by
  haveI : IsDominant (spMap (algebraMap R K)) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R K)).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]; exact bot_le)
  haveI : IsReduced (Over.mk y).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  ext1
  exact ext_of_isDominant_of_isSeparated G.hom (by rw [Over.w u, Over.w v]) (spMap (algebraMap R K)) h

theorem lift_tors [IsIntegrallyClosed R] {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) {q : ℕ}
    (hq : q ≠ 0) {y : Sp R ⟶ S} {y' : Sp K ⟶ S} (hy : spMap (algebraMap R K) ≫ y = y') (w : Over.mk y' ⟶ G)
    (hw : w ^ q = 1) : ∃ v : Over.mk y ⟶ G, spMap (algebraMap R K) ≫ v.left = w.left := by
  haveI := (AbTorsionAnyBase.isFinite_and_flat_torsion S G hG q (Nat.one_le_iff_ne_zero.2 hq)).1
  have e : w ≫ mulN G q = CartesianMonoidalCategory.toUnit _ ≫ η[G] := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hw]; rfl
  let w₁ : Over.mk y' ⟶ torsion G q := Limits.pullback.lift w _ e
  have h₁ : w₁ ≫ torsion.ι G q = w := Limits.pullback.lift_fst _ _ _
  obtain ⟨v, hv, hv'⟩ := lift_finite (torsion G q).hom y w₁.left ((Over.w w₁).trans hy.symm)
  refine ⟨(Over.homMk v hv : Over.mk y ⟶ torsion G q) ≫ torsion.ι G q, ?_⟩
  rw [← h₁, Over.comp_left, Over.comp_left, ← hv', Category.assoc]
  rfl

end Gen

end GlobalTheory.LabelExt

end
