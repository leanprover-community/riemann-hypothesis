module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheafA
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.SncStalk

theorem rsp_of_units {R : Type} [CommRing R] [IsLocalRing R] {n : ℕ} (y z : Fin n → R) (u : Fin n → Rˣ)
    (h : ∀ i, z i = (u i : R) * y i) (hy : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R n y) :
    ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R n z := by
  refine ⟨?_, hy.2⟩
  rw [← hy.1]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [h i]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have : y i = ((u i)⁻¹ : Rˣ) * z i := by rw [h i, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem stalk_snc : ∀ (X : Scheme.{0}) (I : X.IdealSheafData), ReciprocityTheory.AnForm.R.FinalTheorems.Snc I →
    ∀ (U : X.affineOpens) (x : X) (hx : x ∈ U.1), IsRegularLocalRing (X.presheaf.stalk x) ∧
      ∃ (m : ℕ) (a : Fin m → Γ(X, U.1)) (J : Finset (Fin m)),
        ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (X.presheaf.stalk x) m (fun i => (X.presheaf.germ U.1 x hx).hom (a i)) ∧
        (I.ideal U).map (X.presheaf.germ U.1 x hx).hom =
          Ideal.span {(X.presheaf.germ U.1 x hx).hom (∏ i ∈ J, a i)} := by
  intro X I hI U x hx
  obtain ⟨hreg, U₁, hx₁, n, f, J, hR, hI₁⟩ := hI x
  refine ⟨hreg, ?_⟩
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  haveI hloc := U.2.isLocalization_stalk ⟨x, hx⟩
  have halg : ∀ r : Γ(X, U.1), algebraMap Γ(X, U.1) (X.presheaf.stalk x) r =
      (X.presheaf.germ U.1 x hx).hom r := fun r => rfl
  have key : ∀ i : Fin n, ∃ (a : Γ(X, U.1)) (t : Γ(X, U.1)),
      IsUnit ((X.presheaf.germ U.1 x hx).hom t) ∧
      (X.presheaf.germ U.1 x hx).hom a = (X.presheaf.germ U₁.1 x hx₁).hom (f i) * (X.presheaf.germ U.1 x hx).hom t := by
    intro i
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      ((X.presheaf.germ U₁.1 x hx₁).hom (f i))
    refine ⟨a, t, ?_, ?_⟩
    · rw [← halg]; exact IsLocalization.map_units _ t
    · rw [← halg, ← halg, ← hat]
      exact (IsLocalization.mk'_spec _ a t).symm
  choose a t ht hat using key
  refine ⟨n, a, J, ?_, ?_⟩
  · refine rsp_of_units _ _ (fun i => (ht i).unit) ?_ hR
    intro i
    rw [hat i, IsUnit.unit_spec, mul_comm]
  · rw [← ReciprocityTheory.AnForm.R.ds_stalkId_eq_map I U x hx, ReciprocityTheory.AnForm.R.ds_stalkId_eq_map I U₁ x hx₁, hI₁,
      Ideal.map_span, Set.image_singleton, map_prod, map_prod]
    have : ∏ i ∈ J, (X.presheaf.germ U.1 x hx).hom (a i) =
        (∏ i ∈ J, (X.presheaf.germ U.1 x hx).hom (t i)) * ∏ i ∈ J, (X.presheaf.germ U₁.1 x hx₁).hom (f i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hat i, mul_comm]
    rw [this, Ideal.span_singleton_mul_left_unit]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i _ => ht i

end GlobalTheory.SncStalk
