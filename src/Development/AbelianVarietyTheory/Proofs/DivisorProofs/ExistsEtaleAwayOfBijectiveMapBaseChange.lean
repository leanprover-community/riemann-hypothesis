module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
open KaehlerDifferential TensorProduct

theorem bijective_of_bijective_lTensor_residueField {R M N : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Projective R N] (l : M →ₗ[R] N)
    (h : Function.Bijective (l.lTensor (ResidueField R))) : Function.Bijective l := by
  have : Module.Free R N := Module.free_of_flat_of_isLocalRing
  refine ⟨?_, ?_⟩
  · obtain ⟨l', hl'⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective l).mpr h.1
    exact Function.HasLeftInverse.injective ⟨l', LinearMap.congr_fun hl'⟩
  · have hex := lTensor_exact (ResidueField R) (LinearMap.exact_map_mkQ_range l)
      (Submodule.mkQ_surjective _)
    have hsub : Subsingleton (ResidueField R ⊗[R] (N ⧸ LinearMap.range l)) := by
      refine subsingleton_of_forall_eq 0 fun y => ?_
      obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective (ResidueField R) (Submodule.mkQ_surjective _) y
      obtain ⟨z, rfl⟩ := h.2 x
      exact hex.apply_apply_eq_zero z
    rw [IsLocalRing.subsingleton_tensorProduct] at hsub
    rw [← LinearMap.range_eq_top]
    exact Submodule.Quotient.subsingleton_iff.mp hsub

theorem formallyEtale_of_bijective_mapBaseChange (R P B : Type*) [CommRing R] [CommRing P]
    [CommRing B] [Algebra R P] [Algebra R B] [Algebra P B] [IsScalarTower R P B]
    [Algebra.FormallySmooth R B] (h : Function.Bijective (mapBaseChange R P B)) :
    Algebra.FormallyEtale P B := by
  have h1 : Subsingleton Ω[B⁄P] := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := map_surjective R P B x
    exact (exact_mapBaseChange_map R P B y).mpr (h.2 y)
  have h2 : Subsingleton (Algebra.H1Cotangent P B) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    have h3 : Algebra.H1Cotangent.δ R P B x = 0 := by
      apply h.1
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R P B _).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R P B x).mp h3
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨h1, h2⟩

theorem bijective_lTensor_baseChange_of_bijective {B M N : Type*} [CommRing B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] (Q : Ideal B) [Q.IsPrime]
    (φ : M →ₗ[B] N) (h : Function.Bijective (φ.lTensor Q.ResidueField)) :
    Function.Bijective ((φ.baseChange (Localization.AtPrime Q)).lTensor
      (ResidueField (Localization.AtPrime Q))) := by
  let BQ := Localization.AtPrime Q
  let k := ResidueField BQ
  let eM := AlgebraTensorModule.cancelBaseChange B BQ k k M
  let eN := AlgebraTensorModule.cancelBaseChange B BQ k k N
  have key : ∀ x, eN ((φ.baseChange BQ).lTensor k x) = φ.lTensor Q.ResidueField (eM x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => simp only [tmul_add, map_add (f := _)] at hy hz ⊢; rw [hy, hz]
      | tmul q m => simp [eM, eN]
  have : ⇑((φ.baseChange BQ).lTensor k) = eN.symm ∘ (φ.lTensor Q.ResidueField) ∘ eM := by
    funext x; simp [← key]
  rw [this]
  exact eN.symm.bijective.comp (h.comp eM.bijective)

theorem kaehler_map_map_apply (A C B BQ : Type) [CommRing A] [CommRing C] [CommRing B] [CommRing BQ] [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B]
   [Algebra B BQ] [Algebra A BQ] [Algebra C BQ] [IsScalarTower A B BQ] [IsScalarTower C B BQ] [IsScalarTower A C BQ] (ω : Ω[C⁄A]) :
    map A A B BQ (map A A C B ω) = map A A C BQ ω := by
  have : ((map A A B BQ).restrictScalars C).comp (map A A C B) = map A A C BQ := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    simp [map_D, ← IsScalarTower.algebraMap_apply]
  exact LinearMap.congr_fun this ω

theorem exists_etale_away_of_bijective_mapBaseChange : ∀ (A C B : Type) [CommRing A] [CommRing C]
    [CommRing B] [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B] [Algebra.Smooth A C]
    [Algebra.Smooth A B] (Q : Ideal B) [Q.IsPrime],
    Function.Bijective ((KaehlerDifferential.mapBaseChange A C B).lTensor Q.ResidueField) →
      ∃ f : B, f ∉ Q ∧ Algebra.Etale C (Localization.Away f) := by
  intro A C B _ _ _ _ _ _ _ _ _ Q _ h
  let BQ := Localization.AtPrime Q
  let φ := mapBaseChange A C B
  have hψ₀ : Function.Bijective (φ.baseChange BQ) :=
    bijective_of_bijective_lTensor_residueField _ (bijective_lTensor_baseChange_of_bijective Q φ h)
  let eM := AlgebraTensorModule.cancelBaseChange C B BQ BQ Ω[C⁄A]
  have hbc : IsBaseChange BQ (map A A B BQ) :=
    (isLocalizedModule_iff_isBaseChange Q.primeCompl BQ _).mp
      (isLocalizedModule_map A B BQ Q.primeCompl)
  let eN := hbc.equiv
  have key : ∀ x, mapBaseChange A C BQ (eM x) = eN (φ.baseChange BQ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul q y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => simp only [tmul_add, map_add (f := _)] at hy hz ⊢; rw [hy, hz]
      | tmul b ω =>
        simp only [eM, eN, φ, AlgebraTensorModule.cancelBaseChange_tmul, mapBaseChange_tmul,
          LinearMap.baseChange_tmul]
        rw [IsBaseChange.equiv_tmul, map_smul, kaehler_map_map_apply, smul_assoc, smul_comm q b]
  have hψ : Function.Bijective (mapBaseChange A C BQ) := by
    have : ⇑(mapBaseChange A C BQ) = eN ∘ (φ.baseChange BQ) ∘ eM.symm := by
      funext x; simp [← key]
    rw [this]
    exact eN.bijective.comp (hψ₀.comp eM.symm.bijective)
  haveI : Algebra.FormallySmooth B BQ := Algebra.FormallySmooth.of_isLocalization Q.primeCompl
  haveI : Algebra.FormallySmooth A BQ := Algebra.FormallySmooth.comp A B BQ
  haveI : Algebra.IsEtaleAt C Q := formallyEtale_of_bijective_mapBaseChange A C BQ hψ
  haveI : Algebra.FinitePresentation C B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A C B
  exact Algebra.exists_etale_of_isEtaleAt Q

end GlobalTheory.Mum
