module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
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
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem etale_of_formallyUnramified_of_relDim : ∀ (A B C : Type) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (g : ℕ),
    Algebra.IsStandardSmoothOfRelativeDimension g A B →
    Algebra.IsStandardSmoothOfRelativeDimension g A C →
    Algebra.FormallyUnramified B C → Algebra.Etale B C := by
  intro A B C _ _ _ _ _ _ _ g hB hC hU
  have : Algebra.IsStandardSmooth A B := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : Algebra.IsStandardSmooth A C := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have hs : Function.Surjective (KaehlerDifferential.mapBaseChange A B C) := fun x =>
    (KaehlerDifferential.exact_mapBaseChange_map A B C x).mp (Subsingleton.elim _ _)
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange A B C) := by
    rcases subsingleton_or_nontrivial C with hC0 | hC0
    · intro x y _
      exact Subsingleton.elim (α := TensorProduct B C Ω[B⁄A]) x y
    · have : Nontrivial B := (algebraMap B C).domain_nontrivial
      have : Module.Free B Ω[B⁄A] := Algebra.IsStandardSmooth.free_kaehlerDifferential
      have : Module.Free C Ω[C⁄A] := Algebra.IsStandardSmooth.free_kaehlerDifferential
      have hr : Module.rank C Ω[C⁄A] = Module.rank C (TensorProduct B C Ω[B⁄A]) := by
        rw [Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g, Module.rank_baseChange,
          Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g]
        simp
      obtain ⟨e⟩ := nonempty_linearEquiv_of_rank_eq hr
      have h2 : Function.Surjective (e.toLinearMap ∘ₗ KaehlerDifferential.mapBaseChange A B C) :=
        e.surjective.comp hs
      have h3 := OrzechProperty.injective_of_surjective_endomorphism _ h2
      exact fun x y hxy => h3 (by simp [hxy])
  have : Algebra.FormallySmooth B C := by
    rw [Algebra.formallySmooth_iff]
    constructor
    · exact Module.Projective.of_free
    · refine subsingleton_of_forall_eq 0 fun x => ?_
      have h₁ : Algebra.H1Cotangent.δ A B C x = 0 := by
        apply hinj
        rw [map_zero]
        exact (Algebra.H1Cotangent.exact_δ_mapBaseChange A B C).apply_apply_eq_zero x
      obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ A B C x).mp h₁
      rw [Subsingleton.elim y 0, map_zero]
  have : Algebra.FormallyEtale B C := Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
  have : Algebra.FinitePresentation B C := Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A B C
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory
