module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SmoothDescent

theorem smoothOfRelativeDimension_of_etale_cover_noetherian :
    ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp K) (d : ℕ), Etale π → Surjective π → LocallyOfFiniteType s → SmoothOfRelativeDimension d (π ≫ s) → SmoothOfRelativeDimension d s := by
  intro K _ _ X Y π s d _ _ _ hd
  have : Smooth (π ≫ s) := SmoothOfRelativeDimension.smooth d _
  have : Smooth s := smooth_of_comp_of_etale_of_surjective π s
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  choose n W hW hn using H1.exists_dim s
  have key (y : Y) : n y = d := by
    obtain ⟨x, rfl⟩ := π.surjective y
    have := hn (π x)
    have h₁ : SmoothOfRelativeDimension (0 + n (π x)) ((π ∣_ W (π x)) ≫ (W (π x)).ι ≫ s) := inferInstance
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at h₁
    have h₂ : SmoothOfRelativeDimension (0 + d) ((π ⁻¹ᵁ W (π x)).ι ≫ π ≫ s) := inferInstance
    simpa using H1.dim_unique _ h₁ h₂ ⟨x, hW (π x)⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W ?_ fun y => key y ▸ hn y
  rw [← top_le_iff]
  rintro y -
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩

end GlobalTheory.SmoothDescent
