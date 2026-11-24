module

public import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReducedFiniteTypeIffTestRing
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
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.InvSubmonoid
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem testRing_localizationAway :
    ∀ (K : Type) [Field K] (p : TRing K) (g : p.R), ∃ (p' : TRing K) (lam : p.R →ₐ[K] p'.R), IsUnit (lam g) ∧ ∀ (T : Type) [CommRing T] [Algebra K T] (ψ : p.R →ₐ[K] T), IsUnit (ψ g) → ∃ k : p'.R →ₐ[K] T, k.comp lam = ψ := by
  intro K _ p g
  obtain ⟨h1, h2⟩ := reduced_finiteType_iff_testRing K
  obtain ⟨hft, hred⟩ := h2 p
  have hft1 : Algebra.FiniteType p.R (Localization.Away g) :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers g) _
  have hft' : Algebra.FiniteType K (Localization.Away g) := Algebra.FiniteType.trans hft hft1
  have hred' : IsReduced (Localization.Away g) :=
    isReduced_localizationPreserves (Submonoid.powers g) _ hred
  obtain ⟨p', ⟨e⟩⟩ := h1 (Localization.Away g) hft' hred'
  refine ⟨p', e.symm.toAlgHom.comp (IsScalarTower.toAlgHom K p.R (Localization.Away g)), ?_, ?_⟩
  · exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map e.symm
  · intro T _ _ ψ hψ
    have hu : ∀ y : Submonoid.powers g, IsUnit (ψ y) := by
      rintro ⟨_, n, rfl⟩
      simpa using hψ.pow n
    refine ⟨(IsLocalization.liftAlgHom (M := Submonoid.powers g) (S := Localization.Away g)
      (f := ψ) hu).comp e.toAlgHom, ?_⟩
    apply AlgHom.ext
    intro x
    simp [IsLocalization.liftAlgHom]

end GlobalTheory
