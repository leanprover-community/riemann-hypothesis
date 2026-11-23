module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.SurjOfCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TranslPull

theorem transl_comp_of_isGrpPullback : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (x : 𝟙_ (Over S') ⟶ G') (s : 𝟙_ (Over S) ⟶ G), x.left ≫ φ = f ≫ s.left → (lift (toUnit G' ≫ x) (𝟙 G') ≫ μ[G']).left ≫ φ = φ ≫ (lift (toUnit G ≫ s) (𝟙 G) ≫ μ[G]).left := by
  intro S S' G' _ G _ f φ h x s hx
  have hu' : ∀ (Y : Over S'), (toUnit Y).left = Y.hom := fun Y => by
    simpa using Over.w (toUnit Y)
  have hu : ∀ (Y : Over S), (toUnit Y).left = Y.hom := fun Y => by
    simpa using Over.w (toUnit Y)
  have hs : s.left ≫ G.hom = 𝟙 S := by simpa using Over.w s
  let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk (G'.hom ≫ f ≫ s.left) (by
    simp [hs])
  let y₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ (by simpa using h.1.w)
  have key := h.2 G' (toUnit G' ≫ x) (𝟙 G') x₀ y₀ (by
      simp [x₀, hu', hx]) (by simp [y₀])
  have e1 : lift (toUnit G' ≫ x) (𝟙 G') ≫ μ[G'] = (toUnit G' ≫ x) * 𝟙 G' := rfl
  have e2 : x₀ * y₀ = (Over.homMk φ (by simpa using h.1.w) : Over.mk (G'.hom ≫ f) ⟶ G) ≫ (lift (toUnit G ≫ s) (𝟙 G) ≫ μ[G]) := by
    rw [← Category.assoc, comp_lift, Category.comp_id]
    have hx0 : x₀ = ((Over.homMk φ (by simpa using h.1.w) : Over.mk (G'.hom ≫ f) ⟶ G) ≫ toUnit G) ≫ s := by
      apply Over.OverMorphism.ext
      simp [x₀, hu]
    rw [hx0]
    rfl
  rw [e1, ← key, e2]
  rfl
end GlobalTheory.TranslPull
