module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

variable {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] (j : G₀ ⟶ G)

abbrev RangeIsId : Prop := ∀ x : G.left, x ∈ Set.range j.left ↔
  x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))

include j in
theorem unit_mem_fibre (s : S) : (η[G]).left s ∈ G.hom ⁻¹' {s} := by
  show G.hom ((η[G]).left s) = s
  rw [← Scheme.Hom.comp_apply, Over.w]
  rfl

theorem isConnected_fibre [IsOpenImmersion j.left] (hr : RangeIsId j) (s : S) :
    _root_.IsConnected (G₀.hom ⁻¹' {s}) := by
  have hw : ∀ x, G.hom (j.left x) = G₀.hom x := fun x => by
    rw [← Scheme.Hom.comp_apply, Over.w]
  have himg : j.left '' (G₀.hom ⁻¹' {s}) = connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := (hr (j.left x)).1 ⟨x, rfl⟩
      rwa [hw, show G₀.hom x = s from hx] at this
    · intro hy
      have hys : G.hom y = s := connectedComponentIn_subset (G.hom ⁻¹' {s}) _ hy
      obtain ⟨x, rfl⟩ := (hr y).2 (by rwa [hys])
      exact ⟨x, by rw [Set.mem_preimage, ← hw, hys]; rfl, rfl⟩
  have hc : _root_.IsConnected (connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s)) :=
    isConnected_connectedComponentIn_iff.mpr (unit_mem_fibre j s)
  rw [← himg] at hc
  exact ⟨hc.nonempty.of_image, j.left.isOpenEmbedding.isInducing.isPreconnected_image.1 hc.isPreconnected⟩

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId
