module

public import Mathlib.Algebra.Group.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem addition_factor_through_cubical_even_iso : ∀ (H U : Type) [CommGroup H] [CommGroup U] (W sL sM : H → U) (cL cM : H → H → H → U) (rL rM : U), rM = W 1 * rL → (∀ x, sM x * W x = W x⁻¹ * sL x) → (∀ x y u, cM x y u * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * cL x y u) → ∀ x y, W x ^ 2 * W y ^ 2 * (cL x y y⁻¹ * (sL y)⁻¹ * rL ^ 2) = cM x y y⁻¹ * (sM y)⁻¹ * rM ^ 2 * (W (x * y) * W (x * y⁻¹)) := by
  intro H U _ _ W sL sM cL cM rL rM hr hs hc x y
  have h1 := hc x y y⁻¹
  rw [mul_inv_cancel, mul_inv_cancel_right] at h1
  have h2 : sM y = W y⁻¹ * sL y * (W y)⁻¹ := eq_mul_inv_of_mul_eq (hs y)
  have h3 : cM x y y⁻¹ = W x * W x * W y * W y⁻¹ * cL x y y⁻¹ *
      (W (x * y) * W (x * y⁻¹) * W 1 * W 1)⁻¹ := by
    apply eq_mul_inv_of_mul_eq
    rw [← h1]
    simp only [_root_.mul_assoc]
  rw [h2, h3, hr]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

end GlobalTheory
