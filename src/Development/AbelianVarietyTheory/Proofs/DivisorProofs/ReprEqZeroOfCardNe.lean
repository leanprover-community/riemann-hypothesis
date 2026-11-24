module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.LineForm

namespace GlobalTheory.PullTop

theorem repr_eq_zero_of_card_ne {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder I]
    (b : Module.Basis I R M) {k : ℕ} (x : ⋀[R]^k M) {S : Finset I} (hS : S.card ≠ k) :
    b.ExteriorAlgebra.repr (x : ExteriorAlgebra R M) S = 0 := by
  have h : (Finsupp.lapply S ∘ₗ b.ExteriorAlgebra.repr.toLinearMap ∘ₗ (⋀[R]^k M).subtype) = 0 := by
    refine (b.exteriorPower k).ext fun s => ?_
    have hs : (s : Finset I) ≠ S := fun e => hS (e ▸ s.2)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, ← ExteriorAlgebra.basis_eq_coe_basis,
      LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply, LinearMap.zero_apply]
    exact Finsupp.single_eq_of_ne' hs
  exact LinearMap.congr_fun h x

end GlobalTheory.PullTop
