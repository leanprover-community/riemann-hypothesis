module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyPow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve

theorem exists_mem_coordOpen_two {R : Type} [CommRing R] (W : WeierstrassCurve R) (s : Sp R) :
    ∃ x : scheme W, toSpec W x = s ∧ x ∈ coordOpen W 2 := by
  have : Module.Finite (Polynomial R) W.toAffine.CoordinateRing :=
    .of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)
  have : FaithfulSMul (Polynomial R) W.toAffine.CoordinateRing :=
    ⟨fun {p q} h => by
      have e := congrArg (fun a => (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine).repr a 0)
        (h (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine 0))
      simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul] at e
      exact (mul_one p).symm.trans (e.trans (mul_one q))⟩
  obtain ⟨y, hy⟩ := Algebra.IsIntegral.comap_surjective (Polynomial R) W.toAffine.CoordinateRing
    (PrimeSpectrum.comap (Polynomial.evalRingHom 0) s)
  refine ⟨chartZ W y, ?_, (opensRange_chartZ W).le ⟨y, rfl⟩⟩
  refine (Scheme.Hom.comp_apply (chartZ W) (toSpec W) y).symm.trans ?_
  rw [chartZ_toSpec]
  change PrimeSpectrum.comap (algebraMap R W.toAffine.CoordinateRing) y = s
  rw [IsScalarTower.algebraMap_eq R (Polynomial R), PrimeSpectrum.comap_comp_apply, hy]
  have e : (Polynomial.evalRingHom (0 : R)).comp (algebraMap R (Polynomial R)) = RingHom.id R := by
    ext; simp
  exact congrArg (fun f => PrimeSpectrum.comap f s) e

end GlobalTheory.KeyPow
