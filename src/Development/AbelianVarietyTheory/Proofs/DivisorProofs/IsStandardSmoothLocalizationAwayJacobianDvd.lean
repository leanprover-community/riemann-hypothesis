module

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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd
    (R ν σ : Type) [CommRing R] [Finite ν] [Fintype σ] [DecidableEq σ] (m : σ → ν)
    (hm : Function.Injective m) (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R)
    (hdvd : (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det ∣ h) :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ν - Nat.card σ) R
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
  classical
  set A := MvPolynomial ν R ⧸ Ideal.span (Set.range F)
  set T := Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)
  let P := Algebra.PreSubmersivePresentation.naive (v := F) m hm
  let Q := Algebra.SubmersivePresentation.localizationAway T
    (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)
  have hPjac : P.jacobian = Ideal.Quotient.mk (Ideal.span (Set.range F))
      (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det := by
    rw [P.jacobian_eq_jacobiMatrix_det, Algebra.Generators.algebraMap_apply]
    have hM : P.jacobiMatrix = Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t) := by
      ext i j
      simp [P]
    rw [hM]
    have : MvPolynomial.aeval P.val = Ideal.Quotient.mkₐ R (Ideal.span (Set.range F)) :=
      MvPolynomial.algHom_ext fun v => by simp [P]
    rw [this]
    rfl
  let P' : Algebra.SubmersivePresentation R T (Unit ⊕ ν) (Unit ⊕ σ) :=
    { __ := Q.toPreSubmersivePresentation.comp P
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def]
        refine IsUnit.mul ?_ Q.jacobian_isUnit
        rw [hPjac]
        exact isUnit_of_dvd_unit (map_dvd _ (map_dvd _ hdvd))
          (IsLocalization.Away.algebraMap_isUnit _) }
  refine P'.isStandardSmoothOfRelativeDimension ?_
  change (Q.toPreSubmersivePresentation.comp P).dimension = _
  rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  simp [Algebra.Presentation.dimension, P]

end GlobalTheory.Pinch
