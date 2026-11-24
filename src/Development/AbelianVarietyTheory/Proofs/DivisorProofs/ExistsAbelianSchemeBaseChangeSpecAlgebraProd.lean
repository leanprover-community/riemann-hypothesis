module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

set_option backward.isDefEq.respectTransparency false in
theorem exists_baseChange_spAlg_prod (R D : Type) [CommRing R] [CommRing D] [Algebra R D]
    (B : Over (Sp R)) [GrpObj B] (g : ℕ) :
    IsAbelianScheme B → SmoothOfRelativeDimension g B.hom →
      ∃ (B' : Over (Sp D)) (_ : GrpObj B') (π : B'.left ⟶ B.left)
        (q : B'.left ⟶ (SpAlg R D ⊗ B).left),
        IsGrpPullback B' B (spMap (algebraMap R D)) π ∧ IsAbelianScheme B' ∧
          SmoothOfRelativeDimension g B'.hom ∧ IsIso q ∧
          q ≫ (fst (SpAlg R D) B).left = B'.hom ∧ q ≫ (snd (SpAlg R D) B).left = π := by
  intro hA hg
  let f := spMap (algebraMap R D)
  refine ⟨(Over.pullback f).obj B, inferInstance, Limits.pullback.fst B.hom f,
    (Limits.pullbackSymmetry B.hom f).hom,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B f,
    GlobalTheory.isAbelianScheme_pullback_obj f B hA,
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (CategoryTheory.IsPullback.of_hasPullback B.hom f) hg,
    inferInstance, Limits.pullbackSymmetry_hom_comp_fst B.hom f,
    Limits.pullbackSymmetry_hom_comp_snd B.hom f⟩

end GlobalTheory
