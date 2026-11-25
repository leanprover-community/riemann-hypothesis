module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
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

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

namespace GlobalTheory.PtExt.SumMulFacts

theorem ptAlg_comp_right {R D D' E : Type} [CommRing R] [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    [CommRing E] [Algebra R E] (φ : D →ₐ[R] D') (y : Pt (SpAlg R D') E) :
    ptAlg (R := R) (D := D) (E := E) (y ≫ spOver φ) = (ptAlg y).comp φ := by
  conv_lhs => rw [← spOver_ptAlg y, spOver_comp]
  exact ptAlg_spOver _

theorem main : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] (B : Over (Sp R))
    (J : Type) [Fintype J] (d : J → D) (b : J → Fn1 B),
    ((∀ i, IsCoc (whole B) (b i)) → IsCoc (whole _) (sumMul d b)) ∧
      ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D'),
        (sumMul d b).pull (spOver φ ▷ B) = sumMul (fun i ↦ φ (d i)) b := by
  intro R D _ _ _ B J _ d b
  refine ⟨fun hb ↦ ?_, fun D' _ _ φ ↦ ?_⟩
  · unfold IsCoc at hb ⊢
    intro E _ _ E' _ _ E'' _ _ φ ψ z _
    have hα := ptAlg_comp (D := D) φ (z ≫ fst (SpAlg R D) B)

    simp only [sumMul, hα, map_sum, map_mul, AlgHom.comp_apply, Category.assoc]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h := hb i E E' E'' φ ψ (z ≫ snd _ _) (sm_whole _)
    rw [h]
    ring
  · unfold Fn1
    funext E _ _ E' _ _ ψ y
    simp only [Fn1.pull, sumMul, Category.assoc, whiskerRight_fst, whiskerRight_snd]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [← Category.assoc, ptAlg_comp_right, AlgHom.comp_apply]

end GlobalTheory.PtExt.SumMulFacts
