module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
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

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

namespace GlobalTheory.PtExt

theorem chi_natural (p : ℕ) (R : Type) [CommRing R] (hp : (p : R) = 0)
    (A : Over (Sp R)) [GrpObj A] (f : Fn1 A) (g : Fn2 A) (hg : IsAdd f g)
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt A D) :
    chi p g D' (spOver φ ≫ x) - φ (chi p g D x) = f D D' φ (x ^ p) - f D D' φ 1 := by
  have hp' : (p : D') = 0 := by
    rw [← map_natCast (algebraMap R D') p, hp, map_zero]
  unfold chi
  rw [map_sum φ, ← Finset.sum_sub_distrib]
  have h : ∀ i ∈ Finset.range p, g D' ((spOver φ ≫ x) ^ i) (spOver φ ≫ x) - φ (g D (x ^ i) x) =
      (f D D' φ (x ^ (i + 1)) - f D D' φ (x ^ i)) - f D D' φ x := by
    intro i _
    rw [← MonObj.comp_pow, hg D D' φ (x ^ i) x, pow_succ]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_range_sub (fun i ↦ f D D' φ (x ^ i)) p,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, hp', zero_mul, sub_zero, pow_zero]

end GlobalTheory.PtExt
