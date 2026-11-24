module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightObjects
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PHeightRecR
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem eval_smul_of_isMultiHomog (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ)
    (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (c : ι → ℂ) (z : Coord n → ℂ) :
    eval (fun p ↦ c p.1 * z p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) s) := by
  have key : ∀ f : MvPolynomial (Coord n) ℤ,
      eval c (Geo.mConeMap (ι := blockIdx n) z f) = eval (fun p ↦ c p.1 * z p) (map (Int.castRingHom ℂ) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => simp [Geo.mConeMap]
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | mul_X f p hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [Geo.mConeMap, mul_comm]
  classical
  rw [← key, mConeMap_of_isMultiHomog z s a hs, eval_map]
  simp [map_prod, mul_comm]

end GroundTheory.Heights₂.Heights
