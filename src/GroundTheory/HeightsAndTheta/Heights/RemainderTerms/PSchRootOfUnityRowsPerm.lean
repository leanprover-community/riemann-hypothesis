module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchRootOfUnityRowsPerm.proof : SchRootOfUnityRowsPerm.Statement := by
  intro k l π hk hl
  have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  have hζk : rootOfUnity k ^ k = 1 := by
    unfold rootOfUnity
    exact (Complex.isPrimitiveRoot_exp k hk0).pow_eq_one
  have hmod : ∀ j n : ℕ, rootOfUnity k ^ (j * n) = rootOfUnity k ^ (j * (n % k)) := by
    intro j n
    conv_lhs => rw [← Nat.mod_add_div n k]
    rw [mul_add, pow_add, mul_left_comm j k, pow_mul (rootOfUnity k) k, hζk, one_pow, mul_one]
  have hM : (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * l i)) =
      (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).submatrix π id := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id]
    rw [hmod, hl i]
  rw [hM, Matrix.det_permute]

end GroundTheory.Heights₂.Heights.RestTerms
