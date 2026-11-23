module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Valuation.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset Filter Topology

namespace ReciprocityTheory.PGsh.Up.Det2

theorem v_det_scaled {C : Type} [Field C] (v : Valuation C NNReal) {ι : Type} [Fintype ι]
    [DecidableEq ι] (c : Matrix ι ι C) (y z : ι → C) :
    v (Matrix.of fun j k => c j k * (y j / z k)).det =
      v c.det * (∏ j, v (y j)) / ∏ k, v (z k) := by
  have hM : (Matrix.of fun j k => c j k * (y j / z k)) =
      Matrix.diagonal y * c * Matrix.diagonal fun k => (z k)⁻¹ := by
    ext j k
    simp only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, div_eq_mul_inv]
    ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, map_mul, map_mul,
    map_prod, map_prod]
  simp only [map_inv₀, Finset.prod_inv_distrib, div_eq_mul_inv]
  ring

end ReciprocityTheory.PGsh.Up.Det2
