module

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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.DualLattices.StThmA
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.Basis.Defs
public import ReciprocityTheory.DualLattices.SqZeroOfSpan

@[expose] public section

noncomputable section

open TensorProduct Matrix

namespace ReciprocityTheory.PGsh

variable {R₀ : Type} [CommRing R₀]

private lemma ev_expand (B : BX R₀) {O : LAlg R₀} {g : ℕ} (gb : Module.Basis (Fin g) R₀ B.gg)
    (h : B.gg →ₗ[R₀] (O : Type)) (b : B.gg ⊗[R₀] (O : Type)) :
    B.ev h b = ∑ a, h (gb a) * B.ev (Algebra.linearMap R₀ (O : Type) ∘ₗ gb.coord a) b := by
  induction b using TensorProduct.induction_on with
  | zero => simp [BX.ev]
  | tmul x r =>
    simp only [BX.ev, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.id_apply,
      LinearMap.comp_apply, Algebra.linearMap_apply, Module.Basis.coord_apply]
    conv_lhs => rw [← gb.sum_repr x]

    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, Algebra.smul_def]
    ring
  | add a b ha hb =>
    simp only [BX.ev, map_add (f := _)] at *
    rw [ha, hb, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

end ReciprocityTheory.PGsh
