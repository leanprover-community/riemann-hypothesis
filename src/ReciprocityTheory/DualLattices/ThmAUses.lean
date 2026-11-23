module

public import ReciprocityTheory.DualLattices.SmallLevelClassSet
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Basic

@[expose] public section

noncomputable section

open Matrix TensorProduct

namespace ReciprocityTheory.PGsh

section Mat

variable {D : Type} [CommRing D] {g : ℕ}

lemma stdJ_mul_self : stdJ D g * stdJ D g = -1 := by
  ext (i | i) (j | j) <;> simp [stdJ, Matrix.fromBlocks_multiply, Matrix.one_apply]

lemma det_stdJ_sq : (stdJ D g).det ^ 2 = 1 := by
  rw [sq, ← Matrix.det_mul, stdJ_mul_self, Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_sum,
    Fintype.card_fin, ← two_mul, pow_mul]
  simp

lemma isUnit_det_stdJ : IsUnit (stdJ D g).det := by
  exact isUnit_iff_exists_inv.2 ⟨(stdJ D g).det, by rw [← sq, det_stdJ_sq]⟩

lemma det_sq_eq (E Φ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (c : D)
    (hJ : Φᵀ * stdJ D g * Φ = c • E) :
    Φ.det ^ 2 = c ^ (2 * g) * (E.det * (stdJ D g).det) := by
  have h := congrArg Matrix.det hJ
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_sum, Fintype.card_fin,
    ← two_mul] at h
  have hJ2 := det_stdJ_sq (D := D) (g := g)
  calc Φ.det ^ 2 = Φ.det ^ 2 * ((stdJ D g).det ^ 2) := by rw [hJ2, mul_one]
    _ = (Φ.det * (stdJ D g).det * Φ.det) * (stdJ D g).det := by ring
    _ = c ^ (2 * g) * (E.det * (stdJ D g).det) := by rw [h]; ring

end Mat


variable {R₀ : Type} [CommRing R₀]



variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]


end ReciprocityTheory.PGsh
