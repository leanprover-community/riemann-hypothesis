module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearIndependentIterates
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

@[expose] public section

open Polynomial Matrix

namespace GlobalTheory.ConjLocal

theorem conj_of_charpoly_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y Y' : Matrix (Fin n) (Fin n) R),
    Y.charpoly = Y'.charpoly → Y.charpoly.Separable →
    ∃ g : GL (Fin n) R, Y' = (g⁻¹ : GL (Fin n) R).val * Y * g.val := by
  intro R _ _ n Y Y' h hs
  obtain ⟨v, hv⟩ := exists_isUnit_det_iterMat Y hs
  obtain ⟨v', hv'⟩ := exists_isUnit_det_iterMat Y' (h ▸ hs)
  let u : GL (Fin n) R := nonsingInvUnit (iterMat Y v) hv
  let u' : GL (Fin n) R := nonsingInvUnit (iterMat Y' v') hv'
  have e1 : Y * u.val = u.val * compMat Y.charpoly := mul_iterMat Y v
  have e2 : Y' * u'.val = u'.val * compMat Y.charpoly := by rw [h]; exact mul_iterMat Y' v'
  refine ⟨u * u'⁻¹, ?_⟩
  rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
  calc Y' = Y' * u'.val * (u'⁻¹ : GL (Fin n) R).val := by rw [mul_assoc, Units.mul_inv, mul_one]
    _ = u'.val * compMat Y.charpoly * (u'⁻¹ : GL (Fin n) R).val := by rw [e2]
    _ = u'.val * ((u⁻¹ : GL (Fin n) R).val * (u.val * compMat Y.charpoly)) * (u'⁻¹ : GL (Fin n) R).val := by
      rw [← mul_assoc (u⁻¹ : GL (Fin n) R).val, Units.inv_mul, one_mul]
    _ = u'.val * ((u⁻¹ : GL (Fin n) R).val * (Y * u.val)) * (u'⁻¹ : GL (Fin n) R).val := by rw [e1]
    _ = _ := by simp only [mul_assoc]

end GlobalTheory.ConjLocal
