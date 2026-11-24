module

public import Development.EtaleCohomology.DivisorCycles.OpenCoset
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix Polynomial
namespace LateralTheory.DivDb.SepPolyProof

noncomputable def disc (C : Type) [Field C] (n : ℕ) : MvPolynomial (Fin n × Fin n) C :=
  resultant (charpoly.univ C (Fin n)) (derivative (charpoly.univ C (Fin n))) n (n - 1)

theorem univ_map_ev {C : Type} [Field C] {n : ℕ} (x : Mat C n) :
    (charpoly.univ C (Fin n)).map (MvPolynomial.eval (fun p : Fin n × Fin n => x p.1 p.2)) = x.charpoly := by
  have h := charpoly.univ_map_eval₂Hom (Fin n) (RingHom.id C) (fun p : Fin n × Fin n => x p.1 p.2)
  have hx : (Matrix.of (fun p : Fin n × Fin n => x p.1 p.2).curry) = x := by ext i j; rfl
  rw [hx] at h
  exact h

theorem ev_disc {C : Type} [Field C] [CharZero C] {n : ℕ} (x : Mat C n) :
    ev x (disc C n) = resultant x.charpoly (derivative x.charpoly) := by
  unfold ev disc
  rw [← resultant_map_map, ← derivative_map, univ_map_ev]
  have h1 : x.charpoly.natDegree = n := by simpa using charpoly_natDegree_eq_dim x
  rw [natDegree_derivative, h1]

end LateralTheory.DivDb.SepPolyProof

namespace LateralTheory.DivDb
open LateralTheory.DivDb.SepPolyProof in
theorem SepPoly_of : SepPoly := by
  intro C _ _ n
  refine ⟨disc C n, fun x => ?_⟩
  rw [ev_disc, Ne, resultant_eq_zero_iff]
  have h0 : x.charpoly ≠ 0 := (charpoly_monic x).ne_zero
  simp only [ne_eq, h0, not_false_eq_true, true_or, true_and, not_not]
  rfl
end LateralTheory.DivDb
