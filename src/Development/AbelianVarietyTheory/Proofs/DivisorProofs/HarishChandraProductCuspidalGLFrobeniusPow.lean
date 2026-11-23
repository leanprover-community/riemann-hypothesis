module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldFrobeniusPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLFieldAutomorphismStatement
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

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem hc_congr_deg {F : Type} [Field F] (a b b' : ℕ) (α : GL (Fin a) F → ℂ)
    (β : (m : ℕ) → GL (Fin m) F → ℂ) (n : ℕ) (h : b = b') :
    hc a b α (β b) n = hc a b' α (β b') n := by
  subst h; rfl

theorem deg_map_mul (L : List (ℕ × ℕ)) (c : ℕ) :
    deg (L.map fun p => (p.1, p.2 * c)) = deg L := by
  unfold deg
  rw [List.map_map]
  rfl

theorem J_gal : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ),
    (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (L : List (ℕ × ℕ)) (n : ℕ) (x : GL (Fin n) F),
    J θ L n (gal (t : F →+* F) n x) = J θ (L.map fun p => (p.1, p.2 * ringChar F ^ j)) n x := by
  intro F _ _ θ t j ht L
  induction L with
  | nil => intro n x; rfl
  | cons p L ih =>
    intro n x
    rw [List.map_cons, J_cons, J_cons, GlobalTheory.T.harishChandraInductionGL_fieldAutomorphism F t]
    have h1 : (fun y => cusp θ p.1 p.2 (gal (t : F →+* F) p.1 y)) = cusp θ p.1 (p.2 * ringChar F ^ j) := by
      funext y; exact GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow F θ t j ht p.1 p.2 y
    have h2 : (fun y => J θ L (deg L) (gal (t : F →+* F) (deg L) y)) =
        J θ (L.map fun p => (p.1, p.2 * ringChar F ^ j)) (deg L) := by
      funext y; exact ih (deg L) y
    rw [h1, h2]
    exact congrFun (hc_congr_deg p.1 (deg L) _ _ (J θ (L.map fun p => (p.1, p.2 * ringChar F ^ j))) n
      (deg_map_mul L _).symm) x

end GlobalTheory.Shin
