module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem pos_iff_smul_toV (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (g : grp G β)
    (z : Fin G.n → ℂ) (c : ℂ) : c ≠ 0 →
    (0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ↔ 0 < (star (c • ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)) ⬝ᵥ
      (herm G v β *ᵥ (c • ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)))).re) := by
  intro hc
  set M : Matrix (Fin G.n) (Fin G.n) ℂ := (toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) with hM
  set H := herm G v β
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G v β g
  have hs : (0 : ℚ) < (((g : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := g.2.2
  set s : ℚ := (((g : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)
  have key : star (c • (M *ᵥ z)) ⬝ᵥ (H *ᵥ (c • (M *ᵥ z))) =
      ((Complex.normSq c * s : ℝ) : ℂ) * (star z ⬝ᵥ (H *ᵥ z)) := by
    have e1 : star (M *ᵥ z) ⬝ᵥ (H *ᵥ (M *ᵥ z)) = star z ⬝ᵥ ((Mᴴ * H * M) *ᵥ z) := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, e1, hsim, Matrix.smul_mulVec,
      dotProduct_smul]
    simp only [smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    simp [mul_comm]
  rw [key, Complex.re_ofReal_mul]
  have hpos : 0 < Complex.normSq c * (s : ℝ) :=
    mul_pos (Complex.normSq_pos.2 hc) (by exact_mod_cast hs)
  exact (mul_pos_iff_of_pos_left hpos).symm

end GlobalTheory.LKCx
