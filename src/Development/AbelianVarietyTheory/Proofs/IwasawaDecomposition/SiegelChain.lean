module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.SiegelChain

theorem siegel_chain : ∀ {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ}, GlobalTheory.RedTh.IsSiegel d u →
    ∀ (m : ℕ) (i j : Fin n), (↑j : ℕ) = (↑i : ℕ) + m → d i ≤ (4 : ℝ) ^ m * d j := by
  intro n d u h m
  induction m with
  | zero =>
    intro i j hij
    have : i = j := Fin.ext (by simpa using hij.symm)
    subst this
    simp
  | succ m ih =>
    intro i j hij
    have hk : (i : ℕ) + m < n := by have := j.isLt; omega
    let k : Fin n := ⟨(i : ℕ) + m, hk⟩
    have h1 : d i ≤ 4 ^ m * d k := ih i k rfl
    have h2 : d k ≤ 4 * d j := h.step k j (by simp [k]; omega)
    have h4 : (0 : ℝ) ≤ 4 ^ m := by positivity
    calc d i ≤ 4 ^ m * d k := h1
      _ ≤ 4 ^ m * (4 * d j) := mul_le_mul_of_nonneg_left h2 h4
      _ = 4 ^ (m + 1) * d j := by ring

end GlobalTheory.SiegelChain
