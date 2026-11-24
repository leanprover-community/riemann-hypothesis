module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Ideal.Defs
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem pow_mul_sub_mem_of_roots_mod_pow :
    ∀ (R : Type) [CommRing R] (I : Ideal R) (p : Polynomial R) (x y b lam : R) (n : ℕ),
      p.eval x ∈ I ^ n → p.eval y ∈ I ^ n → x - y ∈ I →
        b * (Polynomial.derivative p).eval x - lam ∈ I → lam ^ n * (x - y) ∈ I ^ n := by
  intro R _ I p x y b lam n hx hy hxy hb
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion p x (y - x)
  have hy' : x + (y - x) = y := by ring
  rw [hy'] at hk
  obtain ⟨d, hdd⟩ : ∃ d, d = y - x := ⟨_, rfl⟩
  rw [← hdd] at hk
  have hd : d ∈ I := by
    have e : d = -(x - y) := by rw [hdd]; ring
    rw [e]; exact I.neg_mem hxy
  obtain ⟨h, hh⟩ : ∃ h, h = (Polynomial.derivative p).eval x + k * d := ⟨_, rfl⟩
  have hdh : d * h ∈ I ^ n := by
    have e : d * h = p.eval y - p.eval x := by rw [hk, hh]; ring
    rw [e]; exact sub_mem hy hx
  obtain ⟨j, hjj⟩ : ∃ j, j = b * h - lam := ⟨_, rfl⟩
  have hj : j ∈ I := by
    have e : j = (b * (Polynomial.derivative p).eval x - lam) + b * k * d := by
      rw [hjj, hh]; ring
    rw [e]; exact add_mem hb (I.mul_mem_left _ hd)
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow lam (-j) n
  have e : lam ^ n * (x - y) = -(b * q * (d * h)) - (-j) ^ n * d := by
    have e1 : lam ^ n = (lam - -j) * q + (-j) ^ n := by rw [← hq]; ring
    have e2 : lam - -j = b * h := by rw [hjj]; ring
    have e3 : x - y = -d := by rw [hdd]; ring
    rw [e1, e2, e3]; ring
  rw [e]
  exact sub_mem (neg_mem (Ideal.mul_mem_left _ _ hdh))
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (neg_mem hj) n))

end GlobalTheory
