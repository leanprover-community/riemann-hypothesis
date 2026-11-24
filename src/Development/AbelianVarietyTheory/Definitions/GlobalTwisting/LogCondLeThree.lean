module

public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.GlobalTheoryTheory NumberField

def NormOne (d M p : ℕ) : Prop := ∃ π : ℤ × ℤ, π.1 ^ 2 + (d : ℤ) * π.2 ^ 2 = 4 * (p : ℤ) ∧ Arith.CongOne M π

def ModRow (s : Scale) (N d : ℕ) : Prop :=
  d.Prime ∧ d % 4 = 3 ∧ 100 ≤ d ∧ 0 < N ∧ d ∣ N ∧ Real.log N ≤ 3 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2

theorem modRow_host {s : Scale} {R : Ranks} (H : Host R)
    (h : Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 3 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) : ModRow s H.condN H.d := by
  have hd : H.d % 16 = 7 := H.hyp.2.2.2.1
  have h1 := H.qd_big.2
  have h2 := R.rank_add_five_le
  have h3 := R.m_add_three_le_k
  have h4 := R.two_le_m
  have hr : 6 ≤ R.r := by unfold Ranks.r; omega
  have ht : 11 ≤ R.t := by omega
  have h5 : 4 * 11 * 6 ≤ 4 * R.t * R.r := by gcongr
  refine ⟨H.hyp.2.1, by omega, by omega, H.condN_pos, Dvd.intro_left _ rfl, ?_⟩
  simpa [Formalism.HC.HostRaw.condN] using h

theorem HostVal.log_cond_le_three {s : Scale} {C8 : ℝ} {R : Ranks} {H : Host R} (h : HostVal s C8 H) :
    Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 3 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
  have h0 : 0 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _) (sq_nonneg _)
  have := h.log_cond_le
  nlinarith

theorem HostVal.modRow {s : Scale} {C8 : ℝ} {R : Ranks} {H : Host R} (h : HostVal s C8 H) : ModRow s H.condN H.d :=
  modRow_host H h.log_cond_le_three

def QDChoice : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ C5 x0 : ℝ, 0 < C5 ∧ ∀ x ≥ x0, ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ 2 * x ^ (2 + 8 * eps) →
    ∃ q d : ℕ, Rowq x eps n q d ∧ QDq x eps C5 q d ∧ Boxq x eps q d


open Classical in
def NormPrimes : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (N d : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R →
    ModRow s N d →
    (((R.k : ℝ) * s.b) ^ 8) ^ ((9 : ℝ) / 10) ≤ (((Finset.range (⌊2 * ((R.k : ℝ) * s.b) ^ 8⌋₊ + 1)).filter (fun g : ℕ =>
      g.Prime ∧ ((R.k : ℝ) * s.b) ^ 8 ≤ (g : ℝ) ∧ NormOne d N g)).card : ℝ)

def LevelPrime : Prop :=
  ∀ eps c : ℝ, 0 < eps → eps < 1 / 52 → 0 < c → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (N d g0 g1 : ℕ) (Ts : ℝ), s.eps = eps →
    x0 ≤ s.x → RankVal s R → ModRow s N d → 1 ≤ g0 → 1 ≤ g1 → (g0 : ℝ) ≤ s.b ^ 9 → (g1 : ℝ) ≤ s.b ^ 9 → 0 < Ts →
    c * R.m * s.L ≤ Real.log Ts →
    ∃ T : ℕ, T.Prime ∧ Ts ≤ (T : ℝ) ∧ (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * Ts ∧ NormOne d (N * (g0 * g1) ^ 2) T

def SmallPrimeOne : Prop := ∃ A : ℝ, 1 ≤ A ∧ ∀ M : ℕ, 2 ≤ M → ∃ p : ℕ, p.Prime ∧ p % M = 1 ∧ (p : ℝ) ≤ (M : ℝ) ^ A


end GlobalTheory.EX

end
