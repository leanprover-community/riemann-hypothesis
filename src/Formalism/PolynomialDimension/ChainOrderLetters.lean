module

public import Formalism.MahlerMeasure.StatementTM
public import Formalism.PolynomialDimension.DigitSumValuationBound
public import Formalism.MahlerMeasure.StatementT
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

@[expose] public section

namespace Formalism.CountingSumsFrames

open Formalism.GM Formalism.GM.M MvPolynomial Finset

def degreeAtPosition {N : ℕ} (LL : Letters N) (j : ℕ) : ℕ := if h : j < N then LL.deg ⟨j, h⟩ else 0

def ChainOrderLetters {s : ℕ} (LL : Letters (2 * s + 1)) : Prop := ∀ x, LL.vec x = decide ((x : ℕ) % 2 = 0)

def ConditionShape (s : ℕ) (T : TieData) : Prop := ∀ k, T.J k = 2 * s + 1 ∨ ∃ i, T.J k = T.pos i + 1

def SizeHypothesis {N : ℕ} (LLt : Letters N) (T : TieData) (r : ℕ) (a : ℝ) (Yl : Fin T.t → ℕ) : Prop :=
  (LLt.total : ℝ) ≤ 8 * a + r ∧
  ∀ i, ((degreeAtPosition LLt (T.pos i) + degreeAtPosition LLt (T.pos i + 1) + r + T.z i + 1 : ℕ) : ℝ) ≤ 8 * a + r ∧
    (Yl i : ℝ) ≤ 8 * a + r ∧ ((2 * T.S LLt i + 1 : ℕ) : ℝ) ≤ 8 * a + r

def TheoremMV7 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (s r : ℕ) [NeZero r] (LL : Letters (2 * s + 1)) (T : TieData)
    (a E : ℝ) (Yl n₀ dd : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → ChainOrderLetters LL → ConditionShape s T →
    1 ≤ a → 1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i) →
    SizeHypothesis (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) T r a Yl →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr)
          ⌊(T.t : ℝ) * (E + kapSeg p a r s) + kapSeg p a r s⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      ∑ i, epsSeg (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) (Yl i) (kapSeg p a r s)
          (lgSeg p a r) E *
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)

def TheoremMV7Of : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (s r : ℕ) [NeZero r] (LL : Letters (2 * s + 1)) (T : TieData)
    (a E : ℝ) (Yl n₀ dd : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → ChainOrderLetters LL → ConditionShape s T →
    1 ≤ a → 1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i) →
    SizeHypothesis (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) T r a Yl →
    (∀ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
      HypP p (LL.setTies T n) ρ ⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊ ∧
      HypW p (r := r) (LL.setTies T n) ⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊ ∧
      ∀ i, GramDeterminantGradedHypothesis p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ
        (((s : ℝ) + 4) * ((r : ℝ) ^ 2 * lgSeg p a r))) →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr)
          ⌊(T.t : ℝ) * (E + kapSeg p a r s) + kapSeg p a r s⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      ∑ i, epsSeg (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) (Yl i) (kapSeg p a r s)
          (lgSeg p a r) E *
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)

end Formalism.CountingSumsFrames
