module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N

namespace UpperTheory.GalS


open Classical in
def thr {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) : ℕ :=
  if ∃ p : ℕ, p.Prime ∧ w ∈ placesOver E p ∧ (placesOver E p).ncard = Module.finrank ℚ E ∧ (n = 1 ∨ 16 * n ^ 2 < p) then 2 else 1

theorem thr_pos {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} : 0 < thr w n := by
  unfold thr
  split_ifs <;> norm_num

theorem thr_split {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {p : ℕ} (hp : p.Prime)
    (hw : w ∈ placesOver E p) (hs : (placesOver E p).ncard = Module.finrank ℚ E) {n : ℕ} (hn : 16 * n ^ 2 < p) :
    thr w n = 2 := if_pos ⟨p, hp, hw, hs, Or.inr hn⟩

theorem thr_anti {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {m n : ℕ} (h : m ≤ n) : thr w n ≤ thr w m := by
  unfold thr
  by_cases hm : ∃ p : ℕ, p.Prime ∧ w ∈ placesOver E p ∧ (placesOver E p).ncard = Module.finrank ℚ E ∧ (m = 1 ∨ 16 * m ^ 2 < p)
  · rw [if_pos hm]
    split_ifs <;> norm_num
  · rw [if_neg hm]
    have hn : ¬ ∃ p : ℕ, p.Prime ∧ w ∈ placesOver E p ∧ (placesOver E p).ncard = Module.finrank ℚ E ∧ (n = 1 ∨ 16 * n ^ 2 < p) := by
      rintro ⟨p, hp, hw, hs, hc⟩
      apply hm
      refine ⟨p, hp, hw, hs, ?_⟩
      rcases hc with rfl | hc
      · interval_cases m
        · right
          simpa using hp.pos
        · left
          rfl
      · right
        have : m ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left h 2
        omega
    rw [if_neg hn]

end UpperTheory.GalS
