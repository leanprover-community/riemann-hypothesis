module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.PrimesInAP
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.Published

def primesInProgression (a q : ℕ) : Set ℕ := {p | p.Prime ∧ p ≡ a [MOD q]}

noncomputable def leastPrimeMod (a q : ℕ) : ℕ := sInf (primesInProgression a q)

def Linnik : Prop :=
  ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ a q : ℕ, 1 ≤ a → 1 ≤ q → a.Coprime q →
    (leastPrimeMod a q : ℝ) ≤ C * (q : ℝ) ^ L

private theorem exists_prime_modEq_of_coprime (a q : ℕ) (hq : 1 ≤ q) (h : a.Coprime q) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] := by
  haveI : NeZero q := ⟨by omega⟩
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 h
  obtain ⟨p, -, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu 0
  exact ⟨p, hp, (ZMod.natCast_eq_natCast_iff p a q).1 hpa⟩

theorem _root_.GlobalTheory.Published.linnik_iff_exists_prime : _root_.GlobalTheory.Published.Linnik ↔
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ a q : ℕ, 1 ≤ a → 1 ≤ q → a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ C * (q : ℝ) ^ L := by
  constructor
  · rintro ⟨C, L, hC, hL, hb⟩
    refine ⟨C, L, hC, hL, fun a q ha hq h => ?_⟩
    have hne : (_root_.GlobalTheory.Published.primesInProgression a q).Nonempty :=
      exists_prime_modEq_of_coprime a q hq h
    have hmem := Nat.sInf_mem hne
    exact ⟨_, hmem.1, hmem.2, hb a q ha hq h⟩
  · rintro ⟨C, L, hC, hL, hb⟩
    refine ⟨C, L, hC, hL, fun a q ha hq h => ?_⟩
    obtain ⟨p, hp, hpa, hpC⟩ := hb a q ha hq h
    have hle : _root_.GlobalTheory.Published.leastPrimeMod a q ≤ p := Nat.sInf_le ⟨hp, hpa⟩
    exact le_trans (by exact_mod_cast hle) hpC

end GlobalTheory.Published
