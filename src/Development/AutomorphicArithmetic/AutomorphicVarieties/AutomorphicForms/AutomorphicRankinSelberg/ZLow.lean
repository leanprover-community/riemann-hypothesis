module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

theorem UpperTheory.V.Af.Rs.zLow :
    UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.KerLow → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZLow := by
  intro hB hL hW L _ s hs z hz
  have hs' : s ∈ Set.Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨-, h0, -, -, -, hub⟩ := hB s hs'
  have hsum : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) := hW.1 (2 * s) (by linarith [hs.1])
  have hk : Summable fun x : Fin 2 → ℤ => UpperTheory.V.Af.Rs.ker s x z :=
    Summable.of_nonneg_of_le (fun x => h0 x z) (fun x => hub x z hz) (hsum.mul_left _)
  have hv : ∀ v ∈ (Finset.univ : Finset (Fin 2 → ZMod L)), Summable fun x : Fin 2 → ℤ =>
      if UpperTheory.V.Af.Rs.cls L x = v then UpperTheory.V.Af.Rs.ker s x z else 0 := by
    intro v _
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hk
    · split_ifs
      · exact h0 x z
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact h0 x z
  have he : ∑ v, UpperTheory.V.Af.Rs.Zc L v s z = ∑' x : Fin 2 → ℤ, UpperTheory.V.Af.Rs.ker s x z := by
    unfold UpperTheory.V.Af.Rs.Zc
    rw [← Summable.tsum_finsetSum hv]
    refine tsum_congr fun x => ?_
    simp
  rw [he, UpperTheory.V.Af.Rs.Wsum, ← tsum_mul_left]
  exact (hsum.mul_left _).tsum_le_tsum (fun x => hL s hs' x z hz) hk
