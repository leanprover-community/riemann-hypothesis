module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem rankOne_of_steps : Descent → CellInv → ChainSum → RankOne := by
  intro hD hI hC G A _ _ K N N' ι c Q d h t t' hbi hfin hle hι hsplit hK hnorm hc hQ hidx hex hconj hdc
  obtain ⟨-, e1⟩ := hD G A K N N' ι h t hfin hle hι hsplit hK hnorm
  obtain ⟨f2, e2⟩ := hD G A K N N' ι h t' hfin hle hι hsplit hK hnorm
  have hcomm : ∀ a, t' * ι a = ι ((c ^ d) a) * t' := fun a => by
    rw [← hconj a]; group
  have key := hC A (K.comap ι) c Q d (fun v => cellSum K N' h (t' * ι v)) hc hQ hidx hex
    (by
      intro v hv a
      have := hI G K N' h (t' * ι a) (ι ((c ^ d) v)) 1 hbi hv K.one_mem (by simp) (by simp)
      show cellSum K N' h (t' * ι (v * a)) = cellSum K N' h (t' * ι a)
      rw [← this, map_mul, ← mul_assoc, hcomm v, mul_one, mul_assoc])
    (by
      intro u hu a
      have := hI G K N' h (t' * ι a) 1 (ι u) hbi K.one_mem hu (hnorm u)
        (fun w hw => by simpa using hnorm u⁻¹ w hw)
      show cellSum K N' h (t' * ι (a * u)) = cellSum K N' h (t' * ι a)
      rw [← this, map_mul, one_mul, mul_assoc])
    f2
  rw [e1, e2, ← key]
  refine finsum_congr fun y => ?_
  obtain ⟨k₁, hk₁, k₂, hk₂, n1, n2, e⟩ := hdc y.out
  have hcc : (c ^ d) ((c ^ (-d)) y.out) = y.out := by
    rw [← MulAut.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, MulAut.one_apply]
  rw [hcomm, map_inv, hcc, map_inv, e, hI G K N' h _ k₁ k₂ hbi hk₁ hk₂ n1 n2]

end GlobalTheory.SatakeWeyl
