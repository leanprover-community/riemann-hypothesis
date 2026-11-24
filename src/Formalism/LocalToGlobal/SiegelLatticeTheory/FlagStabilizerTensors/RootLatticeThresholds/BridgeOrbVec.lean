module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
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

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

section Std

variable {K : Type} [Field K] (σ : K →+* ℂ) (r : ℕ) (g : ℝ)

theorem blk_std (s o : ℕ) (hs : 1 ≤ s) (hos : o + s ≤ r + 1) :
    blkF (-Complex.I * ((g / (2 * Real.pi) : ℝ) : ℂ)) r o (o + s - 1) * (-1) ^ (r + 1 - (o + 1 + s - 1)) =
      (((g / (2 * Real.pi)) ^ Formalism.FourierDecayAlt.S6.nuBlock (r : ℤ) ((o + 1 : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) *
        Complex.I ^ (s - 1) := by
  set a : ℝ := g / (2 * Real.pi)
  set m := (r - o) + (r - (o + s - 1)) with hm
  set e := r + 1 - (o + 1 + s - 1) with he
  have hnu : Formalism.FourierDecayAlt.S6.nuBlock (r : ℤ) ((o + 1 : ℕ) : ℤ) (s : ℤ) = (m : ℤ) := by
    unfold Formalism.FourierDecayAlt.S6.nuBlock; rw [hm]; push_cast; omega
  have hme : m = 2 * e + (s - 1) := by rw [hm, he]; omega
  rw [hnu, zpow_natCast]
  unfold blkF
  rw [← hm, mul_pow, ← mul_assoc, ← mul_pow, neg_mul, one_mul, neg_neg, Complex.ofReal_pow, hme, pow_add, pow_mul,
    Complex.I_sq]
  have h1 : ((-1 : ℂ) ^ e) * ((-1 : ℂ) ^ e) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have h2 : ((-1 : ℂ) ^ e) = (-1) ^ e := rfl
  calc (-1 : ℂ) ^ e * Complex.I ^ (s - 1) * (a : ℂ) ^ (2 * e + (s - 1)) * (-1) ^ e
      = (((-1 : ℂ) ^ e) * ((-1 : ℂ) ^ e)) * ((a : ℂ) ^ (2 * e + (s - 1)) * Complex.I ^ (s - 1)) := by ring
    _ = (a : ℂ) ^ (2 * e + (s - 1)) * Complex.I ^ (s - 1) := by rw [h1, one_mul]

theorem lptOf_toStd : ∀ (L : Formalism.FourierDecayAlt.TB.Pt K) (o : ℕ), (∀ b ∈ L, 1 ≤ b.1) → o + (L.map Prod.fst).sum ≤ r + 1 →
    lptOf σ (-Complex.I * ((g / (2 * Real.pi) : ℝ) : ℂ)) r o ((Formalism.L2.SG.DataInst.signAux r (o + 1) L).map Prod.swap) =
      Formalism.FourierDecayAlt.D.toStd r g (o + 1) (Formalism.FourierDecayAlt.C.loc σ L)
  | [], _, _, _ => rfl
  | (s, t) :: rest, o, hL, ho => by
    simp only [List.map_cons, List.sum_cons] at ho
    have hs : 1 ≤ s := hL (s, t) (List.mem_cons_self)
    simp only [Formalism.L2.SG.DataInst.signAux, List.map_cons, Prod.swap_prod_mk, lptOf, Formalism.FourierDecayAlt.C.loc,
      Formalism.FourierDecayAlt.D.toStd, List.cons.injEq]
    constructor
    · rw [map_mul, map_pow, map_neg, map_one, ← mul_assoc, blk_std r g s o hs (by omega)]
    · have := lptOf_toStd rest (o + s) (fun b hb => hL b (List.mem_cons_of_mem _ hb)) (by omega)
      rw [show o + s + 1 = o + 1 + s by omega] at this
      exact this

end Std

end Formalism.L2.SG.Pf.Bridge
