module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Order.Interval.Finset.Box
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

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem map_pw_eq_pw (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] [CharP F l] [PerfectRing F l]
    (ι : Fl l →+* F) (k : ℤ) (x : Fl l) : ι (GlobalTheory.PSer.pw k x) = GlobalTheory.PMonE.pw l k (ι x) := by
  have hsymm : ∀ y : Fl l, ι ((frobeniusEquiv (Fl l) l).symm y) = (frobeniusEquiv F l).symm (ι y) :=
    fun y => RingHom.map_frobeniusEquiv_symm l ι y
  have hit : ∀ (n : ℕ) (y : Fl l), ι (((frobeniusEquiv (Fl l) l).symm)^[n] y) = ((frobeniusEquiv F l).symm)^[n] (ι y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hsymm, ih]
  have hpos : ∀ (n : ℕ) (y : Fl l), ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ n) y = y ^ l ^ n := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ']
      change (frobeniusEquiv (Fl l) l) (((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ n) y) = _
      rw [ih, frobeniusEquiv_apply, frobenius_def, ← pow_mul, pow_succ]
  have hneg : ∀ (n : ℕ) (y : Fl l), ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-(n : ℤ))) y
      = ((frobeniusEquiv (Fl l) l).symm)^[n] y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [Nat.cast_succ, neg_add, zpow_add, Function.iterate_succ_apply]
      change ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-(n : ℤ)))
        (((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-1 : ℤ)) y) = _
      rw [ih, zpow_neg_one]
      rfl
  cases k with
  | ofNat n =>
    simp only [GlobalTheory.PSer.pw, GlobalTheory.PMonE.pw, Int.ofNat_eq_coe, zpow_natCast, hpos, map_pow]
    simp
  | negSucc n =>
    have hk : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := rfl
    simp only [GlobalTheory.PSer.pw, GlobalTheory.PMonE.pw]
    rw [if_neg (by omega), hk, hneg, hit]
    congr

end GlobalTheory.PSer
