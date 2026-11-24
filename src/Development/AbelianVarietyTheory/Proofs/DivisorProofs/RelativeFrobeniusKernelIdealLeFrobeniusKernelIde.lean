module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory.PDiv

open GlobalTheory.PDivGroup

theorem pow_sub_counit_mem_frobKerIdeal {p : ℕ} [Fact p.Prime] {R H : Type} [CommRing R]
    [CommRing H] [Bialgebra R H] (h : (p : R) = 0) (a : H) :
    a ^ p - algebraMap R H (counit (R := R) (a ^ p)) ∈ frobKerIdeal p R H := by
  have h0 := natCast_eq_zero_of_algebra h H
  have e : a ^ p - algebraMap R H (counit (R := R) (a ^ p)) =
      (a - algebraMap R H (counit (R := R) a)) ^ p := by
    rw [← frobRing_apply h0 (a - _), map_sub, frobRing_apply, frobRing_apply, counit_pow, map_pow]
  rw [e]
  exact pow_mem_frobKerIdeal (by simp [RingHom.mem_ker])

theorem kerIdeal_relFrob_le_frobKerIdeal (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) :
    kerIdeal ((relFrob h G).app n) ≤ frobKerIdeal p R (G.A n) := by
  have key : ∀ x : (frobTwist h G).A n, (relFrob h G).app n x -
      algebraMap R (G.A n) (counit (R := R) ((relFrob h G).app n x)) ∈
        frobKerIdeal p R (G.A n) := by
    intro x
    induction x using frobTwist_induction h n with
    | h0 => simp
    | h1 r a =>
      rw [map_smul, relFrob_app_frobProj, map_smul, smul_eq_mul, map_mul, Algebra.smul_def,
        ← mul_sub]
      exact Ideal.mul_mem_left _ _ (pow_sub_counit_mem_frobKerIdeal h a)
    | h2 x y hx hy =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), add_sub_add_comm]
      exact add_mem hx hy
  refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
  have hx' : counit (R := R) x = 0 := hx
  have := key x
  rw [CoalgHomClass.counit_comp_apply, hx', map_zero, sub_zero] at this
  exact this

end GlobalTheory.PDiv
