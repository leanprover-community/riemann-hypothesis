module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundleDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBall
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

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.BallFinite

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_rep (P : Pair p) (a c : ℤ) : ∃ M : HermLB p, P.Rep a c M := by
  obtain ⟨hL, hA, -⟩ := _root_.GlobalTheory.VolBr.Pair.rep_base k X p P
  have h1 : ∃ M : HermLB p, P.Rep a 0 M := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
    · have := _root_.GlobalTheory.VolBr.Pair.rep_pow k X p P 1 0 P.L n hL
      rw [mul_one, mul_zero] at this
      exact ⟨_, this⟩
    · have := _root_.GlobalTheory.VolBr.Pair.rep_dual k X p P _ _ _ (_root_.GlobalTheory.VolBr.Pair.rep_pow k X p P 1 0 P.L n hL)
      rw [mul_one, mul_zero, neg_zero] at this
      exact ⟨_, this⟩
  have h2 : ∃ M : HermLB p, P.Rep 0 c M := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · have := _root_.GlobalTheory.VolBr.Pair.rep_pow k X p P 0 1 P.A n hA
      rw [mul_one, mul_zero] at this
      exact ⟨_, this⟩
    · have := _root_.GlobalTheory.VolBr.Pair.rep_dual k X p P _ _ _ (_root_.GlobalTheory.VolBr.Pair.rep_pow k X p P 0 1 P.A n hA)
      rw [mul_one, mul_zero, neg_zero] at this
      exact ⟨_, this⟩
  obtain ⟨M₁, h₁⟩ := h1
  obtain ⟨M₂, h₂⟩ := h2
  have := _root_.GlobalTheory.VolBr.Pair.rep_tens k X p P _ _ _ _ M₁ M₂ h₁ h₂
  rw [add_zero, zero_add] at this
  exact ⟨_, this⟩

alias nu_nonneg := _root_.GlobalTheory.VolBr.SmallBall.nu_nonneg

theorem smallSec_tens_shift (N M : HermLB p) (t : ℝ) :
    ((N.tens M).shift (fun _ => t) fun _ => rfl).smallSec ⊆ (N.tens (M.shift (fun _ => t) fun _ => rfl)).smallSec :=
  fun u hu σ y => by
    refine le_of_eq_of_le ?_ (hu σ y)
    simp only [Weight.nsq, HermLB.tens, HermLB.shift, Weight.tens, Weight.addFn]
    congr 2
    ring

theorem bl_finite : GlobalTheory.Published.ArithHilbertSamuel → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t →
    ∀ (a c : ℤ) (R : ℝ), GlobalTheory.Published.ArCalc → (P.Bl a c R).Finite := by
  intro hHS k _ X _ p D hX P b s t hG a c R hC
  obtain ⟨M, hM⟩ := exists_rep P a c
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit (fun _ => P.A)).1
  have hSI := ((hC.arIso k X p D hX).2 Unit (fun _ => P.A) Φ hΦ).1 ()
  obtain ⟨m, hm⟩ := ((hHS k X p D hX P.A (M.shift (fun _ => R) fun _ => rfl) _ hG.nef hSI).1).exists
  have hA := (_root_.GlobalTheory.VolBr.Pair.rep_base k X p P).2.1
  have hAm := _root_.GlobalTheory.VolBr.Pair.rep_pow k X p P 0 1 P.A m hA
  have hT := _root_.GlobalTheory.VolBr.Pair.rep_tens k X p P _ _ _ _ _ _ hAm hM
  have hsm : (((P.A.pow m).tens M).shift (fun _ => R) fun _ => rfl).smallSec.Finite :=
    hm.subset (smallSec_tens_shift _ _ _)
  have hB : (P.Bl (m * 0 + a) (m * 1 + c) (Real.exp R)).Finite := by
    have e := (_root_.GlobalTheory.VolBr.SmallBall.main k X p P _ _ _ hT R 0).2.2
    rw [← Set.encard_lt_top_iff, ← e]
    exact hsm.encard_lt_top
  have hs := hG.s_mem
  obtain ⟨hsH, hsn⟩ := _root_.GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P 0 1 s hs.1 m
  refine (hB.preimage (f := fun f => s ^ m * f) (mul_right_injective₀ (pow_ne_zero m hG.s_ne)).injOn).subset ?_
  intro f hf
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ (s ^ m) f hsH hf.1
  refine ⟨h1, fun σ y => ?_⟩
  rw [h2, hsn]
  have n1 : P.nu 0 1 σ y s ≤ 1 := hs.2 σ y
  calc _ ≤ 1 * P.nu a c σ y f :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (nu_nonneg P 0 1 σ y s) n1) (nu_nonneg P a c σ y f)
    _ ≤ Real.exp R := by rw [one_mul]; exact (hf.2 σ y).trans (by linarith [Real.add_one_le_exp R])

end GlobalTheory.VolBr.BallFinite
