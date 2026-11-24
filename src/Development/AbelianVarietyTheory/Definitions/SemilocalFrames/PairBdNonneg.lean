module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
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
import Mathlib.Tactic.Lemma
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
open NumberField GlobalTheory.DegCnt
namespace GlobalTheory.DegAsm

def pairBd (K : Type) [Field K] [NumberField K] (k g j T x x' : ℕ) : ℝ :=
  let f : ℕ := Formalism.HermitianLatticesTheory.fDeg K
  let Mb : ℝ := (20 * (f : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * (f : ℝ) * (6 + cf K))
  let D₀ : ℝ := (T : ℝ) ^ (2 * f)
  let Y : ℝ := (x : ℝ) * x' * D₀ ^ 2
  ((x : ℝ) * x') ^ ((k : ℝ) / 2) * Y ^ (6 * (j : ℝ) + 10 + 4 * cf K) *
    (1 + Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ f *
        (∑ s ∈ Finset.Ico 1 k, ((32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * Y ^ 7) ^ s) +
      ((2 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * D₀ * x * x') ^ k)

open NumberField in
private lemma vInv_nonneg' (K : Type) [Field K] [NumberField K] :
    0 ≤ _root_.Formalism.HermitianLatticesTheory.vInv K := by
  unfold _root_.Formalism.HermitianLatticesTheory.vInv
  positivity


open NumberField in
theorem _root_.GlobalTheory.DegAsm.pairBd_nonneg (K : Type) [Field K] [NumberField K]
    (k g j T x x' : ℕ) : 0 ≤ _root_.GlobalTheory.DegAsm.pairBd K k g j T x x' := by
  have hv := vInv_nonneg' K
  unfold _root_.GlobalTheory.DegAsm.pairBd
  dsimp only
  have hMb : 0 ≤ (20 * ((_root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) * (2 * _root_.Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^
      (2 * ((_root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) * (6 + _root_.GlobalTheory.DegCnt.cf K)) :=
    Real.rpow_nonneg (by positivity) _
  have hY : 0 ≤ (x : ℝ) * x' * ((T : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K)) ^ 2 := by positivity
  have hxx : 0 ≤ (x : ℝ) * x' := by positivity
  refine mul_nonneg (mul_nonneg (Real.rpow_nonneg hxx _) (Real.rpow_nonneg hY _)) ?_
  refine add_nonneg (add_nonneg zero_le_one (mul_nonneg (mul_nonneg hMb (by positivity)) ?_))
    (by positivity)
  exact Finset.sum_nonneg fun s _ => by positivity

end GlobalTheory.DegAsm
