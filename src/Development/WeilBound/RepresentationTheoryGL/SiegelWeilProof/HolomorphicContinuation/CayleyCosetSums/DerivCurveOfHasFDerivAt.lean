module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocTauAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MatInv
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.MI

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Z1 (Z : M2 n) : M2 n := (1 / 2 : ℂ) • (Z + sig Z)

def Z2 (Z : M2 n) : M2 n := (1 / (2 * Complex.I)) • (Z - sig Z)

theorem curve_zero (x Y : M2 n) : x * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = x := by
  simp

theorem rC_eq (Z : M2 n) (F : M2 n → ℂ) (x : M2 n) :
    rC Z F x = deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Z1 Z))) 0 +
      Complex.I * deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Z2 Z))) 0 := rfl

theorem deriv_curve_of_hasFDerivAt {F : M2 n → ℂ} {D : M2 n →L[ℝ] ℂ} {x : M2 n} (hF : HasFDerivAt F D x) (Y : M2 n) :
    deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Y))) 0 = D (x * Y) := by
  exact (hF.comp_hasDerivAt_of_eq 0 (hasDerivAt_curve x Y) (curve_zero x Y).symm).deriv

theorem rC_of_diff {F : M2 n → ℂ} {x : M2 n} (hF : DifferentiableAt ℝ F x) (Z : M2 n) :
    rC Z F x = fderiv ℝ F x (x * Z1 Z) + Complex.I * fderiv ℝ F x (x * Z2 Z) := by
  rw [rC_eq, deriv_curve_of_hasFDerivAt hF.hasFDerivAt, deriv_curve_of_hasFDerivAt hF.hasFDerivAt]

theorem rC_congr {F F' : M2 n → ℂ} {O : Set (M2 n)} (hO : IsOpen O) {x : M2 n} (hx : x ∈ O) (h : EqOn F F' O)
    (Z : M2 n) : rC Z F x = rC Z F' x := by
  have key : ∀ Y : M2 n, deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Y))) 0 =
      deriv (fun t : ℝ => F' (x * NormedSpace.exp ((t : ℂ) • Y))) 0 := by
    intro Y
    apply Filter.EventuallyEq.deriv_eq
    have hc := (hasDerivAt_curve x Y).continuousAt
    have hO' : O ∈ 𝓝 (x * NormedSpace.exp (((0 : ℝ) : ℂ) • Y)) := by
      rw [curve_zero]
      exact hO.mem_nhds hx
    filter_upwards [hc.preimage_mem_nhds hO'] with t ht
    exact h ht
  rw [rC_eq, rC_eq, key, key]

end PositivityTheory.Rg.Sw.HSt.MI
