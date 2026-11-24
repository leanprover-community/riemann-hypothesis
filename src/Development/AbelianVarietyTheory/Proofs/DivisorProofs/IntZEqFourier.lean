module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
public import Mathlib.Analysis.Fourier.FourierTransform
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

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwo.TermDecay

def qZ (σ : ℂ) (a : ℤ) (b m : ℕ) (y t : ℝ) : ℂ :=
  ((t : ℂ) + (y : ℂ) * I) ^ (-a) * (((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ (-σ - (b : ℂ)) * (y : ℂ) ^ m

def intZ (σ : ℂ) (ν : ℝ) (a : ℤ) (b m : ℕ) (y : ℝ) : ℂ :=
  ∫ t : ℝ, qZ σ a b m y t * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

theorem term_eq_qZ (σ : ℂ) (ν : ℝ) (a b m : ℕ) (y t : ℝ) :
    GlobalTheory.HeckeTwo.TermSmooth.term σ ν a b m y t =
      qZ σ (a : ℤ) b m y t * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) := by
  unfold GlobalTheory.HeckeTwo.TermSmooth.term qZ
  rw [zpow_neg, zpow_natCast, inv_pow]

theorem intT_eq_intZ (σ : ℂ) (ν : ℝ) (a b m : ℕ) (y : ℝ) :
    GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y = intZ σ ν (a : ℤ) b m y := by
  unfold GlobalTheory.HeckeTwo.TermSmooth.intT intZ
  simp_rw [term_eq_qZ]

theorem intZ_eq_fourier (σ : ℂ) (ν : ℝ) (a : ℤ) (b m : ℕ) (y : ℝ) :
    intZ σ ν a b m y = FourierTransform.fourier (qZ σ a b m y) ν := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold intZ
  congr 1
  funext t
  rw [smul_eq_mul, mul_comm]
  congr 1
  push_cast
  ring_nf

end GlobalTheory.HeckeTwo.TermDecay
