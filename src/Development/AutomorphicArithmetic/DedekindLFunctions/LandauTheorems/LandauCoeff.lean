module

public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.IteratedDerivLaplace
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

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_coeff {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) (k : ℕ) {s : ℂ} (hs : 2 < s.re) :
    (-1) ^ k * iteratedDeriv k Φ s / (k.factorial : ℂ) =
      ∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-s * u) / (k.factorial : ℂ) := by
  obtain ⟨C, hC⟩ := hP.growth
  have hev : Φ =ᶠ[𝓝 s] (fun z => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u)) := by
    have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact hP.laplace z hz
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_laplace g hP.meas C hC k s hs, ← integral_const_mul,
    ← integral_div]
  congr 1
  funext u
  push_cast
  have e : ((-1 : ℂ)) ^ k * (-(u : ℂ)) ^ k = (u : ℂ) ^ k := by
    rw [← mul_pow]
    ring
  calc (-1 : ℂ) ^ k * ((g u : ℂ) * (-(u : ℂ)) ^ k * cexp (-s * u)) / (k.factorial : ℂ)
      = (g u : ℂ) * ((-1 : ℂ) ^ k * (-(u : ℂ)) ^ k) * cexp (-s * u) / (k.factorial : ℂ) := by ring
    _ = (g u : ℂ) * (u : ℂ) ^ k * cexp (-s * u) / (k.factorial : ℂ) := by rw [e]

end Deduction

end
