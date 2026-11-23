module

public import Formalism.PeriodIntegrals.JetsPhW
public import Mathlib.Analysis.Normed.Field.Instances
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.JetsPhW.Low

open PI.JetsPhW

variable {p : ℕ} [Fact p.Prime]

theorem coeff_truncatedExp_of_degree_eq_one {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) {e : σ →₀ ℕ}
    (hd : Finsupp.degree e = 1) :
    MvPowerSeries.coeff e (expMv F) = MvPowerSeries.coeff e F := by
  classical
  have he : e ≠ 0 := by
    rintro rfl
    simp at hd
  have h1 : (e.sum fun _ k => k) = 1 := by
    rw [← hd]
    rfl
  change (∑ n ∈ Finset.range ((e.sum fun _ k => k) + 1),
    MvPowerSeries.coeff e (F ^ n) / (n.factorial : ℂ_[p])) = _
  rw [h1, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, MvPowerSeries.coeff_one, if_neg he]
  simp

theorem norm_two (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ‖((2 : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp)
  have e : (2 : ℂ_[p]) = ((algebraMap ℚ_[p] (PadicAlgCl p) ((2 : ℕ) : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) := by
    rw [map_natCast, PadicComplex.coe_natCast]
    norm_num
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends, h]

end PI.JetsPhW.Low
