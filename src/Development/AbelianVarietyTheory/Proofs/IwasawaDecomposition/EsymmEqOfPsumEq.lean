module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
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
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.EsymmOfPowerSums

open MvPolynomial

theorem esymm_eq_of_psum_eq {d : ℕ} (a b : Fin d → ℂ)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ d → ∑ i : Fin d, a i ^ k = ∑ i : Fin d, b i ^ k) :
    ∀ k ≤ d, (MvPolynomial.aeval a : MvPolynomial (Fin d) ℂ → ℂ) (MvPolynomial.esymm (Fin d) ℂ k)
      = (MvPolynomial.aeval b : MvPolynomial (Fin d) ℂ → ℂ) (MvPolynomial.esymm (Fin d) ℂ k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp
    have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    apply mul_left_cancel₀ hk0
    have key := MvPolynomial.mul_esymm_eq_sum (Fin d) ℂ k
    have ha := congrArg (MvPolynomial.aeval a) key
    have hb := congrArg (MvPolynomial.aeval b) key

    simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at ha hb
    rw [ha, hb]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [ih p.1 h2 (by omega)]
    congr 1
    have := h p.2 (by omega) (by omega)
    simpa [MvPolynomial.psum] using this

end GlobalTheory.EsymmOfPowerSums
