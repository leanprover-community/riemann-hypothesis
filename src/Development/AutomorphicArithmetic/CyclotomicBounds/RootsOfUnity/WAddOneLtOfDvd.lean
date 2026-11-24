module

public import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.NuRecord
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.BasicNotions

namespace UpperTheory.Mu

variable {R : Ranks} (H : Host R)

theorem w_add_one_lt_of_dvd {p : ℕ} (hp : 1 < p) (h : H.QS * H.q * H.d ∣ p - 1) : Units.torsionOrder H.E + 1 < p := by
  have hw : Units.torsionOrder H.E ∣ H.QS := w_dvd_QS H
  have hwle : Units.torsionOrder H.E ≤ H.QS := Nat.le_of_dvd H.QS_pos hw
  have hq := H.q_prime.two_le
  have hd := H.d_prime.two_le
  have hle : H.QS * H.q * H.d ≤ p - 1 := Nat.le_of_dvd (by omega) h
  have h4 : H.QS * 4 ≤ H.QS * H.q * H.d := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have hQ := H.QS_pos
  omega

theorem w_add_one_lt {p : ℕ} (hp : 1 < p) (r : ℕ) (h : p % (r * (H.QS * H.q * H.d)) = 1) :
    Units.torsionOrder H.E + 1 < p := by
  apply w_add_one_lt_of_dvd H hp
  have h1 := Nat.dvd_sub_mod (n := r * (H.QS * H.q * H.d)) p
  rw [h] at h1
  exact dvd_trans (Dvd.intro_left r rfl) h1

end UpperTheory.Mu
