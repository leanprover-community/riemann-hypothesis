module

public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.LocalRingCardinality.DataMink
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

private lemma prime_le_succ_of_dvd_minkM' {n p : ℕ} (hp : p.Prime) (h : p ∣ minkM n) : p ≤ n + 1 := by
  have h' : p ∣ ∏ q ∈ (Finset.range (n + 2)).filter Nat.Prime, q ^ Formalism.HermitianLatticeCounting.S6.minkowskiExp n q := h
  rcases (Prime.dvd_finsetProd_iff hp.prime _).1 h' with ⟨q, hq, hdvd⟩
  rw [Finset.mem_filter, Finset.mem_range] at hq
  have hpq := (Nat.prime_dvd_prime_iff_eq hp hq.2).1 (hp.dvd_of_dvd_pow hdvd)
  omega

theorem dGamSmooth_of_dvd {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u,
      ((Fm.D x i).mem u).C.DGam ∣ minkM (2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m)) :
    Pk.DGamSmooth Fm := by
  obtain ⟨x0, hx0⟩ := h
  exact ⟨x0, fun x hx i u p hp hpd => prime_le_succ_of_dvd_minkM' hp (dvd_trans hpd (hx0 x hx i u))⟩

end Formalism.MainNotions.J
