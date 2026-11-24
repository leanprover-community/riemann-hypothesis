module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitOfEventually
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem io_mem_Lat_of_mem_span {M n : ℕ} {x : Ainf l}
    (hx : x ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M}) : io AI x ∈ Lat AI M n := by
  obtain ⟨p, q, rfl⟩ := Ideal.mem_span_pair.1 hx
  rw [map_add (f := _), mul_comm p]
  refine add_mem (io_mem_Lat AI M n p) (FilB_le_Lat AI ?_)
  rw [map_mul, map_pow]
  exact FilB_zero_mul (io_mem AI q) (by simpa using FilB_pow (io_ξ_mem AI) M)

theorem bounded_and_eventually_sub_mem_Lat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (AI : LocAinf l P), LocTied l P AI → ∀ b ∈ FilB P 0, ∀ M n : ℕ,
    (∃ k : ℕ, (l : P.R.BdR) ^ k * b ∈ Lat AI M n) ∧
      ∀ᶠ σ in nhds (1 : GQ l), P.actQdR σ b - b ∈ Lat AI M n := by
  intro l _ P AI T b hb M n
  obtain ⟨k, a, ha⟩ := GlobalTheory.BdRQuot.exists_approx T M b hb
  change (l : P.R.BdR) ^ k * b - io AI a ∈ FilB P (M : ℤ) at ha
  constructor
  · have h0 : (l : P.R.BdR) ^ k * b ∈ Lat AI M 0 := ⟨a, by simpa using ha⟩
    refine ⟨n + k, ?_⟩
    rw [pow_add, mul_assoc]
    exact (pow_mul_mem_Lat_iff AI (k := n) (n := 0)).2 h0
  · filter_upwards [GlobalTheory.AinfCont.eventually_sub_mem AI (k + n) M a] with g hg
    rw [← pow_mul_mem_Lat_iff AI (k := k)]
    have h1 := io_mem_Lat_of_mem_span AI hg
    have h2 := FilB_le_Lat AI (n := k + n) (sub_mem (act_mem g ha) ha)
    have h3 := add_mem h1 h2
    rw [map_sub, io_act, map_sub, map_mul, map_pow, map_natCast] at h3
    convert h3 using 1
    ring

end GlobalTheory.ExpImage
