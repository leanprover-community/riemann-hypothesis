module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuInf
public import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsPrimitiveRootTorsionOrder
public import Formalism.LocalRingCardinality.DataHost
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.NuLe
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.NuQDUnit
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.SplitNotDvd
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.SumFactorizationMulLogLe
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.WDvdQS
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open NumberField Formalism.BasicNotions KStar.Tree

namespace UpperTheory.Mu

theorem tr_odd (R : Ranks) : Odd (R.t * R.r) := by
  refine Nat.odd_mul.2 ⟨R.t_odd, ?_⟩
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have hm := R.two_le_m
  unfold Ranks.r
  exact ⟨a + b - 1, by omega⟩

variable {R : Ranks} (H : Host R)

theorem half_not_dvd {l : ℕ} (h : l = H.q ∨ l = H.d) : ¬ (l - 1) / 2 ∣ R.t * R.r := by
  have hpos : 0 < R.t * R.r := (tr_odd R).pos
  obtain ⟨hq, hd⟩ := H.qd_big
  have e : 4 * R.t * R.r = 4 * (R.t * R.r) := by ring
  rw [e] at hq hd
  apply Nat.not_dvd_of_pos_of_lt hpos
  generalize R.t * R.r = N at *
  rcases h with rfl | rfl <;> omega

theorem w_dvd_QS : H.w ∣ H.QS := (wDvdQS _ H.toHostRaw H.q_ne_three).1

variable (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

theorem nu_eq_zero_of_qd (l : ℕ) [Fact l.Prime] (h : l = H.q ∨ l = H.d) : nuOf l (cyc l H.E Ω) (R.t * R.r) = 0 :=
  nuQD _ H.toHostRaw l Ω _ h (half_not_dvd H h)

theorem nu_eq_zero_of_not_dvd (l : ℕ) [Fact l.Prime] (h : ¬ l ∣ H.QS) : nuOf l (cyc l H.E Ω) (R.t * R.r) = 0 := by
  by_cases hqd : l = H.q ∨ l = H.d
  · exact nu_eq_zero_of_qd H Ω l hqd
  · push_neg at hqd
    have hle := nuLe _ H.toHostRaw l Ω (R.t * R.r) (tr_odd R) hqd.1 hqd.2
    rw [if_neg h, Nat.factorization_eq_zero_of_not_dvd h] at hle
    omega

theorem nu_eq_zero_of_split (l : ℕ) [hl : Fact l.Prime]
    (h : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 H.E) | ((l : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E) :
    nuOf l (cyc l H.E Ω) (R.t * R.r) = 0 :=
  nu_eq_zero_of_not_dvd H Ω l (splitNotDvd _ H.toHostAx H.QS_exact l hl.out h)

theorem sum_nu_le (ν : ℕ → ℝ) (hν : ∀ (l : ℕ) [Fact l.Prime], ν l = (nuOf l (cyc l H.E Ω) (R.t * R.r) : ℝ))
    (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    ∑ l ∈ S, ν l * Real.log l ≤ Real.log (H.QS : ℝ) + Real.log ((R.t * R.r : ℕ) : ℝ) := by
  classical
  let μ : ℕ → ℕ := fun l => if h : l.Prime then (haveI := Fact.mk h; nuOf l (cyc l H.E Ω) (R.t * R.r)) else 0
  have hμ : ∀ (l : ℕ) [Fact l.Prime], μ l = nuOf l (cyc l H.E Ω) (R.t * R.r) := fun l hl => dif_pos hl.out
  refine le_of_eq_of_le (Finset.sum_congr rfl fun l hl => ?_)
    (nuSum _ H.toHostRaw Ω _ (tr_odd R) (half_not_dvd H (Or.inl rfl)) (half_not_dvd H (Or.inr rfl)) μ hμ S hS)
  haveI := Fact.mk (hS l hl)
  rw [hν l, hμ l]

theorem budget_le : Real.log (H.QS : ℝ) + Real.log ((R.t * R.r : ℕ) : ℝ) ≤
    2 * Real.log R.n + Real.log R.t + Real.log R.r := by
  have h1 : Real.log (H.QS : ℝ) ≤ 2 * Real.log R.n := by
    have : ((H.QS : ℕ) : ℝ) ≤ (R.n : ℝ) ^ 2 := by exact_mod_cast H.QS_le
    have h0 : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
    simpa using Real.log_le_log h0 this
  have h2 := (tr_odd R).pos
  have ht : (R.t : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_right h2).ne'
  have hr : (R.r : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_left h2).ne'
  rw [Nat.cast_mul, Real.log_mul ht hr]
  linarith

end UpperTheory.Mu
