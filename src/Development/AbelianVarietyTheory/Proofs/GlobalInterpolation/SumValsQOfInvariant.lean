module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumRangeMulOfPeriodic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory

theorem sum_range_mul_of_periodic {K : Type} [Field K] (g : ℕ → K) (N : ℕ)
    (hg : ∀ i, g (N + i) = g i) (k : ℕ) :
    ∑ i ∈ Finset.range (N * k), g i = (k : K) * ∑ i ∈ Finset.range N, g i := by
  first
  | exact @_root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic
  | exact _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic
  | (apply _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic <;> assumption)
  | (intros; apply _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic ..)

theorem sum_valsQ_of_invariant (E : Type) [Field E] [NumberField E]
    (P : HeightOneSpectrum (𝓞 E)) (K : Type) [Field K] (f : E → K) (B₀ : ℕ)
    (hf : ∀ a u, IntAt P u → f (a + (qOf P : E) ^ B₀ * u) = f a) (A B : ℕ) (hB : B₀ ≤ B) :
    ∑ a ∈ LocE.valsQ E (qOf P) A B, f a
      = (qOf P : K) ^ (B - B₀) * ∑ a ∈ LocE.valsQ E (qOf P) A B₀, f a := by
  classical
  have hq : (qOf P : E) ≠ 0 := by
    have : qOf P ≠ 0 := by
      unfold qOf
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact P.ne_bot
    exact_mod_cast this
  have key : ∀ C : ℕ, ∑ a ∈ LocE.valsQ E (qOf P) A C, f a
      = ∑ i ∈ Finset.range (qOf P ^ (A + C)), f ((i : E) / (qOf P : E) ^ A) := by
    intro C
    unfold LocE.valsQ
    rw [Finset.sum_image]
    intro i _ j _ hij
    have := (div_left_inj' (pow_ne_zero A hq)).1 hij
    exact_mod_cast this
  rw [key, key]
  have e : qOf P ^ (A + B) = qOf P ^ (A + B₀) * qOf P ^ (B - B₀) := by
    rw [← pow_add]; congr 1; omega
  rw [e, sum_range_mul_of_periodic (fun i : ℕ => f ((i : E) / (qOf P : E) ^ A))]
  · push_cast; rfl
  · intro i
    have h1 : IntAt P (1 : E) := by simpa using IntAt.coe P 1
    have := hf ((i : E) / (qOf P : E) ^ A) 1 h1
    rw [← this]
    congr 1
    push_cast
    field_simp
    ring

end GlobalTheory
