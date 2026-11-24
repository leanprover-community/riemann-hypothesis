module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepBasic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepNewton
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Nat.Prime.Int

@[expose] public section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem keyNewton : KeyNewton := by
  intro a b c d ha hd lam hlam m _ _ Λ l x y T i₀ h k hk w hw
  obtain ⟨hOK, -, hθ, -, -, hl, -, -, -⟩ := h
  obtain ⟨hwsat, hwT, p, q, hq, hww⟩ := hw
  obtain ⟨τ, r, s, hτ1, hτ2, hs, hτsat⟩ := rep_tau a b c d hOK Λ hθ hl
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hq0 : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by rintro rfl; exact hq (dvd_zero _)
    exact_mod_cast this
  have hs0 : (s : ℂ) ≠ 0 := by
    have : s ≠ 0 := by rintro rfl; exact hs (dvd_zero _)
    exact_mod_cast this
  set ε : ℂ := ((l ^ k * p : ℤ) : ℂ) / (q : ℂ) with hε
  have hεc : conj ε = ε := by rw [hε, map_div₀, map_intCast, map_intCast]
  have hξ : (1 - ε * τ) * conj (1 - ε * τ) = 1 - ε + ε ^ 2 * ((r : ℂ) / s) := by
    rw [map_sub, map_one, map_mul, hεc]
    linear_combination (-ε) * hτ1 + ε ^ 2 * hτ2
  refine ⟨(1 - ε * τ) • w, ?_, ?_, p ^ 2 * (r * q - s * q + l ^ k * p * r), q ^ 3 * s, ?_, ?_⟩
  · have e : (1 - ε * τ) • w = w - ε • (τ • w) := by rw [sub_smul, one_smul, smul_smul]
    rw [e, hε]
    exact rep_sat_sub l Λ hl hwsat (rep_sat_rat l Λ hl (hτsat w hwsat) _ _ hq)
  · intro j hj; simp [hwT j hj]
  · intro h
    rcases hlp.dvd_mul.mp h with h | h
    · exact hq (hlp.dvd_of_dvd_pow h)
    · exact hs h
  · rw [rep_H_smul, hξ, hww]
    rw [hε]
    push_cast
    field_simp
    ring

end PI.UnitaryGroupMassFormula.UnimodLocStd
