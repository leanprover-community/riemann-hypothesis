module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.NormRepStepOfTrace
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical ComplexConjugate

namespace PI.NRL

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits Polynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_emb (D : D7) (x : D.host.E) : D.host.φ₀ (star x) = conj (D.host.φ₀ x) := by
  haveI := D.host.isCMField_hostE
  show D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = _
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x

theorem star_sqrtMinusD (D : D7) : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [star_emb, map_neg, h, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem traceOne (D : D7) : TraceOne D := by
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d + 1 = 4 * k := ⟨(D.host.d + 1) / 4, by omega⟩
  have hs : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hk' : (D.host.d : D.host.E) + 1 = 4 * (k : D.host.E) := by exact_mod_cast hk
  have hω : ((1 + D.host.sqrtMinusD) / 2) ^ 2 - (1 + D.host.sqrtMinusD) / 2 + (k : D.host.E) = 0 := by
    linear_combination (1 / 4 : D.host.E) * hs - (1 / 4 : D.host.E) * hk'
  have hint : IsIntegral ℤ ((1 + D.host.sqrtMinusD) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k : ℤ), by monicity!, ?_⟩
    simpa using hω
  refine ⟨⟨(1 + D.host.sqrtMinusD) / 2, hint⟩, ?_⟩
  show (1 + D.host.sqrtMinusD) / 2 + star ((1 + D.host.sqrtMinusD) / 2) = 1
  rw [star_div₀, star_add, star_one, star_sqrtMinusD, star_ofNat]
  ring

end PI.NRL
