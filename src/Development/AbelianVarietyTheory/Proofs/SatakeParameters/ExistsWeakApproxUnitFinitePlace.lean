module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace GlobalTheory.HkFin

theorem exists_weak_approx_unit (E : Type) [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) (n : ℕ) :
    ∃ y : E, y ≠ 0 ∧ Valued.v ((y : w.adicCompletion E) * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1)
      ≤ WithZero.exp (-(n : ℤ)) ∧ ∀ v ∈ S, v ≠ w → v.valuation E (y - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  obtain ⟨a, ha0, ha, -⟩ := PI.FinOrdValD.WA.weakApprox (insert w S)
    (Function.update (fun v => (1 : v.adicCompletion E)) w (x : w.adicCompletion E))
    (Function.update (fun _ => exp (-(n : ℤ))) w (Valued.v (x : w.adicCompletion E) * exp (-(n : ℤ))))
    (fun v _ => by
      by_cases h : v = w
      · subst h; simp only [Function.update_self]
        exact mul_ne_zero ((Valuation.ne_zero_iff _).mpr x.ne_zero) exp_ne_zero
      · simp only [Function.update_of_ne h]; exact exp_ne_zero)
  refine ⟨a, ha0, ?_, fun v hv hvw => ?_⟩
  · have h := ha w (Finset.mem_insert_self w S)
    simp only [Function.update_self] at h
    have hx0 : Valued.v (x : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
    have e1 : (a : w.adicCompletion E) * (((x⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E) - 1 =
        (algebraMap E (w.adicCompletion E) a - x) * (((x⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E) := by
      rw [sub_mul, Units.mul_inv]; rfl
    rw [e1, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    rw [mul_comm] at h
    exact (mul_inv_lt_of_lt_mul₀ h).le
  · have h := ha v (Finset.mem_insert_of_mem hv)
    simp only [Function.update_of_ne hvw] at h
    rw [← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, PI.FinOrdValD.WA.val_alg] at h
    exact h.le

end GlobalTheory.HkFin
