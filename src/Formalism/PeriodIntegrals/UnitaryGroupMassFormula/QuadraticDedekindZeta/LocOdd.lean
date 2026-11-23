module

public import Formalism.PeriodIntegrals.ClassNumImQ
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ClassNumImQInt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticInvariants.QuadPolyIrreducible
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

namespace PI.ClassNumImQ.ZetaNonvanishing₂.Loc

variable {d : ℕ} {K : Type} [Field K] [NumberField K] {b : K}

noncomputable def om (hq : QuadData d K b) : 𝓞 K :=
  ⟨(1 + b) / 2, (imag_quadratic_integral_basis d K b hq).1⟩

theorem om_coe (hq : QuadData d K b) : ((om hq : 𝓞 K) : K) = (1 + b) / 2 := rfl

theorem basis (hq : QuadData d K b) (x : 𝓞 K) : ∃ m n : ℤ, x = m + n * om hq := by
  obtain ⟨m, n, h⟩ := (imag_quadratic_integral_basis d K b hq).2 x
  refine ⟨m, n, RingOfIntegers.ext ?_⟩
  rw [h]
  push_cast [om_coe]
  rfl

theorem coeff_unique (hq : QuadData d K b) {m n m' n' : ℤ}
    (h : (m : 𝓞 K) + n * om hq = m' + n' * om hq) : m = m' ∧ n = n' := by
  have hK : (m : K) + n * ((1 + b) / 2) = m' + n' * ((1 + b) / 2) := by
    have h' := congrArg (fun x : 𝓞 K => (x : K)) h
    push_cast [om_coe] at h'
    exact h'
  by_cases hn : n = n'
  · subst hn
    refine ⟨?_, rfl⟩
    exact_mod_cast add_right_cancel hK
  · exfalso
    have hne : ((n : K) - n') ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
    apply PI.UnitaryGroupMassFormula.ClassNumImQInv.b_ne_rat hq ((2 * (m' - m) + n' - n) / (n - n'))
    push_cast
    rw [div_eq_iff hne]
    linear_combination (-2 : K) * hK

end PI.ClassNumImQ.ZetaNonvanishing₂.Loc
