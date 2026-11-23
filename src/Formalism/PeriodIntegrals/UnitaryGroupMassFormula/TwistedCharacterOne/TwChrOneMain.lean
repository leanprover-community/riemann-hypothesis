module

public import Formalism.PeriodIntegrals.TwChrOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.IsIntegralAtSuperdiagonalSum
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwChrOne.Pf

theorem twChrOne_main : PI.TwChrOne.TwChrOne := by
  intro E K _ _ _ _ P psi ξ kj N c hpsi

  have memJ : ∀ r ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c)
      (1 : Sp E (N + c) ≃ₗ[E] Sp E (N + c)), r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c := by
    intro r hr
    unfold Loc.Cbe at hr
    have h2 := (Subgroup.mem_inf.mp hr).2
    rw [Subgroup.mem_comap] at h2
    simpa using h2

  have chi_eq : ∀ r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c,
      ChiL P psi ξ kj N c 1 r = (LocE.unitV ξ (Ment kj N c r).det)⁻¹ := by
    intro r hr
    unfold ChiL
    rw [hpsi _ (isIntegralAt_superdiagonalSum P (hI_of P hr)), inv_one, one_mul, inv_one, one_mul, mul_one]
    rfl
  have unit_of : ∀ r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c,
      IsUnit (redP P (Ment kj N c r).det) := by
    intro r hr
    rw [redP_det_Ment P (hI_of P hr)]
    exact isUnit_Mb P hr
  refine ⟨fun r hr => ?_, fun r hr r' hr' r'' hr'' hx => ?_⟩
  · have hJ := memJ r hr
    rw [chi_eq r hJ]
    refine inv_ne_zero ?_
    unfold LocE.unitV
    rw [dite_eq_left (unit_of r hJ)]
    exact Units.ne_zero _
  · have hJ := memJ r hr
    have hJ' := memJ r' hr'
    have hJ'' := memJ r'' hr''
    rw [chi_eq r hJ, chi_eq r' hJ', chi_eq r'' hJ'', ← mul_inv]
    congr 1
    have hd : redP P (Ment kj N c r'').det =
        redP P (Ment kj N c r).det * redP P (Ment kj N c r').det := by
      rw [redP_det_Ment P (hI_of P hJ''), redP_det_Ment P (hI_of P hJ),
        redP_det_Ment P (hI_of P hJ'), ← Matrix.det_mul]
      congr 1
      apply Mb_mul_of P (fun i hi1 hi2 j hj => red_DA P hJ i hi1 hi2 j hj) (hI_of P hJ) (hI_of P hJ')
      intro t
      have ht : kj + t.1 < N := by have := t.isLt; omega
      have := hx (Loc.eN E N (kj + t.1))
      rwa [inX_eN ht] at this
    have hu := unit_of r hJ
    have hu' := unit_of r' hJ'
    have hu'' := unit_of r'' hJ''
    unfold LocE.unitV
    rw [dite_eq_left hu'', dite_eq_left hu, dite_eq_left hu']
    have hmul : hu''.unit = hu.unit * hu'.unit := Units.ext (by simp [hd])
    rw [hmul, map_mul, Units.val_mul]

end PI.TwChrOne.Pf
