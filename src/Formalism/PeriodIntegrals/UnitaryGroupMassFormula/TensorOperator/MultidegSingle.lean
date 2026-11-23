module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.Development
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MvPolynomial

noncomputable section

namespace PI.TOW.DegW

open PI.TO PI.TOW

variable {K : Type} [Field K] {n' k : ℕ}

theorem multideg_add (a b : Fin n' × Fin k →₀ ℕ) (i : Fin n') :
    multideg (a + b) i = multideg a i + multideg b i := by
  simp only [multideg, Finsupp.add_apply, Finset.sum_add_distrib]

theorem multideg_single (j : Fin n' × Fin k) (i : Fin n') :
    multideg (Finsupp.single j 1) i = if j.1 = i then 1 else 0 := by
  obtain ⟨j₁, j₂⟩ := j
  by_cases h : j₁ = i <;> simp [multideg, Finsupp.single_apply, Prod.ext_iff, h]

theorem step_mem (t : Fin n') (a b : Fin k) (d : Fin n' → ℕ) (G : MvPolynomial (Fin n' × Fin k) K)
    (hG : G ∈ Pol K (ι := Fin n') k d) :
    X (t, a) * pderiv (t, b) G ∈ Pol K (ι := Fin n') k d := by
  rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hG

  rw [G.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hdm : ∀ i, multideg m i = d i := hG hm
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.X, MvPolynomial.monomial_mul]
  by_cases hmb : m (t, b) = 0
  · simp [hmb]
  have hle : Finsupp.single (t, b) 1 ≤ m := by
    rw [Finsupp.single_le_iff]; omega
  have hsplit : m = (m - Finsupp.single (t, b) 1) + Finsupp.single (t, b) 1 :=
    (tsub_add_cancel_of_le hle).symm
  have hexp : ∀ i, multideg (Finsupp.single (t, a) 1 + (m - Finsupp.single (t, b) 1)) i = d i := by
    intro i
    have h1 := multideg_add (m - Finsupp.single (t, b) 1) (Finsupp.single (t, b) 1) i
    rw [← hsplit, hdm i, multideg_single] at h1
    rw [multideg_add, multideg_single]
    simp only at h1 ⊢
    split_ifs at h1 ⊢ <;> omega
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  intro x hx
  have hx' := MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hx)
  rw [Finset.mem_singleton] at hx'
  subst hx'
  exact hexp

theorem stepDeg : StepDeg := by
  intro K _ n' k d l G hG
  induction l with
  | nil => exact hG
  | cons y l ih =>
    simp only [opWord, List.foldr_cons] at ih ⊢
    exact step_mem y.1 y.2.1 y.2.2 d _ ih

end PI.TOW.DegW
