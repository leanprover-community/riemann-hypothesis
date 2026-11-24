module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace GlobalTheory.BoundedScalarNorm

theorem norm_smul_le_self {l : ℕ} [Fact l.Prime] (a : ℤ_[l]) (y : PadicAlgCl l) : ‖a • y‖ ≤ ‖y‖ := by
  have h : a • y = (a : ℚ_[l]) • y := by
    rw [← IsScalarTower.algebraMap_smul ℚ_[l] a y]; rfl
  rw [h, norm_smul]
  have h1 : ‖(a : ℚ_[l])‖ ≤ 1 := a.2
  exact mul_le_of_le_one_left (norm_nonneg _) h1

theorem bounded {l : ℕ} [Fact l.Prime] (M : Submodule ℤ_[l] (PadicAlgCl l)) (h : M.FG) :
    ∃ C : ℝ, ∀ y ∈ M, ‖y‖ ≤ C := by
  obtain ⟨s, rfl⟩ := h
  refine ⟨∑ z ∈ s, ‖z‖, fun y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem z hz => exact Finset.single_le_sum (f := fun z => ‖z‖) (fun _ _ => norm_nonneg _) hz
  | zero => rw [norm_zero]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  | add u v _ _ hu hv => exact (IsUltrametricDist.norm_add_le_max u v).trans (max_le hu hv)
  | smul a u _ hu => exact (norm_smul_le_self a u).trans hu

theorem norm_le_one : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ UpperTheory.V.HV.Coef.O c → ‖x‖ ≤ (1 : ℝ) := by
  intro l _ c x hx
  have hfg : (Subalgebra.toSubmodule c.O).FG := Module.Finite.iff_fg.mp c.fin
  obtain ⟨C, hC⟩ := bounded _ hfg
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
  have := hC (x ^ n) (c.O.pow_mem hx n)
  rw [norm_pow] at this
  exact absurd hn (not_lt.mpr this)

end GlobalTheory.BoundedScalarNorm
