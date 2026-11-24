module

public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Mathlib.Algebra.MvPolynomial.Funext
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

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial GroundTheory.Heights₂.Heights

theorem mem_antisymSpace_of_pointwise :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (R : MvPolynomial (Ψ × Fin N) ℝ),
      R.IsHomogeneous (antisymDegree Ψ N + 1) →
      (∀ (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) →
        ∀ lam : Ψ × Fin N → ℝ, eval lam R + eval (lam ∘ Equiv.swap (τ, a) (τ, b)) R = 0) →
      R ∈ antisymSpace Ψ N j := by
  intro Ψ _ _ N j R hR h
  refine ⟨(mem_homogeneousSubmodule _ _).2 hR, ?_⟩
  rintro σ ⟨τ, a, b, hab, hblock, rfl⟩
  refine MvPolynomial.funext fun lam => ?_
  rw [eval_rename, map_neg]
  exact eq_neg_of_add_eq_zero_right (h τ a b hab hblock lam)

end GlobalTheory.CompanionTheory.Ar.PB
