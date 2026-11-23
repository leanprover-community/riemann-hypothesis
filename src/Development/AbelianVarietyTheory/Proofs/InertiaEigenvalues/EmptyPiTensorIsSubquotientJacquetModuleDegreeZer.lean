module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory

theorem piTensor_isSubquotient_jac_degZero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ), N = 0 → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (π : Representation ℂ (GL (Fin N) k) V) (d : Fin 0 → ℕ) (X : Fin 0 → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (e : (Σ a, Fin (d a)) ≃ Fin N),
    IsSubquotient (piTensor ρ) (jac e π) := by
  intro k _ _ _ _ N hN V _ _ _ π d X _ _ ρ e
  subst hN
  have hK : twKer π (unipRad k e) 1 = ⊥ := by
    refine le_bot_iff.1 (Submodule.span_le.2 ?_)
    rintro w ⟨n, v, rfl⟩
    have h1 : (n : GL (Fin 0) k) = 1 := Subsingleton.elim _ _
    simp [h1]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hx : (Submodule.Quotient.mk v : Jacquet π (unipRad k e)) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_bot]; exact hv
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (Jacquet π (unipRad k e)),
      φ (Submodule.Quotient.mk v) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
  let L : Jacquet π (unipRad k e) →ₗ[ℂ] PiTensorProduct ℂ X :=
    (PiTensorProduct.isEmptyEquiv (Fin 0)).symm.toLinearMap ∘ₗ φ
  refine IsSubquotient.of_surjective ⟨L, fun g => ?_⟩ ?_
  · have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    rw [map_one, map_one]
    rfl
  · have hsurj : Function.Surjective φ := fun c =>
      ⟨(c / φ (Submodule.Quotient.mk v)) • Submodule.Quotient.mk v, by simp [hφ]⟩
    exact (PiTensorProduct.isEmptyEquiv (Fin 0)).symm.surjective.comp hsurj

end GlobalTheory
