module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumsOverConjugacyClasses
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


theorem _root_.GlobalTheory.T.orbit_sum_conj_classes : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ = ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) := by
  first | (exact @GlobalTheory.OrbitUnfold.finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer) | (exact GlobalTheory.OrbitUnfold.finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer) | (intros; apply GlobalTheory.OrbitUnfold.finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer  <;> assumption)
