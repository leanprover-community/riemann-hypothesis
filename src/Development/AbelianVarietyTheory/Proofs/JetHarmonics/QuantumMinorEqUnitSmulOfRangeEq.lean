module

public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.StatementI

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_perm_of_range_eq {t : ℕ} {β : Type} (a a₂ : Fin t → β)
    (ha : Function.Injective a) (ha₂ : Function.Injective a₂) (h : Set.range a = Set.range a₂) :
    ∃ τ : Equiv.Perm (Fin t), a = a₂ ∘ τ := by
  refine ⟨(Equiv.ofInjective a ha).trans ((Set.equivOfEq h).trans (Equiv.ofInjective a₂ ha₂).symm), ?_⟩
  funext i
  simp [Equiv.apply_ofInjective_symm]

theorem qminor_eq_smul_of_range_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a a₂ b b₂ : Fin t → Fin n), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective a₂ → Function.Injective b → Function.Injective b₂ → Set.range a = Set.range a₂ → Set.range b = Set.range b₂ → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u, Formalism.REAL.qminor E a b u = e • Formalism.REAL.qminor E a₂ b₂ u := by
  intro A _ _ n t E a a₂ b b₂ hE ha ha₂ hb hb₂ hra hrb
  obtain ⟨σ, rfl⟩ := exists_perm_of_range_eq a a₂ ha ha₂ hra
  obtain ⟨τ, rfl⟩ := exists_perm_of_range_eq b b₂ hb hb₂ hrb
  refine ⟨(((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ) : ℤ) : ℂ), ?_, fun u => ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h' | h' <;> simp [h, h']
  · rw [Formalism.REAL.quantumMinorRowSkew_holds A n t E a₂ (b₂ ∘ τ) σ u, Formalism.REAL.quantumMinorColSkew_holds A n t E hE a₂ b₂ τ u,
      Int.cast_smul_eq_zsmul, zsmul_eq_mul, ← mul_assoc, Int.cast_mul]

end GlobalTheory
