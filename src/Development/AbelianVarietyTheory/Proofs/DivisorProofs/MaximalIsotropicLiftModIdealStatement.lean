module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIsotropicLiftModIdeal
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.maximal_isotropic_lift_mod_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R) (D : Type) [AddCommGroup D] [Module R D] [Module.Finite R D] [Module.Projective R D] (φ : D →ₗ[R] D →ₗ[R] R), I ^ 2 = ⊥ → IsUnit (2 : R) → (∀ x y, φ x y = -φ y x) → (∀ l : D →ₗ[R] R, ∃ z, ∀ x, l x - φ x z ∈ I) → ∀ F N : Submodule R D, IsCompl F N → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → ∃ E N' : Submodule R D, IsCompl E N' ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ E ⊔ I • (⊤ : Submodule R D) = F ⊔ I • (⊤ : Submodule R D) := by
  first | exact @GlobalTheory.isotropic_summand_lift | exact GlobalTheory.isotropic_summand_lift | (intros; apply GlobalTheory.isotropic_summand_lift <;> assumption)
