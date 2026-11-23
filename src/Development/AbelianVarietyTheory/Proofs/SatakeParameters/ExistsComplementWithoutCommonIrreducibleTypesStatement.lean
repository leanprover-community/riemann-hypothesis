module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplementWithoutCommonIrreducibleTypes
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


theorem _root_.GlobalTheory.T.exists_complement_without_common_irreducible_types : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V), ρ.IsSemisimpleRepresentation → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ X : Subrepresentation ρ, (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → S₂ ≤ X → Nonempty (S₁.toRepresentation.Equiv S₂.toRepresentation) → S₁ ≤ X) → ∃ Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule ∧ (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) ∧ ∀ T : V →ₗ[ℂ] V, (∀ k v, T (ρ k v) = ρ k (T v)) → (∀ v ∈ X.toSubmodule, T v ∈ X.toSubmodule) ∧ ∀ v ∈ Y.toSubmodule, T v ∈ Y.toSubmodule := by
  first | exact @GlobalTheory.TypeComplement.exists_typeComplement | exact GlobalTheory.TypeComplement.exists_typeComplement | (intros; apply GlobalTheory.TypeComplement.exists_typeComplement <;> assumption)
