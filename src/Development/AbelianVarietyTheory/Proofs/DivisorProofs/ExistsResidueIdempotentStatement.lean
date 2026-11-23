module

public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueIdempotent
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

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_residue_idempotent' : ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ] [Nontrivial Λ], ∃ x : Λ, x * x - x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) ∧ (∀ y : Λ, ∃ c : A, x * y * x - c • x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ)) ∧ ∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * x * b i - 1 ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) := by
  first | (exact @GlobalTheory.AzumayaResidue.exists_residue_idempotent) | (exact GlobalTheory.AzumayaResidue.exists_residue_idempotent) | (intros; apply GlobalTheory.AzumayaResidue.exists_residue_idempotent  <;> assumption)
