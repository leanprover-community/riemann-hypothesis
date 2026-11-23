module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringGaloisStableOfKummer
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.mem_valuationSubring_galois_iff_of_kummer_stable : ∀ (l : ℕ), l.Prime → ∀ (F L : Type) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L], IsPGroup l (L ≃ₐ[F] L) → (∃ ζ : F, IsPrimitiveRoot ζ l) → ∀ W : ValuationSubring L, (∀ θ : L, θ ≠ 0 → θ ^ l ∈ (algebraMap F L).range → ∀ τ : L ≃ₐ[F] L, ∀ x ∈ IntermediateField.adjoin F {θ}, τ x ∈ W ↔ x ∈ W) → ∀ (τ : L ≃ₐ[F] L) (x : L), τ x ∈ W ↔ x ∈ W := by
  first | exact @GlobalTheory.valuationSubring_galois_stable_of_kummer | exact GlobalTheory.valuationSubring_galois_stable_of_kummer | (intros; apply GlobalTheory.valuationSubring_galois_stable_of_kummer <;> assumption)
