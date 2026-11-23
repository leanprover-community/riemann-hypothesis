module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.exists_invariant_hermitianForm_cuspidalRep : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) ∧ (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) ∧ (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) ∧ (∀ k φ ψ, H (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = H φ ψ) ∧ ∀ X φ ψ, H (π.op (.lie X) φ) ψ + H φ (π.op (.lie X) ψ) = 0 := by
  first | exact @GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian | exact GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian | (intros; apply GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian <;> assumption)
