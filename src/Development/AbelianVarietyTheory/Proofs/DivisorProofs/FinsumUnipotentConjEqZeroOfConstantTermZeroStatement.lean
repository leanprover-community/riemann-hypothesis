module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumUnipotentConjEqZeroOfConstantTermZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open MeasureTheory Matrix
open scoped Classical

theorem _root_.GlobalTheory.T.finsum_unipotentConj_eq_zero_of_constantTerm_zero : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b) (f : GL ι K → ℂ),
  IsLocallyConstant f → HasCompactSupport f →
  (∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * GlobalTheory.OrbDesc.uGL e X * h)) ∂μ = 0) →
  ∀ K' : Subgroup (GL ι K), IsOpen (K' : Set (GL ι K)) → IsCompact (K' : Set (GL ι K)) →
  (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f (k * g * k') = f g) →
  ∀ γ ∈ GlobalTheory.OrbDesc.blockPar e, (γ : Matrix ι ι K).charpoly.Separable →
  ∑ᶠ q : GL ι K ⧸ (GlobalTheory.OrbDesc.blockUni e ⊓ (GlobalTheory.OrbDesc.blockPar e ⊓ K')),
    (if Quotient.out q ∈ GlobalTheory.OrbDesc.blockUni e then f ((Quotient.out q)⁻¹ * γ * Quotient.out q) else 0) = 0 := by
  first | (exact @GlobalTheory.OrbDesc.NSum.finsum_conj_eq_zero) | (exact GlobalTheory.OrbDesc.NSum.finsum_conj_eq_zero) | (intros; apply GlobalTheory.OrbDesc.NSum.finsum_conj_eq_zero  <;> assumption)
