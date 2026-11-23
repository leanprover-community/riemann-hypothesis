module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCoveringOfTraceDualLowerBound
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
import Formalism.HarderNarasimhan.Statement
import Formalism.HermitianLattices.StatementLat

@[expose] public section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

theorem _root_.GlobalTheory.T.lattice_covering_of_trace_dual_lower_bound : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι ι' : Type) [Fintype ι] [Fintype ι'] (L : Submodule (𝓞 K) (ι → K)) (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ))) (lam : ℝ), L.FG → Submodule.span K (L : Set (ι → K)) = ⊤ → 0 < lam → (∀ (f : ι → K) (c : InfinitePlace K → ι' → ℂ), f ≠ 0 → (∀ y ∈ L, ∃ m : ℤ, Algebra.trace ℚ K (f ⬝ᵥ y) = m) → (∀ (w : InfinitePlace K) (y : ι → ℂ), (fun i => w.embedding (f i)) ⬝ᵥ y = c w ⬝ᵥ M w y) → lam ^ 2 ≤ ∑ w, ∑ i, ‖c w i‖ ^ 2) → ∀ t : InfinitePlace K → ι' → ℂ, ∃ y ∈ L, Real.sqrt (∑ w, ∑ i, ‖t w i - M w (fun j => w.embedding (y j)) i‖ ^ 2) ≤ (Fintype.card (InfinitePlace K) : ℝ) * (Fintype.card ι : ℝ) / (2 * lam) := by
  first | exact @GlobalTheory.TraceCover.cover | exact GlobalTheory.TraceCover.cover | (intros; apply GlobalTheory.TraceCover.cover <;> assumption)
