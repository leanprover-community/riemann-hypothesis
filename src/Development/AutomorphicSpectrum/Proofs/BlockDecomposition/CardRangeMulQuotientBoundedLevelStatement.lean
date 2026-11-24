module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRangeMulQuotientBoundedLevel
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

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

theorem _root_.GlobalTheory.T.card_range_mul_quotient_bounded_level : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → (∀ (j : ℕ) (a : R), σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w))) = ((ε : ℂ) * q) ^ j) → ∀ (k : ℕ) (d : R), σ d = d → ∃ e : ℕ, e ≤ k ∧ Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) = (q ^ 2) ^ e ∧ ∀ a : R, σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ k, ψ k (Ideal.Quotient.mk (lev ϖ k) (a * d) * (barσ σ ϖ hR.fix_ϖ k w * w))) = (q : ℂ) ^ (2 * k) * ((ε : ℂ) / q) ^ e := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.Scaled.gauss_image_level | exact GlobalTheory.CompanionTheory.SiegLoc.Scaled.gauss_image_level | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.Scaled.gauss_image_level <;> assumption)
