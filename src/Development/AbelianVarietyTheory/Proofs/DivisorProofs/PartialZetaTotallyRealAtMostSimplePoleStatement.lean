module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaTotallyRealAtMostSimplePole
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.partialZeta_totallyReal_at_most_simple_pole : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (C C' : ClassGroup (NumberField.RingOfIntegers F)) (Z Z' : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Z → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C' Z' → (∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Z s = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Z' (1 - s)) → ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ ∀ s : ℂ, s ≠ 1 → Z s = R s / (s - 1) := by
  first | exact @GlobalTheory.ZetaPole.zeta_simple_pole | exact GlobalTheory.ZetaPole.zeta_simple_pole | (intros; apply GlobalTheory.ZetaPole.zeta_simple_pole <;> assumption)
