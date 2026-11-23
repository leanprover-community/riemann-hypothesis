module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedEisensteinFxCoefficientSeqOneMemSubring
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


theorem _root_.GlobalTheory.T.smoothedEisensteinFxCoefficientSeq_one_mem_subring : ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (c M : ℕ) (ζ : K) (a b : ℤ), 0 < M → Nat.Coprime c M → ¬ (M : ℤ) ∣ a → ζ ^ b ∈ R → ζ ^ (-b) ∈ R → ∀ n : ℕ, GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M ζ a b n ∈ R := by
  first | exact @GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring | exact GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring | (intros; apply GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring; all_goals assumption)
