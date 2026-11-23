module

public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoQuotientPowFreeOverRegularLocalRing
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

open IsLocalRing

theorem _root_.GlobalTheory.T.modDepthGE_two_quotient_pow_free_over_regularLocalRing : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ≠ 0 → ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B] [Nontrivial B] (k : ℕ), 1 ≤ k → ReciprocityTheory.CA.ModDepthGE R (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k) 2 := by
  first | (exact @GlobalTheory.modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing) | (exact GlobalTheory.modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing) | (intros; apply GlobalTheory.modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing  <;> assumption)
