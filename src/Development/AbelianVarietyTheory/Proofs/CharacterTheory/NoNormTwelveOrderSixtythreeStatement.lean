module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormTwelveOrderSixtythree
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.false_of_sum_sq_eq_12_of_fourier_vanish_order_63 : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 63 → ∑ k ∈ Finset.range 63, c k ^ 2 = 12 → (∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j → ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  first | exact @GlobalTheory.no_norm_twelve_order_sixtythree | exact GlobalTheory.no_norm_twelve_order_sixtythree | (intros; apply GlobalTheory.no_norm_twelve_order_sixtythree <;> assumption)
