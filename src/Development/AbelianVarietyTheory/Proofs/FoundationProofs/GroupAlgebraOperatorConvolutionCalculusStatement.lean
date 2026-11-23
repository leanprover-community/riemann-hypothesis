module

public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GroupAlgebraOperatorConvolutionCalculus
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

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.groupAlgebraOperator_convolution_calculus : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), (∀ a b : G → ℂ, op ρ (conv a b) = op ρ a * op ρ b ∧ op ρ (a - b) = op ρ a - op ρ b ∧ op ρ (a + b) = op ρ a + op ρ b) ∧ op ρ dirac = 1 ∧ (∀ a b c : G → ℂ, conv (conv a b) c = conv a (conv b c) ∧ conv (a - b) c = conv a c - conv b c ∧ conv c (a - b) = conv c a - conv c b) ∧ (∀ a : G → ℂ, conv dirac a = a ∧ conv a dirac = a) ∧ (∀ a b : G → ℂ, IsProj a → IsProj b → conv a b = conv b a → IsProj (conv a b)) ∧ (∀ a : G → ℂ, IsProj a → IsProj (dirac - a)) ∧ ∀ e : G → ℂ, conv e e = e → (rk ρ e : ℂ) = ∑ γ, e γ * LinearMap.trace ℂ M (ρ γ) := by
  first | exact @GlobalTheory.BadShare.convCalc | exact GlobalTheory.BadShare.convCalc | (intros; apply GlobalTheory.BadShare.convCalc <;> assumption)
