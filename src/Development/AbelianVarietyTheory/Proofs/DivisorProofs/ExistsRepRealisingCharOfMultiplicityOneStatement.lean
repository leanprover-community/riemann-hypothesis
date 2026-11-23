module

public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepRealisingCharOfMultiplicityOne
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

@[expose] public section

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.exists_rep_realising_char_of_multiplicity_one : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (χ : G → K), IsAbsIrrChar χ → ∀ (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ), ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) = (Fintype.card P : K) → ∃ (n : ℕ) (τ : Representation K G (Fin n → K)), 0 < n ∧ Function.Surjective τ.asAlgebraHom ∧ ∀ g, LinearMap.trace K (Fin n → K) (τ g) = χ g := by
  first | exact @GlobalTheory.MultOneRealised.exists_rep_of_mult_one | exact GlobalTheory.MultOneRealised.exists_rep_of_mult_one | (intros; apply GlobalTheory.MultOneRealised.exists_rep_of_mult_one <;> assumption)
