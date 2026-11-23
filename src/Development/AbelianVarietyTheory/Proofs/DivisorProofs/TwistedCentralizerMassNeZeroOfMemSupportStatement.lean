module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassNeZeroOfMemSupport
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

open GlobalTheory.LKCount

theorem _root_.GlobalTheory.T.twistedCentralizerMass_ne_zero_of_mem_support : ∀ {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ), Γ' ≤ T → (∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x) → (∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite) → {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite → ∀ y : G, F y ≠ 0 → massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  first | exact @GlobalTheory.massC_ne_zero_of_support | exact GlobalTheory.massC_ne_zero_of_support | (intros; apply GlobalTheory.massC_ne_zero_of_support <;> assumption)
