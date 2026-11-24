module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspValueComparison
import Formalism.CyclotomicNorms.StatementI

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

def radical (k : Type) [CommRing k] (r a : ℕ) : Set (GL (Fin r) k) :=
  {u | ∀ i j : Fin r, (u : Matrix (Fin r) (Fin r) k) i j ≠ (1 : Matrix (Fin r) (Fin r) k) i j → i.val < a ∧ a ≤ j.val}

def NoFixed {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G) : Prop :=
  ∀ x : V, (∀ u ∈ S, τ u x = x) → x = 0

def HypH {P : Type} {k : P → Type} [∀ v, CommRing (k v)] {r : ℕ} {V : P → Type} [∀ v, AddCommGroup (V v)]
    [∀ v, Module ℂ (V v)] (τ : ∀ v, Representation ℂ (GL (Fin r) (k v)) (V v)) : Prop :=
  ∀ a : ℕ, 0 < a → a < r → ∃ v, NoFixed (τ v) (radical (k v) r a)

def IsSubrep {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ G V) (π : Representation ℂ G W) : Prop :=
  ∃ T : V →ₗ[ℂ] W, Function.Injective T ∧ ∀ t : G, T ∘ₗ τ t = π t ∘ₗ T

def FixedVectorBlocks : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (r : ℕ) (b : Fin r → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (blockTri (κ := k) b) W), IsCuspDatum b ρ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin r) k) V), IsSubrep τ (parInd b ρ) →
    ∀ a : ℕ, 0 < a → a < r → ¬ NoFixed τ (radical k r a) →
      ∃ J ⊆ Finset.univ.image b, a = ∑ c ∈ J, Fintype.card {i : Fin r // b i = c}


end GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors
