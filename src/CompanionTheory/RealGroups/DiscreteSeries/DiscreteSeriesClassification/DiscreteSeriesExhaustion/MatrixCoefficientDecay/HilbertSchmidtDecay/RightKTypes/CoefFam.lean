module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.WyKR

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

abbrev CoefFam (X : GMod n) (I : Type) : Type := I → (X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ))

def LeftExp (ε : Fin n → Bool) {X : GMod n} {I : Type} (c : CoefFam X I) : Prop :=
  ∀ i, ∃ (r : ℕ) (is : Fin r → I) (β : Fin r → S7.KG ε → ℂ) (B : ℝ), (∀ l k, ‖β l k‖ ≤ B) ∧
    ∀ (v : X.V) (g : S7.UJ ε) (k : S7.KG ε), c i v (S7.toMK k * S7.toM g) = ∑ l, β l k * c (is l) v (S7.toM g)

def ContFam (ε : Fin n → Bool) {X : GMod n} {I : Type} (c : CoefFam X I) : Prop :=
  ∀ i v, Continuous fun g : S7.UJ ε => c i v (S7.toM g)

structure KAct (ε : Fin n → Bool) (X : GMod n) : Type 1 where
  N : Type
  [ng : NormedAddCommGroup N]
  [ns : NormedSpace ℂ N]
  emb : X.V →ₗ[ℂ] N
  inj : Function.Injective emb
  ρ : S7.KG ε → Module.End ℂ X.V
  compat : ∀ k a b x, ρ k (X.E a b x) = ∑ c, ∑ d, (S7.toMK k c a * (S7.toMK k)ᴴ b d) • X.E c d (ρ k x)
  bdd : ∃ C : ℝ, ∀ k x, ‖emb (ρ k x)‖ ≤ C * ‖emb x‖
  fin : ∀ x, ∃ W : Submodule ℂ X.V, FiniteDimensional ℂ W ∧ ∀ k, ρ k x ∈ W

attribute [instance] KAct.ng KAct.ns

def RightEq {ε : Fin n → Bool} {X : GMod n} (A : KAct ε X) {I : Type} (c : CoefFam X I) : Prop :=
  ∀ i v (g : S7.UJ ε) (k : S7.KG ε), c i v (S7.toM g * S7.toMK k) = c i (A.ρ k v) (S7.toM g)

end CompanionTheory.RgExh.Dec.L.WyKR
