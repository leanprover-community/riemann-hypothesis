module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Development.AbelianVarietyTheory.Definitions.Foundations.Mdl
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.Kd.K4

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def LUnH (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) (m : ℕ) (f : X.K) : Prop :=
  f ≠ 0 ∧ f ∈ lev X H ∧ ∀ W : ValuationSubring X.K, X.OverY W → ∃ c ∈ lev X H, c ≠ 0 ∧ W.valuation (f / c ^ m) = 1

def InvH (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) (m : ℕ) (a : X.Kˣ) : Prop :=
  ∀ γ ∈ H, ∃ h : X.Kˣ, X.sl (ofSL γ) (a : X.K) = a * (h : X.K) ^ m

def IsTr (H Γ : Subgroup SL(2, ℤ)) {ι : Type} (γ : ι → SL(2, ℤ)) : Prop :=
  (∀ i, γ i ∈ Γ) ∧ ∀ δ ∈ Γ, ∃! i, δ * (γ i)⁻¹ ∈ H

def sec (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w : ℕ) (lam : Fin 2 → ℤ) (a : X.Khat l) : X.Fn l :=
  fun u => ((lam 0 : ℤ_[l]) * u 0 + (lam 1 : ℤ_[l]) * u 1) ^ w • a

def trH (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w : ℕ) {ι : Type} [Fintype ι] (γ : ι → SL(2, ℤ)) (lam : Fin 2 → ℤ)
    (a : X.Khat l) : X.Fn l :=
  ∑ i, X.act l (γ i : Matrix (Fin 2) (Fin 2) ℤ) (sec X l w lam a)

end UpperTheory.Kd.K4

end
