module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
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

namespace GlobalTheory.ThBe0

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable {l : ℕ} [Fact l.Prime]

def lg {κ : Type} (k : κ) : MvPowerSeries κ ℂ_[l] :=
  PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries κ ℂ_[l]) (logF l)

structure IsFrob (σ : ℂ_[l] →+* ℂ_[l]) : Prop where
  norm_eq : ∀ x, ‖σ x‖ = ‖x‖
  lift : ∀ x ∈ Wp l, ∃ y ∈ Wp l, σ x = x ^ l + (l : ℂ_[l]) * y

def at2 {κ : Type} (b0 : MvPowerSeries (Fin 2) ℂ_[l]) (x y : MvPowerSeries κ ℂ_[l]) : MvPowerSeries κ ℂ_[l] :=
  MvPowerSeries.subst (fun i : Fin 2 => if i = 0 then x else y) b0

structure IsBe0 (σ : ℂ_[l] →+* ℂ_[l]) (b0 : MvPowerSeries (Fin 2) ℂ_[l]) : Prop where
  coef : CoefWf b0
  axes : ∀ n, MvPowerSeries.coeff n b0 ≠ 0 → n 0 ≠ 0 ∧ n 1 ≠ 0
  add₁ : SimeqW (at2 b0 (lg 0 + lg 1) (lg 2) : MvPowerSeries (Fin 3) ℂ_[l]) (at2 b0 (lg 0) (lg 2) + at2 b0 (lg 1) (lg 2))
  add₂ : SimeqW (at2 b0 (lg 0) (lg 1 + lg 2) : MvPowerSeries (Fin 3) ℂ_[l]) (at2 b0 (lg 0) (lg 1) + at2 b0 (lg 0) (lg 2))
  conj : ∀ α ∈ Wp l, σ (σ α) = α →
    SimeqW (at2 b0 (MvPowerSeries.C α * lg 0) (lg 1) : MvPowerSeries (Fin 2) ℂ_[l]) (at2 b0 (lg 0) (MvPowerSeries.C (σ α) * lg 1))

structure DualOm (σ : ℂ_[l] →+* ℂ_[l]) (d : ℕ) {ρ : Type} [Fintype ρ] [DecidableEq ρ] (om om' : ρ → ℂ_[l]) : Prop where
  card : 2 * Fintype.card ρ = d
  mem : ∀ r, om r ∈ Wp l ∧ om' r ∈ Wp l
  fix : ∀ r, (σ ^ d) (om r) = om r ∧ (σ ^ d) (om' r) = om' r
  dual : ∀ r r', ∑ i ∈ Finset.range (d / 2), (σ ^ (2 * i)) (om r * om' r') = if r = r' then 1 else 0

def zOm (σ : ℂ_[l] →+* ℂ_[l]) {d : ℕ} {ρ : Type} [Fintype ρ] (om om' : ρ → ℂ_[l]) (s : ZMod d) : MvPowerSeries (ρ ⊕ ρ) ℂ_[l] :=
  if Even s.val then ∑ r, MvPowerSeries.C ((σ ^ s.val) (om r)) * lg (Sum.inl r)
  else ∑ r, MvPowerSeries.C ((σ ^ s.val) (om' r)) * lg (Sum.inr r)

end GlobalTheory.ThBe0
