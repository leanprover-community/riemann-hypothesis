module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
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

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FullLevel

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsSympLevel (D : Datum H) {k : Type} [Field k] {Q : Type} [Group Q] (act : 𝓞 E → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) (N : ℕ) (z : kˣ) (ev : D.La → Q) : Prop :=
  (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = act c (ev a)) ∧
    (∀ a, ev a = 1 ↔ ∃ b, a = N • b) ∧ (∀ x : Q, x ^ N = 1 ↔ ∃ a, ev a = x) ∧
    ∀ a b, e N (ev a) (ev b) (z ^ D.EF a b)

def Induces {D : Datum H} (l : Level H) {Q : Type} [Group Q] (etaA eta ev : D.La → Q) : Prop :=
  (∀ a, ev a ^ (l.M' / l.A) = etaA a) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ev a ^ (l.M' / l.M) = eta a

theorem A_dvd_M' (l : Level H) : l.A ∣ l.M' := Nat.dvd_lcm_right _ _

theorem M_dvd_M' (l : Level H) : l.M ∣ l.M' := Nat.dvd_lcm_left _ _

theorem M'_pos (l : Level H) : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos

end GlobalTheory.FullLevel
