module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxEvEqMapArc
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.twist_tx_ev_eq_map_arc_alt : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (u : Cˣ), (u : C) = φ PowerSeries.X → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (β₀ : N₀.Form k) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = β₀.be y z) → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p₀ : N₀.QT (m ^ 2)) (p : N.QT (m ^ 2)), p.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p.1.2 → (N.twist β u).tx m (N.twQ β u hm p) = I.lam * φ (N₀.arcTx β₀.be m p₀) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q₀ : N₀.QT j) (q : N.QT j), j ≠ 0 → q.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q.1.2 → ∀ s : ℕ, (m : ℤ) ^ 2 * β₀.be q₀.1.1.toAdd q₀.1.1.toAdd ≤ s → (u : C) ^ s * (N.twist β u).ev m (N.twQ β u hm p) (N.twQ β u hj q).1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv β₀.be m p₀ q₀ s) := by
  first | exact @GlobalTheory.Ex.twist_tx_ev_eq_map_arc | exact GlobalTheory.Ex.twist_tx_ev_eq_map_arc | (intros; apply GlobalTheory.Ex.twist_tx_ev_eq_map_arc <;> assumption)
