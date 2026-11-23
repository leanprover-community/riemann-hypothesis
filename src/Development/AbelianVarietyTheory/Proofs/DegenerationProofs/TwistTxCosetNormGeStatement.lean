module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxCosetNormGe
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

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.twist_tx_coset_norm_ge_alt : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N : NumD C) (k : ℕ) (β : N.Form k) (u r : Cˣ) (qf : QuadraticMap ℤ N.X ℝ) (n g j : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → 1 ≤ j → ‖(u : C)‖ < 1 → r ^ ((n ^ j) ^ 2) = u → (N.twist β u).Int qf → (∀ y, qf y = -Real.log ‖(u : C)‖ * ((β.be y y : ℝ) / 2)) → N.Tors n g → ∀ (La : Type) [AddCommGroup La] (q : La → N.QT ((n ^ j) ^ 2)), (∀ a : La, n • a = 0 → a = 0) → (∀ a b, N.QEq (q a * q b) (q (a + b))) → (∀ a b, N.QEq (q a) (q b) ↔ ∃ e, a = b + (n ^ j) ^ 2 • e) → (∀ p, ∃ a, N.QEq (q a) p) → ∀ p : La → (N.twist β u).QT ((n ^ j) ^ 2), (∀ x, TwRel β u r (q x) (p x)) → (∃ x, 1 ≤ ‖(N.twist β u).tx (n ^ j) (p x)‖) ∧ ∀ x, ∃ h, ‖(u : C)‖ ^ (β.be (q x).1.1.toAdd (q x).1.1.toAdd).toNat ≤ ‖(N.twist β u).tx (n ^ j) (p (x + n ^ (j - 1) • h))‖ := by
  first | exact @GlobalTheory.twist_tx_coset_norm_ge | exact GlobalTheory.twist_tx_coset_norm_ge | (intros; apply GlobalTheory.twist_tx_coset_norm_ge <;> assumption)
