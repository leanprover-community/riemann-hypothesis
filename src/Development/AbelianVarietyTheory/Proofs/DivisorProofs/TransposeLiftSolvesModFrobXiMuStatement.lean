module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeLiftSolvesModFrobXiMu
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.transpose_lift_solves_mod_frobXi_mu : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (G0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), (∀ i m, Sandwich.mu ε ∣ (V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius - (p : Ainf p O) • G0) i m) → (∀ j m, WittVector.fontaineTheta O p (G0 (Sum.inr j) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * G0 i m := by
  first | exact @GlobalTheory.WinLift.lift_solves_div_frob_xi_mu | exact GlobalTheory.WinLift.lift_solves_div_frob_xi_mu | (intros; apply GlobalTheory.WinLift.lift_solves_div_frob_xi_mu <;> assumption)
