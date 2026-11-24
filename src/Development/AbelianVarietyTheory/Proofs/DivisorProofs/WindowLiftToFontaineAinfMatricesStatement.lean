module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WindowLiftToFontaineAinfMatrices
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

theorem _root_.GlobalTheory.T.window_lift_to_fontaineAinf_matrices : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B), IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin h) (Fin h) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → ∃ (Fa : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)) (Ga : Matrix (Fin h) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) ∧ Fa = Ψ * Fa.map (phiInv p O) ∧ Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) ∧ (∀ i m, WittVector.fontaineTheta O p (Fa i m) = F.θ (Y i m)) ∧ ∀ m i, WittVector.fontaineTheta O p (Ga m i) = F.θ (Gm m i) := by
  first | exact @GlobalTheory.WinLift.Top.window_lift | exact GlobalTheory.WinLift.Top.window_lift | (intros; apply GlobalTheory.WinLift.Top.window_lift <;> assumption)
