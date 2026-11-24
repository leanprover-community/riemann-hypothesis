module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisTransitionMatricesInverse
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.quasiLogarithmBasis_transitionMatrices_inverse : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q), IsBasis μ e → IsBasis μ f → ∀ (P : ι → κ → B) (P' : κ → ι → B), (∀ i, In (⊤ : Ideal B) (e i - comb (P i) f)) → (∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) → Matrix.of P * Matrix.of P' = 1 ∧ Matrix.of P' * Matrix.of P = 1 := by
  first | exact @GlobalTheory.BasisTrans.trans_inverse | exact GlobalTheory.BasisTrans.trans_inverse | (intros; apply GlobalTheory.BasisTrans.trans_inverse <;> assumption)
