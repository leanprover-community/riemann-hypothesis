module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TwistedMeasureMomentsEqShiftedSeriesJets
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.twisted_measure_moments_eq_shifted_series_jets : ∀ (q : ℕ) [Fact q.Prime] (S : ℂ_[q]⟦X⟧) (ζ : ℂ_[q]) (n k : ℕ), Bdd S → ζ ^ (q ^ n) = 1 → ∃ f : C(ℤ_[q], ℂ_[q]), (∀ a, f a = ζ ^ (PadicInt.toZModPow n a).val * zc a ^ k) ∧ HasSum (fun m : ℕ => coeff m S * (fwdDiff (1 : ℤ_[q]))^[m] f 0) (constantCoeff (DT^[k] (shiftS ζ S))) := by
  first | exact @GlobalTheory.MomOne.TwistMom.twisted_moments | exact GlobalTheory.MomOne.TwistMom.twisted_moments | (intros; apply GlobalTheory.MomOne.TwistMom.twisted_moments <;> assumption)
