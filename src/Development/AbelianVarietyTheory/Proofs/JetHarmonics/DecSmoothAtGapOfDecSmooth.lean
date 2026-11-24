module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SideNormalisedGap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SigmaFiniteOfPosLintegralNeTop
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.SideCompare

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open PI.UpqRep (IsDSHpk IsLowUnitH IsHCTypeW IsKFinHpk IsCayleyU InLieHpk lowKSub smoothVecs dsigW)
open Formalism.QuantumDeterminants (Mt UH Hpk Nset UWset inWb Tz IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)
open PI.BesselPeriodGGP (IsHaarOn IsQuotMeas)
open Formalism.FourierDecayAlt GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap (Mat decExp decConst dimV dimN thrG thrS thrSS propExp DecGap Size Thresholds muS mulP IsSide
  IsSideNormalised KFinDecay wordSeminorm DecKFin DecSmooth)

theorem sigmaFinite_of_isQuotMeas {k r : ℕ} {μG μS ν : Measure (Mt k r)} [SigmaFinite μG] [SFinite μS]
    (hS : μS ≠ 0) (hq : IsQuotMeas μG μS ν) : SigmaFinite ν := by
  first
  | (rename_i h_5 h_6; revert k r μG μS ν h_5 h_6 hS hq; exact @_root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas)
  | exact @_root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas
  | exact _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas
  | (apply _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas ..)

theorem muS_ne_zero {k r : ℕ} {μW μN : Measure (Mt k r)} [SFinite μN] (hW : μW ≠ 0) (hN : μN ≠ 0) :
    muS μW μN ≠ 0 := by
  rw [← Measure.measure_univ_ne_zero] at *
  unfold muS
  rw [Measure.map_apply SideNormalisedGap.measurable_mulP MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ,
    Measure.prod_prod]
  exact mul_ne_zero hW hN

section Side

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
  (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
  (σ : Mat k r → (H →L[ℂ] H)) (w₀ : H) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ)
  (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN μG ν : Measure (Mt k r))

end Side

section Decay

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end Decay

end GlobalTheory.SideCompare
