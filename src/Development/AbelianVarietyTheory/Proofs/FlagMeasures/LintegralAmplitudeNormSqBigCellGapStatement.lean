module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralAmplitudeNormSqBigCellGap
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.lintegral_amplitudeNormSq_bigCell_gap : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ (k r : ℕ) (L : LocBessel k r) (μG : Measure (Mt k r)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 2 ≤ k → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsSection k r L.z L.z' μsec → ∃ c : ℝ, 0 < c ∧ ∀ (R : Rep k r) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (w : R.H), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') q * hsNormSq (amp R l l' w μG (bigCell k r q.1 (μsec q.2)))) = ENNReal.ofReal (c / PI.BesselPeriodGGP.fdegH μG R.σ w ^ 3) := by
  first | exact @GlobalTheory.AmpNormGap.lintegral_hsNormSq_amp_gap | exact GlobalTheory.AmpNormGap.lintegral_hsNormSq_amp_gap | (intros; apply GlobalTheory.AmpNormGap.lintegral_hsNormSq_amp_gap <;> assumption)
