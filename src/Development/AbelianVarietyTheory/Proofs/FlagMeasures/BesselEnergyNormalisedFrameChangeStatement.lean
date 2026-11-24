module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselEnergyNormalisedFrameChange
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

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselEnergy_normalised_frame_change : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN : ℝ) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), 1 ≤ k → IsStdOf L μsec Bs → IsRatioN k r cN → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → ∫⁻ p : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p * Formalism.MainNotions.S.hsNormSq (L.J F (bigCell k r p.1 (μsec p.2)))) = ENNReal.ofReal (lamN L cN ^ 4 / D.GamLev k r ‖cStd / L.c‖⁻¹ 1 0) * B.normSq Bs (conjF (cStd / L.c) F) := by
  first | exact @GlobalTheory.ThA.energy_change_of_frame | exact GlobalTheory.ThA.energy_change_of_frame | (intros; apply GlobalTheory.ThA.energy_change_of_frame <;> assumption)
