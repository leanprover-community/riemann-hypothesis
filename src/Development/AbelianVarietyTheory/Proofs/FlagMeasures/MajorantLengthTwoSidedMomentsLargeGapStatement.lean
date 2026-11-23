module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTwoSidedMomentsLargeGap
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.majorantLength_twoSidedMoments_largeGap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ CH : ℝ, 0 ≤ CH ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w (W : LocW D.R.k D.R.rS), GoodW D τ w w 1 W → ∀ A : LocS W, GoodS D (lamD D τ) A → ∀ q : ℕ, q ≤ D.R.k * D.R.m ^ 3 → MomBd W.z W.νS A.Φ q (large₂.sc.b ^ (CH * (D.R.m : ℝ))) ∧ ∀ a : Fin (D.R.rS + 1), ∫⁻ x, ENNReal.ofReal ((lA D.R.k D.R.rS W.z (Matrix.of x) a)⁻¹ ^ (2 * q)) * (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS ≤ ENNReal.ofReal ((large₂.sc.b ^ (CH * (D.R.m : ℝ))) ^ (2 * q)) * l2SG W.νS A.Φ := by
  first | exact @GlobalTheory.TwoSidedMomentsGap.two_sided_moments_gap | exact GlobalTheory.TwoSidedMomentsGap.two_sided_moments_gap | (intros; apply GlobalTheory.TwoSidedMomentsGap.two_sided_moments_gap <;> assumption)
