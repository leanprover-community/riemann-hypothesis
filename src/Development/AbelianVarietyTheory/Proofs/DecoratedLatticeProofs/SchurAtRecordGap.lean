module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmplitudeSchurBoundUniformConstantsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ElementarySizeBoundsOfSizeHypothesesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeMultOneDecayOfLargeGapHypothesesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBessel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypOfUniqGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SchurAlongFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Amp

theorem schur_at_record_gap : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → VanishingOnXAndXPlusBranching.adm11 D large₂ C' Cl Cg cb Cu cT CT C0 1 C := by
  intro Cg cb Cu cT CT C0
  have hH : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  obtain ⟨C₀, hC⟩ := GlobalTheory.T.amplitudeSchurBound_uniform_constants Cg cb Cu cT CT 1
  obtain ⟨m₀, hm⟩ := hC C₀ le_rfl
  obtain ⟨m₁, hL⟩ := GlobalTheory.T.amplitudeMultOneDecay_of_largeGapHypotheses hH Cg cb Cu cT CT C0
  obtain ⟨thr, hthr⟩ := GlobalTheory.T.size_bounds_of_standingHypotheses (max (max m₀ m₁) 1)
  refine ⟨C₀, thr, fun D large₂ C' Cl h1 h2 hT => ?_⟩
  intro hZ
  obtain ⟨h1000, -, hmM, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT h1 h2 hZ.1
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := le_trans (le_max_right _ _) hmM
  have hCm : 1 ≤ Cl * (D.R.m : ℝ) := by nlinarith
  have hBig : ∀ m' : ℝ, m' ≤ max (max m₀ m₁) 1 → Big D large₂ Cl m' :=
    fun m' hm' => ⟨hrd, hCm, le_trans hm' hmM⟩
  exact hm D large₂ C' Cl C0 (hBig m₀ (le_trans (le_max_left _ _) (le_max_left _ _))) hT.cdScale_tie
    (GlobalTheory.GapAmp.bessel_schur_gap hH D large₂ C' Cl Cg cb Cu cT CT C0 h1000)
    (hL D large₂ C' Cl (hBig m₁ (le_trans (le_max_right _ _) (le_max_left _ _)))) hZ

end GlobalTheory.Amp
