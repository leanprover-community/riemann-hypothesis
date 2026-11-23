module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqKFiniteOrbitalIntegralGapStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OpenCellAmplitudeNormEqConstDivDegreeLargeGapStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.CellConvergence
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
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.AmpFamGap

theorem cellConv : GlobalTheory.CellAmp.CellConv := Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence

theorem amplitudeNormDegree_along_family_of_kFiniteIdentity : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ thr : ℝ,
    ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT →
      VanishingOnXAndXPlusBranching.admF9 Fm Cg cb Cu cT CT C0 C1 := by
  intro hH hA Cg cb Cu cT CT C0 C1
  refine ⟨1000, fun eps Fm hC' hCl _ Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := GlobalTheory.T.openCellAmplitudeNorm_eq_const_div_degree_largeGap hH hA cellConv Cg cb Cu cT CT C0 C1 Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  refine ⟨x0, fun x hx i hZ => ?_⟩
  obtain ⟨-, hm0, -, -, hrd, -⟩ := hx0 x hx i
  have hm2 : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by
    have := (Fm.D x i).R.two_le_m
    exact_mod_cast (omega : 1 ≤ (Fm.D x i).R.m)
  have hbig : GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
    ⟨hrd, by nlinarith, hm0⟩
  exact hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) hCl hbig (Fm.ties x i).cdScale_tie hZ

theorem amplitudeNormDegree_along_family_largeGaps : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ thr : ℝ,
    ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT →
      VanishingOnXAndXPlusBranching.admF9 Fm Cg cb Cu cT CT C0 C1 := by
  intro _ hH _
  exact amplitudeNormDegree_along_family_of_kFiniteIdentity hH (GlobalTheory.T.amplitude_eq_kFiniteOrbitalIntegral_gap hH)

end GlobalTheory.AmpFamGap
