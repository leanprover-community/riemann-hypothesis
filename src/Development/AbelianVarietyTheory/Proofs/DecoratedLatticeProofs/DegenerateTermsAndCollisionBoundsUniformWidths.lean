module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CntOnSingleton
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollSOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankTwoCountBoundsOfRowCountBoundsUniform
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTermLoopOfStandingHypotheses
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowAmplitudeBoundsUniformSingletonWidthStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VanishingGramBoundUniformWindowAndParams
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VanishingGramBoundWindowOfTermPairTypeBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InputsOfSubsetWidths
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsPosTypeP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallOnUnivUnconditional
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
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem degenerate_and_collisions_uncond : (∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ ∀ c : ℝ, On {c} CollS := by
  have hSM : Formalism.HermitianLatticesTheory.SiegelMassRatio := GlobalTheory.Mass.siegelMassRatio_holds
  have hS : ∀ c : ℝ, SmallOn {c} := fun c =>
    (inputs_of_subset_widths {c} Set.univ (Set.subset_univ _)).2.1 smallOn_univ_unconditional
  have hP : GlobalTheory.TypeAsm.TypeP := GlobalTheory.rowsPos_typeP
  refine ⟨vanishingGramBound_uniformWindow_and_weightData.1 (vanishingGramBoundWindow_of_termPairTypeBound hP), fun c => ?_⟩
  exact collS_on hSM {c} (GlobalTheory.T.rowAmplitudeBoundsUniform_singleton_width c) (corankTwoCountBounds_of_rowCountBoundsUniform {c} (cntOn_singleton hSM c)) (hS c)
    (tieOn_singleton_uncond c)

end GlobalTheory.Core.Deg
