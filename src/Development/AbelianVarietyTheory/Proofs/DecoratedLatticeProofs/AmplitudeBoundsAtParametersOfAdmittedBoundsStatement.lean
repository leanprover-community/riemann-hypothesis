module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.AbsPointwiseMonoConstant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmplitudeBoundsAtParamsOfAdmittedBounds
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

theorem _root_.GlobalTheory.T.ampAt_of_admitted_bounds : ∀ Cg CPT CDl hilbertNinetyConstant Ca CS : ℝ, 0 ≤ hilbertNinetyConstant → 0 ≤ Ca → ∃ C C2 Ch : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ Cpr δ : ℝ, 0 < δ → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl cb Cu cT CT C0 : ℝ), thr ≤ C' → thr ≤ Cl → 1 ≤ large₂.CGam → VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CPT → VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CDl → VanishingOnXAndXPlusBranching.adm5 D large₂ C' Cl Cg cb Cu cT CT C0 → VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 → DegreeRatioUnitShiftBound D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 hilbertNinetyConstant → AbsAllParameters D large₂ C' Cl Cg cb Cu cT CT C0 1 1 (max Cpr 0) Ca → VanishingOnXAndXPlusBranching.adm11 D large₂ C' Cl Cg cb Cu cT CT C0 1 CS → VanishingOnXAndXPlusBranching.adm12 D → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 Cpr C C2 Ch δ := by
  first | exact @GlobalTheory.ampAt_record_of_inputs | exact GlobalTheory.ampAt_record_of_inputs | (intros; apply GlobalTheory.ampAt_record_of_inputs <;> assumption)
