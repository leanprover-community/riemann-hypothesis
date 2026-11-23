module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionAbsSumBoundOfTwoRowBounds
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.collisionAbsSum_bound_of_two_rowBounds : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ CT C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → CT ≤ C → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), thr ≤ C' → thr ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv → TieAt hF hI large₂ u T Z → UnitaryVolumeMass.FormAt D u → BridgeLemma.RowsND T Z C → BridgeLemma.RowsDeg T Z C → CollS Y u := by
  first | exact @GlobalTheory.Core.Deg.collS_of_rowBounds | exact GlobalTheory.Core.Deg.collS_of_rowBounds | (intros; apply GlobalTheory.Core.Deg.collS_of_rowBounds <;> assumption)
