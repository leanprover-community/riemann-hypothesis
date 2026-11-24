module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermHasRealRelativePoint
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

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.relevant_term_has_real_relative_point : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ, ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) p := by
  first | exact @GlobalTheory.RelPtLift.relPt_lift | exact GlobalTheory.RelPtLift.relPt_lift | (intros; apply GlobalTheory.RelPtLift.relPt_lift <;> assumption)
