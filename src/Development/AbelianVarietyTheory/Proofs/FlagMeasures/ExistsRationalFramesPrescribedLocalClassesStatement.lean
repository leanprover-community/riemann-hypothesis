module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRationalFramesPrescribedLocalClasses
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rational_frames_prescribed_local_classes : ∀ (D : D7) (Z : LocDat D) (u u' : D.what₂.Word) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (P : Finset (PlF D)) (f f' : ∀ p : PlF D, Fin (D.R.rS + 1) → Vp D p), (∀ p ∈ P, Tri (D.s.atP p).Ep (scaled Z p (frame F)) (f p) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F')) (f' p)) → ∃ (G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), StdOff Z P F G F' G' ∧ ∀ p ∈ P, ∃ A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, Uni A ∧ Uni A' ∧ (∀ a b, A a b ∈ (Z.M p).L.O ∧ A' a b ∈ (Z.M p).L.O ∧ A a b - A' a b ∈ Submodule.span (Z.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (LocNG.theta (Z.M p))}) ∧ Chg (f p) A (scaled Z p (frame G)) ∧ Chg (f' p) A' (scaled Z p (frame G')) := by
  first | exact @GlobalTheory.FrameChoice.choose_frames | exact GlobalTheory.FrameChoice.choose_frames | (intros; apply GlobalTheory.FrameChoice.choose_frames <;> assumption)
