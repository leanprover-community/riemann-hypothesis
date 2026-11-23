module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittFlags
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FrameOpFull
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

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopsFinal

namespace Formalism.L2.SG.Pf.LoopBFrame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF))

theorem rowLat_fl' {u u' : D.what₂.Word} (t : D.s.Term u u') :
    IsRowLat D (fl'Of W hI t).fl (lamOf W hI t) := by
  have hR := rowLat_map (Formalism.L2.SG.Pf.WittFlags.LatIso_holds D) (W.δ u) (W.isom u) (X.Fu u) _ (rowLat_tc hI t)
  have hFx := fixedC W hI (Formalism.L2.SG.Pf.WittFlags.LatIso_holds D) t
  obtain ⟨hLift, -, hOK⟩ := pdC W hI t
  exact ⟨hR.1, ⟨hFx.1, hFx.2.1, ⟨hLift.1, rfl⟩, hOK.1⟩, hOK.2⟩

theorem frameChangeAt_holds : FrameChangeAt W hI := by
  intro u u' t ξ hl hd
  obtain ⟨n, hn, hnf⟩ := Formalism.L2.S.Pv.ClassCounting.frameOpFull D u' (fl'Of W hI t).fl (lamOf W hI t) (rowLat_fl' W hI t) ξ hl hd
  exact ⟨n, hn, fun b => hnf b⟩

theorem frameChangeC_holds : FrameChangeC := fun _ _ _ _ hI W => frameChangeAt_holds W hI

end Formalism.L2.SG.Pf.LoopBFrame
