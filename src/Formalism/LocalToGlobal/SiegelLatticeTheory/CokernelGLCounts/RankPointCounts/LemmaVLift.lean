module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClassFrameCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiTrivOut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
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

noncomputable section

namespace Formalism.L2.SG.Pf.LiftCellVolume

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

theorem lemmaVLiftC_of (hRC : Formalism.L2.SG.TermOp.Vanish.RCocompactC) {D : D7} (X : HidaSetting D)
    (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) :
    Formalism.L2.SG.Pf.RowForm.LemmaVLiftC X Y u u' κ := by
  intro R ρ s hs
  exact Formalism.L2.SG.TermOp.Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds
    Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Pf.chiTrivialC_outright Formalism.L2.SG.Pf.psiInfChar_holds
    Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds hRC Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y s.1 hs

theorem LemmaVLiftC_holds {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) :
    Formalism.L2.SG.Pf.RowForm.LemmaVLiftC X Y u u' κ :=
  lemmaVLiftC_of Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds X Y u u' κ

end Formalism.L2.SG.Pf.LiftCellVolume
