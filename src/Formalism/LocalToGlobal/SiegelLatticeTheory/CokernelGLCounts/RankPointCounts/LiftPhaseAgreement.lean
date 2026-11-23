module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClassFrameNormal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormRepX
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FinitePhaseSimp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PhaseLiftCell
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.LiftedPhaseAgreement

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

theorem liftAtSomeC_holds : Formalism.L2.SG.Pf.RowForm.LiftAtSomeC X Y u u' κ := by
  intro R ρ s hs
  have hA := Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u' s.1.toTerm
  have hG : s.1.toTerm.G ≠ 0 := by
    intro h
    apply s.2.1
    show Formalism.L2.SG.TermOp.Gt s.1 = 0
    simp [Formalism.L2.SG.TermOp.Gt, Formalism.L2.SG.TermOp.GTerm.G, h]
  exact hA hG hs

theorem phaseTieC_holds (hP : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) :
    Formalism.L2.SG.Pf.RowForm.PhaseTieC X Y u u' κ :=
  Formalism.L2.SG.Pf.PhaseLiftCell.phaseAgreement_of_lift X Y u u' κ (liftAtSomeC_holds X Y u u' κ)
    (Formalism.L2.SG.Pf.FinitePhaseConjugation.finPhaseC_of (hNR := Formalism.L2.SG.Pf.normRepExists_of
      (Formalism.L2.SG.Pf.NormRepX.norm_representative_holds D u u' hP) (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u))
      (h1 := liftAtSomeC_holds X Y u u' κ))

end Formalism.L2.SG.Pf.LiftedPhaseAgreement
