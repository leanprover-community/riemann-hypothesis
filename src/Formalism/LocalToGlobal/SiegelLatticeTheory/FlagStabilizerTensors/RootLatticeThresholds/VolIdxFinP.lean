module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.AtNormRep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.DeltaAE
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Development
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.DiagMulOfBt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.InvMulMemOfScaledEntriesCongr
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexAStable
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBBounded
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBCongruence
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBStable
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfCong
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermAttrConst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.TermStableHolds
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

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.VolPinAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hyps_of {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (hPH : PrimeHyp D u (Tu D u')) :
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.Hyps D u u' (X.Fu u) (Y.what₂ u) := by
  refine ⟨PI.TCS.termStable_holds D u u', Formalism.L2.SG.Pf.term_equivalence_iff D u u', term_function_const D u u',
    hPH, D.sp.Y_sig 0, Y.rowsOK u⟩

theorem volIdxFinP (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (hPH : PrimeHyp D u (Tu D u')) :
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.VolumeIndexFiniteNonzero D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M := Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_finite_of_hyps D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M (hyps_of Y u u' hPH)
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.commens Formalism.L2.SG.Pf.StabilizerIndexVolumes.stClosed (Formalism.L2.SG.Pf.StabilizerIndexVolumes.deltaAE_holds D _ _)
    (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_a_stable D u u' _ _ _ _) (Formalism.L2.SG.Pf.StabIntCong.aBddOf u u' _ _ _ _)
    (Formalism.L2.SG.Pf.StabIntCong.aCong u u' _ _ _ _) (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_stable D u u' _ _ _ _)
    (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_bounded D u u' _ _ _ _) (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_congruence D u u' _ _ _ _)

theorem volume_generic_odd_of_rep (hD : DictC) (hC : CovolOne3C) : Formalism.L2.SG.VolPin.VolumeOddGeneric := by
  refine volume_generic_odd_of hD hC (fun D X Y u u' hPH t w F' L U hrel hgen hNR hG => ?_)
    (fun D X Y u u' h => volIdxFinP D X Y u u' h)
  exact Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_stable D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M Formalism.L2.SG.Pf.StabilizerIndexVolumes.stClosed
    (hyps_of Y u u' hPH) Y.agree t.toTerm w F' L U hrel hgen hNR hG

end Formalism.L2.SG.Pf.VolPinAsm
