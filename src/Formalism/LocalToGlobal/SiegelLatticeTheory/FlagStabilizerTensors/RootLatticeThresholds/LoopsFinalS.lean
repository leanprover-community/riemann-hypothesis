module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FibreCountHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittExistsHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpFibreConstHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MemPerpMapFlag
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PairAmpConstWd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WRowPinHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittFlags
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AutLzFinite
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SplittingAdmissibleOfTermData
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsCut
  Formalism.L2.SG.LoopsFinal Formalism.L2.SG.LoopsEv Formalism.FourierDecayAlt

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ThrS

end ThrS

section Point

variable {D : D7} (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (hCT : ConcTie X Y)

def wOf : WittDat X := Classical.choice (Formalism.L2.SG.Pf.WittFlags.WittExists_holds D X)

theorem hOf : TieHyp (wOf X) hI :=
  { lat := Formalism.L2.SG.Pf.WittFlags.LatIso_holds D
    idG := fun u u' => identityCell_vanishes u u'
    atSome := fun u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds _ _ Y u u'
    autFin := fun u => Formalism.L2.SG.Pf.autFin_of (automorphism_lattice_finite D) (D.sp.Y_sig 0)
      (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u)
      (Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D ((wOf X).δ u) ((wOf X).isom u) (X.Fu u) (Y.what₂ u) (Y.rowsOK u))
    dim := fun u => Formalism.L2.SG.Pf.dimTie X u
    pairs := Formalism.L2.SG.Pf.pairTiesAll_holds _ _ Y hF (wOf X) hI }

def aOf : AmpDat X := Classical.choose (Formalism.L2.SG.Pf.KernelOfEmbedding.pvalForm_holds (wOf X) hI hCT.2.2.2.2.1)

end Point

section PointW

variable {D : D7} (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF))
  (hWD : Formalism.L2.SG.WuDecay.WuDecay X)

def aOfW : AmpDat X := Classical.choose (Formalism.L2.SG.Pf.KernelOfEmbedding.pvalForm_holds (wOf X) hI hWD)

theorem hvOfW : PvalForm (wOf X) hI (aOfW X Y hF hI hWD) :=
  Classical.choose_spec (Formalism.L2.SG.Pf.KernelOfEmbedding.pvalForm_holds (wOf X) hI hWD)

def atOfW : TermTie D := termTieOf (wOf X) hI (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD)

def ccOfW : ConcAt0 D (atOfW X Y hF hI hWD) :=
  ⟨X, Y, hF, hI,
    jtPin_of (wOf X) hI (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD)
      (Formalism.L2.SG.Pf.FibreCounting.AmpFibreConst_holds Y),
    Formalism.L2.SG.Pf.WittFlags.WRowPin_holds hF hI (wOf X) (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD),
    Formalism.L2.SG.Pf.FibreCounting.FibreCount_holds Y⟩

end PointW

end Formalism.L2.SG.LoopsTies
