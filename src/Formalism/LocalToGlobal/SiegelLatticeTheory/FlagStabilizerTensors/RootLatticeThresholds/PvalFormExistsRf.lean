module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KernelOfEmbedding
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActRow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AmpIota
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PairAmpConstOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PvalFormExistsAlt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PvalFormExistsOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormChiNBi
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

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X}

theorem pairAmpConst_holds (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y)
    (hOI : ∀ w w', OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w')) : PairAmpConst Y :=
  pairAmpConst_of (fun w => Formalism.L2.SG.Closed.NeatKu_holds X w Y.hK) hRF Formalism.L2.SG.Pf.iotaRepC_holds
    Formalism.L2.SG.Pf.ampRepNC_holds (fun _ X => chi_n_bilinear X) hOI

variable {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF))

theorem pvalForm_exists_rf (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y)
    (hOI : ∀ w w', OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w')) (hN : FibreCountEq hF) :
    ∃ A : AmpDat X, PvalForm W hI A :=
  pvalForm_exists' W hI (AmpCov_holds Y) (pairAmpConst_holds hRF hOI) hN

theorem rowFree_holds : Formalism.L2.SG.Pf.FibreCounting.RowFree Y :=
  Formalism.L2.SG.Pf.Act.rowFree_of (fun w => Formalism.L2.SG.Closed.NeatKu_holds X w Y.hK) Formalism.L2.SG.Pf.iotaRepC_holds

theorem pvalForm_exists_oi (hOI : ∀ w w', OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w'))
    (hN : FibreCountEq hF) : ∃ A : AmpDat X, PvalForm W hI A :=
  pvalForm_exists_rf W hI rowFree_holds hOI hN

end Formalism.L2.SG.Pf.KernelOfEmbedding
