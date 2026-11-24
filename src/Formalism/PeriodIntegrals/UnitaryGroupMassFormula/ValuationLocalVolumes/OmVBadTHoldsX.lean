module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiffProd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVSt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVTop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OmegaUnramifiedHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LocalOmegaVolumeUnique
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertBHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfFfX
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVMemEFHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVPrimOfDdX
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVScaleHoldsX
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HostStarConj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.InclRMemOEv

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVLocU_holds : OmVLocU X ψ := fun v a Y =>
  PI.OmLocU.Done.omLocU_closed X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) a Y

theorem omVBadT_holdsX : Formalism.L2.SG.Pf.NcX.OmVSt.OmVBadT X u' ψ :=
  PI.OmVg.omVBadT_of_ffX X u' ψ (Formalism.L2.SG.Pf.NcX.OmVSt.omega_standard_holds X ψ) (Formalism.L2.SG.Pf.NcX.OmVSt.omega_lattice_holds X)
    (OmW.omVGram_holds X u') PI.OmVe.Top.fFInertB_holds PI.OmVe.Top.fFSplitB_holds

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ

namespace Formalism.L2.SG.Pf.NcX.OmVSt


variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVZGram : OmVGram X u' := Formalism.L2.SG.Pf.NcVal.OmVSt.OmW.omVGram_holds X u'

theorem omVZDet : OmVDet X u' := Formalism.L2.SG.Pf.NcVal.OmVSt.OmW.omVDet_holds X u'

theorem omVZLocU : OmVLocU X ψ := Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ.omVLocU_holds X ψ

theorem omVZ_holdsX : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ :=
  omV_of X u' ψ (omega_standard_holds X ψ) (omega_lattice_holds X) (Formalism.L2.SG.Pf.NcVal.OmVSt.OmX.omVSD_holdsX X)
    (omega_unramified_holds X) (Formalism.L2.SG.Pf.NcVal.OmVSt.OmX.omVPrim_holdsX X u') (omVZGram X u') (omVZDet X u')
    (Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc.omVScale_holdsX X u' ψ) (Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ.omVBadT_holdsX X u' ψ)
    (omVZLocU X ψ)

end Formalism.L2.SG.Pf.NcX.OmVSt

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ


theorem omV_holdsX {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ :=
  Formalism.L2.SG.Pf.NcX.OmVSt.omVZ_holdsX X u' ψ

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ
