module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHI
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ArchPosHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibInf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DetAdm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.EventuallyStruct
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExChar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExFDStabFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExOmTOfSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabOrb
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibDis
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensCnt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHH
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensIdxF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensQ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolDone
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocPosV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosTest
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SWeqOm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SdDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SdTestInf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoMuInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoNuFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnfoldFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWOf
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

namespace PI.VolStabS.Assembly

open PI.VolStabS

theorem fibPin_closed : FibPin := fibPin_holds

theorem sWeqOm_closed : SWeqOm := sWeqOm_of densFibInf_holds densFibV_holds

theorem sdUniq_closed : SdUniq :=
  sdUniq_of_inf sdTestInf_holds

theorem exOmT_holds : ExOmT :=
  exOmT_of_open (fibInfEx_of DiscreteGroups.fibOfDens_holds tensAll_holds densInf_holds)
    (fibVEx_of DiscreteGroups.fibOfDens_holds tensAll_holds densV_holds) sdUniq_closed restrProd_holds

theorem nuInv_holds : NuInv := nuInv_of_pin detAdm_holds compG_holds fibPin_closed sdUniq_closed

theorem volStabFromSW_of_nuNe (hN : NuNeZero) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of exChar_holds exOmT_holds (exStab_of_nu nuInv_holds nuFin_holds hN)
    exFDStab_holds sWeqOm_closed unfold_holds posTest_holds

theorem volStabFromSW_of_open_dens (hDA : DensAA) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_nuNe (nuNeZero_of_dens archPos_holds locPos_holds hDA qvSum_holds)

theorem volStabFromSW_of_open_aa (hV : VolAA) (hH : HensAA) (hI : IdxH) (hC : CntAA) :
    PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_dens (densAA_of_open hV hH hI hC)

theorem volStabFromSW_of_open_vic (hV : VolAA) (hI : IdxH) (hC : CntAA) :
    PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_aa hV hensAA_holds hI hC

theorem volStabFromSW_of_open_ic (hI : IdxH) (hC : CntAA) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_vic volAA_holds hI hC

theorem volStabFromSW_of_cntAA (hC : CntAA) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_ic idxH_holds hC

theorem volStabFromSW_holds : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_cntAA cntAA_holds

end PI.VolStabS.Assembly
