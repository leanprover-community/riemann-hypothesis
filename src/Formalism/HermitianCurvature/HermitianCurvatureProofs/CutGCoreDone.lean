module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvTr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolRest
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLocal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefAn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnAnn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnReal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTKLine
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRConst
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRInt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRMove
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTopAct
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTrans
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferFn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddDone
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTSS
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gTCRefTrace_of_rotK (h : GTRRotK) : GTCRefTrace :=
  gTCRefTrace_of_cutK radial_gauge_move radial_gauge_constant_holds top_normal_form_of_curvature top_action_on_gauge_holds h radial_gauge_integrality_holds radial_gauge_transition_holds gauge_reality_holds

theorem gTCRef_of_rotK (h : GTRRotK) : GTCRef :=
  gTCRef_of_cut gauge_reality_holds curvature_identity_holds curvature_trace_holds (gTCRefTrace_of_rotK h) reference_annulus_holds

theorem gTConn_of_rotK (h : GTRRotK) : GTConn :=
  gTConn_of_leaves gauge_locality_holds gauge_reality_holds (gTCCurv_of_ref (gTCRef_of_rotK h)) (gTCHol_of_ref (gTCRef_of_rotK h)) annulus_condition_holds

theorem genTransfer_of_rotK (h : GTRRotK) : GenTransfer :=
  genTransfer_of_cut GT.gauge_function_holds gauge_kappa_holds (gTConn_of_rotK h) second_shift_gauge_holds

theorem gCore_of_rotK (h : GTRRotK) : GCore := gCore_of_genTransfer (genTransfer_of_rotK h)

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_rotK (hJ : JfSmoothDS) (hR : Gauge.GC.GTRRotK) (h : JA.SSn.SSnRep) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_ssnRep hJ (Gauge.GC.genTransfer_of_rotK hR) h

end Formalism.FourierDecayAlt.P.CutMP
