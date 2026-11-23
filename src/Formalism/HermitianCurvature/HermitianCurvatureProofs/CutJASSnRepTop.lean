module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConstS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLines
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSEntry
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSPointwise
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCoreAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepPolyFinish
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConstAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConstAsmS
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

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem thConst_of_open (hMC : Core.TC.ModConst) (hLN : Core.TC.LineNonzero)
    (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : Core.ThConst := by
  rcases hPoly with h | h
  · exact Core.TC.theta_constancy_assembly h hMC hLN Core.TC.polynomial_finish_holds
  · exact Core.TC.theta_constancy_assembly_scalar h hMC hLN Core.TC.polynomial_finish_holds

theorem ssnRep_of_open (hPE : PRho.PRhoExists) (hTF : ThtFacts) (hMC : Core.TC.ModConst)
    (hLN : Core.TC.LineNonzero) (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : SSnRep :=
  second_shift_representation_assembly hPE Formalism.FourierDecayAlt.P.CutMP.JA.gauge_lines_holds hTF datum_unit_norm_holds
    (Core.theta_gauge_constancy_holds Formalism.FourierDecayAlt.P.CutMP.JA.quadratic_second_shift_form Formalism.FourierDecayAlt.P.CutMP.JA.second_shift_pointwise_holds
      (thConst_of_open hMC hLN hPoly) Formalism.FourierDecayAlt.P.CutMP.JA.second_shift_entry_holds hPE Formalism.FourierDecayAlt.P.CutMP.JA.gauge_lines_holds
      datum_unit_norm_holds)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
