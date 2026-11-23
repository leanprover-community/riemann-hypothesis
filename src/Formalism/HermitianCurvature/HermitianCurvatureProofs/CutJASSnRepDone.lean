module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConstS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThtFacts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDatumTransit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCLineNonzero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCModConst
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaugeConstructionHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SsnRepOfOpen2
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SRaiseSNorm
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

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

theorem modular_constancy_holds : ModConst :=
  modConst_of_cut line_nonvanishing_holds line_at_most_one_holds datum_transitivity_holds s_raise_section s_norm_section
    Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.theta_facts_hold

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem ssnRep_of_polyS (h : Core.TC.PolyRadialS) : SSnRep :=
  ssnRep_of_open2 rho_projection_existence Core.TC.MC.modular_constancy_holds Core.TC.line_nonvanishing_holds (Or.inr h)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_polyS (hJ : JfSmoothDS) (h : JA.SSn.Rep.Core.TC.PolyRadialS) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_SSnRep hJ (JA.SSn.Rep.ssnRep_of_polyS h)

end Formalism.FourierDecayAlt.P.CutMP
