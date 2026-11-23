module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCFamLocal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCGenToQQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCModelLocal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCRadSpSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCSecMove
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGQLFam
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGRawSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSectionStab
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

theorem gCore_of_genTransfer (hGT : GenTransfer) : GCore :=
  gauge_construction_of_truncation gauge_section_exists section_move_holds family_locality_holds hGT generator_to_quadratic_form model_locality_holds
    radial_space_smoothness Formalism.FourierDecayAlt.P.CutMP.Gauge.raw_gauge_smoothness_holds Formalism.FourierDecayAlt.P.CutMP.Gauge.quadratic_local_family_holds assumption_on_sections_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
