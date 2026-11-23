module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Imports
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsAlt
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormBirational
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormExists
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimComponent
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimOfChowForm
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PFGNullstellensatz
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PGenericLinearTrdeg
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealDim
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealPrime
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncidenceGeneric
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PLengthQuotientDet
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PMinimalPrimeHomog
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.POrdPolynomialLocalization
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PProjNullstellensatz
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem FGNullstellensatz.full : FGNullstellensatz.Statement :=
  FGNullstellensatz.proof

theorem ProjNullstellensatz.full : ProjNullstellensatz.Statement :=
  ProjNullstellensatz.proof FGNullstellensatz.full

theorem IncidenceGeneric.full : IncidenceGeneric.Statement :=
  IncidenceGeneric.proof FGNullstellensatz.full

theorem IncIdealPrime.full : IncIdealPrime.Statement :=
  IncIdealPrime.proof IncidenceGeneric.full

theorem ChowFormMultiHomog.full : ChowFormMultiHomog.Statement :=
  ChowFormMultiHomog.proof ProjNullstellensatz.full

theorem GenericLinearTrdeg.full : GenericLinearTrdeg.Statement :=
  GenericLinearTrdeg.proof

theorem MinimalPrimeHomog.full : MinimalPrimeHomog.Statement :=
  MinimalPrimeHomog.proof

theorem ConeDimComponent.full : ConeDimComponent.Statement :=
  ConeDimComponent.proof MinimalPrimeHomog.full

theorem LengthQuotientDet.full : LengthQuotientDet.Statement :=
  LengthQuotientDet.proof

theorem OrdPolynomialLocalization.full : OrdPolynomialLocalization.Statement :=
  OrdPolynomialLocalization.proof

theorem ChowFormBirational.full : ChowFormBirational.Statement :=
  ChowFormBirational.proof IncidenceGeneric.full ChowFormMultiHomog.full

theorem IncIdealDim.of_affineChartTrdeg (hA : AffineChartTrdeg.Statement) :
    IncIdealDim.Statement :=
  IncIdealDim.proof IncidenceGeneric.full GenericLinearTrdeg.full hA

theorem ConeDimOfChowForm.of_affineChartTrdeg (hA : AffineChartTrdeg.Statement) :
    ConeDimOfChowForm.Statement :=
  ConeDimOfChowForm.proof (IncIdealDim.of_affineChartTrdeg hA) IncIdealPrime.full

theorem ChowFormExists.of_affineChartTrdeg (hA : AffineChartTrdeg.Statement) :
    ChowFormExists.Statement :=
  ChowFormExists.proof (IncIdealDim.of_affineChartTrdeg hA) IncIdealPrime.full

end GroundTheory.Heights₂.Heights
