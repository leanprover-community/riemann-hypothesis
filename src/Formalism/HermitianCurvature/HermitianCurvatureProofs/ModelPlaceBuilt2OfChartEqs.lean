module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEllRegW
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRSSnRep
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelPlaceBuilt2OfPublished
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

namespace Formalism.FourierDecayAlt.P.CutMP

theorem jfSmoothBuilt_of_chartEqs (hE : SmoothTransferRegularity.ChartEqs) : JfSmoothBuilt :=
  SmoothTransferRegularity.jfSmoothBuilt_of_chart hE SmoothTransferRegularity.elliptic_regularity_weighted

theorem modelPlaceBuilt2_of_chartEqs (hE : SmoothTransferRegularity.ChartEqs) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_jf (jfSmoothBuilt_of_chartEqs hE)

end Formalism.FourierDecayAlt.P.CutMP
