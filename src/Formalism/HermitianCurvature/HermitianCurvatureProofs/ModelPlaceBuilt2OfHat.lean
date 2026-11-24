module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddOp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDQQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDQQAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JAdjTrQQOfThree
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

theorem modelPlaceBuilt2_of_hat (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer)
    (hHat : JDHatOpQQ) (hBdd : JA.JABddOpQQ) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_genTransfer hJ hG (jDecayTrQQ_of_open hHat) (JA.jAdjTrQQ_of_three hHat hBdd JA.star_operator_transfer_holds)

end Formalism.FourierDecayAlt.P.CutMP
