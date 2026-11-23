module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSRadLoc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceDone
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEOneLetterDens
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopHer
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfSpectralData
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

namespace Formalism.FourierDecayAlt.P.CutSE

theorem leibniz_class : LeibnizCls := leibnizCls_of_radLoc spectral_radial_locality

theorem density_smooth_class : DensSmoothCls := densSmoothCls_of_radLoc spectral_radial_locality

theorem thmPActualCpt_of_spec (h : RDIdentSpec) : Formalism.FourierDecayAlt.P5.ThmPActualCpt :=
  thmPActualCpt_of_leaves (one_letter_density_estimate leibniz_class density_smooth_class) density_smooth_class
    (radDecay_of_spec h)

end Formalism.FourierDecayAlt.P.CutSE
