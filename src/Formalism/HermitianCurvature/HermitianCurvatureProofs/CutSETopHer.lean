module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEDecayAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSESiteOpsC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEWaveOutJ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPCompactOfStepSquare
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

namespace Formalism.FourierDecayAlt.P.CutSE

theorem stepExp0_of_leaves (hO : OneLetterDens) (hS : DensSmoothCls) (hR : RadDecay) : Formalism.FourierDecayAlt.P5.HerD.StepExp0 :=
  stepExp0_of_open hO hS (decayPair2_of_smooth hS) (decayPair3_of wave_outgoing_orbital (clsDecayJ_of hR))
    (decayPair4_of wave_outgoing_orbital (clsDecayJ_of hR) site_multiplication_orbital)

theorem thmPActualCpt_of_leaves (hO : OneLetterDens) (hS : DensSmoothCls) (hR : RadDecay) :
    Formalism.FourierDecayAlt.P5.ThmPActualCpt :=
  Formalism.FourierDecayAlt.P5.HerD.thmPActualCpt_of_stepExp0 (stepExp0_of_leaves hO hS hR)

end Formalism.FourierDecayAlt.P.CutSE
