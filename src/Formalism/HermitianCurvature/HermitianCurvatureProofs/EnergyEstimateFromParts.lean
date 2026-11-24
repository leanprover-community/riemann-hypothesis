module

public import Formalism.HermitianCurvature.StatementLE
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaEprimeFromSteps
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightedL2ConstMul
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

namespace Formalism.FourierDecayAlt.P

theorem le_thetaRange_proof : Formalism.FourierDecayAlt.LE.ThetaRange := by
  intro ε σ x hε hσ hx
  simp only [LE.th]
  have hb : 0 < x / (x + ε) := by positivity
  exact ⟨Real.rpow_pos_of_pos hb σ, Real.rpow_le_one hb.le ((div_le_one (by linarith)).mpr (by linarith)) hσ⟩

theorem le_thetaSmooth_proof : Formalism.FourierDecayAlt.LE.ThetaSmooth := Formalism.FourierDecayAlt.P.LEx1.thetaSmooth

theorem cutoff_bound : Formalism.FourierDecayAlt.LE.CutBound := Formalism.FourierDecayAlt.P.LEx1.cutBound

theorem cutoff_theta : Formalism.FourierDecayAlt.LE.CutTheta := Formalism.FourierDecayAlt.P.LEx1.cutTheta

end Formalism.FourierDecayAlt.P
