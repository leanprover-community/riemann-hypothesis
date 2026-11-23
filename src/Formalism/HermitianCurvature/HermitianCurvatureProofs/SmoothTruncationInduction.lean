module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DetLowW
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBCutOff
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

namespace Formalism.FourierDecayAlt.P

theorem smooth_truncation_induction : Formalism.FourierDecayAlt.P.LevelPointCoordinates.CutOffStep := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ _ _ hγ hΩ t ht e Fc hFc hag
  exact Formalism.FourierDecayAlt.P.CutHB.truncation_off_induction Wp Wq P p F j hj w h hh γ hγ hΩ t ht e Fc hFc hag

theorem smooth_truncation_exists : Formalism.FourierDecayAlt.P.LevelPointCoordinates.CutOffExists := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh hF _ t ht e
  exact Formalism.FourierDecayAlt.P.CutHB.truncation_off_exists_formula Wp Wq P p F j hj w h hh hF t ht e

end Formalism.FourierDecayAlt.P
