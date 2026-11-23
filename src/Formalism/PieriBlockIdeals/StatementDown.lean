module

public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
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

noncomputable section

namespace Formalism.CohomologicalDescent.Down

section SLD

open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD

end SLD

section SLD2

open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD

end SLD2

section SF06

open CategoryTheory CategoryTheory.Limits
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds

end SF06

section SF07

open TensorProduct MvPolynomial CategoryTheory CategoryTheory.Limits
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative

end SF07

section SF09

open TensorProduct MvPolynomial
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

def InclWReal : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι),
    W.Ok P → ∀ (l : ℕ) (X : HidaSetting ι P.Nr W.lam), l.Prime → ¬ IsUnit ((l : ℕ) : X.O) →
    P.lJ < (l : ℝ) → X.WInputs l (kc P) W.j W.T2 (W.iW P l) →
    X.Incl l (W.JW P l) ∧ X.Jmin l ≤ W.JW P l

end SF09

end Formalism.CohomologicalDescent.Down
