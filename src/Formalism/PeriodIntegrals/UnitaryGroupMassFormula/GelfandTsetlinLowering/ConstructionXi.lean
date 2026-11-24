module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.EvalInitMinorNormLe
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
import Formalism.LocalRingCardinality.Params

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem xi_coefficient_facts : XiFacts := by
  intro n N h lam sg hI
  refine ⟨XiB.xi_ne h lam sg, XiB.xi_mem h lam sg hI, ?_, ?_, ?_, ?_⟩
  · intro g hlow hdiag
    exact XiB.xi_unitri h lam sg g hlow hdiag
  · intro t
    exact XiB.xi_torus h lam sg hI t
  · intro a
    exact XiB.xi_last h lam sg hI a
  · intro x hx
    exact XiB.xi_unitary h lam sg x hx

end PI.WGL
