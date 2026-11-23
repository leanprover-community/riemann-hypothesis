module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RulesOnPbT
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
import Mathlib.Tactic.Linter.Style
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

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBQ

theorem rules_eq : CutHB.RulesEq := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj _hF
  refine ⟨fun g hg m hm => ⟨minorDomain_mul_unipotent p.T.base j hg.2 hm, ?_⟩,
    fun g hg a => ⟨domP_N_mul p.T.base j hg.2 (nL_mem hj a), ?_⟩⟩
  · exact pbF_right _ _ _ F g m hm
  · show pbF (p.T.bs j) p.T.base _ F (LevelPointCoordinates.nL P.k P.r j hj a * g) =
      psi P.k P.r p.T.base.z cStd (LevelPointCoordinates.nL P.k P.r j hj a) • pbF (p.T.bs j) p.T.base _ F g
    rw [nL_castM hj a, pbF_left_rn p.T.base _ (p.T.bs j).z_mem F (cL a, 0) g,
      psi_castM _ (p.T.bs j).z p.T.base.z (p.T.z_lev j (by omega))]

end Formalism.FourierDecayAlt.P
