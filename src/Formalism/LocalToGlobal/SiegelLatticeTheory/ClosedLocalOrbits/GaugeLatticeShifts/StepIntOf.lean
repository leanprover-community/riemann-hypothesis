module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WuDecayPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.WuDecay

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.WuDecay Formalism.L2.SG.WuDecayPf
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal Classical
open Matrix

namespace Formalism.L2.SG.RealObj.StepIntOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar


variable {D : D7} (X : HidaSetting D)


def StIntOfLint : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf),
    ∫⁻ x, ‖X.Wu u x‖ₑ * ‖X.Wu u' (γ⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ →
      Formalism.L2.SG.TermOp.OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') γ

end Formalism.L2.SG.RealObj.StepIntOf

namespace Formalism.L2.SG.RealObj.StepIntOf.Steps

open Formalism.L2.SG.RealObj.StepIntOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem norm_rank_one_le {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (v : V) (w : V') :
    ‖Formalism.L2.SG.TermOp.rk1 v w‖ ≤ ‖v‖ * ‖w‖ := by
  unfold Formalism.L2.SG.TermOp.rk1
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

theorem stIntOfLint : StIntOfLint := by
  intro D X u u' γ hfin
  unfold Formalism.L2.SG.TermOp.OOInt
  rw [integrableOn_univ]
  have hW : Continuous (X.Wu u) := (X.Wu_spec u).2.2.1
  have hW' : Continuous (X.Wu u') := (X.Wu_spec u').2.2.1
  have hW'' : Continuous fun x : X.B.I.Ginf => X.Wu u' (γ⁻¹ * x) := hW'.comp (continuous_const.mul continuous_id)
  have hc : Continuous fun x : X.B.I.Ginf => Formalism.L2.SG.TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x)) := by
    rw [continuous_clm_apply]
    intro ξ
    simp only [Formalism.L2.SG.TermOp.rankOneInnerOperator_apply]
    exact (hW''.inner continuous_const).smul hW
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
  simp only []
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_rank_one_le _ _)

end Formalism.L2.SG.RealObj.StepIntOf.Steps

namespace Formalism.L2.SG.RealObj.StepIntOf.Theta

open Formalism.L2.SG.RealObj.StepIntOf

section

variable {D : D7} (X : HidaSetting D)

end

end Formalism.L2.SG.RealObj.StepIntOf.Theta

namespace Formalism.L2.SG.RealObj.StepIntOf

end Formalism.L2.SG.RealObj.StepIntOf
