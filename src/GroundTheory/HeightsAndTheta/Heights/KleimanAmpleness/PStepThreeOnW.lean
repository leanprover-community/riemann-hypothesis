module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWLift
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWGen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnW
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem StepThree.OnW.proof (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) : StepThree.OnW.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK pp hpp
  obtain ⟨c₁, h₁⟩ := hL k Ω N x T hK pp hpp
  obtain ⟨c₂, h₂⟩ := hG k Ω N x T hK pp hpp
  refine ⟨max c₁ c₂, fun b c hb hc I => ?_⟩
  refine (h₂ b c hb (le_of_max_le_right hc) I).trans (sup_le ?_ le_sup_right)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨s, hs, hcomp, rfl⟩
  obtain ⟨t, ht, hts⟩ := h₁ b c hb (le_of_max_le_left hc) s hs hcomp
  have he : s I = t - (t - s I) := by abel
  rw [SetLike.mem_coe, he]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span (SetLike.mem_coe.mpr ht)))
    (Submodule.mem_sup_right (hts I))

end

end GroundTheory.Heights₂.Heights.Kleiman
