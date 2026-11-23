module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section



section
noncomputable section
namespace GlobalTheory.HeckeCharacterEquality
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
theorem sixth_character_equality_holds_alt_alt : _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' := by
  intro D hA i χ χ' s ρ h h'
  have hAN := hA.1.1.2.2.2.2.2.2.1
  have hloc : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.locG χ w = D.naut.locG χ' w := by
    intro w hw
    have e := congrArg (fun a => D.naut.lpTw a (-s)) ((h w hw).symm.trans (h' w hw))
    simpa [D.naut.lpTw_add, D.naut.lpTw_zero] using e
  have hp := hAN [⟨1, χ, 1⟩] [⟨1, χ', 1⟩] (by simp) (by simp) (by
    have hfin := placesOver_finite_joint_conditions_zpowers D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero
    filter_upwards [hfin.compl_mem_cofinite] with w hw
    simp only [isoLoc, spehLoc, List.foldr]
    rw [hloc w hw])
  have := List.perm_singleton.1 hp
  simpa using this
end GlobalTheory.HeckeCharacterEquality
end
end
