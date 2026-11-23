module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryBC GlobalTheory.LFun Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.PRep

theorem UpperTheory.V.Z.Mult.lcLev :
    UpperTheory.V.Z.Mult.LcLev := by
  intro E _ _ _ n w hw f hf
  obtain ⟨K', hKo, hKle, hK⟩ := hf
  have hU : UL n w = ⊤ := if_pos hw
  have hcl : IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) := by
    rw [hU]
    exact isClosed_univ
  refine ⟨K'.subgroupOf (UL n w), hKo.preimage continuous_subtype_val, ?_, ?_, ?_⟩
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hKle (Subgroup.mem_subgroupOf.mp hx))
  · exact hK.1.comp_isClosedEmbedding hcl.isClosedEmbedding_subtypeVal
  · intro k hk x
    exact hK.2 k.1 (Subgroup.mem_subgroupOf.mp hk) x.1
