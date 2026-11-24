module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEq
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open scoped Classical

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.unramOf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.UnramOf := by
  intro E _ _ _ n S π K' hlev w hw hK
  obtain ⟨φ, hφ, h0, hfix⟩ := hlev
  refine ⟨φ, hφ, h0, fun x hx hk => hfix w hw x hx ?_⟩
  have hmem : cLoc w x ∈ UL n w := by
    by_cases hs : IsSplitAt w
    · unfold UL
      rw [if_pos hs]
      trivial
    · exact GlobalTheory.LocInj.cLoc_mem_UL hs x
  refine ⟨⟨cLoc w x, hmem⟩, ?_, rfl⟩
  rw [hK]
  exact Subgroup.mem_subgroupOf.2 hk
