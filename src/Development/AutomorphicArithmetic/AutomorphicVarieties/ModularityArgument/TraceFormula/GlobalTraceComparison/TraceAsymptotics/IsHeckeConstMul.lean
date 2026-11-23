module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.BlkOneMem
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
import Mathlib.Tactic.Basify
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

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

private theorem isHecke_add {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {f g : G → ℂ}
    (hf : IsHecke K f) (hg : IsHecke K g) : IsHecke K fun y => f y + g y := by
  refine ⟨hf.1.add hg.1, fun k hk x => ?_⟩
  simp only [(hf.2 k hk x).1, (hf.2 k hk x).2, (hg.2 k hk x).1, (hg.2 k hk x).2, and_self]

private theorem isHecke_const_mul {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {f : G → ℂ}
    (c : ℂ) (hf : IsHecke K f) : IsHecke K fun y => c * f y := by
  refine ⟨hf.1.mul_left (f := fun _ => c), fun k hk x => ?_⟩
  simp only [(hf.2 k hk x).1, (hf.2 k hk x).2, and_self]

theorem ctLin : CtLin := by
  intro E _ _ _ w n a b h f g c hf hg
  refine ⟨funext fun m => ?_, funext fun m => ?_⟩
  · obtain ⟨e, -⟩ := ctSph E w n a b h _ (isHecke_add hf hg) m
    obtain ⟨e₁, s₁⟩ := ctSph E w n a b h f hf m
    obtain ⟨e₂, s₂⟩ := ctSph E w n a b h g hg m
    rw [e, e₁, e₂, finsum_add_distrib s₁ s₂, mul_add]
  · obtain ⟨e, -⟩ := ctSph E w n a b h _ (isHecke_const_mul c hf) m
    obtain ⟨e₁, s₁⟩ := ctSph E w n a b h f hf m
    rw [e, e₁, mul_left_comm c, mul_finsum _ c]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
