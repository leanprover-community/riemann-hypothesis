module

public import Formalism.WeaklyAdmissibleFiltrations.Statement
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
public import Mathlib.RingTheory.Localization.Finiteness

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations in
theorem UpperTheory.Reformulated.B.Ue16.exists_smul_mem
    {G : Type} [inst : Group G] {LL : Type} [inst_1 : Field LL] {O : Type} [inst_2 : CommRing O]
    [inst_3 : Algebra O LL] [IsDomain O] [IsFractionRing O LL] {V : Type}
    [inst_6 : AddCommGroup V] [inst_7 : Module LL V] [inst_8 : Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (x : V) :
    ∃ a : O, a ≠ 0 ∧ a • x ∈ L.T := by
  have hx : x ∈ Submodule.span LL (L.T : Set V) := by
    rw [L.span]
    exact Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) LL (L.T : Set V) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩
