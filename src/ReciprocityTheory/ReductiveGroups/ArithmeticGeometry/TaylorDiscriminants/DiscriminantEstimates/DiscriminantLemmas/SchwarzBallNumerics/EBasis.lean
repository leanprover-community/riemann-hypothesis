module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ScaledBoundInequalityHypothesesOne
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

theorem eBasis : ReciprocityTheory.ChartRestriction.G.TB.EBasisSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.EBasisSt
  intro E _ _ W _ _ _ _ _ ι _ v hv hcard
  classical
  haveI : FiniteDimensional ℚ W := Module.Finite.trans E W
  have hinj : Function.Injective v := hv.injective
  have hspanQ : Submodule.span ℚ (Set.range v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hv, hcard, Module.finrank_mul_finrank]
  have hspanE : Submodule.span E (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℚ (Set.range v) := by rw [hspanQ]; trivial
    exact Submodule.span_le_restrictScalars ℚ E (Set.range v) hx
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent E (Set.range v)
  let s : Finset ι := Finset.univ.filter (fun i => v i ∈ b)
  have hrange : Set.range (fun i : s => v i) = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (Finset.mem_filter.mp i.2).2
    · intro hx
      obtain ⟨i, rfl⟩ := hbsub hx
      exact ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩, rfl⟩
  have hli : LinearIndependent E (fun i : s => v i) := by
    let f : s → b := fun i => ⟨v i, (Finset.mem_filter.mp i.2).2⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      exact hinj (congrArg Subtype.val hij)
    exact hbli.comp f hf
  have hspan : Submodule.span E (Set.range fun i : s => v i) = ⊤ := by
    rw [hrange, hbspan, hspanE]
  refine ⟨s, ?_, hli, hspan⟩
  have hfr := finrank_span_eq_card hli
  rw [hspan, finrank_top, Fintype.card_coe] at hfr
  exact hfr.symm

end PI.UnitaryGroupMassFormula.TBNum
