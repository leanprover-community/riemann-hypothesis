module

public import Mathlib.RingTheory.Finiteness.Defs
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Quotient.Defs

@[expose] public section

namespace GlobalTheory.SaturatedComplement

theorem exists_isCompl_of_saturated {O M : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [AddCommGroup M] [Module O M] [Module.Finite O M]
    (N : Submodule O M) (h : ∀ (a : O) (x : M), a ≠ (0 : O) → a • x ∈ N → x ∈ N) :
    ∃ C : Submodule O M, IsCompl N C := by
  have htf : Module.IsTorsionFree O (M ⧸ N) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro a q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.Quotient.mk_eq_zero]
      exact h a x ha hq
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hsec : ∀ q, N.mkQ (s q) = q := fun q => by
    simpa using LinearMap.congr_fun hs q
  refine ⟨LinearMap.range s, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hxN ⟨q, rfl⟩
    have hq : q = 0 := by
      rw [← hsec q, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hxN
    rw [hq, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x - s (N.mkQ x) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← Submodule.mkQ_apply,
        ← Submodule.mkQ_apply, hsec, sub_self]
    have := Submodule.add_mem_sup hx (LinearMap.mem_range_self s (N.mkQ x))
    simpa using this

end GlobalTheory.SaturatedComplement
