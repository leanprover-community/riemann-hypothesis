module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_normal_finiteIndex_fixing (L : Type) [Field L] (G : Type) [Group G]
    [MulSemiringAction G L] (S : Finset L) (hS : ∀ s ∈ S, (MulAction.orbit G s).Finite) :
    ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix L U) ∧
      ∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x := by
  classical
  set T : Set L := ⋃ s ∈ S, MulAction.orbit G s with hT
  have hTfin : T.Finite := Set.Finite.biUnion S.finite_toSet (fun s hs => hS s hs)
  have hTstab : ∀ g : G, ∀ x ∈ T, g • x ∈ T := by
    intro g x hx
    simp only [hT, Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hx⟩ := hx
    exact ⟨s, hs, MulAction.mem_orbit_of_mem_orbit g hx⟩
  set F : Finset L := hTfin.toFinset
  have hF : ∀ x, x ∈ F ↔ x ∈ T := fun x => hTfin.mem_toFinset
  let U : Subgroup G := ⨅ x ∈ F, MulAction.stabilizer G x
  have hU : ∀ g : G, g ∈ U ↔ ∀ x ∈ T, g • x = x := by
    intro g
    simp only [U, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff, hF]
  have hST : ∀ s ∈ S, s ∈ T := by
    intro s hs
    simp only [hT, Set.mem_iUnion]
    exact ⟨s, hs, MulAction.mem_orbit_self s⟩
  have hFix : ∀ x ∈ T, x ∈ Fix L U := by
    intro x hx
    change ∀ m : U, m • x = x
    rintro ⟨g, hg⟩
    exact (hU g).1 hg x hx
  refine ⟨U, ?_, ?_, fun s hs => hFix s (hST s hs), ?_⟩
  · refine ⟨fun n hn g => ?_⟩
    rw [hU] at hn ⊢
    intro x hx
    have := hn (g⁻¹ • x) (hTstab g⁻¹ x hx)
    rw [mul_smul, mul_smul, this, smul_inv_smul]
  · refine Subgroup.finiteIndex_iInf' _ (fun x hx => ?_)
    refine ⟨?_⟩
    rw [MulAction.index_stabilizer]
    have hx' := (hF x).1 hx
    simp only [hT, Set.mem_iUnion] at hx'
    obtain ⟨s, hs, hxs⟩ := hx'
    rw [MulAction.orbit_eq_iff.mpr hxs]
    exact (Set.ncard_pos (hS s hs)).mpr ⟨s, MulAction.mem_orbit_self s⟩ |>.ne'
  · intro h hh
    rw [hU] at hh
    push_neg at hh
    obtain ⟨x, hx, hne⟩ := hh
    exact ⟨x, hFix x hx, hne⟩

end GlobalTheory.AlmostEt
