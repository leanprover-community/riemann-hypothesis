module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

namespace GlobalTheory.SchurAdmissibility

theorem schur_admissible (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N)
    (hirr : Representation.IsIrreducible π) (hadm : GlobalTheory.PRep.IsAdmissible π)
    (φ : N →ₗ[ℂ] N) (hφ : ∀ (g : G) (x : N), φ (π g x) = π g (φ x)) :
    ∃ c : ℂ, φ = c • LinearMap.id := by
  by_cases hN : ∀ v : N, v = 0
  · exact ⟨0, LinearMap.ext fun v => by rw [hN (φ v)]; simp⟩
  push Not at hN
  obtain ⟨v, hv⟩ := hN
  let S : Subgroup G :=
    { carrier := {g : G | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSo : IsOpen (S : Set G) := hadm.1 v
  have hSc : IsClosed (S : Set G) := S.isClosed_of_isOpen hSo
  have hLo : IsOpen ((K ⊓ S : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKo.inter hSo
  have hLc : IsCompact ((K ⊓ S : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKc.inter_right hSc
  haveI hfd := hadm.2 (K ⊓ S) hLo hLc
  have hmem : ∀ w : N, w ∈ GlobalTheory.PRep.fixed π (K ⊓ S) ↔
      ∀ h : (K ⊓ S : Subgroup G), π (h : G) w = w := by
    intro w
    change (∀ h : (K ⊓ S : Subgroup G), π (h : G) w = _) ↔ _
    simp
  have hvm : v ∈ GlobalTheory.PRep.fixed π (K ⊓ S) := (hmem v).2 fun h => h.2.2
  haveI : Nontrivial (GlobalTheory.PRep.fixed π (K ⊓ S)) :=
    ⟨⟨⟨v, hvm⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hres : ∀ w ∈ GlobalTheory.PRep.fixed π (K ⊓ S), φ w ∈ GlobalTheory.PRep.fixed π (K ⊓ S) := by
    intro w hw
    rw [hmem] at hw ⊢
    intro h
    rw [← hφ, hw h]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrict hres)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : N) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hw1 : φ w = c • (w : N) := congrArg Subtype.val hw.apply_eq_smul
  let U : Subrepresentation π :=
    { toSubmodule := Module.End.eigenspace φ c
      apply_mem_toSubmodule := by
        intro g x hx
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        rw [hφ, hx, map_smul] }
  refine ⟨c, ?_⟩
  rcases hirr.eq_bot_or_eq_top U with h | h
  · exfalso
    have h1 : (w : N) ∈ U.toSubmodule := Module.End.mem_eigenspace_iff.2 hw1
    rw [h] at h1
    exact hw0 h1
  · ext x
    have h1 : x ∈ U.toSubmodule := by
      rw [h]; trivial
    exact Module.End.mem_eigenspace_iff.1 h1

end GlobalTheory.SchurAdmissibility
