module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjSub
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.ProdEP2Core

open Formalism.L2.SG.Pf.IndexCocycleOrbits

variable {G : Type} [Group G]

structure Retr (S N : Subgroup G) (π : G → G) : Prop where
  le : S ≤ N
  mul : ∀ x ∈ N, ∀ y ∈ N, π (x * y) = π x * π y
  mem : ∀ x ∈ N, π x ∈ S
  id : ∀ s ∈ S, π s = s

theorem Retr.one {S N : Subgroup G} {π : G → G} (h : Retr S N π) : π 1 = 1 := by
  have h1 := h.mul 1 N.one_mem 1 N.one_mem
  rw [mul_one] at h1
  simpa using h1

theorem Retr.inv {S N : Subgroup G} {π : G → G} (h : Retr S N π) {x : G} (hx : x ∈ N) : π x⁻¹ = (π x)⁻¹ := by
  have h1 := h.mul x⁻¹ (N.inv_mem hx) x hx
  rw [inv_mul_cancel, h.one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

def img {S N : Subgroup G} {π : G → G} (h : Retr S N π) (H : Subgroup G) (hH : H ≤ N) : Subgroup G where
  carrier := π '' H
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, H.mul_mem hx hy, h.mul x (hH hx) y (hH hy)⟩
  one_mem' := ⟨1, H.one_mem, h.one⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, H.inv_mem hx, h.inv (hH hx)⟩

theorem cj_eq_cj_img {S N : Subgroup G} {π : G → G} (h : Retr S N π) {H : Subgroup G} (hH : H ≤ N) {g₀ : G}
    (hg : g₀ ∈ N) (hC : cj g₀ H ≤ S) : cj g₀ H = cj (π g₀) (img h H hH) := by
  ext y
  rw [mem_cj, mem_cj]
  constructor
  · intro hy
    have hyS : y ∈ S := hC ((mem_cj).2 hy)
    have hyN : y ∈ N := h.le hyS
    refine (Set.mem_image π _ _).2 ⟨g₀ * y * g₀⁻¹, hy, ?_⟩
    rw [h.mul _ (N.mul_mem hg hyN) _ (N.inv_mem hg), h.mul _ hg _ hyN, h.inv hg, h.id y hyS]
  · intro hy
    obtain ⟨x, hx, hxe⟩ := (Set.mem_image π _ _).1 hy
    have hz : g₀⁻¹ * x * g₀ ∈ cj g₀ H := by
      rw [mem_cj]
      simpa [mul_assoc] using hx
    have hzS := hC hz
    have e1 : π (g₀⁻¹ * x * g₀) = g₀⁻¹ * x * g₀ := h.id _ hzS
    rw [h.mul _ (N.mul_mem (N.inv_mem hg) (hH hx)) _ hg, h.mul _ (N.inv_mem hg) _ (hH hx), h.inv hg,
      hxe] at e1
    have hyz : y = g₀⁻¹ * x * g₀ := by
      rw [← e1]
      group
    rw [hyz]
    simpa [mul_assoc] using hx

end Formalism.L2.SG.Pf.ProdEP2Core
