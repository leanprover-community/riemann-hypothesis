module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open GlobalTheory.SplitFlip

namespace GlobalTheory.FlipPathPairwise

def srcDiff (e : Edge) : ℤ := (e.src.1 : ℤ) - e.src.2

theorem srcDiff_of_join {e e' : Edge} (h : e.tgt = e'.src) : srcDiff e' = srcDiff e + 1 := by
  cases e <;> cases e' <;> simp only [Edge.src, Edge.tgt, Prod.mk.injEq] at h <;>
    simp only [srcDiff, Edge.src] <;> omega

theorem pairwise_of_isPath {γ : List Edge} (h : IsPath γ) :
    γ.Pairwise fun a b => srcDiff a < srcDiff b := by
  have h' : γ.IsChain fun a b => srcDiff a < srcDiff b :=
    List.IsChain.imp (fun a b hab => by rw [srcDiff_of_join hab]; omega) h
  haveI : Trans (fun a b : Edge => srcDiff a < srcDiff b) (fun a b => srcDiff a < srcDiff b)
      (fun a b => srcDiff a < srcDiff b) := ⟨fun h1 h2 => lt_trans h1 h2⟩
  exact h'.pairwise

end GlobalTheory.FlipPathPairwise


open GlobalTheory.FlipPathPairwise in
theorem GlobalTheory.SplitFlip.isPath_flipPath : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ →
    IsPath (flipPath i j γ) := by
  intro γ i j hγ hP
  obtain ⟨s, t, rfl⟩ := hP
  have hpw := pairwise_of_isPath hγ
  rw [List.pairwise_append, List.pairwise_append] at hpw
  have hs : ∀ a ∈ s, a ≠ .theta i j ∧ a ≠ .ex i j := fun a ha => by
    have h1 := hpw.1.2.2 a ha (.theta i j) (by simp)
    have h2 := hpw.1.2.2 a ha (.ex i j) (by simp)
    exact ⟨fun h => by subst h; exact lt_irrefl _ h1, fun h => by subst h; exact lt_irrefl _ h2⟩
  have ht : ∀ a ∈ t, a ≠ .theta i j ∧ a ≠ .ex i j := fun a ha => by
    have h1 := hpw.2.2 (.theta i j) (by simp) a ha
    have h2 := hpw.2.2 (.ex i j) (by simp) a ha
    exact ⟨fun h => by subst h; exact lt_irrefl _ h1, fun h => by subst h; exact lt_irrefl _ h2⟩
  have hflip : flipPath i j (s ++ [Edge.theta i j, Edge.ex i j] ++ t) =
      s ++ Edge.ex i (j + 1) :: Edge.theta (i + 1) j :: t := by
    have key : ∀ l : List Edge, (∀ a ∈ l, a ≠ .theta i j ∧ a ≠ .ex i j) →
        l.map (fun e => if e = .theta i j then Edge.ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e)
          = l := fun l hl =>
      (List.map_congr_left fun a ha => by simp [hl a ha]).trans (List.map_id l)
    unfold flipPath
    rw [List.map_append, List.map_append, key s hs, key t ht]
    simp
  rw [hflip]
  unfold IsPath at hγ ⊢
  rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append, List.isChain_append] at hγ
  obtain ⟨h1, h2, h3⟩ := hγ
  rw [List.isChain_cons_cons] at h2
  obtain ⟨-, h2⟩ := h2
  rw [List.isChain_cons] at h2
  refine List.isChain_append.2 ⟨h1, ?_, ?_⟩
  · rw [List.isChain_cons_cons, List.isChain_cons]
    exact ⟨rfl, h2.1, h2.2⟩
  · intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact h3 x hx (Edge.theta i j) rfl
