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

namespace GlobalTheory.SplitFlip.PathSplit
open GlobalTheory.SplitFlip

def vdiff (X : ℕ × ℕ) : ℤ := (X.1 : ℤ) - X.2

theorem vdiff_tgt (e : Edge) : vdiff e.tgt = vdiff e.src + 1 := by
  cases e <;> simp [vdiff] <;> push_cast <;> ring

theorem pairwise_of_isPath : ∀ {γ : List Edge}, IsPath γ → γ.Pairwise (fun a b => vdiff a.src < vdiff b.src)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    unfold IsPath at h
    rw [List.isChain_cons_cons] at h
    have ih : (b :: l).Pairwise (fun a b => vdiff a.src < vdiff b.src) :=
      pairwise_of_isPath (γ := b :: l) (show IsPath (b :: l) from h.2)
    have hab : vdiff a.src < vdiff b.src := by
      have := vdiff_tgt a; rw [h.1] at this; omega
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hab
    · exact hab.trans (List.rel_of_pairwise_cons ih hc)

theorem nodup_of_isPath {γ : List Edge} (h : IsPath γ) : γ.Nodup :=
  (pairwise_of_isPath h).imp fun hab heq => by subst heq; exact lt_irrefl _ hab

end GlobalTheory.SplitFlip.PathSplit

namespace GlobalTheory.SplitFlip
open GlobalTheory.SplitFlip.PathSplit

theorem flipPath_split : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ →
    ∃ l₁ l₂ : List Edge, γ = l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂ ∧
      flipPath i j γ = l₁ ++ [Edge.ex i (j + 1), Edge.theta (i + 1) j] ++ l₂ := by
  intro γ i j hγ hp
  obtain ⟨l₁, l₂, rfl⟩ := hp
  have hnd := nodup_of_isPath hγ
  refine ⟨l₁, l₂, rfl, ?_⟩
  have hfix : ∀ l : List Edge, Edge.theta i j ∉ l → Edge.ex i j ∉ l →
      l.map (fun e => if e = .theta i j then .ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e) = l :=
    fun l h1 h2 => by
      refine (List.map_congr_left fun e he => ?_).trans (List.map_id l)
      have e1 : e ≠ .theta i j := fun h => h1 (h ▸ he)
      have e2 : e ≠ .ex i j := fun h => h2 (h ▸ he)
      simp [e1, e2]
  rw [List.nodup_append, List.nodup_append] at hnd
  obtain ⟨⟨_, _, hd1⟩, _, hd2⟩ := hnd
  have a1 : Edge.theta i j ∉ l₁ := fun h => hd1 _ h _ (by simp) rfl
  have a2 : Edge.ex i j ∉ l₁ := fun h => hd1 _ h _ (by simp) rfl
  have b1 : Edge.theta i j ∉ l₂ := fun h => hd2 _ (by simp) _ h rfl
  have b2 : Edge.ex i j ∉ l₂ := fun h => hd2 _ (by simp) _ h rfl
  simp only [flipPath, List.map_append, hfix l₁ a1 a2, hfix l₂ b1 b2]
  simp

end GlobalTheory.SplitFlip
