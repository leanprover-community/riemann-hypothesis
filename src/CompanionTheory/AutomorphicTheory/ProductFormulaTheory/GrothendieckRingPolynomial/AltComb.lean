module

import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.AltComb
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Zc.Cos

namespace CompanionTheory.Groth.AltC

theorem filter_mem_eq_of_sublist {α : Type*} [DecidableEq α] {l m : List α} (hs : l.Sublist m)
    (hm : m.Nodup) : m.filter (fun x => decide (x ∈ l)) = l := by
  apply PositivityTheory.Groth.AltC.filter_mem_eq_of_sublist <;> assumption

theorem mem_sub {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (i : Fin h) (x : α) :
    x ∈ sub W c i ↔ ∃ p, c p = i ∧ W.get p = x := by
  apply PositivityTheory.Groth.AltC.mem_sub <;> assumption

theorem mem_sub_self {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (p : Fin W.length) :
    W.get p ∈ sub W c (c p) := by
  apply PositivityTheory.Groth.AltC.mem_sub_self <;> assumption

theorem sub_sublist {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (i : Fin h) :
    (sub W c i).Sublist W := by
  apply PositivityTheory.Groth.AltC.sub_sublist <;> assumption


open Classical in
theorem shuffleCount_eq {α : Type*} {h : ℕ} (W : List α) (D : Fin h → List α) (hW : W.Nodup) :
    shuffleCount W D = if (∀ i, (D i).Sublist W) ∧ (∀ x ∈ W, ∃! i, x ∈ D i) then 1 else 0 := by
  apply PositivityTheory.Groth.AltC.shuffleCount_eq <;> assumption

theorem cond_map {β α : Type*} {h : ℕ} (f : β → α) (hf : Function.Injective f) (w : List β)
    (E : Fin h → List β) :
    ((∀ i, ((E i).map f).Sublist (w.map f)) ∧ (∀ x ∈ w.map f, ∃! i, x ∈ (E i).map f)) ↔
      ((∀ i, (E i).Sublist w) ∧ (∀ y ∈ w, ∃! i, y ∈ E i)) := by
  apply PositivityTheory.Groth.AltC.cond_map <;> assumption

def wN (L : ℕ) (T : Finset ℕ) : List ℕ :=
  ((List.range L).filter (fun x => decide (x ∈ T))).reverse ++ (List.range L).filter (fun x => decide (x ∉ T))

theorem mem_wN {L x : ℕ} {T : Finset ℕ} : x ∈ wN L T ↔ x < L := by
  apply PositivityTheory.Groth.AltC.mem_wN <;> assumption

theorem nodup_wN (L : ℕ) (T : Finset ℕ) : (wN L T).Nodup := by
  apply PositivityTheory.Groth.AltC.nodup_wN <;> assumption

theorem sublist_of_lt {l m : List ℕ} (hl : l.Pairwise (· < ·)) (hm : m.Pairwise (· < ·))
    (hs : ∀ x ∈ l, x ∈ m) : l.Sublist m := by
  apply PositivityTheory.Groth.AltC.sublist_of_lt <;> assumption

theorem run_sublist {L b l : ℕ} {T : Finset ℕ} (hbl : b + l ≤ L) :
    ((List.range' b l).reverse).Sublist (wN L T) ↔ ∀ x, b < x → x < b + l → x ∈ T := by
  apply PositivityTheory.Groth.AltC.run_sublist <;> assumption

def Cond (L : ℕ) (T : Finset ℕ) {h : ℕ} (b l : Fin h → ℕ) : Prop :=
  (∀ i, ((List.range' (b i) (l i)).reverse).Sublist (wN L T)) ∧
    (∀ x ∈ wN L T, ∃! i, x ∈ (List.range' (b i) (l i)).reverse)

theorem cond_iff {L : ℕ} {T : Finset ℕ} {h : ℕ} {b l : Fin h → ℕ} (hl : ∀ i, 0 < l i) :
    Cond L T b l ↔ (∀ i, b i + l i ≤ L) ∧ (∀ x < L, ∃! i, b i ≤ x ∧ x < b i + l i) ∧
      (∀ i x, b i < x → x < b i + l i → x ∈ T) := by
  apply PositivityTheory.Groth.AltC.cond_iff <;> assumption

end CompanionTheory.Groth.AltC

namespace CompanionTheory.Groth.AltC


open Classical in
theorem altSumN (L : ℕ) (hL : 0 < L) (s : Finset (Finset (Fin L))) (hs : ∀ S, S ∈ s ↔ ∀ a ∈ S, (a : ℕ) ≠ 0)
    {h : ℕ} (b l : Fin h → ℕ) (hl : ∀ i, 0 < l i) (f : Finset (Fin L) → ℤ)
    (hf : ∀ S, f S = (-1) ^ S.card * if Cond L (S.map Fin.valEmbedding) b l then 1 else 0) :
    ∑ S ∈ s, f S = if h = 1 ∧ ∀ i, b i = 0 ∧ l i = L then (-1) ^ (L - 1) else 0 := by
  apply PositivityTheory.Groth.AltC.altSumN <;> assumption

end CompanionTheory.Groth.AltC

end
