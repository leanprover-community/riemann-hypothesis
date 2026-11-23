module

import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentProductEquivalence.ReorderCommon
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquivStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace CompanionTheory.PfEss.Zc2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ntrans {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U]
    [Module ℂ U] {G : Type} [Group G] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {τ : Representation ℂ G U} (a : Nonempty (ρ.Equiv σ)) (b : Nonempty (σ.Equiv τ)) : Nonempty (ρ.Equiv τ) := by
  apply PositivityTheory.PfEss.Zc2.ntrans (W := W) (σ := σ) <;> assumption

theorem prodIrr_equiv_of_eq {h N : ℕ} {y y' : Fin h → IrrGL (k := k)} (e : y = y') (hy : ∑ a, (y a).1 = N)
    (hy' : ∑ a, (y' a).1 = N) : Nonempty ((prodIrr y hy).Equiv (prodIrr y' hy')) := by
  apply PositivityTheory.PfEss.Zc2.prodIrr_equiv_of_eq <;> assumption

theorem cut_e {h j : ℕ} (hj : j + 1 < h) : j + (2 + (h - (j + 2))) = h := by
  apply PositivityTheory.PfEss.Zc2.cut_e <;> assumption

theorem cutC_lt {h j b : ℕ} (hb : b < h - (j + 2)) : j + 2 + b < h := by
  apply PositivityTheory.PfEss.Zc2.cutC_lt <;> assumption

def cutA {α : Type*} {h : ℕ} (x : Fin h → α) (j : ℕ) (hj : j + 1 < h) : Fin j → α :=
  fun a => x ⟨a.1, lt_trans a.2 (Nat.lt_of_succ_lt hj)⟩

def cutC {α : Type*} {h : ℕ} (x : Fin h → α) (j : ℕ) : Fin (h - (j + 2)) → α :=
  fun b => x ⟨j + 2 + b.1, cutC_lt b.2⟩


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem sum_append {q c : ℕ} (Q : Fin q → IrrGL (k := k)) (C : Fin c → IrrGL (k := k)) :
    ∑ a, (Fin.append Q C a).1 = ∑ a, (Q a).1 + ∑ a, (C a).1 := by
  apply PositivityTheory.PfEss.Zc2.sum_append <;> assumption


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem sum_split2 {p q n : ℕ} (A : Fin p → IrrGL (k := k)) (R : Fin q → IrrGL (k := k)) (w : Fin n → IrrGL (k := k)) (e : p + q = n)
    (hw : ∀ m : Fin (p + q), w (Fin.cast e m) = Fin.append A R m) :
    ∑ a, (w a).1 = ∑ a, (A a).1 + ∑ a, (R a).1 := by
  apply PositivityTheory.PfEss.Zc2.sum_split2 <;> assumption




theorem stage2 {p q n rA rR : ℕ} (A : Fin p → IrrGL (k := k)) (R : Fin q → IrrGL (k := k)) (w : Fin n → IrrGL (k := k))
    (e : p + q = n) (hw : ∀ m : Fin (p + q), w (Fin.cast e m) = Fin.append A R m)
    (hA : ∑ a, (A a).1 = rA) (hR : ∑ a, (R a).1 = rR) (hN : ∑ a, (w a).1 = rA + rR) :
    Nonempty ((prod₂ (prodIrr A hA) (prodIrr R hR)).Equiv (prodIrr w hN)) := by
  apply PositivityTheory.PfEss.Zc2.stage2 <;> assumption




theorem head_swap {c rQ rC : ℕ} (Q Q' : Fin 2 → IrrGL (k := k)) (C : Fin c → IrrGL (k := k))
    (hQ : ∑ a, (Q a).1 = rQ) (hQ' : ∑ a, (Q' a).1 = rQ) (hC : ∑ a, (C a).1 = rC)
    (hR : ∑ a, (Fin.append Q C a).1 = rQ + rC) (hR' : ∑ a, (Fin.append Q' C a).1 = rQ + rC)
    (E : Nonempty ((prodIrr Q hQ).Equiv (prodIrr Q' hQ'))) :
    Nonempty ((prodIrr (Fin.append Q C) hR).Equiv (prodIrr (Fin.append Q' C) hR')) := by
  apply PositivityTheory.PfEss.Zc2.head_swap <;> assumption


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem split_alt_alt {h j : ℕ} (hj : j + 1 < h) (e : j + (2 + (h - (j + 2))) = h) (x : Fin h → IrrGL (k := k))
    (m : Fin (j + (2 + (h - (j + 2))))) :
    x (Fin.cast e m) = Fin.append (cutA x j hj)
      (Fin.append ![x ⟨j, Nat.lt_of_succ_lt hj⟩, x ⟨j + 1, hj⟩]
        (cutC x j)) m := by
  apply PositivityTheory.PfEss.Zc2.split_alt_alt <;> assumption


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem split_swap {h j : ℕ} (hj : j + 1 < h) (e : j + (2 + (h - (j + 2))) = h) (x : Fin h → IrrGL (k := k))
    (m : Fin (j + (2 + (h - (j + 2))))) :
    x (Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩ (Fin.cast e m)) =
      Fin.append (cutA x j hj)
      (Fin.append ![x ⟨j + 1, hj⟩, x ⟨j, Nat.lt_of_succ_lt hj⟩]
        (cutC x j)) m := by
  apply PositivityTheory.PfEss.Zc2.split_swap <;> assumption




theorem swap_adj {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (j : ℕ) (hj : j + 1 < h) (M : ℕ)
    (hd2 : ∑ a, (![x ⟨j, Nat.lt_of_succ_lt hj⟩, x ⟨j + 1, hj⟩] a).1 = M)
    (hd2' : ∑ a, (![x ⟨j + 1, hj⟩, x ⟨j, Nat.lt_of_succ_lt hj⟩] a).1 = M)
    (hd' : ∑ a, (x (Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩ a)).1 = N)
    (E : Nonempty ((prodIrr ![x ⟨j, Nat.lt_of_succ_lt hj⟩, x ⟨j + 1, hj⟩] hd2).Equiv
      (prodIrr ![x ⟨j + 1, hj⟩, x ⟨j, Nat.lt_of_succ_lt hj⟩] hd2'))) :
    Nonempty ((prodIrr x hd).Equiv
      (prodIrr (fun a => x (Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩ a)) hd')) := by
  apply PositivityTheory.PfEss.Zc2.swap_adj <;> assumption

def Reach {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (σ : Equiv.Perm (Fin h)) : Prop :=
  ∀ hd' : ∑ a, (x (σ a)).1 = N, Nonempty ((prodIrr x hd).Equiv (prodIrr (x ∘ σ) hd'))



theorem reach_step (hcomm : LUnlinkedComm k) {h N : ℕ} {Δ : Fin h → Segment k} {x : Fin h → IrrGL (k := k)}
    (hd : ∑ a, (x a).1 = N) (hL : ∀ i, IsLSeg (Δ i) (x i).rep) (σ : Equiv.Perm (Fin h)) (hσ : Reach x hd σ)
    (j : ℕ) (hj : j + 1 < h) (hu : ¬ (Δ (σ ⟨j, Nat.lt_of_succ_lt hj⟩)).Linked (Δ (σ ⟨j + 1, hj⟩))) :
    Reach x hd (σ * Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩) := by
  apply PositivityTheory.PfEss.Zc2.reach_step <;> assumption

theorem strictMono_of_adj {h : ℕ} (f : Fin h → Fin h)
    (H : ∀ (j : ℕ) (hj : j + 1 < h), f ⟨j, Nat.lt_of_succ_lt hj⟩ < f ⟨j + 1, hj⟩) : StrictMono f := by
  apply PositivityTheory.PfEss.Zc2.strictMono_of_adj <;> assumption

theorem swap_lt_swap {h j : ℕ} (hj : j + 1 < h) {u v : Fin h} (hvu : v < u)
    (H : Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩ u < Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩ v) :
    v.1 = j ∧ u.1 = j + 1 := by
  apply PositivityTheory.PfEss.Zc2.swap_lt_swap <;> assumption

def invSet {h : ℕ} (σ : Equiv.Perm (Fin h)) : Finset (Fin h × Fin h) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ σ.symm p.2 < σ.symm p.1

theorem symm_mul_swap_apply {h : ℕ} (σ s : Equiv.Perm (Fin h)) (a b : Fin h) (hs : s = Equiv.swap a b)
    (p : Fin h) : (σ * s).symm p = s (σ.symm p) := by
  apply PositivityTheory.PfEss.Zc2.symm_mul_swap_apply <;> assumption

theorem reach_of_inv (hcomm : LUnlinkedComm k) {h N : ℕ} {Δ : Fin h → Segment k} {x : Fin h → IrrGL (k := k)}
    (hd : ∑ a, (x a).1 = N) (hL : ∀ i, IsLSeg (Δ i) (x i).rep) :
    ∀ (n : ℕ) (σ : Equiv.Perm (Fin h)), (invSet σ).card = n →
      (∀ a b, a < b → σ.symm b < σ.symm a → ¬ (Δ a).Linked (Δ b)) → Reach x hd σ := by
  apply PositivityTheory.PfEss.Zc2.reach_of_inv <;> assumption

end CompanionTheory.PfEss.Zc2
