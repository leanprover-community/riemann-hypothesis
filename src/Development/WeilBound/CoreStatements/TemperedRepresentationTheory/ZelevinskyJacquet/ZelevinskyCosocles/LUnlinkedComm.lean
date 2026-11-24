module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace Zc.Cos

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def decWord (Γ : Segment k) : List (IrrGL (k := k)) := (List.ofFn Γ.term).reverse


open Classical in
def jmL (W : List (IrrGL (k := k))) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) : ℕ∞ :=
  if h : ∑ a, (W.get a).1 = N then jm W.get h π else 0

def sub {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (i : Fin h) : List α :=
  ((List.finRange W.length).filter (fun p => c p = i)).map W.get


open Classical in
def shuffleCount {α : Type*} {h : ℕ} (W : List α) (D : Fin h → List α) : ℕ :=
  (Finset.univ.filter fun c : Fin W.length → Fin h => ∀ i, sub W c i = D i).card

def IsRevOrdered {h : ℕ} (Γ : Fin h → Segment k) : Prop :=
  ∀ i j, i < j → ¬ (Γ j).Precedes (Γ i)

def IsCanon {h : ℕ} (Γ : Fin h → Segment k) : Prop :=
  (∀ i j, i < j → (¬ ∃ n : ℕ, 0 < n ∧ (Γ i).first = (Γ j).first.nu (n : ℂ)) ∧
    ((Γ i).first = (Γ j).first → (Γ i).len ≤ (Γ j).len)) ∧
  ∀ i j l, i < j → j < l → Γ i = Γ l → Γ j = Γ i

def LUnlinkedIrr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (h N : ℕ) (Δ : Fin h → Segment k) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N),
    (∀ i j, ¬ (Δ i).Linked (Δ j)) → (∀ i, IsLSeg (Δ i) (x i).rep) → (prodIrr x hd).IsIrreducible

def LUnlinkedComm (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (Δ Δ' : Segment k) (x y : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N) (hd' : ∑ a, (![y, x] a).1 = N),
    ¬ Δ.Linked Δ' → IsLSeg Δ x.rep → IsLSeg Δ' y.rep → Nonempty ((prodIrr ![x, y] hd).Equiv (prodIrr ![y, x] hd'))

end Zc.Cos

end
