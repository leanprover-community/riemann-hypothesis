module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace Zc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def jm {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) : ℕ∞ :=
  jhMult (piTensor fun a => (x a).rep) (jac (stdBlocks (fun a => (x a).1) hd) π)

def below {s : ℕ} (Γ : Fin s → Segment k) (a : Fin s) : ℕ :=
  ∑ b ∈ Finset.univ.filter (fun b => a < b), (Γ b).len

def IsTopCut (Δ : Segment k) {s : ℕ} (Γ : Fin s → Segment k) : Prop :=
  (∑ a, (Γ a).len = Δ.len) ∧ ∀ a, (Γ a).first = Δ.first.nu ((below Γ a : ℕ) : ℂ)

def segLow (Δ : Segment k) (a : ℕ) (ha : 0 < a) : Segment k :=
  Segment.ofFirst Δ.first Δ.isCusp_first a ha

def segHigh (Δ : Segment k) (a : ℕ) (ha : a < Δ.len) : Segment k :=
  Segment.ofFirst (Δ.first.nu ((a : ℕ) : ℂ)) (Δ.isCusp_first.nu _) (Δ.len - a) (Nat.sub_pos_of_lt ha)

def LSegExists (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ Δ : Segment k, ∃ π : IrrRep (GL (Fin Δ.deg) k), IsLSeg Δ π.ρ

def LSegJacquet (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsLSeg Δ π → ∀ (s : ℕ) (y : Fin s → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N), (∀ a, 0 < (y a).1) →
      ((∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep) → jm y hd π = 1) ∧
      ((¬ ∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep) → jm y hd π = 0)


open Classical in
def dualCl (x : IrrGL (k := k)) : IrrGL (k := k) :=
  if h : (contra x.rep).IsIrreducible then IrrGL.of (contra x.rep) (isSmooth_smoothRep _) h else x


open Classical in
def segDual (Δ : Segment k) : Segment k :=
  if hc : (dualCl Δ.first).IsCusp then
    Segment.ofFirst ((dualCl Δ.first).nu (1 - (Δ.len : ℂ))) (hc.nu _) Δ.len Δ.len_pos
  else Δ

def LSegDual (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsLSeg Δ π → IsLSeg (segDual Δ) (contra π)

end Zc

end
