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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace CompanionTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def EmbL (x : IrrGL (k := k)) (l : List (IrrGL (k := k))) : Prop :=
  ∃ hd : ∑ a, (l.get a).1 = x.1, ∃ f : x.rep.IntertwiningMap (prodIrr l.get hd), Function.Injective f

def SubqL (x : IrrGL (k := k)) (l : List (IrrGL (k := k))) : Prop :=
  ∃ hd : ∑ a, (l.get a).1 = x.1, IsSubquotient x.rep (prodIrr l.get hd)

def up (Δ : Segment k) : Segment k := Segment.ofFirst Δ.first Δ.isCusp_first (Δ.len + 1) (Nat.succ_pos _)

variable (k)

def MidP : Prop := ∀ (x : IrrGL (k := k)) (A M B : List (IrrGL (k := k))), EmbL x (A ++ M ++ B) → ∃ σ, SubqL σ M ∧ EmbL x (A ++ [σ] ++ B)

def RefineP : Prop := ∀ (x σ : IrrGL (k := k)) (A M B : List (IrrGL (k := k))), EmbL σ M → EmbL x (A ++ [σ] ++ B) → EmbL x (A ++ M ++ B)

def SwapP : Prop := ∀ (x a b : IrrGL (k := k)) (A B : List (IrrGL (k := k))) (Δ Γ : Segment k), IsLSeg Δ a.rep → IsLSeg Γ b.rep → ¬ Δ.Linked Γ →
  EmbL x (A ++ [a, b] ++ B) → EmbL x (A ++ [b, a] ++ B)

def CuspEmbP : Prop := ∀ x : IrrGL (k := k), ∃ l : List (IrrGL (k := k)), (∀ ρ ∈ l, ρ.IsCusp) ∧ EmbL x l

def SuppP : Prop := ∀ (x a y : IrrGL (k := k)) (l : List (IrrGL (k := k))) (𝔫 : Multiset (Segment k)), (∀ ρ ∈ l, ρ.IsCusp) → EmbL x l →
  EmbL x [a, y] → IsL 𝔫 y.rep → ∀ Δ ∈ 𝔫, Δ.first ∈ l

def JuxtP : Prop := ∀ (σ b : IrrGL (k := k)) (Δ : Segment k), IsLSeg Δ b.rep → SubqL σ [Δ.first.nu ((Δ.len : ℕ) : ℂ), b] →
  IsLSeg (up Δ) σ.rep ∨ EmbL σ [b, Δ.first.nu ((Δ.len : ℕ) : ℂ)]

def LinkP : Prop := ∀ (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) (Δ : Segment k), (Segment.single ρ hρ).Linked Δ →
  Δ.first = ρ.nu 1 ∨ ρ = Δ.first.nu ((Δ.len : ℕ) : ℂ)

def MinP : Prop := ∀ l : List (IrrGL (k := k)), l ≠ [] → (∀ ρ ∈ l, ρ.IsCusp) →
  ∃ ρ ∈ l, ∀ ρ' ∈ l, ∀ j : ℕ, 0 < j → ρ ≠ ρ'.nu (j : ℕ)

end CompanionTheory.Exh

end
