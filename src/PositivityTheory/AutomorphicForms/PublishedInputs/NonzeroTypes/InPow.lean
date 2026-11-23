module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def InPow (c : ℕ) (x : k) : Prop :=
  ∃ y : 𝒪[k], y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c ∧ algebraMap 𝒪[k] k y = x

def cond (ψ : 𝒪[k]ˣ →* ℂˣ) : ℕ :=
  sInf {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → ψ u = 1}

abbrev res (μ : kˣ →* ℂˣ) : 𝒪[k]ˣ →* ℂˣ := μ.comp (unitIncl k)

def cc {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b : Fin s) : ℕ := cond (res (μ a / μ b))


variable (k) in
structure Grp (n : ℕ) where
  s : ℕ
  d : Fin s → ℕ
  pos : ∀ a, 0 < d a
  hd : ∑ a, d a = n
  μ : Fin s → kˣ →* ℂˣ
  smooth : ∀ a, IsSmoothChar (μ a)
  dist : ∀ a b, a ≠ b → res (μ a) ≠ res (μ b)
  ball : ∀ a a' b' b : Fin s, a ≤ a' → a' < b' → b' ≤ b → cc μ a' b' ≤ cc μ a b

namespace Grp

variable {n : ℕ} (G : Grp k n)

abbrev e : (Σ a, Fin (G.d a)) ≃ Fin n := stdBlocks G.d G.hd

abbrev bl (i : Fin n) : Fin G.s := (G.e.symm i).1

abbrev chi (i : Fin n) : kˣ →* ℂˣ := G.μ (G.bl i)

end Grp

end UpperTheory.TNZ
