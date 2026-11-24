module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

namespace GlobalTheory.SeeSaw

variable {D : D7} {c : Comm D}

def Tup.col (t : Tup c) (i : ℕ) (ψ : t.Col 0) : t.Col i := Nat.rec (motive := fun i => t.Col i) ψ (fun i φ => t.K i φ) i

def iterS {α β : Type} (S : β → α → α) (ε : ℕ → β) (n : ℕ) (x : α) : α :=
  Nat.rec (motive := fun _ => α) x (fun i y => S (ε (2 * i)) y) n

def Tup.KBack (t : Tup c) : Prop :=
  ∀ j, j < D.R.m → t.cK j ≠ 0 ∧ ∀ y', ∃ (n : ℕ) (y : Fin n → c.Fr j) (P : Fin n → PolF D (c.X (j + 1)).rank (c.X j).rank),
    ∀ ψ ∈ t.Ram j, ∀ γ, t.cK j • t.rd (j + 1) γ (t.K j ψ) y' =
      ∑ a, ∑ α, (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P a) (t.rd j α ψ (y a))

def Tup.TailRd (t : Tup c) : Prop :=
  ∀ n (h : n = D.R.m), ∀ ψ ∈ t.Ram n, ∀ ψ' ∈ t.Ram n, ∀ a : ℂ, (∀ β y, t.rd n β ψ y = a • t.rd n β ψ' y) →
    ∀ F, t.tail n h ψ F = a * t.tail n h ψ' F

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι)

def TDat.cL (o : TDat c k ι) (j : ℕ) : ℂ :=
  ((((resCard k : ℝ) ^ ((((c.X (j + 1)).rank : ℝ) - (c.X j).rank) / 2) : ℝ) : ℂ)) ^ o.I.length

def LiftS (t : Tup c) : Prop :=
  ∀ j, j < D.R.m → ∀ α γ P, ∀ φ ∈ o.Ram j, (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) P φ ∈ o.Ram (j + 1) ∧
    ∀ η : ι → 𝓀[k]ˣ, o.S (fun _ => η) (j + 1) ((t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) P φ) =
      o.cL j • (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) P (o.S (fun _ => η) j φ)

structure ReadS (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0) : Prop where
  ram : ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram j, ∀ α y, t.rd j α ψ y ∈ o.Ram j
  S : ∀ j, j + 2 ≤ D.R.m → ∀ ψ ∈ t.Ram j, ∀ α y, t.rd j α (t.S j ψ) y = o.S ε j (t.rd j α ψ y)
  S₀ : ∀ η, ∀ ψ ∈ t.Ram 0, S₀ η ψ ∈ t.Ram 0 ∧ ∀ α y, t.rd 0 α (S₀ η ψ) y = o.S (fun _ => η) 0 (t.rd 0 α ψ y)

def TDat.cS (o : TDat c k ι) (n : ℕ) : ℂ := ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range (2 * i), o.cL j

def CommX (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0) : Prop :=
  ∀ n (h : 2 * n = D.R.m), ∀ ψ ∈ t.Ram 0, ∀ F,
    t.tail (2 * n) h (t.up n ψ) F = o.cS n * t.tail (2 * n) h (t.col (2 * n) (iterS S₀ ε n ψ)) F

end GlobalTheory.SeeSaw

end
