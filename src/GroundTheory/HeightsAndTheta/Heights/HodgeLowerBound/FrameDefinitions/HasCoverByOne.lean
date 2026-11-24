module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Cover

variable {Ω : Type} [Field Ω]

def HasCoverBy (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (Pr : Ω → Prop) : Prop :=
  ∃ (m : ℕ) (f cc : Fin m → Ω), (∀ l, f l ∈ chartRing ℤ (segreCoord y) c) ∧
    (∀ l, cc l ∈ chartRing ℤ (segreCoord y) c) ∧ ∑ l, cc l * f l = 1 ∧ ∀ l, Pr (f l)


def zMono (z : (Σ k, ι k) → ℂ) (c : (k : K) → ι k) (a : K → ℤ) : ℂ := ∏ k, z ⟨k, c k⟩ ^ a k

end Cover

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

theorem step_le {N : ℕ} (i : Fin (N - 1)) : (i : ℕ) + 1 ≤ N := by have := i.isLt; omega

structure PlueckerData (D : ComponentData II Ψ K ι Ω E) where

  e : ∀ τ, Fin D.N → E τ
  e_indep : ∀ τ, LinearIndependent Ω (e τ)
  e_span : ∀ τ, Submodule.span Ω (Set.range (e τ)) = ⊤

  M : Ψ → Fin (D.N - 1) → ℕ
  M_ge : ∀ τ (i : Fin (D.N - 1)), Nat.choose D.N ((i : ℕ) + 1) ≤ M τ i

  bdeg : Ψ → Fin (D.N - 1) → K → ℤ

  gen : ∀ τ (i : Fin (D.N - 1)), Fin (M τ i) → Module.Dual Ω (⋀[Ω]^((i : ℕ) + 1) (E τ))
  global : ∀ τ (i : Fin (D.N - 1)) m (c : (k : K) → ι k), segreCoord D.y c ≠ 0 → ∀ v : Fin ((i : ℕ) + 1) → E τ,
    (∀ a, v a ∈ (D.W τ).lat c) →
      gen τ i m (exteriorPower.ιMulti Ω _ v) * chartMono D.y c (-bdeg τ i) ∈ chartRing ℤ (segreCoord D.y) c
  generates : ∀ τ (i : Fin (D.N - 1)) (c : (k : K) → ι k), segreCoord D.y c ≠ 0 → HasCoverBy D.y c fun f =>
    ∃ b : Fin D.N → E τ, IsFrameOver D.y (D.W τ) c f b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ A : Fin ((i : ℕ) + 1) → Fin D.N, StrictMono A → ∃ a : Fin (M τ i) → Ω,
        (∀ m, ∃ n : ℕ, f ^ n * a m ∈ chartRing ℤ (segreCoord D.y) c) ∧
        ∀ A' : Fin ((i : ℕ) + 1) → Fin D.N, StrictMono A' →
          ∑ m, a m * (gen τ i m (exteriorPower.ιMulti Ω _ (b ∘ A')) * chartMono D.y c (-bdeg τ i)) =
            if A' = A then 1 else 0

  wdeg : Ψ → K → ℤ

  ω : ∀ τ, ⋀[Ω]^D.N (E τ)
  detW : ∀ τ (c : (k : K) → ι k), segreCoord D.y c ≠ 0 → HasCoverBy D.y c fun f =>
    ∃ b : Fin D.N → E τ, IsFrameOver D.y (D.W τ) c f b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∃ u : Ω, IsUnitOn D.y c f u ∧ ω τ = (u * chartMono D.y c (-wdeg τ)) • exteriorPower.ιMulti Ω D.N b

namespace PlueckerData

variable {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D)

def ιY : K ⊕ (Ψ × Fin (D.N - 1)) → Type := Sum.elim ι fun q => Fin (Pl.M q.1 q.2)

instance instFintypeιY : ∀ k, Fintype (Pl.ιY k)
  | Sum.inl k => inferInstanceAs (Fintype (ι k))
  | Sum.inr q => inferInstanceAs (Fintype (Fin (Pl.M q.1 q.2)))

abbrev ΩY (_Pl : PlueckerData D) : Type := FractionRing (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω)

def ofΩ (x : Ω) : Pl.ΩY := algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (C x)

def gvar (τ : Ψ) (a b : Fin D.N) : Pl.ΩY :=
  algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (X (τ, a, b))


abbrev Incr (s N : ℕ) : Type := {A : Fin s → Fin N // StrictMono A}



end PlueckerData

end GroundTheory.Heights₂.Heights.LowerBoundFree
