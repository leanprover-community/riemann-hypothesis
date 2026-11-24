module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
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
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionRingFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∃ (r : ℕ) (d : Fin r → ℕ) (e : Fin r → Ω), (∀ i, e i ∈ chartLat y a (d i)) ∧
      ∀ n : ℕ, chartLat y a n ≤ AddSubgroup.closure
        {s | ∃ (i : Fin r) (μ : Fin q → ℕ), d i + ∑ j, μ j = n ∧ s = e i * ∏ j, w j ^ μ j}

def SectionBounded.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (q : ℕ) (w : Fin q → Ω),
    (∀ j, w j ∈ chartLat y A.a 1) → KH.GeneratesOn y A.a w → (∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)) →
    ∀ (n : ℕ) (s : Ω), s ∈ chartLat y A.a n → ∃ C : ℝ, IsBoundedH (mCoordIdeal y) y A n C s

def SectionBoundedMul.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n m : ℕ) (C C' : ℝ) (s t : Ω),
    s ∈ chartLat y A.a n → t ∈ chartLat y A.a m →
    IsBoundedH (mCoordIdeal y) y A n C s → IsBoundedH (mCoordIdeal y) y A m C' t →
    IsBoundedH (mCoordIdeal y) y A (n + m) (C * C') (s * t)

section Inhabitants

open ProjLine

theorem isBoundedH_one_of_isSmallH {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ : ℕ} {s : Ω}
    (h : IsSmallH P y A τ s) : IsBoundedH P y A τ 1 s := by
  intro dg dh g h' z hg hh hdeg he hz
  rw [one_mul]
  exact h dg dh g h' z hg hh hdeg he hz

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
