module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
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

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top

structure RootFlat {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (τ : Ψ) where
  F : Type
  [field : Field F]
  [numberField : NumberField F]
  φ : F →+* M.Ω
  overInt : OverInt M.y φ
  A : HermLine M.ι
  A_smooth : IsSmoothHerm A
  S : FlatHerm M.y φ A
  deg : ∑ i, M.xdeg (τ, i) = A.a
  v : ℝ → ((Σ k, M.ι k) → ℂ) → ℝ
  v_inv : ∀ t (c : M.K → ℂ) z, (∀ k, c k ≠ 0) → v t (fun p => c p.1 * z p) = v t z
  v_smooth : ∀ t, SmoothFn (v t)
  prod : ∀ t, 0 < t → ∀ z ∈ mcPts M.P, ∏ i, (M.x t (τ, i)).h z = A.h z * Real.exp (-v t z)
  small : ∀ m : Ψ × Fin N →₀ ℕ, m.degree = dimFl Ψ N →
    Tendsto (fun t => ptsIntegral M.P (pot (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N))) (v t))
      (𝓝[>] 0) (𝓝 0)

attribute [instance] RootFlat.field RootFlat.numberField

def RootFlat.ht {Ψ : Type} [Fintype Ψ] {N : ℕ} {M : RootModel Ψ N} {τ : Ψ} (R : RootFlat M τ) : ℝ := R.S.ht

def NearRecord (N : ℕ) (bad : Finset ℕ) (rd Lval h : ℝ) : Prop :=
  ∃ (hrec : ℝ) (d v : ℕ → ℝ), |hrec| ≤ N * (3 / 2 * Real.log rd + |Lval| / 2) ∧ h = hrec + ∑ p ∈ bad, d p ∧
    (∀ p ∈ bad, 0 ≤ v p ∧ |d p| ≤ (N / ((p : ℝ) - 1) + N * v p) * Real.log p) ∧
    ∑ p ∈ bad, v p * Real.log p ≤ Real.log rd

end GlobalTheory.CompanionTheory.Ar.Flat
