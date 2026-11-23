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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

section Objects

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

def blockMapC {J : Type} (k₀ : K) (M : Matrix J (ι k₀) ℤ) (z : (Σ k, ι k) → ℂ) : J → ℂ :=
  fun j => ∑ i, (M j i : ℂ) * z ⟨k₀, i⟩

def IsBlockImage {Ω : Type} [Field Ω] {J : Type} [Fintype J] (y : (Σ k, ι k) → Ω) (k₀ : K)
    (M : Matrix J (ι k₀) ℤ) (N : Matrix (ι k₀) J ℤ) (x : J → Ω) : Prop :=
  (∀ j, x j = ∑ i, (M j i : Ω) * y ⟨k₀, i⟩) ∧ ∀ i, y ⟨k₀, i⟩ = ∑ j, (N i j : Ω) * x j

end Objects

def BlockImageDatum.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ (d₀ : HSMBlockDatum D K ι Ω) (r : ℕ) (M : Matrix (Ix (Fin r)) (ι d.k₀) ℤ)
      (N : Matrix (ι d.k₀) (Ix (Fin r)) ℤ) (d' : HSMDatum D Ω (Fin r)),
      d₀.y = d.y ∧ d₀.k₀ = d.k₀ ∧ IsBlockImage d.y d.k₀ M N d'.x ∧
      (∀ z ∈ mcPts (mCoordIdeal d.y), d₀.A.h z = d'.m.ρ (blockMapC d.k₀ M z)) ∧
      ∀ n, blockChi d₀ n = resChi d' n

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
