module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

noncomputable section

open Topology

namespace GlobalTheory.ShFam.Hor.LogCh

def IsLatBasis {g r : ℕ} (K : Set (Fin g → ℂ)) (b : Fin r → Fin g → ℂ) : Prop :=
  LinearIndependent ℝ b ∧ ∀ w, w ∈ K ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • b j

def IsLatFam {n g : ℕ} (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) : Prop :=
  IsOpen B ∧ (∀ b ∈ B, ∃ H : AddSubgroup (Fin g → ℂ), (H : Set (Fin g → ℂ)) = K b) ∧
    IsOpen {q : (Fin n → ℂ) × (Fin g → ℂ) | q.1 ∈ B ∧ q.2 ∉ K q.1} ∧
    ∀ b₀ ∈ B, ∀ w₀ ∈ K b₀, ∃ ζ : (Fin n → ℂ) → Fin g → ℂ, ζ b₀ = w₀ ∧ AnalyticAt ℂ ζ b₀ ∧
      ∀ᶠ q in 𝓝 (b₀, w₀), q.2 ∈ K q.1 ↔ q.2 = ζ q.1

section Exp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

def IsExpAt (t : SAB H X) (y : Sp ℂ ⟶ X) {g : ℕ} (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) : Prop :=
  (∀ v w, e (v + w) = e v * e w) ∧
    (∀ w, ∃! v, IsTanAtG t y v ∧ IsDerivAt0 (fun u => (e u).left) w v) ∧
    ∀ v, IsTanAtG t y v → ∃! w, IsDerivAt0 (fun u => (e u).left) w v

end Exp

end GlobalTheory.ShFam.Hor.LogCh
