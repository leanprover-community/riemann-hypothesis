module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
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
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegCmp

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt
open scoped ENNReal

section Generic

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def hilb (ev : V →ₗ[K] Ω) (τ : ℕ) : ℕ∞ :=
  Cardinal.toENat (Module.rank K (↥((LinearMap.range ev) ^ τ : Submodule K Ω)))

def coneAlg (ev : V →ₗ[K] Ω) : Subalgebra K (Polynomial Ω) :=
  Algebra.adjoin K (Set.range fun v => Polynomial.X * Polynomial.C (ev v))

def IsIntDeg (ev : V →ₗ[K] Ω) (τ : ℕ) (t : Ω) : Prop :=
  IsIntegral (coneAlg ev) (Polynomial.X ^ τ * Polynomial.C t : Polynomial Ω)

def IsRatio (ev : V →ₗ[K] Ω) (τ : ℕ) (t : Ω) : Prop :=
  ∃ (e : ℕ) (h : Ω), h ∈ ((LinearMap.range ev) ^ e : Submodule K Ω) ∧ h ≠ 0 ∧
    t * h ∈ ((LinearMap.range ev) ^ (τ + e) : Submodule K Ω)

end Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)

def UnfAll : Prop := ∀ σ, GoodEmb c σ → IsUnf (U σ)

def Proport : Prop :=
  ∀ (Z : Comp Xo c) (la : Weight Dw), (∀ τ, StrictAnti (la τ)) →
    growthOn U Z (wtOf Dw la 0) = ENNReal.ofReal (topDeg U Z la)

def EqVolume : Prop := ∀ Z Z' : Comp Xo c, vZero U Z = vZero U Z'

set_option synthInstance.maxHeartbeats 100000 in
def RatioOn (Z : Comp Xo c) (G : WTZ E) : Prop :=
  ∀ (τ : ℕ), ∀ t ∈ cuspOn U Z (τ • G), IsRatio (genPoint Z (cuspOn U Z G)) τ (genVal Z t)

end GlobalTheory.DegCmp
