module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}

def gen (y : (Σ k, J k) → Ω) (a : K → ℤ) (e₀ : Ω) (c : (k : K) → J k) : Ω :=
  (∏ k, y ⟨k, c k⟩ ^ a k) * e₀

def IsCls {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (b₀ : Fin r → E) (i : Fin r) (e : E) (t : Ω) : Prop :=
  e - t • b₀ i ∈ flagStep Ω b₀ i

def Sandwich {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
    (M : LieModel G ξ Li) (V : Lat ξ Li) {r : ℕ} (b₀ : Fin r → Li) (m : ℕ) : Prop :=
  ∀ p : Cpt ξ, ∃ (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li), (∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i) ∧
    V.IsFrameAt b p ∧ (∀ i, (m : Ω) • b i ∈ M.lat p) ∧ (∀ i j, π i (b j) = if i = j then 1 else 0) ∧
    ∀ i, ∀ e ∈ M.lat p, (m : Ω) * π i e ∈ regAt ξ p

def gramAt {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {M : LieModel G ξ Li} {y : (Σ k, J k) → Ω} (h : LieMetric M y) (z : Sp ℂ ⟶ X) {n : ℕ}
    (v : Fin n → (epsAt z ⟶ G)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => h.ip z (v a) (v b)

def locRatio {L : Type} [Field L] [NumberField L] (a : K → ℤ) (w : (Σ k, J k) → L)
    (c : (k : K) → J k) (v : FinitePlace L) : ℝ :=
  ∏ k, ((⨆ i, v (w ⟨k, i⟩)) / v (w ⟨k, c k⟩)) ^ a k

end GlobalTheory.CompanionTheory.Ar.RootHt
