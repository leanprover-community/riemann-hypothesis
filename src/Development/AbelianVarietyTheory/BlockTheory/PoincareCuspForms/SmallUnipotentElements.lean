module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements

open NumberField ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def OpNormLe {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (A : Matrix (Fin r) (Fin r) E)
    (c : ℝ) : Prop :=
  ∀ u : Fin r → ℂ, X.maj x τ ((A.map τ.1).mulVec u) ≤ c ^ 2 * X.maj x τ u

def OpNormLtOne {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (A : Matrix (Fin r) (Fin r) E) :
    Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ OpNormLe X x τ A c

def IsLatEnd {r : ℕ} (L : Submodule (𝓞 E) (Fin r → E)) (N : Matrix (Fin r) (Fin r) E) : Prop :=
  ∀ v ∈ L, N.mulVec v ∈ L

def NoContraction {r : ℕ} (X : DataX E r) (x : Frame X.Ψ r) : Prop :=
  ∀ N : Matrix (Fin r) (Fin r) E, IsLatEnd X.L' N → (∀ τ : X.Ψ, OpNormLtOne X.toData x τ N) → N = 0

def NoShortVector {r : ℕ} (X : DataX E r) (x : Frame X.Ψ r) : Prop :=
  ∀ v ∈ X.L', v ≠ 0 → (fdeg E : ℝ) ≤ ∑ τ : X.Ψ, X.maj x τ (Data.emb τ.1 v)

def IsTotallySplitPrime (E : Type) [Field E] [NumberField E] (g : ℕ) : Prop :=
  g.Prime ∧ ((Ideal.span {(g : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E

def IsUnipotentModOver {r : ℕ} (L : Submodule (𝓞 E) (Fin r → E)) (g : ℕ) (γ : GL (Fin r) E) : Prop :=
  ∀ P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E), ∃ k : ℕ, ∀ v ∈ L,
    (((γ : Matrix (Fin r) (Fin r) E) - 1) ^ k).mulVec v ∈ P • L

def BalancedPointStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : DataX E r), ∃ x ∈ X.dom, NoContraction X x ∧ NoShortVector X x

def SmallElementStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (g : ℕ), IsTotallySplitPrime E g → 3 * r < g →
    ∀ Γo : Subgroup (GL (Fin r) E), (∀ γ ∈ Γo, IsUStab X.Gm X.L' γ) →
    (∀ γ ∈ Γo, IsUnipotentModOver X.L' g γ) →
    ∀ x ∈ X.dom, NoContraction X x →
    ∀ γ ∈ Γo, (∀ τ : X.Ψ, OpNormLe X.toData x τ (γ : Matrix (Fin r) (Fin r) E)
      (Real.exp (1 / (3 * (r : ℝ))))) → γ = 1

end

end GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements
