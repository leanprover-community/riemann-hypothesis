module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def genIdeal {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
    (y : (Σ k, ι k) → Ω) : Ideal (MRingOver ℚ ι) :=
  (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))

def GeneratesOn {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] {ι' : Type*} [Fintype ι']
    (y : (Σ k, ι k) → Ω) (n : K → ℤ) (x' : ι' → Ω) : Prop :=
  ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ u : ι' → Ω, (∀ j, u j ∈ chartRingZ y c) ∧
    ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) = 1

def SecEqStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    (∀ k, 1 ≤ a k) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
    ∃ τ₀ : ℕ, ∀ τ : ℕ, τ₀ ≤ τ → chartLat y (fun k => (a k : ℤ)) τ = secM y (fun k => τ * a k)

def CondStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    (∀ k, 1 ≤ a k) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → Birational y →
    ∃ (k : ℕ) (c : MRing ι), IsMultiHomog c (fun κ => k * a κ) ∧ aeval y c ≠ 0 ∧
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun κ => (a κ : ℤ)) τ, aeval y c * s ∈ secM y (fun κ => (τ + k) * a κ)

def SiuZStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (α : K → ℤ) (I : IFamily ℚ ι),
    IsFieldIntersection I → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → NefOnF I (genIdeal y) α →
    0 < I (genIdeal y) D (fun _ => α) →
    ∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1) 1, e ≠ 0

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
