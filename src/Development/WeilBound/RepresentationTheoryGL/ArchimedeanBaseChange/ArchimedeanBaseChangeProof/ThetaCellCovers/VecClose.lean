module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace PositivityTheory.Rg.BcB.E1

def Ctx.IsVec (X : Ctx) {ι : Type} (Φ : Matrix ι ι (X.G → ℂ)) (y : X.G) (j : ι) (k : X.Hs ι) : Prop :=
  ∀ l, (k l : X.G → ℂ) =ᵐ[X.ν] fun z => ker X.Γ (Φ l j) z y

def TwoUnif : Prop := ∀ (X : Ctx) (φ : X.G → ℂ) (ε : ℝ), Tst φ → 0 < ε →
  ∃ W ∈ nhds (1 : X.G), ∀ z ∈ W, ∀ w ∈ W, ∀ y, ‖φ (z * y * w) - φ y‖ ≤ ε

def IsBump (X : Ctx) (ψ : X.G → ℂ) : Prop :=
  Tst ψ ∧ (∀ z, ψ z = (‖ψ z‖ : ℝ)) ∧ ∫ z, ‖ψ z⁻¹‖ ∂X.μ = 1

def BumpEx : Prop := ∀ (X : Ctx), ∀ W ∈ nhds (1 : X.G), ∃ ψ, IsBump X ψ ∧ tsupport ψ ⊆ W

def ApproxU : Prop := ∀ (X : Ctx) (φ : X.G → ℂ) (ε : ℝ), Tst φ → 0 < ε → ∃ W ∈ nhds (1 : X.G), ∀ ψ, IsBump X ψ →
  tsupport ψ ⊆ W → ∀ y, ‖cv X.μ φ ψ y - φ y‖ ≤ ε ∧ ‖cv X.μ (adj ψ) (cv X.μ φ ψ) y - φ y‖ ≤ ε

def KerClose : Prop := ∀ (X : Ctx) (Ω : Set X.G) (x y : X.G), IsCompact Ω → ∃ N : ℝ, 0 ≤ N ∧ ∀ (φ φ' : X.G → ℂ) (ε : ℝ),
  Function.support φ ⊆ Ω → Function.support φ' ⊆ Ω → (∀ z, ‖φ z - φ' z‖ ≤ ε) → ‖ker X.Γ φ x y - ker X.Γ φ' x y‖ ≤ N * ε

def VecClose : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ Φ' : Matrix ι ι (X.G → ℂ)) (Ω : Set X.G) (ε : ℝ) (y : X.G) (j : ι)
  (k k' : X.Hs ι), IsCompact Ω → (∀ l, Tst (Φ l j) ∧ Tst (Φ' l j) ∧ Function.support (Φ l j) ⊆ Ω ∧
    Function.support (Φ' l j) ⊆ Ω ∧ ∀ z, ‖Φ l j z - Φ' l j z‖ ≤ ε) → X.IsVec Φ y j k → X.IsVec Φ' y j k' →
  ‖k - k'‖ₑ ^ 2 ≤ Fintype.card ι * (ENNReal.ofReal ε ^ 2 * X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y)

def VecNorm : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ)), (∀ i j, Tst (Φ i j)) →
  ∃ (C : ℝ≥0∞) (Ω : Set X.G), C ≠ ⊤ ∧ IsCompact Ω ∧ ∀ y j k, X.IsVec Φ y j k → ‖k‖ₑ ^ 2 ≤ C * cnt X.Γ Ω y

def VecEx : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ)), (∀ i j, Tst (Φ i j)) →
  ∃ k : X.G → ι → X.Hs ι, (∀ j, Continuous fun y => k y j) ∧ ∀ y j, X.IsVec Φ y j (k y j)

def VecInner : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ)) (y : X.G) (j : ι) (k u : X.Hs ι),
  (∀ i j, Tst (Φ i j)) →
  (X.IsVec Φ y j k → inner ℂ u k = ∑ l, ∫ z, starRingEnd ℂ ((u l : X.G → ℂ) z) * ker X.Γ (Φ l j) z y ∂X.ν) ∧
  (X.IsVec (fun i j => adj (Φ j i)) y j k → inner ℂ k u = ∑ l, ∫ z, ker X.Γ (Φ j l) y z * (u l : X.G → ℂ) z ∂X.ν)

def VecLim : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ)) (T : X.Hs ι →L[ℂ] X.Hs ι) (y : X.G) (j : ι)
  (k : X.Hs ι) (ε : ℝ), (∀ i j, Tst (Φ i j)) → X.IsOp Φ T → X.IsVec Φ y j k → 0 < ε →
  ∃ W ∈ nhds (1 : X.G), ∀ ψ, IsBump X ψ → tsupport ψ ⊆ W → ∀ u, X.IsCol ψ y j u → ‖T u - k‖ ≤ ε

def PtEq : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ₁ Φ₂ Φ : Matrix ι ι (X.G → ℂ)) (T₁ T₂ U : X.Hs ι →L[ℂ] X.Hs ι),
  (∀ i j, Tst (Φ₁ i j)) → (∀ i j, Tst (Φ₂ i j)) → (∀ i j, Tst (Φ i j)) → X.IsOp Φ₁ T₁ → X.IsOp Φ₂ T₂ →
  X.IsOp Φ (T₁ * U * T₂) → ∀ x y i j k₁ k₂, X.IsVec (fun i j => adj (Φ₁ j i)) x i k₁ → X.IsVec Φ₂ y j k₂ →
    ker X.Γ (Φ i j) x y = inner ℂ k₁ (U k₂)

end PositivityTheory.Rg.BcB.E1

end
