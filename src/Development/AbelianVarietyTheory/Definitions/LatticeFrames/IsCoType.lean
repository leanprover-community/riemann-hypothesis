module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
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

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition

namespace GlobalTheory.ParHecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

def IsReps (g : GL (A ⊕ D) k) (R : Finset (GL (A ⊕ D) k)) (d : GL (A ⊕ D) k → kˣ) : Prop :=
  (∀ j ∈ R, j ∈ parahoric k A D ∧ (d j : k) = j.1.toBlocks₂₂.det) ∧
    ∀ j ∈ parahoric k A D, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ parahoric k A D

def IsTOp {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (ξ : kˣ →* ℂˣ) (g : GL (A ⊕ D) k)
    (x y : V) : Prop :=
  ∀ R d, IsReps g R d → y = ∑ j ∈ R, (((ξ (d j))⁻¹ : ℂˣ) : ℂ) • π (j * g) x

def indic (s : Finset D) : D → ℤ := fun i => if i ∈ s then 1 else 0

def genVal (q r N : ℕ) (B : Multiset ℂˣ) (n : ℕ) : ℂ :=
  ((Real.sqrt q : ℝ) : ℂ) ^ (r * n + n * (N - n)) * (B.map fun b : ℂˣ => (b : ℂ)).esymm n

def IsGen {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (ξ : kˣ →* ℂˣ) (ϖ : kˣ)
    (B : Multiset ℂˣ) (x : V) : Prop :=
  x ∈ typeSpace π ξ ∧ B.card = Fintype.card D ∧ ∀ s : Finset D,
    IsTOp π ξ (mtor ϖ (indic s)) x (genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card • x)

def IsCoType {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (ξ : kˣ →* ℂˣ) (ℓ : V →ₗ[ℂ] ℂ) : Prop :=
  ∀ j ∈ parahoric k A D, ∀ d : kˣ, (d : k) = j.1.toBlocks₂₂.det → ∀ v, ℓ (π j v) = (ξ d : ℂ) * ℓ v

def schur (x : Matrix (A ⊕ D) (A ⊕ D') k) : Matrix D D' k := x.toBlocks₂₂ - x.toBlocks₂₁ * x.toBlocks₁₁⁻¹ * x.toBlocks₁₂

def liftS (ξ : kˣ →* ℂˣ) (ψ : Matrix D D' k → ℂ) (x : Matrix (A ⊕ D) (A ⊕ D') k) : ℂ := datum ξ x * ψ (schur x)


open Classical in
def intInd (y : Matrix D D' k) : ℂ := if ∀ i j, y i j ∈ 𝒪[k] then 1 else 0

def IsRepsK (g₀ : GL D k) (R : Finset (GL D k)) : Prop :=
  (∀ g ∈ R, ∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * g₀ * κ') ∧ ∀ κ ∈ KO k D, ∃! g, g ∈ R ∧ g⁻¹ * (κ * g₀) ∈ KO k D

def IsHgt {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) (H : GL n k → ℝ) : Prop :=
  (∀ κ ∈ KO k n, ∀ g, H (κ * g) = H g ∧ H (g * κ) = H g) ∧ ∀ e : n → ℤ, H (torusElt k n ϖ e) = (resCard k : ℝ) ^ (-(sumAbs e))

def segL (ϖ : kˣ) (z : ℂˣ) (t : ℕ) : Multiset ℂˣ :=
  (Multiset.range t).map fun n : ℕ => z * absPow k ((n : ℂ) - ((t : ℂ) - 1) / 2) ϖ

def omTwo {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μS μT : kˣ →* ℂˣ) (g : GL a k) (h : GL b k)
    (u : Matrix b a k → ℂ) : Matrix b a k → ℂ :=
  (((μS * μT⁻¹) (GeneralLinearGroup.det h) : ℂˣ) : ℂ) • om μT⁻¹ g h u

end GlobalTheory.ParHecke

end
