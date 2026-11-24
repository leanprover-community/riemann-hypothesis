module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount

section Vol

variable {G : Type} [Group G]

def vol (C H : Subgroup G) : ℚ := ((C.relIndex H : ℕ) : ℚ) / ((H.relIndex C : ℕ) : ℚ)

def orbC (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
    ((vol C (GlobalTheory.BCT.twCent θ δ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℚ) : ℂ)⁻¹ *
      f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q))

def orbK (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  orbC θ K (GlobalTheory.BCT.twCent θ δ ⊓ K) δ f

def massC (Γ' T C : Subgroup G) : ℚ :=
  ∑ᶠ q : DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T),
    ((Nat.card ((Γ'.subgroupOf T) ⊓ (C.subgroupOf T).map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup T) : ℕ) : ℚ)⁻¹

end Vol

section Count

variable {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂]

def stab (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (x : G₁ × G₂) : Subgroup Γ :=
  (K₁.map (MulAut.conj x.1).toMonoidHom).comap ι₁ ⊓ (K₂.map (MulAut.conj x.2).toMonoidHom).comap ι₂

def pointSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q)) : ℕ) : ℂ)⁻¹ *
      (f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) * φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2))

def pointSide (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ((massC (ι₁.prod ι₂).range (GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ))
      (GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ) ⊓ K₁.prod K₂) : ℚ) : ℂ) *
    (orbK (MonoidHom.id G₁) K₁ γ f₁ * orbK θ K₂ δ φ)

def term (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (δ : G₂) (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (x : G₁ × G₂) (γ : Γ) : ℂ :=
  f₁ (x.1⁻¹ * ι₁ γ * x.1) * φ (x.2⁻¹ * (ι₂ γ * δ) * θ x.2)

def centSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (γ : Γ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (((Subgroup.centralizer {γ}).map (ι₁.prod ι₂) : Subgroup (G₁ × G₂)) : Set (G₁ × G₂))
      ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q) ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
      term ι₁ ι₂ θ δ f₁ φ (Quotient.out q) γ

end Count

section Examples

end Examples

end GlobalTheory.LKCount
