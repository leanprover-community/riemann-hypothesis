module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def StCut0 : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), ∀ g ∈ GV k r, ∀ v ∈ DDinf D X, X.σ g v ∈ DDinf D X

def StCut1p : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (A : ℝ) (m : ℕ) (f : Mat k r → ℂ) (X₀ : Wp →L[ℂ] Wp), InCC A m f → InCC A m (fun g => f g • X₀)

def StCut1 : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → ∀ d : ℝ, IsFdegG D X d →
    ∀ (f : Mat k r → ℂ) (x y a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp), (∀ g ∈ GV k r, f g = mc X x y g) →
    ∀ p : SS k r, D.inSS p →
      Ph D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀) p =
        hsInner ((D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹)) X₀ *
          (mc X x a₂ (Matrix.of p.2.2 * Matrix.of p.2.1) *
            star (mc X y b₂ (Matrix.of p.1.2 * Matrix.of p.1.1))) / (d : ℂ)

def StCut2 : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → ∀ d : ℝ, IsFdegG D X d →
    ∀ (f : Mat k r → ℂ) (x y a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp), (∀ g ∈ GV k r, f g = mc X x y g) →
    Integrable (beInt D X x a₂) (D.μW.prod D.μN) → Integrable (beInt D X y b₂) (D.μW.prod D.μN) →
      Integrable (Ph D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀)) D.μSS ∧
      ∫ p, xiTau D (1, 1) p * Ph D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀) p ∂D.μSS =
        hsInner ((ContinuousLinearMap.adjoint (beOp D X y b₂)).comp (beOp D X x a₂)) X₀ / (d : ℂ)

def StCut4 : Prop :=
  StSchurW →
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp), IsDiag D → ∀ (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (P₁ Q P₂ Q₂ : Wp →L[ℂ] Wp),
    (∀ h ∈ UWset k r D.z, (ContinuousLinearMap.adjoint P₁).comp ((D.π h).comp Q) =
      (ContinuousLinearMap.adjoint P₂).comp ((D.π (th k r γ h)).comp Q₂)) →
    ((∀ x y x' y' : Wp, ∫ h : Mt k r, ⟪y, D.π (th k r γ (Matrix.of h)) x⟫_ℂ *
        star ⟪y', D.π (Matrix.of h) x'⟫_ℂ ∂D.μW = 0) →
      ∀ x y ξ η : Wp, ⟪η, Q x⟫_ℂ * ⟪P₁ y, ξ⟫_ℂ = 0) ∧
    (∀ C₀ : Wp ≃ₗᵢ⋆[ℂ] Wp,
      (∀ h ∈ UWset k r D.z, ∀ x y : Wp, ⟪y, D.π (th k r γ h) x⟫_ℂ = ⟪C₀ x, D.π h (C₀ y)⟫_ℂ) →
      ∀ x y ξ η : Wp, ⟪η, Q x⟫_ℂ * ⟪P₁ y, ξ⟫_ℂ = ⟪η, C₀ (P₂ y)⟫_ℂ * ⟪C₀ (Q₂ x), ξ⟫_ℂ)

def StCut3 : Prop :=
  StInvGroup →
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∀ x y x' y' : X.Hs,
      ∫ g : Mt k r, ⟪y, X.σ (th k r γ (Matrix.of g)) x⟫_ℂ * star ⟪y', X.σ (Matrix.of g) x'⟫_ℂ ∂D.μG = 0) →
    ∀ (a₁ b₁ a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp) (p : SS k r), D.inSS p →
      Ph D (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) (fun g => mc X a₂ b₂ g • X₀) p = 0

end ReciprocityTheory.ChartRestriction.DS.Mult1
