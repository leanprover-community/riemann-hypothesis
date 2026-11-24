module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerLeftBlock
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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

open Matrix MeasureTheory
open scoped NNReal

namespace GlobalTheory.CompanionTheory.Jp

def sumG {k : Type} [Field k] {n : ℕ} (f : GL (Ix n) k → ℂ) : ℂ := ∑ᶠ g, f g

def JpIw : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (g : GL (Ix n) L), ∃ (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) (κ : GL (Ix n) O),
      g = pM a d b * inL κ

def JpHgt : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ nv : Lˣ →* ℝ≥0, NvOK (O := O) nv w → ∀ h : GL (Ix n) L → ℝ≥0, IsHgt (O := O) nv h → ∀ κ : GL (Ix n) O,
      h (inL κ * (tauM w)⁻¹) = (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) ^ (2 * iD (resK κ)) /
        (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) ^ n

def JpUnif : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) (ϖ : O),
    Irreducible ϖ → ∀ (X : Type) [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X) [IsProbabilityMeasure ν]
    [ν.IsMulLeftInvariant] (ρ : X →* GL (Ix n) O), Function.Surjective ρ →
    MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) O))) → ∀ φ : GL (Ix n) O → ℂ,
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∫ x, φ (ρ x) ∂ν = avgK ϖ φ

def JpCmp : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ Ψ : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ, (∀ a d b g, Ψ (pM a d b * g) = Ψ g) →
    ∀ T : GL (Ix n) O → GL (Ix n) (IsLocalRing.ResidueField O), (∀ κ, IsRed (O := O) w κ (T κ)) →
      avgK ϖ (fun κ => Ψ (T κ)) =
        sumG (fun g => (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Ψ g) /
          sumG (fun g : GL (Ix n) (IsLocalRing.ResidueField O) =>
            (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g))

def JpPos : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (n r m : ℕ) (ψ₀ : AddChar k ℂ), ψ₀ ≠ 1 → ∀ β : Matrix (Fin n) (Fin n) k, β.rank = r →
    r ≤ m → ∃ x : ℝ, 0 < x ∧
      sumG (fun g : GL (Ix n) k => ∑ Y : Matrix (Fin n) (Fin n) k,
        (Fintype.card k : ℂ) ^ (r * iD g) * coY ψ₀ β Y * (Fintype.card k : ℂ) ^ (m * iD (g * nU Y))) = x

def JpCondition : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [Fintype (IsLocalRing.ResidueField O)] (n r t : ℕ), r + t = n → 1 ≤ r →
    ∀ ψ₀ : AddChar (IsLocalRing.ResidueField O) ℂ, ψ₀ ≠ 1 →
    ∀ β : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O), β.rank = r →
    ∃ c : ℂ → ℂ, Differentiable ℂ c ∧ c ((t : ℂ) / 2) ≠ 0 ∧
      ∀ (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
      ∀ ℓ : IsLocalRing.ResidueField O → O, (∀ a, IsLocalRing.residue O (ℓ a) = a) →
      ∀ nv : Lˣ →* ℝ≥0, NvOK (O := O) nv w → ∀ h : GL (Ix n) L → ℝ≥0, IsHgt (O := O) nv h →
      ∀ (X : Type) [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X) [IsProbabilityMeasure ν]
        [ν.IsMulLeftInvariant] (ρ : X →* GL (Ix n) O), Function.Surjective ρ →
        MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) O))) → ∀ z : ℂ,
        ∫ x, ∑ Y : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O), coY ψ₀ β Y *
          (((h (inL (ρ x) * nU ((w⁻¹ : Lˣ).1 • liftM (L := L) ℓ Y)) : ℝ≥0) : ℝ) : ℂ) ^ (z + (n : ℂ) / 2) ∂ν = c z

end GlobalTheory.CompanionTheory.Jp

end
