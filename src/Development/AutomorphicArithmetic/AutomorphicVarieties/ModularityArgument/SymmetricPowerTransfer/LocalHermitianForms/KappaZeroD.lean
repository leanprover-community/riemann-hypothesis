module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LcountNorm
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

namespace UpperTheory.V.Z.Sym.Loc

open QuadraticAlgebra Glob

section

variable (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K] {Δ τ : K}

abbrev dS (j : (Etau K τ)ˣ →* DX Δ) (γ : DX Δ) : ℂ :=
  orb j (Cint O τ) (MonoidHom.id _) (ZD Δ ⊔ KD Δ O) (fun g => one (g ∈ KD Δ O)) γ

abbrev dK (j : (Etau K τ)ˣ →* DX Δ) (χ : Kˣ →* ℂˣ) (z : (Etau K τ)ˣ) : ℂ :=
  orb j (Cint O τ) (MonoidHom.id _) (ZD Δ ⊔ KD Δ O) (fZD O χ) (j z)

end

def DIso : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    ∃ φ : DX Δ ≃* GL (Fin 2) K, (∀ g, φ g ∈ KG O K ↔ g ∈ KD Δ O) ∧
    (∀ z g, IsScal z g ↔ φ g = Matrix.GeneralLinearGroup.scalar (Fin 2) z) ∧
    (∀ g, algebraMap K (Lsq K Δ) (φ g : Matrix (Fin 2) (Fin 2) K).det = (mt g).det) ∧
    ∀ (τ : K) (γ : DX Δ) (j : (Etau K τ)ˣ →* DX Δ), HasTr γ τ → IsEmb τ γ j →
      ∃ j' : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K, j' ω = (φ γ : Matrix (Fin 2) (Fin 2) K) ∧ (j' ω).trace = τ ∧ ∀ z, φ (j z) = jU j' z

def DOrb : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (γ : DX Δ) (j : (Etau K τ)ˣ →* DX Δ), HasTr γ τ → IsEmb τ γ j →
    ∃ j' : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K, (j' ω).trace = τ ∧
      (∀ a : (Etau K τ)ˣ, (a : Etau K τ) = ω → dS O j γ = gOrb O j' 1 a) ∧ ∀ χ : Kˣ →* ℂˣ, Unr O χ → ∀ z, dK O j χ z = gOrb O j' χ z

def FinD : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (γ : DX Δ) (j : (Etau K τ)ˣ →* DX Δ), HasTr γ τ → IsEmb τ γ j →
    FinOrb j (MonoidHom.id _) (ZD Δ ⊔ KD Δ O) (fun g => one (g ∈ KD Δ O)) γ ∧
    (∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → ∀ χ : Kˣ →* ℂˣ, FinOrb j (MonoidHom.id _) (ZD Δ ⊔ KD Δ O) (fZD O χ) (j z)) ∧
    ∀ y : DX Δ ⧸ (ZD Δ ⊔ KD Δ O), (MulAction.stabilizer (DX Δ) y).comap j ≤ Cint O τ ∧
      ((MulAction.stabilizer (DX Δ) y).comap j).relIndex (Cint O τ) ≠ 0

def OneD : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (γ : DX Δ) (j : (Etau K τ)ˣ →* DX Δ), HasTr γ τ → IsEmb τ γ j →
    γ ∈ KD Δ O → (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) → (ZD Δ ⊔ KD Δ O).comap j = Cint O τ ∧
    (∀ y, y⁻¹ * γ * y ∈ ZD Δ ⊔ KD Δ O → ∃ t, ∃ u ∈ ZD Δ ⊔ KD Δ O, y = j t * u) ∧
    ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → j z ∈ KD Δ O ∧ ∀ y, y⁻¹ * j z * y ∈ ZD Δ ⊔ KD Δ O → ∃ t, ∃ u ∈ ZD Δ ⊔ KD Δ O, y = j t * u

def FzdLaw : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    ∀ χ : Kˣ →* ℂˣ, Unr O χ → (∀ g : DX Δ, g ∉ ZD Δ ⊔ KD Δ O → fZD O χ g = 0) ∧
    ∀ (z : Kˣ) (s k : DX Δ), IsScal z s → k ∈ KD Δ O → fZD O χ (s * k) = (((χ z)⁻¹ : ℂˣ) : ℂ)

def FinUq : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ (δ : U3 Δ) (ι : (Etau K τ)ˣ →* U3 Δ) (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)), Models c d m δ ι P →
    orb ι (Cint O τ) (theta Δ) (KU O Δ) (fun g => one (g ∈ KU O Δ)) δ = lcount O c d m ∧
    FinOrb ι (theta Δ) (KU O Δ) (fun g => one (g ∈ KU O Δ)) δ ∧
    ∀ y : U3 Δ ⧸ KU O Δ, (MulAction.stabilizer (U3 Δ) y).comap ι ≤ Cint O τ ∧ ((MulAction.stabilizer (U3 Δ) y).comap ι).relIndex (Cint O τ) ≠ 0

end UpperTheory.V.Z.Sym.Loc
