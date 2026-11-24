module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.SplitS
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem sigL_zero' {K : Type} [Field K] (Δ τ : K) : sigL (0 : EL Δ τ) = 0 := by
  ext <;> simp [sigL.eq_1]

private theorem herm_pair_zero_eq {K : Type} [Field K] (Δ τ : K) (c : K) (m : EL Δ τ) (x : Sp Δ τ) (a : Lsq K Δ) :
    herm c m x ((a, 0) : Sp Δ τ) = algebraMap K (Lsq K Δ) c * x.1 * star a := by
  rw [herm.eq_1]
  simp [sigL_zero']

theorem UpperTheory.V.Z.Sym.Loc.One.fst :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
        τ ∈ (algebraMap O K).range → (∃ u : Oˣ, algebraMap O K u = 2 - τ) → ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ S₀ S₁ : Set (Sp Δ τ), IsFix O c d m S₀ → IsFix O c d m S₁ →
        ∀ a : Lsq K Δ, ((a, 0) : Sp Δ τ) ∈ S₀ → ((a, 0) : Sp Δ τ) ∈ S₁ := by
  intro O K _ _ _ _ _ Δ τ hL hτ hu c d m hD S₀ S₁ h₀ h₁ a ha
  have hs₁ := One.splitS O K Δ τ hL hτ hu c d m hD S₁ h₁
  have hconj : ∀ S : Set (Sp Δ τ), IsFix O c d m S → ∀ b : Lsq K Δ,
      ((b, 0) : Sp Δ τ) ∈ S → ((star b, 0) : Sp Δ τ) ∈ S := by
    intro S hS b hb
    rw [← hS.stab]
    refine ⟨(b, 0), hb, ?_⟩
    rw [semi.eq_1]
    simp [sigL_zero']
  have hsq : ∀ S : Set (Sp Δ τ), IsFix O c d m S → ∀ b : Lsq K Δ,
      ((b, 0) : Sp Δ τ) ∈ S → IsInt O (algebraMap K (Lsq K Δ) c * b * b) := by
    intro S hS b hb
    have h := (hS.dual _).1 (hconj S hS b hb) (b, 0) hb
    rw [herm_pair_zero_eq, star_star] at h
    exact h
  rw [h₁.dual]
  intro x hx
  rw [herm_pair_zero_eq]
  have hx1 : ((x.1, 0) : Sp Δ τ) ∈ S₁ := hs₁.2.2.1 x hx
  have e1 := hsq S₁ h₁ x.1 hx1
  have e2 := hsq S₀ h₀ (star a) (hconj S₀ h₀ a ha)
  rw [IsInt.eq_1] at e1 e2 ⊢
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  have e3 : (algebraMap K (Lsq K Δ) c * x.1 * star a) ^ 2 =
      (algebraMap K (Lsq K Δ) c * x.1 * x.1) * (algebraMap K (Lsq K Δ) c * star a * star a) := by
    ring
  rw [e3]
  exact e1.mul e2
