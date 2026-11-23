module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.exists_linear_section_automorphicFunctions_of_free :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub), X.Free τ θ U → ∀ (c N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → (∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j) → ∀ tt : Gp → X.I.T, (∀ b ∈ X.I.Iw 0, ∀ s : X.I.T, tt (s * b) = s * tt b) → ∃ s : (Fin N × Fin m → A) →ₗ[A] X.Fn A m, ∀ v γ i, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, s v (X.glob γ * x i * ((u : Ga), b)) = (((θ (tt b))⁻¹ : Aˣ) : A) • ((τ u⁻¹ : Matrix (Fin m) (Fin m) A) *ᵥ fun j => v (i, j)) := by
  intro Γ Ga Gp _ _ _ X A _ m τ θ U hF c N x hcov hsep tt htt
  choose γ0 i0 u0 hu0 b0 hb0 hg using hcov
  have hle : X.I.Iw c ≤ X.I.Iw 0 := sup_le_sup_left (X.I.Nm_anti (Nat.zero_le c)) _
  refine ⟨{ toFun := fun v g => (((θ (tt (b0 g)))⁻¹ : Aˣ) : A) •
              ((τ (u0 g)⁻¹ : Matrix (Fin m) (Fin m) A) *ᵥ fun j => v (i0 g, j))
            map_add' := fun v w => ?_
            map_smul' := fun a v => ?_ }, fun v γ i u hu b hb => ?_⟩
  · funext g
    rw [Pi.add_apply, ← smul_add, ← mulVec_add]
    rfl
  · funext g
    rw [Pi.smul_apply, RingHom.id_apply, smul_comm a, ← mulVec_smul _ a]
    rfl
  · have h := hg (X.glob γ * x i * ((u : Ga), b))
    have hu1 := hu0 (X.glob γ * x i * ((u : Ga), b))
    have hb1 := hb0 (X.glob γ * x i * ((u : Ga), b))
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    generalize γ0 (X.glob γ * x i * ((u : Ga), b)) = γ1 at h
    generalize i0 (X.glob γ * x i * ((u : Ga), b)) = i1 at h ⊢
    generalize u0 (X.glob γ * x i * ((u : Ga), b)) = u1 at h hu1 ⊢
    generalize b0 (X.glob γ * x i * ((u : Ga), b)) = b1 at h hb1 ⊢
    have hw : ((((u1 * u⁻¹ : X.Ub) : Ga), b1 * b⁻¹) : Ga × Gp) = ((u1 : Ga), b1) * ((u : Ga), b)⁻¹ := rfl
    have hwU : u1 * u⁻¹ ∈ U := mul_mem hu1 (inv_mem hu)
    have hwI : b1 * b⁻¹ ∈ X.I.Iw c := mul_mem hb1 (inv_mem hb)
    have hi : i1 = i := by
      refine hsep i1 i (γ⁻¹ * γ1) _ hwU _ hwI ?_
      rw [hw, map_mul, map_inv, ← mul_assoc, mul_assoc (X.glob γ)⁻¹, mul_assoc (X.glob γ)⁻¹, ← h]
      group
    subst hi
    obtain ⟨-, hs, he⟩ := hF (x i1) (γ1⁻¹ * γ) _ hwU _ (hle hwI) (by
      rw [hw, map_mul, map_inv, mul_assoc, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← h]
      group)
    have ht : tt b1 = ⟨b1 * b⁻¹, hs⟩ * tt b := by
      rw [← htt b (hle hb) ⟨b1 * b⁻¹, hs⟩]
      simp
    have hτ : (τ u1⁻¹ : Matrix (Fin m) (Fin m) A) =
        (θ ⟨b1 * b⁻¹, hs⟩ : A) • (τ u⁻¹ : Matrix (Fin m) (Fin m) A) := by
      have e : u⁻¹ = u1⁻¹ * (u1 * u⁻¹) := by group
      rw [e, map_mul, Units.val_mul, ← Matrix.mul_smul, he, Matrix.mul_one]
    rw [ht, hτ, map_mul, smul_mulVec, smul_smul, ← Units.val_mul]
    congr 2
    rw [mul_inv, mul_right_comm, inv_mul_cancel, one_mul]
