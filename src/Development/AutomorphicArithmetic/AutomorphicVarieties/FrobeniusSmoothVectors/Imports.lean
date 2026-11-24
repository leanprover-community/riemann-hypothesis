module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.star :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → (∀ g : F.G0, F.star (F.star g) = g) ∧ (∀ g h : F.G0, F.star (g * h) = F.star h * F.star g) ∧ (∀ g : F.G0, F.Ψ (F.star g) = (F.Ψ g)⁻¹) ∧ Continuous F.star ∧ ∀ {n : ℕ} {K : Type} [CommRing K] (ρ : NRep F n K) (g : F.G0) (i j : Fin n), ρ.r (F.star g) i j = ρ.r g j.rev i.rev := by
  intro l _ k _ _ F C₀ hF
  have hs : ∀ g : F.G0, ((F.star g : F.G0) : F.Γ) = F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := fun g => by
    simp [Frame.star, Frame.conj, MulAut.conjNormal_apply, mul_assoc]
  have hc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
  refine ⟨fun g => ?_, fun g h => ?_, fun g => ?_, ?_, fun {n} {K} _ ρ g i j => ?_⟩
  · apply Subtype.ext
    rw [hs, hs, hc]
    simp only [_root_.mul_inv_rev, inv_inv, hc]
    calc F.c * (F.c * ((g : F.Γ) * F.c)) * F.c = (F.c * F.c) * (g : F.Γ) * (F.c * F.c) := by group
      _ = g := by rw [hF.c_sq]; group
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hs, _root_.mul_inv_rev, hc]
    calc F.c * ((h : F.Γ)⁻¹ * (g : F.Γ)⁻¹) * F.c
        = F.c * (h : F.Γ)⁻¹ * (F.c * F.c) * (g : F.Γ)⁻¹ * F.c := by rw [hF.c_sq]; group
      _ = F.c * (h : F.Γ)⁻¹ * F.c * (F.c * (g : F.Γ)⁻¹ * F.c) := by group
  · rw [hs, map_mul, map_mul, map_inv, map_inv, hF.Ψ_c]
    simp
  · refine continuous_induced_rng.2 ?_
    have : (fun g : F.G0 => ((F.star g : F.G0) : F.Γ)) = fun g : F.G0 => F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := funext hs
    change Continuous (fun g : F.G0 => ((F.star g : F.G0) : F.Γ))
    rw [this]
    exact (continuous_const.mul continuous_subtype_val.inv).mul continuous_const
  · rw [ρ.pol]
    simp only [Matrix.mul_apply, Jmat, Matrix.transpose_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
    have h : ∀ a : Fin n, (j = a.rev) ↔ (a = j.rev) := fun a => by
      constructor <;> rintro rfl <;> simp
    simp [h]
