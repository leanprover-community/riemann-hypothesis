module

public import Formalism.SatakeDualWeyl.DefsCS
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

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG Formalism.UG.CS

theorem class_injective_of_span_recovery (hSpanRecover : Formalism.UG.CS.SpanRecover)
    (hGlobLatEquiv : Formalism.UG.CS.GlobLatEquiv) : Formalism.UG.CS.ClassInj := by
  intro F E _ _ _ _ _ n _ _ σ J Λ hfin hspan g g' γ hγ hlat
  set A := FiniteAdeleRing (𝓞 F) F with hA
  set L := latS (F := F) A (tensInt (F := F) A (intOE E) (intAd F)) Λ with hL
  set γA : GL n (E ⊗[F] A) := bc (inclE (F := F) A) γ with hγA

  have hsig : ∀ e : E, sigR σ A (inclE (F := F) A e) = inclE (F := F) A (σ e) := by
    intro e
    simp [sigR, inclE]
  have hγm : (γA : Matrix n n (E ⊗[F] A)) = (γ : Matrix n n E).map (inclE (F := F) A) := rfl
  have hγU : γA ∈ UPts σ J A := by
    change cT (sigR σ A) (γA : Matrix n n (E ⊗[F] A)) * J.map (inclE (F := F) A)
      * (γA : Matrix n n (E ⊗[F] A)) = J.map (inclE (F := F) A)
    have h0 : cT (σ : E →+* E) (γ : Matrix n n E) * J * (γ : Matrix n n E) = J := hγ
    have hc : cT (sigR σ A) (γA : Matrix n n (E ⊗[F] A))
        = (cT (σ : E →+* E) (γ : Matrix n n E)).map (inclE (F := F) A) := by
      ext i j
      simp [cT, hγm, hsig]
    rw [hc, hγm, ← Matrix.map_mul, ← Matrix.map_mul, h0]

  have heq : globLat (γA * (g' : GL n (E ⊗[F] A))) Λ = globLat (g : GL n (E ⊗[F] A)) Λ := by
    have h1 := hGlobLatEquiv F E n Λ γ (g' : GL n (E ⊗[F] A)) 1 (one_mem _)
    rw [mul_one] at h1
    rw [h1, hlat]
  have hR : ∀ u : n → E ⊗[F] A,
      (((g : GL n (E ⊗[F] A))⁻¹ : GL n (E ⊗[F] A)) : Matrix n n _) *ᵥ u ∈ L ↔
        (((γA * (g' : GL n (E ⊗[F] A)))⁻¹ : GL n (E ⊗[F] A)) : Matrix n n _) *ᵥ u ∈ L := by
    intro u
    have h1 := hSpanRecover F E n Λ hfin hspan (g : GL n (E ⊗[F] A)) u
    have h2 := hSpanRecover F E n Λ hfin hspan (γA * (g' : GL n (E ⊗[F] A))) u
    rw [heq] at h2
    exact h1.symm.trans h2
  set k : GL n (E ⊗[F] A) := (g : GL n (E ⊗[F] A))⁻¹ * (γA * (g' : GL n (E ⊗[F] A))) with hk
  have hkS : k ∈ stabGL L := by
    intro x
    have h := hR (((γA * (g' : GL n (E ⊗[F] A)) : GL n (E ⊗[F] A)) : Matrix n n _) *ᵥ x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h
    exact h.symm
  have hkU : k ∈ UPts σ J A :=
    mul_mem (inv_mem g.2) (mul_mem hγU g'.2)
  rw [DoubleCoset.eq]
  refine ⟨⟨γA⁻¹, inv_mem hγU⟩, ?_, ⟨k, hkU⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact ⟨γ⁻¹, inv_mem hγ, map_inv _ _⟩
  · rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨hkU, hkS⟩
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hk]
    group

end Formalism.UG.P
