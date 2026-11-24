module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem hgp_twist_tE {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {i j n : ℕ} (h : (i + 1) + j = n)
    (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : HGPg k h)
    (hq : (1 : GL (Fin (n + 1)) k) * ((g : Mir k n) : GL (Fin (n + 1)) k) * (1 : GL (Fin (n + 1)) k)⁻¹ ∈
      parab k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1))))
    (v : ⨂[ℂ] x, TwoT V W x) :
    ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g (tE V W v) =
      tE V W (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩ v) := by
  have hL : leviProj k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1))) ⟨_, hq⟩ =
      leviTwo k (Fin (i + 1)) (Fin (j + 1)) ((gpProjg k h g).1, ((gpProjg k h g).2 : GL (Fin (j + 1)) k)) := by
    have e : (⟨_, hq⟩ : parab k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1)))) = hgpInclg k h g :=
      Subtype.ext (by simp [hgpInclg])
    rw [e]
    funext x
    cases x <;> rfl
  have key : ∀ x : ∀ b, TwoT V W b,
      ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g
          (tE V W (PiTensorProduct.tprod ℂ x)) =
      tE V W (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) := by
    intro x
    set g₁ : GL (Fin (i + 1)) k := (gpProjg k h g).1 with hg₁
    set g₂ : Mir k j := (gpProjg k h g).2 with hg₂
    have hl : ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g
          (tE V W (PiTensorProduct.tprod ℂ x)) =
        ((twist π₁ (dpow (i + 1) (((j + 1 : ℕ) : ℝ) / 2)) g₁ (x false) : V) ⊗ₜ[ℂ]
          (twist (π₂.comp (Mir k j).subtype) (dpowM j (-((i + 1 : ℕ) : ℝ) / 2)) g₂ (x true) : W) : V ⊗[ℂ] W) :=
      (congrArg _ (Exponents.boolTensorEquiv_tprod x)).trans (extTensor_tmul _ _ _ _ _)
    have hr : tE V W (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) =
        ((deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviTwo k (Fin (i + 1)) (Fin (j + 1)) (g₁, (g₂ : GL (Fin (j + 1)) k))) : ℂˣ) : ℂ) •
          ((π₁ g₁ (x false) : V) ⊗ₜ[ℂ] (π₂ (g₂ : GL (Fin (j + 1)) k) (x true) : W) : V ⊗[ℂ] W) := by
      show tE V W (twist (piTensor (twoRep π₁ π₂)) (deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))))
        (leviProj k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1))) ⟨_, hq⟩) (PiTensorProduct.tprod ℂ x)) = _
      rw [hL, twist_apply, piTensor_tprod, map_smul]
      exact congrArg _ (Exponents.boolTensorEquiv_tprod _)
    rw [hl, hr, deltaHalf_two]
    simp only [twist_apply, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, MonoidHom.comp_apply,
      Units.val_mul, dpow, dpowM, detChar_apply]
    have c₁ : ((((j + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) = (Fintype.card (Fin (j + 1)) : ℂ) / 2 := by
      rw [Fintype.card_fin]
      push_cast
      rfl
    have c₂ : ((-((i + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) = -(Fintype.card (Fin (i + 1)) : ℂ) / 2 := by
      rw [Fintype.card_fin]
      push_cast
      rfl
    rw [c₁, c₂, mul_comm]
    rfl
  have := LinearMap.congr_fun (PiTensorProduct.ext (MultilinearMap.ext key) :
    ((((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g) ∘ₗ (tE V W).toLinearMap) =
      (tE V W).toLinearMap ∘ₗ (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩)) v
  exact this

end GlobalTheory.CompanionTheory.BZRes
