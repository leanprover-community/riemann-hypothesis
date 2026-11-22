module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero

namespace I195MixedCoordinates_c8055b1c0896c062cd00c0d6

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_c8055b1c0896c062cd00c0d6

@[expose] public section

noncomputable section

open scoped NNReal
open MeasureTheory Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSW

variable {D : D7}

section SlopeTestRemainingChoices

variable {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r)

def stab : Subgroup (GA D T) where
  carrier := {q | ∃ α : GL (Fin r) (AE D), mt T q ⬝ d.jX = d.jX ⬝ α.1}
  one_mem' := ⟨1, by rw [mt_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩
  mul_mem' := fun ⟨α, h⟩ ⟨β, h'⟩ => ⟨α * β, by
    rw [mt_mul, Matrix.mul_assoc, h', cancel₂ h, Units.val_mul, Matrix.mul_assoc]⟩
  inv_mem' := fun {q} ⟨α, h⟩ => ⟨α⁻¹, by
    have e := cancel₂ h (α⁻¹).1
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at e
    conv_lhs => rw [← e, cancel₂ (mt_inv_mul T q), Matrix.one_mul]⟩

theorem eq_of_mul_jX {q : GA D T} {α : Mx D r r} (h : mt T q ⬝ d.jX = d.jX ⬝ α) : α = d.pX ⬝ (mt T q ⬝ d.jX) := by
  rw [h, cancel₂ d.pX_jX, Matrix.one_mul]

def onX : stab d →* GL (Fin r) (AE D) :=
  MonoidHom.mk' (fun q => q.2.choose) fun p q => Units.ext <| by
    have h1 := p.2.choose_spec
    have h2 := q.2.choose_spec
    have h3 := (p * q).2.choose_spec
    generalize p.2.choose = α, q.2.choose = β, (p * q).2.choose = γ at *
    rw [eq_of_mul_jX d h3, Subgroup.coe_mul, mt_mul, Matrix.mul_assoc, h2, cancel₂ h1, Matrix.mul_assoc,
      cancel₂ d.pX_jX, Matrix.one_mul, Units.val_mul]

theorem mul_jX (q : stab d) : mt T q ⬝ d.jX = d.jX ⬝ (onX d q).1 := q.2.choose_spec

theorem levi_mem (α : GL (Fin r) (AE D)) : d.levi α ∈ stab d := ⟨α, d.levi_jX α⟩

def absDet : stab d →* ℝ≥0 := (absA D).comp (Matrix.GeneralLinearGroup.det.comp (onX d))

def HasIw (K : Subgroup (GA D T)) : Prop := ∀ h : GA D T, ∃ q : stab d, ∃ k ∈ K, h = q * k

theorem continuous_onX : Continuous (onX d) := by
  have h : Continuous fun q : stab d => (onX d q).1 :=
    (continuous_const.matrix_mul (((continuous_mt T).comp continuous_subtype_val).matrix_mul continuous_const)).congr
      fun q => (eq_of_mul_jX d (mul_jX d q)).symm
  exact Units.continuous_iff.2 ⟨h, (h.comp continuous_inv).congr fun q => by simp⟩

theorem continuous_absDet : Continuous (absDet d) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact continuous_absE.comp (Units.continuous_iff.2
    ⟨(Units.continuous_val.comp (continuous_onX d)).matrix_det,
      (Units.continuous_coe_inv.comp (continuous_onX d)).matrix_det.congr fun p => by
        rw [MonoidHom.comp_apply, ← map_inv]; rfl⟩)

theorem isClosed_stab : IsClosed (stab d : Set (GA D T)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  haveI := t2Space_tensorProduct_finiteExtension (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have h1 : IsClosed {q : GA D T | mt T q ⬝ d.jX = d.jX ⬝ (d.pX ⬝ (mt T q ⬝ d.jX))} :=
    isClosed_eq ((continuous_mt T).matrix_mul continuous_const)
      (continuous_const.matrix_mul (continuous_const.matrix_mul ((continuous_mt T).matrix_mul continuous_const)))
  have key : ∀ p q : GA D T, mt T q ⬝ d.jX = d.jX ⬝ (d.pX ⬝ (mt T q ⬝ d.jX)) → mt T p * mt T q = 1 →
      d.pX ⬝ (mt T p ⬝ d.jX) * (d.pX ⬝ (mt T q ⬝ d.jX)) = 1 := fun p q hq e => by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hq, cancel₂ e, Matrix.one_mul, d.pX_jX]
  convert h1.inter (h1.preimage continuous_inv) using 1
  refine Set.ext fun q => ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨⟨_, _, key q q⁻¹ h.2 (mt_mul_inv T q),
    key q⁻¹ q h.1 (mt_inv_mul T q)⟩, h.1⟩⟩
  · obtain ⟨α, h⟩ := h
    exact h.trans (congrArg _ (eq_of_mul_jX d h))
  · obtain ⟨α, h⟩ := inv_mem h
    exact h.trans (congrArg _ (eq_of_mul_jX d h))

variable (b : GL (Fin T.rank) (AE D))

def rhoH (T : HSp D) (r : ℕ) : ℝ := ((T.rank : ℝ) - r) / 2

end SlopeTestRemainingChoices

section Schwartz

variable {S T T' : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))

def projK {K : Subgroup (GA D T)} (ν : Measure K) (φ : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ∫ k, om (1, (k : GA D T)) φ w ∂ν

def ikeda (ψ : AddChar (AF D.host.F) ℂ) {t : ℕ} (d : HypDec T T' t) (μ : Measure (Mx D t S.rank))
    (𝓕 : Set (Mx D t S.rank)) (φ : WO S T → ℂ) : WO S T' → ℂ := (_root_.I195MixedCoordinates_c8055b1c0896c062cd00c0d6.target d) S ψ μ 𝓕 φ 0

theorem ikeda_apply (ψ : AddChar (AF D.host.F) ℂ) {t : ℕ} (d : HypDec T T' t) (μ : Measure (Mx D t S.rank))
    (𝓕 : Set (Mx D t S.rank)) (φ : WO S T → ℂ) (w : WO S T') :
    ikeda ψ d μ 𝓕 φ w = ∫ ξ in 𝓕, φ (d.jX ⬝ ξ + d.j0 ⬝ w) ∂μ := by
  refine integral_congr_ae (.of_forall fun ξ => (d.integrandT_eq φ 0 ξ w).trans ?_)
  rw [map_zero, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]
  rfl

variable (θ : InfFam D) (τ : D.what₂.Tau)

end Schwartz

section Integrals

variable {S T T₀ : HSp D} {r : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
  (m : Measure (GA D T))

variable (θ : InfFam D) (τ : D.what₂.Tau) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D))

end Integrals

end GlobalTheory.RegSW

namespace GlobalTheory.Published

open GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)

end GlobalTheory.Published

end
