module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxPointCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxCut
import Mathlib.Tactic.TypeStar

@[expose] public section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
universe u

theorem prime_eq_of_isLocalization_atPrime' {F : Type*} [Field F] {B R : Subring F} (h : B ≤ R)
    (𝔭₁ 𝔭₂ : Ideal B) [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (hl₁ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₁)
    (hl₂ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₂) : 𝔭₁ = 𝔭₂ := by
  let _ := (Subring.inclusion h).toAlgebra
  rw [← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₁,
    ← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₂]

theorem BlowUpOverLocMaxPoint.proof (h₁ : BlowUpOverLocMaxCentre.Statement.{u})
    (h₂ : BlowUpOverLocFibreMinimal.Statement.{u}) (h₃ : BlowUpOverLocPointDeg.Statement.{u}) :
    BlowUpOverLocMaxPoint.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  intro 𝔫 h𝔫
  obtain ⟨W', hp, hhom, hr, hle, hc, h, hl⟩ :=
    h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel 𝔫 h𝔫
  have hmin := h₂ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel W' hp hhom hr hle hc
  obtain ⟨_, 𝔫', h𝔫', hl', hdeg⟩ :=
    h₃ O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel W' hmin hr hc
  obtain rfl := prime_eq_of_isLocalization_atPrime' h 𝔫 𝔫' hl hl'
  exact ⟨W', ⟨hmin, hr, hc⟩, ⟨h, hl⟩, hdeg⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
