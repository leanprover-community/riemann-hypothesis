import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfForallMemDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyGenInt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

theorem value_mem_valuationSubring (κ : Rule) (hU : UnitSp κ) (S K : Type) [CommRing S] [Field K] [CharZero K] [Algebra S K]
    (y : KeyIn S) (x : KeyIn K) (h : KeyPB x y (algebraMap S K)) (V : ValuationSubring K) (hV : IsDiscreteValuationRing V)
    (hS : ∀ s : S, algebraMap S K s ∈ V) : (κ K x : K) ∈ V ∧ (κ K x : K)⁻¹ ∈ V := by
  let j : S →+* V := (algebraMap S K).codRestrict V.toSubring hS
  obtain ⟨yV, hyV⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y j
  have hc : (algebraMap V K).comp j = algebraMap S K := RingHom.ext fun _ => rfl
  have hx : KeyPB x yV (algebraMap V K) :=
    GlobalTheory.KeyCancel.keyPB_cancel S V K y yV x j (algebraMap V K) hyV (by rw [hc]; exact h)
  obtain ⟨u, hu, -⟩ := hU V K yV x hx
  refine ⟨?_, ?_⟩
  · rw [hu]; exact (u : V).2
  · have : (κ K x : K)⁻¹ = algebraMap V K (u⁻¹ : Vˣ) := by
      rw [hu]
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← map_mul, Units.mul_inv, map_one]
    rw [this]; exact ((u⁻¹ : Vˣ) : V).2

theorem isIntegral_value : ∀ κ : Rule, UnitSp κ → ∀ (S K : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field K]
    [CharZero K] [Algebra S K] [IsFractionRing S K] (y : KeyIn S) (x : KeyIn K), KeyPB x y (algebraMap S K) →
    IsIntegral S (κ K x : K) ∧ IsIntegral S ((κ K x : K)⁻¹) := by
  intro κ hU S K _ _ _ _ _ _ _ y x h
  exact ⟨GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring S K _ fun V hV hS => (value_mem_valuationSubring κ hU S K y x h V hV hS).1,
    GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring S K _ fun V hV hS => (value_mem_valuationSubring κ hU S K y x h V hV hS).2⟩

end GlobalTheory.KeyGenInt
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyValUnit

theorem valUnit : ∀ κ : Rule, Funct κ → UnitSp κ → ValUnit κ := by
  intro κ hF hU S V K _ _ _ _ _ _ _ _ _ g y x hx
  have := RingHom.ker_isPrime g
  let S₀ := S ⧸ RingHom.ker g
  let K₀ := FractionRing S₀
  let g₀ : S₀ →+* V := RingHom.kerLift g
  let f₀ : S₀ →+* K := (algebraMap V K).comp g₀
  have hf₀ : Function.Injective f₀ := (IsFractionRing.injective V K).comp (RingHom.kerLift_injective g)
  let j : K₀ →+* K := IsFractionRing.lift hf₀
  have hj : j.comp (algebraMap S₀ K₀) = (algebraMap V K).comp g₀ :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hf₀ a
  have : CharZero K₀ := j.charZero
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y (Ideal.Quotient.mk (RingHom.ker g))
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y₀ (algebraMap S₀ K₀)
  have e : j.comp ((algebraMap S₀ K₀).comp (Ideal.Quotient.mk (RingHom.ker g))) = (algebraMap V K).comp g := by
    rw [← RingHom.comp_assoc, hj]
    exact RingHom.ext fun a => congrArg (algebraMap V K) (RingHom.kerLift_mk g a)
  have hxj : KeyPB x x₀ j := GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y x₀ x _ _
    (GlobalTheory.keyPB_trans _ _ _ y y₀ x₀ _ _ hy₀ hx₀) (e.symm ▸ hx)
  have hval := hF K₀ K j x₀ x hxj
  obtain ⟨h₁, h₂⟩ := GlobalTheory.KeyGenInt.isIntegral_value κ hU S₀ K₀ y₀ x₀ hx₀
  have h₁' : IsIntegral V (κ K x : K) := hval ▸ h₁.map_of_comp_eq g₀ j hj.symm
  have h₂' : IsIntegral V ((κ K x : K)⁻¹) := by
    rw [hval, ← map_inv₀]
    exact h₂.map_of_comp_eq g₀ j hj.symm
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 h₁'
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 h₂'
  have hab : a * b = 1 := IsFractionRing.injective V K (by
    rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ (κ K x).ne_zero])
  exact ⟨Units.mkOfMulEqOne a b hab, ha.symm⟩

end GlobalTheory.KeyValUnit
end
