import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTateGaloisAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsFixedFrobeniusPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TlLevSurjKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K] [Fintype K]

local notation "Fr" K => FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)


variable (l : ℕ) [Fact l.Prime]





abbrev tv (A : AbVar K) : Tl l A →ₗ[ℤ_[l]] Vl l A := TensorProduct.mk ℤ_[l] ℚ_[l] (Tl l A) 1

instance isLocalizedModule_tv (A : AbVar K) : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (tv l A) := by
  rw [isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l]]
  exact TensorProduct.isBaseChange _ _ _



theorem tv_injective (hl : (l : K) ≠ 0) (A : AbVar K) : Function.Injective (tv l A) := by
  haveI := (tl_free_finrank K l hl A).1
  intro u v h
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ_[l]) (tv l A)).1 h
  exact smul_right_injective (Tl l A) (nonZeroDivisors.coe_ne_zero c) hc



end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar


end GlobalTheory.AV.AbVar
