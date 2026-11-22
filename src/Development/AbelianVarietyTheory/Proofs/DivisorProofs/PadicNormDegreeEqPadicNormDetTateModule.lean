module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetEqInvCardCokerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapInjectiveCardCokerOfIsogenyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffTateModuleMapInjectiveAndIsogenyIffStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem norm_natCast_padicInt (l : ℕ) [Fact l.Prime] {n : ℕ} (hn : n ≠ 0) :
    ‖((n : ℕ) : ℤ_[l])‖ = (l : ℝ) ^ (-(padicValNat l n : ℤ)) := by
  rw [PadicInt.norm_def]
  push_cast
  have h := Padic.eq_padicNorm (p := l) (n : ℚ)
  push_cast at h
  rw [h, padicNorm.eq_zpow_of_ne_zero (by exact_mod_cast hn)]
  push_cast
  rw [Nat.padicValNat_def, padicValRat_of_nat]

end GlobalTheory.AV.AbVar
