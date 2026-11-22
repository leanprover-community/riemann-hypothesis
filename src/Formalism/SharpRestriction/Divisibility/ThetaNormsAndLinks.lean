module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ThetaNormsAndLinks

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

namespace MetX

variable {D : D7} {r j p : ℕ} {Lc : ModuliIntegralCharts.Loc D r j p} {G : LiftErrorLocal.GeoX Lc} (M : MetX G)

end MetX

attribute [instance] QPack.rA QPack.aT QPack.mT QPack.aM QPack.mM

section Int

variable {D : D7} {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

end Int

section admitted

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (Z : Loc8 X)

end admitted

section Conclusion₂

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

end Conclusion₂

section Joint

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

end Joint

section Stmt

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (Z : Loc8 X)

end Stmt

theorem vAdd_nonneg_int {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    0 ≤ vAdd la (a : K) := by
  unfold vAdd
  have h := la.valuation_le_one (K := K) a
  by_cases h0 : la.valuation K (a : K) = 0
  · rw [h0]; simp
  · have := (WithZero.log_le_log h0 one_ne_zero).2 h
    simp at this
    omega

section Forms

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (W : WeightAlgebra.PJ D B P j)

end Forms

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch)
  (ZF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc8 (XF x hx i))

end Fam

end Formalism.MainNotions.ThetaNormsAndLinks

end
