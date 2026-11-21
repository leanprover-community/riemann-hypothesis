import Formalism.LocalToGlobal.Columns.CoefficientsModP

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

section

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (lam : ι → DomWeight n)



theorem dualFr_tauLat_isLattice (τ : ι) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice K (dualFr (tauLat emb τ L)) :=
  (@dualFrLattice K _ _ starRingOfComm n 1 _ (by simp) (tauLatLattice E K ι n emb τ L hL)).1

theorem nabAtr_isLattice (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice K (nabAtr emb lam L) :=
  (nabDelLattice K ι n lam _ fun τ => dualFr_tauLat_isLattice emb τ L hL).1

theorem delAtr_isLattice (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice K (delAtr emb lam L) :=
  (nabDelLattice K ι n lam _ fun τ => dualFr_tauLat_isLattice emb τ L hL).2

omit [NumberField E] [NumberField K] [Fintype ι] in
theorem isUnit_det_gramK (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det) (τ : ι) : IsUnit (gramK emb J τ).det := by
  have : (gramK emb J τ).det = emb τ J.det := ((emb τ).map_det J).symm
  rw [this]
  exact hJ.map _

omit [NumberField E] [NumberField K] [Fintype ι] in
theorem isUnit_det_gramKd (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det) (τ : ι) : IsUnit (gramKd emb J τ).det := by
  unfold gramKd
  rw [Matrix.det_transpose, Matrix.det_nonsing_inv]
  have := isUnit_det_gramK emb J hJ τ
  unfold gramK at this
  exact this.ringInverse

variable [StarRing K]



variable (cE : E →+* E) (hc : ∀ τ x, star (emb τ x) = emb τ (cE x)) (J : Matrix (Fin n) (Fin n) E)
  (hJ : Formalism.UG.IsHerm cE J) (hdet : IsUnit J.det) (L L' : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
  (hL' : ∀ y, y ∈ L' ↔ ∀ x ∈ L, Formalism.UG.hform cE J x y ∈ (algebraMap (𝓞 E) E).range)

include hc hJ hdet hL hL'



end

end Formalism.L2.DIV
