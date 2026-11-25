module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Columns.CoefficientsModP

@[expose] public section

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

section

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (lam : ι → DomWeight n)

theorem dualFr_tauLat_isLattice (τ : ι) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsFullLattice K (dualFr (tauLat emb τ L)) :=
  (@dualFrLattice K _ _ starRingOfComm n 1 _ (by simp) (tauLatLattice E K ι n emb τ L hL)).1

theorem nabAtr_isLattice (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsFullLattice K (nabAtr emb lam L) :=
  (nabDelLattice K ι n lam _ fun τ => dualFr_tauLat_isLattice emb τ L hL).1

end

end Formalism.L2.DIV
