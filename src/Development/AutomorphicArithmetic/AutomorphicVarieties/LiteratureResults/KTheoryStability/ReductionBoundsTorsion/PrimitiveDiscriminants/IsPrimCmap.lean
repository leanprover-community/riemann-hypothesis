import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Mathlib

section
open Matrix
open scoped Kronecker

namespace PositivityTheory.KB.LargePrimeDiscriminant

variable {R S : Type} [CommRing R] [CommRing S]

noncomputable def resRing (d n : ℕ) (ρ : S →+* Matrix (Fin d) (Fin d) R) :
    Matrix (Fin n) (Fin n) S →+* Matrix (Fin (d * n)) (Fin (d * n)) R :=
  ((Matrix.reindexAlgEquiv R R ((Equiv.prodComm (Fin n) (Fin d)).trans finProdFinEquiv)).toRingEquiv.toRingHom.comp
    (Matrix.compRingEquiv (Fin n) (Fin d) R).toRingHom).comp ρ.mapMatrix

noncomputable def res (d n : ℕ) (ρ : S →+* Matrix (Fin d) (Fin d) R) :
    GL (Fin n) S →* GL (Fin (d * n)) R :=
  Units.map (resRing d n ρ).toMonoidHom

end PositivityTheory.KB.LargePrimeDiscriminant
end

section
noncomputable section

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB

namespace LargePrimeDiscriminant

theorem isCyc_cmap (hC : SChain) {G H : Type} [Group G] [Group H] (f : G →* H) {m : ℕ}
    {z : Chn G (m + 1)} (hz : IsCyc z) : IsCyc (cmap f (m + 1) z) := by
  unfold IsCyc at hz ⊢
  rw [hC.2.1 G H f m z, hz, map_zero]

end LargePrimeDiscriminant

end PositivityTheory.KB

end
end
