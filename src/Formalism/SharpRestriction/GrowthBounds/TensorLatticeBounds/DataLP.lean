import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataLPa
import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataLPb
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.JOInjective

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

abbrev Z0 (n' : ℕ) : Fin n' → Fin (0 + 1) → ℤ := fun _ _ => 0


def oneV (Kf : Type) [Field Kf] (n' : ℕ) : Vsp Kf (Z0 n') := ⟨1, one_mem_Vsp Kf⟩

def evV (Kf : Type) [Field Kf] (n' : ℕ) : Module.Dual Kf (Vsp Kf (Z0 n')) := (ccL Kf _).comp (Vsp Kf (Z0 n')).subtype





theorem ext_lat (h : HidaSetting p n' W Qq O Kf ι σ j w) (L : Submodule W (Fin (0 + 1) → Qq)) (hL : IsLattice W L) (s : ℕ) :
    IsLattice O (extO O ι σ s L) :=
  LatticeSystems.je_extO_lat (gat1 h) (0 : Fin 1) s L hL







end Formalism.MainNotions.G.Inhab

end
