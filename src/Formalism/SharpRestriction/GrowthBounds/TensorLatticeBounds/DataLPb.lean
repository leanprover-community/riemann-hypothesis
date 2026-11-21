import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataLoc

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

def gen (Qq : Type) [Field Qq] (p : ℕ) (a : ℤ) : Fin 1 → Qq := fun _ => (p : Qq) ^ a

theorem gen_mem (a : ℤ) : gen Qq p a ∈ line W (Qq := Qq) p a := Submodule.mem_span_singleton_self _




def toQuot (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] (p : ℕ) (a : ℤ) :
    W →ₗ[W] (↥(line W (Qq := Qq) p a) ⧸ Submodule.comap (line W (Qq := Qq) p a).subtype (line W p (a + 1))) :=
  (Submodule.mkQ _).comp (LinearMap.toSpanSingleton W _ ⟨gen Qq p a, Submodule.mem_span_singleton_self _⟩)




def edge1 (W : Type) (Qq : Type) [CommRing W] [Field Qq] [Algebra W Qq] (p : ℕ) (a : ℤ) : Edge W Qq 1 :=
  ⟨line W p (a + 1), line W p a⟩



end Formalism.MainNotions.G.Inhab

end
