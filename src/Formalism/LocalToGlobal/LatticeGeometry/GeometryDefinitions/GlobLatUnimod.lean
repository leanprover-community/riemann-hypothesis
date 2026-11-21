import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.DualFrame
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox

noncomputable section

open Module Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P

namespace Formalism.L2.Geo.Def.G1

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem star_int (r : 𝓞 E) :
    star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := by
  have h : IsIntegral ℤ (star (algebraMap (𝓞 E) E r)) :=
    (RingOfIntegers.isIntegral_coe r).map (starRingEnd E).toIntAlgHom
  exact ⟨⟨_, h⟩, rfl⟩

theorem mem_one_iff (e : E) : e ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ e := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨e, h⟩, rfl⟩



end Glob

end Formalism.L2.Geo.Def.G1
