module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.GaloisModules.CoeGalRootsOfUnityHomApply
public import GroundTheory.LocalFields.HerbrandLocalBase
public import GroundTheory.LocalFields.UnitsGalois
public import GroundTheory.TateCohomology.Characters

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory GroundTheory.LocalField ValuativeRel

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

noncomputable abbrev galIntegerUnitsZ : Rep ℤ Gal(L/K) :=
  Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ

noncomputable def integerUnitsToUnits : galIntegerUnitsZ K L ⟶ galUnitsZ K L :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (unitsIncl L)).toIntLinearMap, fun σ => by
    ext x
    rfl⟩

noncomputable def unitsValuation : galUnitsZ K L ⟶ Rep.trivial ℤ Gal(L/K) ℤ :=
  Rep.ofHom ⟨(unitsOrd (L := L)).toIntLinearMap, fun σ => by
    ext x
    change ord (↑(σ • x.toMul) : L) = ord (x.toMul : L)
    have hOrd : ord (σ (x.toMul : L)) = ord (x.toMul : L) := by
      rw [ord, ord, normalizedValuation_apply, normalizedValuation_apply,
        valuation_algEquiv_apply K L σ (x.toMul : L)]
    rw [AlgEquiv.smul_units_def, Units.coe_map]
    exact hOrd⟩

@[simp]
theorem unitsValuation_hom_apply (x : Additive Lˣ) :
    (unitsValuation K L).hom x = ord ((x.toMul : Lˣ) : L) :=
  rfl

noncomputable def unitsValuationSES : ShortComplex (Rep ℤ Gal(L/K)) :=
  ShortComplex.mk (integerUnitsToUnits K L) (unitsValuation K L) (by
    ext x
    exact ord_unit (K := L) x.toMul)

end GroundTheory.ProfCoh
