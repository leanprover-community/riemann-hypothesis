module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscEquiv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapes
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityEighth

@[expose] public section

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem jK_conjO (z : 𝓞 K) : jK (conjO K z) = star (jK z) := rfl

theorem star_mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (hF : IsFixF K F) {r : K}
    (hr : r ∈ HU.SP K 𝔭) : star r ∈ HU.SP K 𝔭 := by
  obtain ⟨t, ht, z, hz⟩ := HU.mem_SP.1 hr
  refine HU.mem_SP.2 ⟨t, ht, conjO K z, ?_⟩
  rw [jK_conjO, hz, star_mul', star_jK_ι hF, mul_comm]

theorem div_mem_SP_of_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} (hd : d ≠ 0) {x : 𝓞 K}
    {k : ℕ} (hk : vF 𝔭 d ≤ k) (hx : x ∈ extP K 𝔭 ^ k) :
    haveI := h𝔭.isPrime; jK x / jK (ι d) ∈ HU.SP K 𝔭 :=
  (div_mem_SP_iff h𝔭 hd _).2 (Ideal.pow_le_pow_right hk hx)

end Formalism.L2.SG.Pf.fibreCountingData
