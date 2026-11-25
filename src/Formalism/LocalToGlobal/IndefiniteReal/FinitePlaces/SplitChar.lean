module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Star.Int
import Formalism.LocalToGlobal.IndefiniteReal.InjectiveDecompositionAction
import Formalism.LocalToGlobal.IndefiniteReal.DeterminantProjection

@[expose] public section
noncomputable section

open Formalism.BasicNotions Formalism.L2.Theta IsDedekindDomain NumberField

namespace Formalism.IndefR.Fin.SplitChar

theorem exists_place_two (F : Type) [Field F] [NumberField F] :
    ∃ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal := by
  obtain ⟨M, hM, h2M⟩ := exists_max_ideal_of_mem_nonunits (a := (2 : 𝓞 F)) (by
    simpa only [map_ofNat] using (map_mem_nonunits_iff (algebraMap ℤ (𝓞 F)) (2 : ℤ)).2
      (by norm_num [mem_nonunits_iff, Int.isUnit_iff]))
  refine ⟨⟨M, hM.isPrime, ?_⟩, h2M⟩
  exact (Submodule.ne_bot_iff M).2 ⟨2, h2M, two_ne_zero⟩

theorem exists_splitIdem_D (D : D7) : ∃ e, IsSplitIdem D e := by
  obtain ⟨v, hv⟩ := exists_place_two D.host.F
  obtain ⟨e, _, he, -, -⟩ := twoSplitIdem D v hv
  exact ⟨e, he⟩

variable {D : D7}

end Formalism.IndefR.Fin.SplitChar

end
