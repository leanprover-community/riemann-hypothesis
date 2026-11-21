import Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevFinIdxPI

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def LocIdxFin {hc : CMData F E} {S : HSpace E} {gp : Fin 2 → ℕ} {T f : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 F))}
    (X : Formalism.L2.Herm.StepLevelQ hc S gp T f Q) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ((gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal ∨ (T : 𝓞 F) ∈ v.asIdeal ∨ v ∈ Q) →
    (X.Uloc v).relIndex (levelVL hc.sig S.gram v X.Lb) ≠ 0

theorem finite_setOf_mem_asIdeal {x : 𝓞 F} (hx : x ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | x ∈ v.asIdeal}.Finite := by
  have hI : (Ideal.span {x} : Ideal (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hx
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  exact Ideal.dvd_span_singleton.mpr hv



end Formalism.L2.G
