import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateInfinite.Restrict
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerFrob
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSUnram
import GroundTheory.ArithmeticGeometry.SelmerPairing.Unramified
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

section Finite

variable {S : Set (HeightOneSpectrum (𝓞 K.1))}

def finitePlaceUnder (E : IntermediateField K.1 ℚ̄) [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    HeightOneSpectrum (𝓞 K.1) where
  asIdeal := w.asIdeal.under (𝓞 K.1)
  isPrime := Ideal.IsPrime.under (𝓞 K.1) w.asIdeal
  ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot




end Finite

section Unramified

open GroundTheory.LocalField

variable (T : Set (HeightOneSpectrum (𝓞 K.1))) {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

theorem inertiaGroup_le_ker_decompHomS (hv : v ∉ T) :
    inertiaGroup (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) ≤
      (decompHomS (v.adicCompletion K.1) T ι).ker := by
  intro g hg
  refine MonoidHom.mem_ker.2 (decompHomS_eq_one_of_unramifiedDegree_eq_one T ι hv g ?_)
  rw [← MonoidHom.mem_ker, ker_unramifiedDegree]
  exact hg

def decompHomSUnram (hv : v ∉ T) :
    Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ⧸
        inertiaGroup (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) →ₜ*
      galUnramifiedOutside K.1 ℚ̄ T :=
  ⟨QuotientGroup.lift _ (decompHomS (v.adicCompletion K.1) T ι) (inertiaGroup_le_ker_decompHomS T ι hv),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
      (continuous_decompHomS (Kv := v.adicCompletion K.1) T ι)⟩


variable (v) in

theorem exists_isZHatGenerator_inertia_adicCompletion :
    ∃ σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ⧸
        inertiaGroup (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)),
      IsZHatGenerator σ :=
  GroundTheory.Arith.Selmer.exists_isZHatGenerator_inertia _ _

end Unramified

end

end GroundTheory.ProfCoh
