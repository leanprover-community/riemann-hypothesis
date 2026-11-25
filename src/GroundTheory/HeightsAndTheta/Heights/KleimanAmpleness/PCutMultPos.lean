module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutMultPosSt
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Tactic.TypeStar

@[expose] public section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
open IsLocalRing

def locQuotEquiv {R : Type*} [CommRing R] (q : Ideal R) [q.IsPrime] (J : Ideal R) :
    (Localization.AtPrime q ⧸ J.localized' (Localization.AtPrime q) q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime q))) ≃ₗ[Localization.AtPrime q]
      LocalizedModule q.primeCompl (R ⧸ J) :=
  (IsLocalizedModule.linearEquiv q.primeCompl
    (J.toLocalizedQuotient' _ q.primeCompl (Algebra.linearMap R (Localization.AtPrime q)))
    (LocalizedModule.mkLinearMap _ _)).restrictScalars _

theorem CutMultPos.proof : CutMultPos.Statement := by
  intro S _ _ N J qq h
  have : qq.IsPrime := h.isPrime
  let A := Localization.AtPrime qq
  let I := J.map (algebraMap (Poly S N) A)
  have hm : maximalIdeal A ∈ I.minimalPrimes := by
    simpa only [I, A, IsLocalization.minimalPrimes_map qq.primeCompl, Set.mem_preimage,
      Localization.AtPrime.under_maximalIdeal] using h
  have : IsArtinianRing (A ⧸ I) := quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hm
  rw [cutMult, ← (locQuotEquiv qq J).length_eq, Ideal.localized'_eq_map,
    Module.length_eq_of_surjective (R := A ⧸ I) Ideal.Quotient.mk_surjective,
    Module.length_pos_iff, Ideal.Quotient.nontrivial_iff]
  exact ⟨ne_top_of_le_ne_top hm.isPrime.ne_top' hm.le, Module.length_ne_top.lt_top⟩

end
end GroundTheory.Heights₂.Heights.Kleiman
