import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.placeRankTwoOne NumberField Formalism.FrobeniusOrbits
open scoped Pointwise

namespace Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent

theorem bb_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1



theorem absNorm_smul {K : Type} [Field K] [NumberField K] (σ : K ≃ₐ[ℚ] K) (I : Ideal (𝓞 K)) :
    Ideal.absNorm (σ • I) = Ideal.absNorm I := by
  have e : (𝓞 K ⧸ I) ≃+* (𝓞 K ⧸ (σ • I)) :=
    Ideal.quotientEquiv I (σ • I) (MulSemiringAction.toRingEquiv (K ≃ₐ[ℚ] K) (𝓞 K) σ) rfl
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr e.toEquiv).symm



theorem discr_K (D : D7) : discr D.host.K = -(D.host.d : ℤ) := by
  have hb : D.host.sqd ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  let x : D.host.K := ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hx : x ^ 2 = ((-(D.host.d : ℤ) : ℤ) : D.host.K) := by
    apply Subtype.ext
    simpa [x] using hb
  have htop : IntermediateField.adjoin ℚ {x} = ⊤ := by
    apply Formalism.HF.P.adjoin_top_of_lift
    rw [Set.image_singleton]
    rfl
  exact Formalism.HF.Final.quadDiscr D.host.K _ x hx htop (Formalism.HF.P.sqf_neg _ D.host.hyp.2.1)
    (by have := D.host.hyp.2.2.2.1; omega)

theorem finrank_K (D : D7) : Module.finrank ℚ D.host.K = 2 :=
  SplitK.finrank_K (L := D.host.E) (b := D.host.sqd) (d := D.host.d) D.host.hyp.2.1.pos
    (D.host.sqd_sq)


noncomputable def JJ (D : D7) (τ : D.what₂.Tau) : Ideal (𝓞 D.what₂.LL) :=
  (D.host.conj • D.host.𝔟).map (RingOfIntegers.mapRingHom (embTau D τ))




end Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent
