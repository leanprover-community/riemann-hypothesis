import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum

open IsDedekindDomain NumberField

namespace GlobalTheory.AbsNormAdicBounds

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem exists_norm_eq_zpow (y : v.adicCompletion F) (hy : y ≠ 0) :
    ∃ k : ℤ, ‖y‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  have h0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  refine ⟨Multiplicative.toAdd (WithZero.unzero h0), ?_⟩
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
  simp

theorem norm_absNorm_lt_one :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ < 1 := by
  have h := (NumberField.FinitePlace.norm_lt_one_iff_mem F v
    ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2 (Ideal.absNorm_mem v.asIdeal)
  rwa [map_natCast, map_natCast] at h



end GlobalTheory.AbsNormAdicBounds
