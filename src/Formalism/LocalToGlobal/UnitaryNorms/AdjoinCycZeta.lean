module

public import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.EqZeroOfNegEq

@[expose] public section

noncomputable section

open IntermediateField NumberField

namespace Formalism.HC.HostRaw

open Formalism.FrobeniusOrbits Formalism.L2.Host

variable {φ : Frame} (H : HostRaw φ)

def EQ : Fld := ⨆ j : H.E →ₐ[ℚ] Qb, j.fieldRange

theorem exists_aut (j j' : H.E →ₐ[ℚ] Qb) : ∃ σ : H.E ≃ₐ[ℚ] H.E, ∀ x, j' x = j (σ x) := by
  have := H.galois
  have inj : Function.Injective (fun σ : H.E ≃ₐ[ℚ] H.E => j.comp (σ : H.E →ₐ[ℚ] H.E)) := by
    intro σ τ hst
    exact AlgEquiv.ext fun x => j.toRingHom.injective (DFunLike.congr_fun hst x)
  have hb := (Fintype.bijective_iff_injective_and_card _).mpr ⟨inj, by
    rw [AlgHom.card, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]⟩
  obtain ⟨σ, hσ⟩ := hb.2 j'
  exact ⟨σ, fun x => (DFunLike.congr_fun hσ x).symm⟩

theorem range_eq (j : H.E →ₐ[ℚ] Qb) : j.fieldRange = H.EQ := by
  refine le_antisymm (le_iSup (fun j : H.E →ₐ[ℚ] Qb => j.fieldRange) j) (iSup_le fun j' => ?_)
  obtain ⟨σ, hσ⟩ := H.exists_aut j j'
  rintro _ ⟨x, rfl⟩
  exact ⟨σ x, (hσ x).symm⟩

instance fin_EQ : FiniteDimensional ℚ H.EQ := by
  obtain ⟨j⟩ := H.nonempty_emb
  exact (H.jOf j).toLinearEquiv.finiteDimensional

instance normal_EQ : Normal ℚ H.EQ := by
  obtain ⟨j⟩ := H.nonempty_emb
  have := H.galois
  exact Normal.of_algEquiv (H.jOf j)

instance fin_FQ : FiniteDimensional ℚ H.FQ :=
  FiniteDimensional.of_injective (inclusion H.FQ_le_EQ).toLinearMap (inclusion H.FQ_le_EQ).toRingHom.injective

variable {H}

variable (H)

end Formalism.HC.HostRaw

end
