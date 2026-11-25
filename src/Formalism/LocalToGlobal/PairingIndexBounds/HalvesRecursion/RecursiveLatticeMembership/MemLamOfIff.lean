module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.Statement
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole

@[expose] public section

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem eisG_eq_G (Λ : AddSubgroup ℂ) (L : PeriodPair) (h : ∀ w : ℂ, w ∈ Λ ↔ w ∈ L.lattice) (k : ℕ)
    (hk : 0 < k) : eisG Λ k = L.G (2 * k) := by
  unfold eisG PeriodPair.G
  have h1 := tsum_subtype ({w : ℂ | w ∈ Λ ∧ w ≠ 0} : Set ℂ) (fun z : ℂ => 1 / z ^ (2 * k))
  have h2 := tsum_subtype ((L.lattice : Set ℂ)) (fun z : ℂ => (z ^ (2 * k))⁻¹)
  refine h1.trans (Eq.trans ?_ h2.symm)
  congr 1
  funext w
  by_cases hw : w = 0
  · subst hw
    have : (0 : ℂ) ^ (2 * k) = 0 := zero_pow (by omega)
    simp [Set.indicator, this]
  · have hiff : w ∈ ({w : ℂ | w ∈ Λ ∧ w ≠ 0} : Set ℂ) ↔ w ∈ (L.lattice : Set ℂ) :=
      ⟨fun hh => (h w).1 hh.1, fun hh => ⟨(h w).2 hh, hw⟩⟩
    by_cases hm : w ∈ (L.lattice : Set ℂ)
    · rw [Set.indicator_of_mem (hiff.2 hm), Set.indicator_of_mem hm, one_div]
    · rw [Set.indicator_of_notMem (fun hh => hm (hiff.1 hh)), Set.indicator_of_notMem hm]

variable (D : D7)

def psi : 𝓞 D.host.K →+ ℂ where
  toFun c := D.host.φ₀ (((c : D.host.K) : D.host.E))
  map_zero' := by simp
  map_add' a b := by simp

theorem exists_pp (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) :
    ∃ L : PeriodPair, ∀ w : ℂ, w ∈ lamOf D cc 1 ↔ w ∈ L.lattice := by
  apply GlobalTheory.CurveLattice.exists_periodPair_one <;> assumption

theorem discrNZ : DiscrNZ D := by
  intro cc hcc
  obtain ⟨L, hL⟩ := exists_pp D cc hcc.1
  have h4 := eisG_eq_G _ L hL 2 (by norm_num)
  have h6 := eisG_eq_G _ L hL 3 (by norm_num)
  have := Formalism.L2.Th1.F.discNeZero L
  unfold Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3
  rw [h4, h6]
  simpa [PeriodPair.g₂, PeriodPair.g₃] using this

end Formalism.L2.PairingIndexBounds.Rec
