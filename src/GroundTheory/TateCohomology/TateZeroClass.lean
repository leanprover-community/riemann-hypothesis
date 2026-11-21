import Mathlib
import GroundTheory.TateCohomology.TateLow
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

noncomputable def tateZeroClass (M : Rep.{u} k G) : M.ρ.invariants →ₗ[k] tateCohomology M 0 :=
  ((tateCohomologyZeroIso k G).app M).inv.hom ∘ₗ (normRangeInvariants M).mkQ

lemma tateZeroClass_eq_homologyπ (M : Rep.{u} k G) (z : (tateComplex M).cycles 0)
    (x : M.ρ.invariants) (hx : (cochainsIso₀ M).inv.hom x = ((tateComplex M).iCycles 0).hom z) :
    tateZeroClass M x = ((tateComplex M).homologyπ 0).hom z :=
  tateCohomologyZeroIso_inv_mk M z x hx

lemma tateZeroClass_surjective (M : Rep.{u} k G) : Function.Surjective (tateZeroClass M) := by
  intro y
  obtain ⟨q, hq⟩ := ((ModuleCat.epi_iff_surjective ((tateCohomologyZeroIso k G).app M).inv).1
    inferInstance) y
  obtain ⟨x, rfl⟩ := (normRangeInvariants M).mkQ_surjective q
  exact ⟨x, hq⟩



end GroundTheory.GroupCoh
