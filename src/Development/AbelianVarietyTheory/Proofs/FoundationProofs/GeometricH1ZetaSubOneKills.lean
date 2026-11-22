module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmallTracesSubgroupGaloisTowerTopStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteGaloisApproximationStatement

@[expose] public section

open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.TateGeo

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem mem_geoTop_iff (T : Tower p Ω) (g : Gal p Ω) :
    g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n ↔
      (∀ x : Ω, IsAlgZp p x → g x = x) ∧ ∀ n, g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := by
  rw [Subgroup.mem_inf, Subgroup.mem_iInf]
  refine and_congr Iff.rfl (forall_congr' fun n => ?_)
  rw [Gn, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  rfl

theorem exists_moved (T : Tower p Ω) {g : Gal p Ω} (hg : g ∉ Ggeo p Ω ⊓ ⨅ n, Gn T n) :
    ∃ a : Ω, g a ≠ a ∧ ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, h a = a := by
  rw [mem_geoTop_iff] at hg
  by_contra hno
  push_neg at hno
  apply hg
  refine ⟨fun x hx => ?_, fun n => ⟨?_, ?_⟩⟩
  · by_contra hne
    obtain ⟨h, hh, hx'⟩ := hno x hne
    exact hx' (((mem_geoTop_iff T h).mp hh).1 x hx)
  · by_contra hne
    obtain ⟨h, hh, hx'⟩ := hno _ hne
    exact hx' (((mem_geoTop_iff T h).mp hh).2 n).1
  · by_contra hne
    obtain ⟨h, hh, hx'⟩ := hno _ hne
    exact hx' (((mem_geoTop_iff T h).mp hh).2 n).2

end GlobalTheory.K5.TateGeo
