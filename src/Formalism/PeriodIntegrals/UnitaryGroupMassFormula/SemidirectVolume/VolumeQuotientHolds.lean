import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.FundamentalDomainExists

noncomputable section

namespace PI.VolSemiDirect.W

open MeasureTheory

section Dec

variable {X : Type} [Group X] [TopologicalSpace X] {K N H : Subgroup X}


theorem dec_unique (e : (N × H) ≃ₜ K) (he : ∀ p : N × H, ((e p : K) : X) = (p.1 : X) * (p.2 : X))
    {n1 n2 : N} {h1 h2 : H} (h : (n1 : X) * (h1 : X) = (n2 : X) * (h2 : X)) :
    n1 = n2 ∧ h1 = h2 := by
  have h1 : e (n1, h1) = e (n2, h2) := Subtype.ext (by rw [he, he]; exact h)
  have h2 := e.injective h1
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

theorem symm_eq (e : (N × H) ≃ₜ K) (he : ∀ p : N × H, ((e p : K) : X) = (p.1 : X) * (p.2 : X))
    {k : K} {n : N} {h : H} (hk : (k : X) = (n : X) * (h : X)) : e.symm k = (n, h) := by
  rw [e.symm_apply_eq]
  exact Subtype.ext (by rw [he]; exact hk)

end Dec

theorem memΓ {X : Type} [Group X] {Γ K : Subgroup X} (γ : ratG Γ K) : ((γ : K) : X) ∈ Γ := by
  have := Subgroup.mem_subgroupOf.mp γ.2
  exact (Subgroup.mem_inf.mp this).1

def mkR {X : Type} [Group X] {Γ K : Subgroup X} (x : K) (hx : (x : X) ∈ Γ) : ratG Γ K :=
  ⟨x, Subgroup.mem_subgroupOf.2 ⟨hx, x.2⟩⟩


end PI.VolSemiDirect.W
