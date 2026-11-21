import Mathlib
import Formalism.FrobeniusOrbits.HostOrbitCountSg
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Orbits

noncomputable section

namespace Formalism.FrobeniusOrbits

namespace OrbitSg



def emb {e : ℕ} (τ : GG e) (x : ℤˣ × HGrp e) : GG e :=
  ((if x.1 = 1 then 1 else (sg e).1) * τ.1, x.2 * τ.2)

lemma sg_fst_ne_one (e : ℕ) : (sg e).1 ≠ 1 := by
  simp only [sg]; decide

lemma emb_injective {e : ℕ} (τ : GG e) : Function.Injective (emb τ) := by
  rintro ⟨s, t⟩ ⟨s', t'⟩ h
  simp only [emb, Prod.mk.injEq, mul_left_inj] at h
  obtain ⟨h1, h2⟩ := h
  refine Prod.ext ?_ h2
  have hne := sg_fst_ne_one e
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or s' with rfl | rfl
  · rfl
  · simp at h1; exact absurd h1.symm hne
  · simp at h1; exact absurd h1 hne
  · rfl

end OrbitSg

open OrbitSg


end Formalism.FrobeniusOrbits
