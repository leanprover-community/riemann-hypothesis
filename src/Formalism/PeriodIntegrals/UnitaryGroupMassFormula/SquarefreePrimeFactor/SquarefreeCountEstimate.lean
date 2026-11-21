import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.MonicDegFnNatDegree

open Polynomial

noncomputable section

namespace PI.SqfPrimeFactor.W

open PI.SqfLab

def bad (g r p : ℕ) [Fact g.Prime] : Finset (ZMod g)[X] :=
  (irrDeg g p ×ˢ monicDeg g (r - p)).image (fun x => x.1 * x.2)

section

variable {g : ℕ} [Fact g.Prime]

theorem irr_dvd_of_dvd_mul {q q' h : (ZMod g)[X]} (hq : Irreducible q) (hh : h ≠ 0)
    (hdeg : h.natDegree < q.natDegree) (hd : q ∣ q' * h) : q ∣ q' := by
  rcases hq.prime.dvd_or_dvd hd with h1 | h1
  · exact h1
  · exact absurd (natDegree_le_of_dvd h1 hh) (not_le.2 hdeg)

theorem mul_injOn (r p : ℕ) (hp : r < 2 * p) :
    Set.InjOn (fun x : (ZMod g)[X] × (ZMod g)[X] => x.1 * x.2)
      ↑(irrDeg g p ×ˢ monicDeg g (r - p)) := by
  rintro ⟨q, h⟩ hx ⟨q', h'⟩ hx' he
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_irrDeg, mem_monicDeg] at hx hx'
  simp only at he
  obtain ⟨⟨⟨hqm, hqd⟩, hqi⟩, hhm, hhd⟩ := hx
  obtain ⟨⟨⟨hqm', hqd'⟩, hqi'⟩, hhm', hhd'⟩ := hx'
  have h1 : q ∣ q' := irr_dvd_of_dvd_mul hqi hhm'.ne_zero (by omega) ⟨h, he.symm⟩
  have hqq : q' = q := eq_of_monic_of_dvd_of_natDegree_le hqm hqm' h1 (by omega)
  subst hqq
  have : h = h' := mul_left_cancel₀ hqm.ne_zero he
  rw [this]

theorem card_bad (r p : ℕ) (hp : r < 2 * p) :
    (bad g r p).card = (irrDeg g p).card * g ^ (r - p) := by
  unfold bad
  rw [Finset.card_image_of_injOn (mul_injOn r p hp), Finset.card_product, card_monicDeg]

theorem mem_bad {r p : ℕ} {f : (ZMod g)[X]} (hf : f ∈ bad g r p) :
    ∃ q h : (ZMod g)[X], f = q * h ∧ q.Monic ∧ q.natDegree = p ∧ Irreducible q ∧
      h.Monic ∧ h.natDegree = r - p := by
  obtain ⟨⟨q, h⟩, hx, rfl⟩ := Finset.mem_image.1 hf
  simp only [Finset.mem_product, mem_irrDeg, mem_monicDeg] at hx
  obtain ⟨⟨⟨hqm, hqd⟩, hqi⟩, hhm, hhd⟩ := hx
  exact ⟨q, h, rfl, hqm, hqd, hqi, hhm, hhd⟩



end


end PI.SqfPrimeFactor.W
