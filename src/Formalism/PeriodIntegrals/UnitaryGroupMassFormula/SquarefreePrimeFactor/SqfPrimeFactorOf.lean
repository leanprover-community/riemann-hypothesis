import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.BigPrimes
import Mathlib
import Formalism.PeriodIntegrals.PrimesDyadicRS

section
open Polynomial

noncomputable section

namespace PI.SqfPrimeFactor.W

open PI.SqfLab

theorem claim_of (hA : CountA) (hB : IrrLower) (hC : Analytic) : PI.SqfPrimeFactor.Claim := by
  intro g r _ hr hg T hT
  refine (hA g r T hT).trans (le_trans ?_ (hC g r hr hg))
  gcongr with p hp
  have hpp : p.Prime := (Finset.mem_filter.1 hp).2.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  rw [div_le_iff₀ hp0]
  have := hB g p hpp
  linarith

end PI.SqfPrimeFactor.W
end
end

section
open Polynomial

noncomputable section

namespace PI.SqfPrimeFactor.W

variable {g : ℕ} [Fact g.Prime]

theorem monicDeg_fn_monic (d : ℕ) (c : Fin d → ZMod g) :
    (X ^ d + ∑ i, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).Monic :=
  monic_X_pow_add (degree_sum_fin_lt c)

theorem monicDeg_fn_natDegree (d : ℕ) (c : Fin d → ZMod g) :
    (X ^ d + ∑ i, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).natDegree = d := by
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt c

theorem monicDeg_fn_coeff (d : ℕ) (c : Fin d → ZMod g) (i : Fin d) :
    (X ^ d + ∑ j, C (c j) * X ^ (j : ℕ) : (ZMod g)[X]).coeff i = c i := by
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.is_lt), zero_add, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg]
    intro h
    exact hj (Fin.ext h).symm
  · simp

theorem mem_monicDeg {d : ℕ} {f : (ZMod g)[X]} :
    f ∈ monicDeg g d ↔ f.Monic ∧ f.natDegree = d := by
  constructor
  · intro hf
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hf
    exact ⟨monicDeg_fn_monic d c, monicDeg_fn_natDegree d c⟩
  · rintro ⟨hm, hd⟩
    refine Finset.mem_image.2 ⟨fun i => f.coeff i, Finset.mem_univ _, ?_⟩
    show X ^ d + ∑ i : Fin d, C (f.coeff i) * X ^ (i : ℕ) = f
    rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i) d]
    have h := hm.as_sum
    rw [hd] at h
    exact h.symm

theorem card_monicDeg (d : ℕ) : (monicDeg g d).card = g ^ d := by
  unfold monicDeg
  rw [Finset.card_image_of_injective]
  · simp [Finset.card_univ, ZMod.card]
  · intro c c' h
    funext i
    have := congrArg (fun f : (ZMod g)[X] => f.coeff i) h
    simpa only [monicDeg_fn_coeff] using this

open Classical in
theorem mem_irrDeg {d : ℕ} {q : (ZMod g)[X]} :
    q ∈ irrDeg g d ↔ (q.Monic ∧ q.natDegree = d) ∧ Irreducible q := by
  unfold irrDeg
  rw [Finset.mem_filter, mem_monicDeg]

end PI.SqfPrimeFactor.W
end
end

section
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
end
end

section
open Polynomial Finset

noncomputable section

namespace PI.SqfPrimeFactor.W



end PI.SqfPrimeFactor.W
end
end

section
noncomputable section

namespace PI.SqfPrimeFactor.W

open Finset






end PI.SqfPrimeFactor.W
end
end

section
noncomputable section

namespace PI.SqfPrimeFactor.W


end PI.SqfPrimeFactor.W
end
end

section
namespace PI.SqfPrimeFactor.W


end PI.SqfPrimeFactor.W
end
