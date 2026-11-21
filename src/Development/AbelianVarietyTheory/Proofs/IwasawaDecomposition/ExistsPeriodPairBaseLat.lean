import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EisGEqZeroOfInfinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaNormUnimodularLattice

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.Per.ConjCM

open GlobalTheory.ConjPoint

theorem transfer {L L' : PeriodPair} (σ : ℂ ≃+* ℂ)
    (hj : σ (1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) = 1728 * L'.g₂ ^ 3 / (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2))
    {α : ℂ} (hα : ∀ l ∈ L.lattice, α * l ∈ L.lattice) {t : ℂ} (h2 : 2 * t ∈ L.lattice)
    (ha : α * t ∉ L.lattice) (hb : (1 - α) * t ∉ L.lattice) :
    (∀ l ∈ L'.lattice, σ α * l ∈ L'.lattice) ∧
      ∃ t', 2 * t' ∈ L'.lattice ∧ σ α * t' ∉ L'.lattice ∧ (1 - σ α) * t' ∉ L'.lattice := by
  have h0 := GlobalTheory.g₂_cube_sub_g₃_sq_ne_zero L
  have h0' := GlobalTheory.g₂_cube_sub_g₃_sq_ne_zero L'
  have hσ0 : σ L.g₂ ^ 3 - 27 * σ L.g₃ ^ 2 ≠ 0 := by
    have := (map_ne_zero σ).2 h0
    simpa [map_ofNat] using this
  obtain ⟨M, m₂, m₃⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants hσ0
  simp only [map_div₀, map_mul, map_sub, map_pow, map_ofNat] at hj
  rw [div_eq_div_iff hσ0 h0'] at hj
  obtain ⟨c, hc⟩ := GlobalTheory.exists_isHomothetic_of_j_eq (L := M) (L' := L')
    (by rw [m₂, m₃]; linear_combination hj / 1728)
  have hc0 := hc.ne_zero
  obtain ⟨s, -, hs⟩ := exists_conjEquiv m₂ m₃
  obtain ⟨u, hu⟩ := GlobalTheory.latticePoint_surjective M (s (GlobalTheory.latticePoint L t))
  have hu' : IsConj L M σ t u := (hs _ _).2 hu.symm
  have hβ : ∀ l ∈ L.lattice, (1 - α) * l ∈ L.lattice := fun l hl => by
    rw [sub_mul, one_mul]; exact sub_mem hl (hα l hl)
  refine ⟨fun l hl => ?_, c * u, ?_, ?_, ?_⟩
  · have h1 : c⁻¹ * l ∈ M.lattice := (hc _).1 (by simpa [hc0] using hl)
    have h3 := IsConj.mul m₂ m₃ hα (t := 0) (t' := c⁻¹ * l) (.inl ⟨zero_mem _, h1⟩)
    rcases h3 with h | h
    · have := (hc _).2 h.2
      rwa [show c * (σ α * (c⁻¹ * l)) = σ α * l by field_simp] at this
    · exact absurd (by simp) h.1
  · have := (hc _).2 ((hu'.nsmul_mem_iff m₂ m₃ 2).1 (by exact_mod_cast h2))
    rwa [show c * (((2 : ℕ) : ℂ) * u) = 2 * (c * u) by push_cast; ring] at this
  · rw [mul_left_comm, hc]
    exact ((IsConj.mul m₂ m₃ hα hu').resolve_left fun h => ha h.1).2.1
  · rw [mul_left_comm, hc]
    have := ((IsConj.mul m₂ m₃ hβ hu').resolve_left fun h => hb h.1).2.1
    rwa [map_sub, map_one] at this

variable {R : Ranks} (H : Host R)

theorem mem_baseLat (w : ℂ) :
    w ∈ baseLat H ↔ ∃ c ∈ H.ccK, w = H.φ₀ (((c : H.K) : H.E)) := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, H.ccK.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', H.ccK.add_mem hc hc', by simp⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, H.ccK.neg_mem hc, by simp⟩
  · exact fun hw => AddSubgroup.subset_closure hw

theorem exists_periodPair_baseLat : ∃ L : PeriodPair, ∀ z, z ∈ baseLat H ↔ z ∈ L.lattice := by
  have hr : Module.finrank ℚ H.K = 2 :=
    Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos (H.sqd_sq)
  have hd : NumberField.discr H.K = -(H.d : ℤ) :=
    GlobalTheory.discr_eq_neg_of_sq_eq hr H.hyp.2.1.squarefree
      (by have := H.hyp.2.2.2.1; omega)
      (Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq))
  let σ : H.K →+* ℂ := H.φ₀.comp H.K.val.toRingHom
  let I : (Ideal (𝓞 H.K))⁰ := ⟨H.ccK, mem_nonZeroDivisors_of_ne_zero H.ccK_ne_bot⟩
  obtain ⟨L, hL⟩ := GlobalTheory.QuadraticZeta.exists_periodPair hr hd σ (FractionalIdeal.mk0 H.K I)
  refine ⟨L, fun z => ?_⟩
  rw [mem_baseLat, ← SetLike.mem_coe (p := L.lattice), hL]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(c : H.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨c, hc, rfl⟩


theorem root_cases {d : ℕ} {α : ℂ} (h : (2 * α - 1) ^ 2 = -(d : ℂ)) :
    (α = (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 ∧ 1 - α = (1 - Complex.I * (Real.sqrt d : ℂ)) / 2) ∨
    (1 - α = (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 ∧ α = (1 - Complex.I * (Real.sqrt d : ℂ)) / 2) := by
  have h1 : (2 * α - 1) ^ 2 = (Complex.I * (Real.sqrt d : ℂ)) ^ 2 := by
    rw [h, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e
  · exact .inl ⟨by linear_combination e / 2, by linear_combination -e / 2⟩
  · exact .inr ⟨by linear_combination -e / 2, by linear_combination e / 2⟩



end GlobalTheory.Mem.Per.ConjCM
