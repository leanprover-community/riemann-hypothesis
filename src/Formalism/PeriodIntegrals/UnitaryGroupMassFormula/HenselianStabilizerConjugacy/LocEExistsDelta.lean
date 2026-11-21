import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HenselianStabilizerConjugacy.IsSelfDual

noncomputable section

open scoped Classical
set_option linter.style.haveILetI false
open ValuativeRel

namespace PI.SelfDualHermitianLattices.Hd

open Formalism.MainNotions.S.Loc

section Alg

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem locE_nontrivial (L : LocE F E) : Nontrivial E := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have := L.rank
  rw [Module.finrank_zero_of_subsingleton] at this
  omega


theorem locE_algMap_mem (L : LocE F E) [IsNonarchimedeanLocalField F] {f : F} :
    algebraMap F E f ∈ L.O ↔ f ∈ 𝒪[F] := by
  haveI := locE_nontrivial L
  rw [L.O_def]
  constructor
  · intro h
    have h' : IsIntegral 𝒪[F] f :=
      (isIntegral_algHom_iff ((Algebra.ofId F E).restrictScalars 𝒪[F])
        (algebraMap F E).injective).mp h
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
    rw [← hy]; exact y.2
  · intro h
    have : algebraMap F E f = algebraMap 𝒪[F] E ⟨f, h⟩ := by
      rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]; rfl
    rw [this]; exact isIntegral_algebraMap



end Alg

section Alg2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]


structure QBasis (L : LocE F E) where
  ω : E
  hω : ω ∈ L.O
  hnot : ω ∉ Set.range (algebraMap F E)
  t : 𝒪[F]
  n : 𝒪[F]
  hcj : L.cj ω = algebraMap F E (t : F) - ω
  hn : ω * L.cj ω = algebraMap F E (n : F)
  span : ∀ x ∈ L.O, ∃ a b : 𝒪[F], x = algebraMap F E (a : F) + algebraMap F E (b : F) * ω

theorem QBasis.sq {L : LocE F E} (Q : QBasis L) :
    Q.ω * Q.ω = algebraMap F E (Q.t : F) * Q.ω - algebraMap F E (Q.n : F) := by
  have := Q.hn; rw [Q.hcj] at this; rw [← this]; ring


end Alg2

section Alg3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_a_mod [IsNonarchimedeanLocalField F] (t n : 𝒪[F]) (hΔ : t * t - 4 * n ∈ 𝓂[F]) :
    ∃ a : 𝒪[F], t + 2 * a ∈ 𝓂[F] ∧ a * a - n ∈ 𝓂[F] := by
  by_cases h2 : IsUnit (2 : 𝒪[F])
  · obtain ⟨u, hu⟩ := h2
    have hmul : (u : 𝒪[F]) * ↑u⁻¹ = 1 := u.mul_inv
    refine ⟨-(t * ↑u⁻¹), ?_, ?_⟩
    · have : t + 2 * -(t * ↑u⁻¹) = 0 := by
        linear_combination (-t) * hmul + (t * ↑u⁻¹) * hu
      rw [this]; exact zero_mem _
    · have : -(t * ↑u⁻¹) * -(t * ↑u⁻¹) - n = ↑u⁻¹ * ↑u⁻¹ * (t * t - 4 * n) := by
        linear_combination (n * ((u : 𝒪[F]) * ↑u⁻¹ + 1)) * hmul +
          (-(n * ↑u⁻¹ * ↑u⁻¹ * ((u : 𝒪[F]) + 2))) * hu
      rw [this]; exact Ideal.mul_mem_left _ _ hΔ
  · have h2m : (2 : 𝒪[F]) ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal _).mpr h2
    have htt : t * t ∈ 𝓂[F] := by
      have : t * t = (t * t - 4 * n) + 2 * (2 * n) := by ring
      rw [this]; exact add_mem hΔ (Ideal.mul_mem_right _ _ h2m)
    have ht : t ∈ 𝓂[F] := by
      rcases (IsLocalRing.maximalIdeal.isMaximal 𝒪[F]).isPrime.mem_or_mem htt with h | h <;> exact h
    have h2k : (2 : 𝓀[F]) = 0 := by
      have := (IsLocalRing.residue_eq_zero_iff (2 : 𝒪[F])).mpr h2m
      rwa [map_ofNat] at this
    have hinj : Function.Injective (fun x : 𝓀[F] => x * x) := by
      intro x y hxy
      simp only at hxy
      have h1 : (x + y) * (x + y) = 0 := by
        linear_combination (-1 : 𝓀[F]) * hxy + (x * x + x * y) * h2k
      have h3 : x + y = 0 := mul_self_eq_zero.mp h1
      linear_combination h3 - y * h2k
    obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.mp hinj) (IsLocalRing.residue 𝒪[F] n)
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective r
    refine ⟨a, add_mem ht (Ideal.mul_mem_right _ _ h2m), ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_mul, ha]
    simp only at hr; rw [hr, sub_self]

variable (L : LocE F E) [IsNonarchimedeanLocalField F]

theorem QBasis.normE {L : LocE F E} (Q : QBasis L) (a b : F) :
    (algebraMap F E a + algebraMap F E b * Q.ω) * L.cj (algebraMap F E a + algebraMap F E b * Q.ω) =
      algebraMap F E (a * a + (Q.t : F) * a * b + (Q.n : F) * b * b) := by
  have hn := Q.hn
  rw [Q.hcj] at hn
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]
  simp only [map_add, map_mul]
  linear_combination (algebraMap F E b * algebraMap F E b) * hn

theorem QBasis.disc_unit {L : LocE F E} (Q : QBasis L) : IsUnit (Q.t * Q.t - 4 * Q.n) := by
  by_contra hΔ
  have hΔm : Q.t * Q.t - 4 * Q.n ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal _).mpr hΔ
  obtain ⟨a, h1, h2⟩ := exists_a_mod Q.t Q.n hΔm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  rw [hϖ.maximalIdeal_eq] at h1 h2
  obtain ⟨p1, hp1⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨p2, hp2⟩ := Ideal.mem_span_singleton'.mp h2
  have e1 : algebraMap F E (p1 : F) * algebraMap F E (ϖ : F) =
      algebraMap F E (Q.t : F) + 2 * algebraMap F E (a : F) := by
    have e1F : (p1 : F) * (ϖ : F) = (Q.t : F) + 2 * (a : F) := by
      have := congrArg Subtype.val hp1; push_cast at this; exact this
    rw [← map_mul, e1F, map_add, map_mul, map_ofNat]
  have e2 : algebraMap F E (p2 : F) * algebraMap F E (ϖ : F) =
      algebraMap F E (a : F) * algebraMap F E (a : F) - algebraMap F E (Q.n : F) := by
    have e2F : (p2 : F) * (ϖ : F) = (a : F) * (a : F) - (Q.n : F) := by
      have := congrArg Subtype.val hp2; push_cast at this; exact this
    rw [← map_mul, e2F, map_sub, map_mul]
  set y := Q.ω + algebraMap F E (a : F) with hy
  have hyO : y ∈ L.O := add_mem Q.hω ((locE_algMap_mem L).mpr a.2)
  have hsq : y * y = algebraMap F E (p1 : F) * Q.ω * algebraMap F E (ϖ : F) +
      algebraMap F E (p2 : F) * algebraMap F E (ϖ : F) := by
    rw [hy]; linear_combination Q.sq - Q.ω * e1 - e2
  have hmemO : algebraMap F E (p1 : F) * Q.ω + algebraMap F E (p2 : F) ∈ L.O :=
    add_mem (mul_mem ((locE_algMap_mem L).mpr p1.2) Q.hω) ((locE_algMap_mem L).mpr p2.2)
  have hspan : y * y ∈ Submodule.span L.O {algebraMap F E ((ϖ : 𝒪[F]) : F)} := by
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨_, hmemO⟩, ?_⟩
    rw [Subring.smul_def, smul_eq_mul, hsq]; simp only; ring
  have hyd := L.unram ϖ hϖ y hyO (by simpa using hspan)
  obtain ⟨⟨w, hw⟩, hwy⟩ := Submodule.mem_span_singleton.mp hyd
  rw [Subring.smul_def, smul_eq_mul] at hwy
  obtain ⟨a', b', hab'⟩ := Q.span w hw
  have hwy' : w * algebraMap F E (ϖ : F) = y := hwy
  rw [hab'] at hwy'
  apply Q.hnot
  have hne : (1 : F) - (ϖ : F) * (b' : F) ≠ 0 := by
    intro h
    apply hϖ.not_isUnit
    have hm : ϖ * b' = 1 := Subtype.ext (by push_cast; linear_combination -h)
    exact ⟨⟨ϖ, b', hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  refine ⟨((ϖ : F) * (a' : F) - (a : F)) / (1 - (ϖ : F) * (b' : F)), ?_⟩
  have hu : IsUnit (algebraMap F E (1 - (ϖ : F) * (b' : F))) := (IsUnit.mk0 _ hne).map _
  apply hu.mul_left_cancel
  rw [← map_mul, mul_div_cancel₀ _ hne]
  simp only [map_sub, map_mul, map_one]
  rw [hy] at hwy'
  linear_combination hwy'

theorem QBasis.trace_nondeg {L : LocE F E} (Q : QBasis L) {ϖ : 𝒪[F]} {x : E} (hx : x ∈ L.O)
    (h : ∀ c ∈ L.O, ∃ z : 𝒪[F], c * x + L.cj (c * x) = algebraMap F E ((ϖ : F) * (z : F))) :
    ∃ w ∈ L.O, x = algebraMap F E (ϖ : F) * w := by
  haveI := locE_nontrivial L
  obtain ⟨a, b, hab⟩ := Q.span x hx
  obtain ⟨z1, hz1⟩ := h 1 (one_mem _)
  obtain ⟨z2, hz2⟩ := h Q.ω Q.hω
  have hn := Q.hn
  rw [Q.hcj] at hn
  have i1 : (2 * (a : F) + (b : F) * (Q.t : F)) = (ϖ : F) * (z1 : F) := by
    apply (algebraMap F E).injective
    rw [← hz1, one_mul, hab, map_add L.cj, map_mul L.cj, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]
    simp only [map_add, map_mul, map_ofNat]; ring
  have i2 : ((a : F) * (Q.t : F) + (b : F) * ((Q.t : F) * (Q.t : F) - 2 * (Q.n : F))) =
      (ϖ : F) * (z2 : F) := by
    apply (algebraMap F E).injective
    rw [← hz2, hab, map_mul L.cj, map_add L.cj, map_mul L.cj, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]
    simp only [map_add, map_mul, map_sub, map_ofNat]
    linear_combination (2 * algebraMap F E (b : F)) * hn
  obtain ⟨u, hu⟩ := Q.disc_unit
  have hinv : ((u⁻¹ : (𝒪[F])ˣ) : F) * ((Q.t : F) * (Q.t : F) - 4 * (Q.n : F)) = 1 := by
    have := congrArg (fun z : 𝒪[F] => (z : F)) (u.inv_mul)
    rw [hu] at this; push_cast at this; exact this
  set v : F := ((u⁻¹ : (𝒪[F])ˣ) : F)
  have hv : v ∈ 𝒪[F] := ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]).2
  set al : F := v * (((Q.t : F) * (Q.t : F) - 2 * (Q.n : F)) * (z1 : F) - (Q.t : F) * (z2 : F))
  set be : F := v * (2 * (z2 : F) - (Q.t : F) * (z1 : F))
  have hal : al ∈ 𝒪[F] := mul_mem hv (sub_mem (mul_mem (sub_mem (mul_mem Q.t.2 Q.t.2)
    (mul_mem (by simpa using (2 : 𝒪[F]).2) Q.n.2)) z1.2) (mul_mem Q.t.2 z2.2))
  have hbe : be ∈ 𝒪[F] := mul_mem hv (sub_mem (mul_mem (by simpa using (2 : 𝒪[F]).2) z2.2)
    (mul_mem Q.t.2 z1.2))
  have ha : (a : F) = (ϖ : F) * al := by
    linear_combination (v * ((Q.t : F) * (Q.t : F) - 2 * (Q.n : F))) * i1 + (-(v * (Q.t : F))) * i2 +
      (-(a : F)) * hinv
  have hb : (b : F) = (ϖ : F) * be := by
    linear_combination (-(v * (Q.t : F))) * i1 + (2 * v) * i2 + (-(b : F)) * hinv
  refine ⟨algebraMap F E al + algebraMap F E be * Q.ω,
    add_mem ((locE_algMap_mem L).mpr hal) (mul_mem ((locE_algMap_mem L).mpr hbe) Q.hω), ?_⟩
  rw [hab, ha, hb]; simp only [map_mul]; ring

end Alg3

end PI.SelfDualHermitianLattices.Hd
