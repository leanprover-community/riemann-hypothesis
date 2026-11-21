import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert

section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.grMaxOf :
    ∀ (p : ℕ) [Fact p.Prime] (R G : Type) [CommRing R] [IsLocalRing R] [CommGroup G] [Finite G], (p : R) ∈ IsLocalRing.maximalIdeal R → IsPGroup p G → ∀ M : Ideal (MonoidAlgebra R G), M.IsMaximal → M = (IsLocalRing.maximalIdeal R).comap (aug R G) := by
  intro p _ R G _ _ _ _ hpm hG M hM
  classical
  have hcomap : M.comap (algebraMap R (MonoidAlgebra R G)) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
  letI : Field (MonoidAlgebra R G ⧸ M) := Ideal.Quotient.field M
  have hpQ : ((p : ℕ) : MonoidAlgebra R G ⧸ M) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]
    have h0 : (p : R) ∈ M.comap (algebraMap R (MonoidAlgebra R G)) := by
      rw [hcomap]; exact hpm
    simpa using h0
  haveI : CharP (MonoidAlgebra R G ⧸ M) p := by
    have h := CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) hpQ
    exact h ▸ ringChar.charP _
  have hg : ∀ g : G, Ideal.Quotient.mk M (MonoidAlgebra.single g 1) = 1 := by
    intro g
    obtain ⟨k, hk⟩ := hG g
    have h1 : (Ideal.Quotient.mk M (MonoidAlgebra.single g (1 : R)) - 1) ^ p ^ k = 0 := by
      rw [sub_pow_char_pow, one_pow, ← map_pow, MonoidAlgebra.single_pow, one_pow, hk,
        ← MonoidAlgebra.one_def, map_one, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mp h1)
  have hext : Ideal.Quotient.mkₐ R M = (Algebra.ofId R _).comp (aug R G) := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp [hg, aug_single]
    · exact Subsingleton.elim _ _
  have hle : (IsLocalRing.maximalIdeal R).comap (aug R G) ≤ M := by
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h3 := congrArg (fun f => f x) hext
    simp only [Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, Algebra.ofId_apply] at h3
    rw [h3, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
    have h2 : aug R G x ∈ M.comap (algebraMap R (MonoidAlgebra R G)) := by
      rw [hcomap]; exact hx
    exact h2
  haveI : ((IsLocalRing.maximalIdeal R).comap (aug R G)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (aug R G) (fun r => ⟨MonoidAlgebra.single 1 r, aug_single R G 1 r⟩)
  exact (Ideal.IsMaximal.eq_of_le this hM.ne_top hle).symm
end

section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.augKer :
    ∀ (R G : Type) [CommRing R] [CommGroup G], RingHom.ker (aug R G) = augIdeal R G ∧ Function.Surjective (aug R G) := by
  intro R G _ _
  have key : ∀ x : MonoidAlgebra R G,
      x - algebraMap R (MonoidAlgebra R G) (aug R G x) ∈ augIdeal R G := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, map_add, add_sub_add_comm]
      exact add_mem hx hy
    | single g r =>
      rw [aug_single]
      have h1 : MonoidAlgebra.single g r - algebraMap R (MonoidAlgebra R G) r =
          MonoidAlgebra.single 1 r * (MonoidAlgebra.of R G g - 1) := by
        rw [mul_sub, mul_one, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, one_mul,
          mul_one, MonoidAlgebra.coe_algebraMap]
        rfl
      rw [h1]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, rfl⟩)
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · intro x hx
    have := key x
    rwa [RingHom.mem_ker.mp hx, map_zero, sub_zero] at this
  · rw [augIdeal, Ideal.span_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, MonoidAlgebra.of_apply, aug_single,
      sub_self]
  · intro r
    exact ⟨MonoidAlgebra.single 1 r, aug_single R G 1 r⟩
end

section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.grLocal :
    ∀ (p : ℕ) [Fact p.Prime] (R G : Type) [CommRing R] [IsLocalRing R] [CommGroup G] [Finite G], (p : R) ∈ IsLocalRing.maximalIdeal R → IsPGroup p G → ∃ _ : IsLocalRing (MonoidAlgebra R G), IsLocalRing.maximalIdeal (MonoidAlgebra R G) = (IsLocalRing.maximalIdeal R).comap (aug R G) ∧ IsLocalRing.maximalIdeal (MonoidAlgebra R G) = (IsLocalRing.maximalIdeal R).map (algebraMap R (MonoidAlgebra R G)) ⊔ augIdeal R G ∧ ∀ x, IsUnit x ↔ IsUnit (aug R G x) := by
  intro p _ R G _ _ _ _ hpm hG
  set J : Ideal (MonoidAlgebra R G) := (IsLocalRing.maximalIdeal R).comap (aug R G) with hJdef
  have hJ : J.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (aug R G) (UpperTheory.V.CF.augKer R G).2
  have huniq : ∃! I : Ideal (MonoidAlgebra R G), I.IsMaximal :=
    ⟨J, hJ, fun M hM => UpperTheory.V.CF.grMaxOf p R G hpm hG M hM⟩
  letI hloc : IsLocalRing (MonoidAlgebra R G) := IsLocalRing.of_unique_max_ideal huniq
  have hmax : IsLocalRing.maximalIdeal (MonoidAlgebra R G) = J :=
    (IsLocalRing.eq_maximalIdeal hJ).symm
  have hsec : ∀ r : R, aug R G (algebraMap R (MonoidAlgebra R G) r) = r := fun r => (aug R G).commutes r
  refine ⟨hloc, hmax, ?_, ?_⟩
  · rw [hmax]
    apply le_antisymm
    · intro x hx
      have hax : aug R G x ∈ IsLocalRing.maximalIdeal R := hx
      have h1 : algebraMap R (MonoidAlgebra R G) (aug R G x) ∈
          (IsLocalRing.maximalIdeal R).map (algebraMap R (MonoidAlgebra R G)) :=
        Ideal.mem_map_of_mem _ hax
      have h2 : x - algebraMap R (MonoidAlgebra R G) (aug R G x) ∈ augIdeal R G := by
        rw [← (UpperTheory.V.CF.augKer R G).1, RingHom.mem_ker]
        show aug R G (x - algebraMap R (MonoidAlgebra R G) (aug R G x)) = 0
        rw [map_sub, hsec, sub_self]
      have : x = algebraMap R (MonoidAlgebra R G) (aug R G x) +
          (x - algebraMap R (MonoidAlgebra R G) (aug R G x)) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
    · apply sup_le
      · rw [Ideal.map_le_iff_le_comap]
        intro r hr
        show aug R G (algebraMap R (MonoidAlgebra R G) r) ∈ IsLocalRing.maximalIdeal R
        rw [hsec]
        exact hr
      · intro x hx
        rw [← (UpperTheory.V.CF.augKer R G).1, RingHom.mem_ker] at hx
        show aug R G x ∈ IsLocalRing.maximalIdeal R
        rw [show aug R G x = 0 from hx]
        exact zero_mem _
  · intro x
    constructor
    · intro hx
      exact hx.map (aug R G)
    · intro hx
      by_contra hnx
      have hxm : x ∈ IsLocalRing.maximalIdeal (MonoidAlgebra R G) := hnx
      rw [hmax] at hxm
      exact hxm hx
end
