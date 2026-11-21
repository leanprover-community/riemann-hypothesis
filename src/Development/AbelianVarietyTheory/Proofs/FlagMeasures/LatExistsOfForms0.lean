import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LatExistsOfSteps
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsSat
import BuildAid.ForwardExisting
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedDegreeOneOfNcardPlacesOver

section
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_mem_notMem_coeIdeal_mul {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (c : FractionalIdeal (nonZeroDivisors R) K) (hc : c ≠ 0)
    (P : Ideal R) (hP : P ≠ ⊤) :
    ∃ b : K, b ∈ c ∧ b ∉ (P : FractionalIdeal (nonZeroDivisors R) K) * c := by
  by_contra h
  push_neg at h
  have h1 : c ≤ (P : FractionalIdeal (nonZeroDivisors R) K) * c := fun b hb => h b hb
  have h2 : c * c⁻¹ ≤ (P : FractionalIdeal (nonZeroDivisors R) K) * c * c⁻¹ := by
    gcongr
  rw [mul_assoc, mul_inv_cancel₀ hc, mul_one, ← FractionalIdeal.coeIdeal_top,
    FractionalIdeal.coeIdeal_le_coeIdeal] at h2
  exact hP (top_le_iff.mp h2)

theorem exists_mem_forall_notMem_coeIdeal_mul {R K : Type} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (c : FractionalIdeal (nonZeroDivisors R) K)
    (hc : c ≠ 0) (S : Finset (Ideal R)) (hS : ∀ Q ∈ S, Q.IsMaximal) :
    ∃ a : K, a ∈ c ∧ ∀ Q ∈ S, a ∉ (Q : FractionalIdeal (nonZeroDivisors R) K) * c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, c.zero_mem, by simp⟩
  | insert P S hPS ih =>
    obtain ⟨a, ha, haS⟩ := ih (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ))
    have hP : P.IsMaximal := hS P (Finset.mem_insert_self _ _)
    by_cases haP : a ∈ (P : FractionalIdeal (nonZeroDivisors R) K) * c
    swap
    · refine ⟨a, ha, fun Q hQ => ?_⟩
      rcases Finset.mem_insert.mp hQ with rfl | hQ
      · exact haP
      · exact haS Q hQ
    obtain ⟨b, hb, hbP⟩ := exists_mem_notMem_coeIdeal_mul c hc P hP.ne_top
    have hnle : ¬ S.inf id ≤ P := by
      rw [hP.isPrime.inf_le']
      rintro ⟨Q, hQ, hQP⟩
      have : Q = P := (hS Q (Finset.mem_insert_of_mem hQ)).eq_of_le hP.ne_top hQP
      exact hPS (this ▸ hQ)
    obtain ⟨e, heS, heP⟩ := SetLike.not_le_iff_exists.mp hnle
    have key : ∀ (Q : Ideal R) (x : R), x ∈ Q →
        x • b ∈ (Q : FractionalIdeal (nonZeroDivisors R) K) * c := by
      intro Q x hx
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hx) hb
    refine ⟨a + e • b, (c : Submodule R K).add_mem ha ((c : Submodule R K).smul_mem e hb),
      fun Q hQ h => ?_⟩
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    · obtain ⟨y, p, hp, hy⟩ := hP.exists_inv heP
      set J : Submodule R K := (((Q : FractionalIdeal (nonZeroDivisors R) K) * c :
        FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) with hJ
      have h1 : e • b ∈ J := (J.add_mem_iff_right haP).mp h
      have h2 : y • (e • b) + p • b ∈ J := J.add_mem (J.smul_mem y h1) (key Q p hp)
      rw [smul_smul, ← add_smul, hy, one_smul] at h2
      exact hbP h2
    · have heQ : e ∈ Q := (Finset.inf_le (f := id) hQ) heS
      set J : Submodule R K := (((Q : FractionalIdeal (nonZeroDivisors R) K) * c :
        FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) with hJ
      exact haS Q hQ ((J.add_mem_iff_left (key Q e heQ)).mp h)

theorem exists_mem_fractionalIdeal_generator_at_primes_over :
    ∀ (E : Type) [Field E] [NumberField E] (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
      c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ ∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q →
        a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  intro E _ _ c hc N hN
  have hN' : Ideal.span {N} ≠ (0 : Ideal (𝓞 E)) := by
    simpa using hN
  have hfin : {Q : Ideal (𝓞 E) | Q.IsMaximal ∧ N ∈ Q}.Finite := by
    refine ((Ideal.finite_factors hN').image (fun v => v.asIdeal)).subset ?_
    rintro Q ⟨hQ, hNQ⟩
    have h0 : Q ≠ ⊥ := by
      rintro rfl
      exact hN (by simpa using hNQ)
    refine ⟨⟨Q, hQ.isPrime, h0⟩, ?_, rfl⟩
    simpa [Ideal.dvd_iff_le] using hNQ
  obtain ⟨a, ha, h⟩ := exists_mem_forall_notMem_coeIdeal_mul c hc hfin.toFinset
    (fun Q hQ => (hfin.mem_toFinset.mp hQ).1)
  exact ⟨a, ha, fun Q hQ hNQ => h Q (hfin.mem_toFinset.mpr ⟨hQ, hNQ⟩)⟩

end GlobalTheory
end

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_fractionalIdeal_generator_at_primes_over' : ∀ (E : Type) [Field E] [NumberField E] (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ ∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q → a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  atlas_forward_decl GlobalTheory.exists_mem_fractionalIdeal_generator_at_primes_over
end

section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_add_mul_notMem_of_maximal_ge {R : Type*} [CommRing R] [IsDedekindDomain R]
    (J : Ideal R) (hJ : J ≠ 0) (n x : R)
    (h : ∀ p : Ideal R, p.IsMaximal → J ≤ p → n ∈ p → x ∉ p) :
    ∃ s : R, ∀ p : Ideal R, p.IsMaximal → J ≤ p → x + n * s ∉ p := by
  classical
  haveI : Fintype {p : Ideal R // p ∣ J} := UniqueFactorizationMonoid.fintypeSubtypeDvd J hJ
  let ι := {p : Ideal R // p.IsMaximal ∧ J ≤ p}
  haveI : Finite ι := Finite.of_injective
    (fun p : ι => (⟨p.1, Ideal.dvd_iff_le.2 p.2.2⟩ : {p : Ideal R // p ∣ J}))
    (fun a b hab => Subtype.ext (Subtype.mk.inj hab))
  have hc : Pairwise fun i j : ι => IsCoprime i.1 j.1 := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne i.2.1 j.2.1 (fun e => hij (Subtype.ext e))
  obtain ⟨s, hs⟩ := Ideal.pi_quotient_surjective (I := fun i : ι => i.1) hc
    (fun i => Ideal.Quotient.mk i.1 (if x ∈ i.1 then 1 else 0))
  refine ⟨s, fun p hp hJp hmem => ?_⟩
  have h1 := Ideal.Quotient.eq.1 (hs ⟨p, hp, hJp⟩)
  by_cases hx : x ∈ p
  · simp only [hx, if_true] at h1
    have h2 : n * s ∈ p := by simpa using p.sub_mem hmem hx
    have h3 : n ∈ p := by
      have := p.sub_mem h2 (p.mul_mem_left n h1)
      have e : n * s - n * (s - 1) = n := by ring
      rwa [e] at this
    exact h p hp hJp h3 hx
  · simp only [hx, if_false, sub_zero] at h1
    apply hx
    simpa using p.sub_mem hmem (p.mul_mem_left n h1)

theorem exists_unimodular_lift_of_unimodular_mod :
    ∀ (F : Type) [Field F] [NumberField F] (b : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), b ≠ 0 → ∀ (n x₀ : 𝓞 F) (y₀ : F), n ≠ 0 → y₀ ∈ b → (∀ p : Ideal (𝓞 F), p.IsMaximal → n ∈ p → ¬ (x₀ ∈ p ∧ y₀ ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b)) → ∃ (s : 𝓞 F) (t : F), t ∈ b ∧ ∀ p : Ideal (𝓞 F), p.IsMaximal → ¬ (x₀ + n * s ∈ p ∧ y₀ + (n : F) * t ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b) := by
  intro F _ _ b hb n x₀ y₀ hn hy₀ H
  have hnF : (n : F) ≠ 0 := by
    intro e
    exact hn (RingOfIntegers.ext e)
  obtain ⟨t, ht, hy⟩ : ∃ t : F, t ∈ b ∧ y₀ + (n : F) * t ≠ 0 := by
    by_cases h0 : y₀ = 0
    · obtain ⟨t, ht, ht0⟩ : ∃ t : F, t ∈ b ∧ t ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hb (FractionalIdeal.eq_zero_iff.2 hcon)
      exact ⟨t, ht, by rw [h0, zero_add]; exact mul_ne_zero hnF ht0⟩
    · exact ⟨0, b.zero_mem, by simpa using h0⟩
  set y := y₀ + (n : F) * t with hydef
  have hyb : y ∈ b := by
    have h1 : n • t ∈ (b : Submodule (𝓞 F) F) := Submodule.smul_mem _ n ht
    exact Submodule.add_mem (b : Submodule (𝓞 F) F) hy₀ h1
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y * b⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hb]
    exact mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 hyb) _
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hJb : (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b
      = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y := by
    rw [hJ, mul_assoc, inv_mul_cancel₀ hb, mul_one]
  have hJ0 : J ≠ 0 := by
    rintro rfl
    apply hy
    rw [← FractionalIdeal.spanSingleton_eq_zero_iff (S := nonZeroDivisors (𝓞 F)), ← hJb]
    simp
  have key : ∀ p : Ideal (𝓞 F),
      y ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b ↔ J ≤ p := by
    intro p
    rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.coeIdeal_le_coeIdeal F]
    constructor
    · intro h
      have := mul_le_mul_left h b⁻¹
      rwa [mul_assoc, mul_inv_cancel₀ hb, mul_one, ← hJ] at this
    · intro h
      rw [← hJb]
      exact mul_le_mul_left h b
  obtain ⟨s, hs⟩ := exists_add_mul_notMem_of_maximal_ge J hJ0 n x₀ (by
    intro p hp hJp hnp hx
    refine H p hp hnp ⟨hx, ?_⟩
    have h1 := (key p).2 hJp
    have h2 : (n : F) * t ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b :=
      FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hnp) ht
    have h3 := Submodule.sub_mem
      (((p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b : FractionalIdeal _ F) : Submodule (𝓞 F) F) h1 h2
    have e : y - (n : F) * t = y₀ := by rw [hydef]; ring
    rw [e] at h3
    exact h3)
  exact ⟨s, t, ht, fun p hp h => hs p hp ((key p).1 h.2) h.1⟩

end GlobalTheory
end

section
section
open NumberField IsDedekindDomain

namespace GlobalTheory
open Formalism.L2.SG.Pf.LatEx

theorem fractionalIdeal_restrictScalars_isLattice_of_tower (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hc : c ≠ 0) :
    Submodule.IsLattice F ((c : Submodule (𝓞 E) E).restrictScalars (𝓞 F)) := by
  refine ⟨?_, ?_⟩
  · exact (FractionalIdeal.fg_of_isNoetherianRing le_rfl c).restrictScalars
  · obtain ⟨x, hxc, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := (c : Submodule (𝓞 E) E))
      (by rwa [Ne, FractionalIdeal.coeToSubmodule_eq_bot])
    rw [eq_top_iff]
    intro y _
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) (y / x)
    dsimp only at hrs
    have hs0 : (s : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero s
    have hspan : Ideal.span {(s : 𝓞 E)} ≠ ⊥ := by simpa using hs0
    have hm0 : Ideal.absNorm (Ideal.span {(s : 𝓞 E)}) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {(s : 𝓞 E)}))
    set m := Ideal.absNorm (Ideal.span {(s : 𝓞 E)})
    have hmem : (algebraMap (𝓞 E) E (u * r)) * x ∈ c :=
      (c : Submodule (𝓞 E) E).smul_mem (u * r) hxc
    have hyeq : y = ((m : F)⁻¹) • ((algebraMap (𝓞 E) E (u * r)) * x) := by
      have hu' : algebraMap (𝓞 E) E u * algebraMap (𝓞 E) E s = (m : E) := by
        rw [← map_mul, hu, map_natCast]
      have hmE : (m : E) ≠ 0 := Nat.cast_ne_zero.mpr hm0
      rw [Algebra.smul_def, map_inv₀, map_natCast, map_mul]
      have hyx : y = algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E s * x := by
        have hsE : algebraMap (𝓞 E) E s ≠ 0 := by simpa using hs0
        rw [← hrs]; field_simp
      rw [hyx, ← hu']
      have hsE : algebraMap (𝓞 E) E s ≠ 0 := by simpa using hs0
      have huE : algebraMap (𝓞 E) E u ≠ 0 := by
        intro h; rw [h, zero_mul] at hu'; exact hmE hu'.symm
      field_simp
    rw [hyeq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem exists_basis_latSpanV_eq_of_finrank_two (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (hE : Module.finrank F E = 2) (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hc : c ≠ 0) :
    ∃ (e : Fin 2 → E) (b : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), LinearIndependent F e ∧ b ≠ 0 ∧
      (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) =
        latSpanV (Fin.snoc (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (fun _ => 1) b) e := by
  have hL := fractionalIdeal_restrictScalars_isLattice_of_tower F E c hc
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hE
  let w := Module.finBasisOfFinrankEq F E hE
  obtain ⟨e, b, he, -, hb, heq⟩ := satBasisV_holds F E _ hL 1 w w.linearIndependent (fun _ => 1)
    (fun _ => one_ne_zero)
  refine ⟨e, b, he, hb, ?_⟩
  rw [← heq, w.span_eq]
  simp

theorem basis_repr_mem_of_mem_latSpanV_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (B : Module.Basis (Fin 2) F E) (C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    {z : E} (hz : z ∈ latSpanV C B) (i : Fin 2) : B.repr z i ∈ C i := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, x, hx, rfl⟩ := hy
    rw [map_smul, B.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; simpa using hx
    · rw [smul_zero]; exact (C i : Submodule (𝓞 F) F).zero_mem
  | zero => rw [map_zero, Finsupp.zero_apply]; exact (C i : Submodule (𝓞 F) F).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add, Finsupp.add_apply]; exact (C i : Submodule (𝓞 F) F).add_mem hx hy
  | smul r x _ hx =>
    rw [← algebraMap_smul F r x, map_smul, Finsupp.smul_apply, algebraMap_smul]
    exact (C i : Submodule (𝓞 F) F).smul_mem r hx

theorem algebraMap_ringOfIntegers_tower_mul_eq_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (π : 𝓞 F) (z : E) :
    algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) * z = (algebraMap (𝓞 F) F π) • z := by
  rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem basis_repr_mem_of_mem_map_mul_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (B : Module.Basis (Fin 2) F E) (C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hc : (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) = latSpanV C B) (p : Ideal (𝓞 F)) {a : E}
    (ha : a ∈ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) (i : Fin 2) :
    B.repr a i ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * C i := by
  let T : Submodule (𝓞 F) F := (↑((p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * C i) : Submodule (𝓞 F) F)
  have hcoord : ∀ z ∈ c, B.repr z i ∈ C i := fun z hz =>
    basis_repr_mem_of_mem_latSpanV_two B C (by rw [← hc]; exact hz) i
  have hgen : ∀ π ∈ p, ∀ z ∈ c,
      B.repr (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) * z) i ∈ T := by
    intro π hπ z hz
    rw [algebraMap_ringOfIntegers_tower_mul_eq_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hπ) (hcoord z hz)
  have hq : ∀ q ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p, ∀ z ∈ c,
      B.repr (algebraMap (𝓞 E) E q * z) i ∈ T := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨π, hπ, rfl⟩ := hy
      exact hgen π hπ
    | zero => intro z _; simp [T.zero_mem]
    | add x y _ _ hx hy =>
      intro z hz; rw [map_add, add_mul, map_add, Finsupp.add_apply]; exact T.add_mem (hx z hz) (hy z hz)
    | smul r x _ hx =>
      intro z hz
      have e1 : algebraMap (𝓞 E) E (r * x) * z = algebraMap (𝓞 E) E x * (algebraMap (𝓞 E) E r * z) := by
        rw [RingHom.map_mul]; ring
      rw [smul_eq_mul, e1]
      exact hx _ ((c : Submodule (𝓞 E) E).smul_mem r hz)
  refine FractionalIdeal.mul_induction_on (C := fun a => B.repr a i ∈ T) ha ?_ ?_
  · intro u hu z hz
    obtain ⟨q, hq', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hu
    exact hq q hq' z hz
  · intro x y hx hy
    simp only [map_add, Finsupp.add_apply]
    exact T.add_mem hx hy

theorem mem_map_mul_of_basis_repr_mem_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (B : Module.Basis (Fin 2) F E) (C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hc : (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) = latSpanV C B) (p : Ideal (𝓞 F)) {a : E}
    (ha : ∀ i, B.repr a i ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * C i) :
    a ∈ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  let M : Submodule (𝓞 E) E := (↑(((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) : Submodule (𝓞 E) E)
  have hterm : ∀ i, B.repr a i • B i ∈ M := by
    intro i
    refine FractionalIdeal.mul_induction_on (C := fun u => u • B i ∈ M) (ha i) ?_ ?_
    · intro u hu x hx
      obtain ⟨π, hπ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hu
      have hxc : x • B i ∈ c := by
        have : x • B i ∈ latSpanV C B := Submodule.subset_span ⟨i, x, hx, rfl⟩
        rw [← hc] at this; exact this
      show (algebraMap (𝓞 F) F π * x) • B i ∈ M
      rw [mul_smul, ← algebraMap_ringOfIntegers_tower_mul_eq_smul]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _
        (Ideal.mem_map_of_mem _ hπ)) hxc
    · intro x y hx hy
      show (x + y) • B i ∈ M
      rw [add_smul]; exact M.add_mem hx hy
  have hsum := B.sum_repr a
  rw [Fin.sum_univ_two] at hsum
  show a ∈ M
  rw [← hsum]
  exact M.add_mem (hterm 0) (hterm 1)

theorem exists_mem_fractionalIdeal_primitive_local_generator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ (∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q → a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) ∧ ∀ p : Ideal (𝓞 F), p.IsMaximal → a ∉ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  intro F E _ _ _ _ _ hE c hc N hN
  obtain ⟨e, b, he, hb, hce⟩ := exists_basis_latSpanV_eq_of_finrank_two F E hE c hc
  let B : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank he (by simp [hE])
  have hBe : ⇑B = e := coe_basisOfLinearIndependentOfCardEqFinrank he _
  let C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F := Fin.snoc (n := 1) (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (fun _ => 1) b
  have hc' : (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) = latSpanV C B := by rw [hBe]; exact hce
  have hC0 : C 0 = 1 := rfl
  have hC1 : C 1 = b := rfl
  have hspanN : Ideal.span {N} ≠ ⊥ := by simpa using hN
  have hm0 : Ideal.absNorm (Ideal.span {N}) ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hmN : ((Ideal.absNorm (Ideal.span {N}) : ℕ) : 𝓞 E) ∈ Ideal.span {N} := Ideal.absNorm_mem _
  set m := Ideal.absNorm (Ideal.span {N})
  obtain ⟨a₀, ha₀c, ha₀⟩ := GlobalTheory.T.exists_mem_fractionalIdeal_generator_at_primes_over' E c hc (m : 𝓞 E) (Nat.cast_ne_zero.mpr hm0)
  have hco : ∀ i, B.repr a₀ i ∈ C i := fun i =>
    basis_repr_mem_of_mem_latSpanV_two B C (show a₀ ∈ latSpanV C B by rw [← hc']; exact ha₀c) i
  obtain ⟨x₀, hx₀⟩ := (FractionalIdeal.mem_one_iff _).mp (hC0 ▸ hco 0)
  have hy₀ : B.repr a₀ 1 ∈ b := hC1 ▸ hco 1
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := FaithfulSMul.algebraMap_injective _ _
  have hmono : ∀ (I J : Ideal (𝓞 E)), I ≤ J → (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c ≤
      (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
    intro I J hIJ
    have : (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ J := (FractionalIdeal.coeIdeal_le_coeIdeal E).mpr hIJ
    gcongr
  obtain ⟨s, t, ht, hst⟩ := GlobalTheory.exists_unimodular_lift_of_unimodular_mod F b hb (m : 𝓞 F) x₀ (B.repr a₀ 1)
    (Nat.cast_ne_zero.mpr hm0) hy₀ (by
      rintro p hp hnp ⟨hxp, hyp⟩
      have hmem := mem_map_mul_of_basis_repr_mem_two B C c hc' p (a := a₀) (by
        refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · rw [← hx₀, hC0, mul_one]; exact FractionalIdeal.mem_coeIdeal_of_mem _ hxp
        · exact hyp)
      obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) p (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
      have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ Q := Ideal.map_le_iff_le_comap.mpr hQp.ge
      have hmQ : (m : 𝓞 E) ∈ Q := hle (by
        rw [← map_natCast (algebraMap (𝓞 F) (𝓞 E)) m]; exact Ideal.mem_map_of_mem _ hnp)
      exact ha₀ Q hQ hmQ (hmono _ _ hle hmem))
  let w : E := (algebraMap (𝓞 F) F s) • B 0 + t • B 1
  have hw : w ∈ c := by
    have : w ∈ latSpanV C B := Submodule.add_mem _
      (Submodule.subset_span ⟨0, _, (FractionalIdeal.mem_one_iff _).mpr ⟨s, rfl⟩, rfl⟩)
      (Submodule.subset_span ⟨1, t, ht, rfl⟩)
    rw [← hc'] at this; exact this
  have hmw : (m : F) • w = algebraMap (𝓞 E) E (m : 𝓞 E) * w := by
    rw [map_natCast, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  refine ⟨a₀ + (m : F) • w, ?_, ?_, ?_⟩
  · rw [hmw]; exact (c : Submodule (𝓞 E) E).add_mem ha₀c ((c : Submodule (𝓞 E) E).smul_mem _ hw)
  · intro Q hQ hNQ ha
    have hmQ : (m : 𝓞 E) ∈ Q := (Ideal.span_singleton_le_iff_mem Q).mpr hNQ hmN
    have h2 : (m : F) • w ∈ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
      rw [hmw]; exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hmQ) hw
    refine ha₀ Q hQ hmQ ?_
    have e2 : a₀ = (a₀ + (m : F) • w) - (m : F) • w := by abel
    rw [e2]
    exact Submodule.sub_mem (↑((Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) : Submodule (𝓞 E) E) ha h2
  · intro p hp ha
    have h := basis_repr_mem_of_mem_map_mul_two B C c hc' p ha
    have hr : ∀ i, B.repr (a₀ + (m : F) • w) i = B.repr a₀ i + (m : F) * ((algebraMap (𝓞 F) F s) *
        (Finsupp.single 0 1 : Fin 2 →₀ F) i + t * (Finsupp.single 1 1 : Fin 2 →₀ F) i) := by
      intro i
      simp only [w, map_add, map_smul, B.repr_self, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    refine hst p hp ⟨?_, ?_⟩
    · have h0 := h 0
      rw [hC0, mul_one, hr 0] at h0
      obtain ⟨x', hx'p, hx'⟩ := (FractionalIdeal.mem_coeIdeal _).mp h0
      have : x' = x₀ + (m : 𝓞 F) * s := by
        apply IsFractionRing.injective (𝓞 F) F
        rw [hx', map_add, map_mul, map_natCast, hx₀]
        simp
      exact this ▸ hx'p
    · have h1 := h 1
      rw [hC1, hr 1] at h1
      convert h1 using 1
      simp

end GlobalTheory
end

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_fractionalIdeal_primitive_local_generator' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ (∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q → a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) ∧ ∀ p : Ideal (𝓞 F), p.IsMaximal → a ∉ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  atlas_forward_decl GlobalTheory.exists_mem_fractionalIdeal_primitive_local_generator
end

section
section
open NumberField IsDedekindDomain

namespace GlobalTheory.UnramifiedConj

theorem exists_of_fixed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (y : 𝓞 E)
    (hy : RingOfIntegers.mapRingHom (starRingEnd E) y = y) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a = y := by
  have hfix : star (y : E) = (y : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) hy
    simpa only [RingOfIntegers.mapRingHom_apply, starRingEnd_apply] using h
  obtain ⟨b, hb⟩ := (hc.fixed (y : E)).1 hfix

  have hint : IsIntegral ℤ b := by
    have hy' : IsIntegral ℤ (algebraMap F E b) := by
      rw [hb]
      exact RingOfIntegers.isIntegral_coe y
    exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).mp hy'
  refine ⟨⟨b, hint⟩, ?_⟩
  ext
  exact hb

private lemma mem_map_comap_of_star_fixed {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (Q : Ideal (𝓞 E))
    (z : 𝓞 E) (hz : RingOfIntegers.mapRingHom (starRingEnd E) z = z) (hzQ : z ∈ Q) :
    z ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
  obtain ⟨a, ha⟩ := exists_of_fixed hc z hz
  rw [← ha]
  apply Ideal.mem_map_of_mem
  rw [Ideal.mem_comap, ha]
  exact hzQ

theorem le_map_comap_of_le_conj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (P Q : Ideal (𝓞 E)) (hQ : Q.IsMaximal)
    (h1 : P ≤ Q) (h2 : P ≤ Q.comap (RingOfIntegers.mapRingHom (starRingEnd E))) :
    P ≤ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
  have hinv : ∀ z : 𝓞 E, RingOfIntegers.mapRingHom (starRingEnd E)
      (RingOfIntegers.mapRingHom (starRingEnd E) z) = z := by
    intro z
    ext
    simp only [RingOfIntegers.mapRingHom_apply, starRingEnd_apply, star_star]

  have hD : Ideal.span (Set.range fun θ : 𝓞 E => θ - RingOfIntegers.mapRingHom (starRingEnd E) θ)
      = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hDM⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨_, _, hU⟩ := hc.cmUnram
    obtain ⟨θ, t, ht, hθ⟩ := hU M hM
    have htθ : t = RingOfIntegers.mapRingHom (starRingEnd E) θ := by
      ext
      rw [RingOfIntegers.mapRingHom_apply, starRingEnd_apply]
      exact ht
    subst htθ
    exact hθ (hDM (Ideal.subset_span ⟨θ, rfl⟩))
  intro x hx
  have hxQ : x ∈ Q := h1 hx
  have hsxQ : RingOfIntegers.mapRingHom (starRingEnd E) x ∈ Q := h2 hx

  have hgen : ∀ θ : 𝓞 E,
      x * (θ - RingOfIntegers.mapRingHom (starRingEnd E) θ) ∈
        Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
    intro θ
    set s := RingOfIntegers.mapRingHom (starRingEnd E) with hs
    have e : x * (θ - s θ) = (x + s x) * θ - (x * s θ + s x * θ) := by ring
    rw [e]
    refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ ?_) ?_
    · refine mem_map_comap_of_star_fixed hc Q _ ?_ (Q.add_mem hxQ hsxQ)
      rw [map_add, hinv]
      ring
    · refine mem_map_comap_of_star_fixed hc Q _ ?_
        (Q.add_mem (Q.mul_mem_right _ hxQ) (Q.mul_mem_right _ hsxQ))
      rw [map_add, map_mul, map_mul, hinv, hinv]
      ring
  have key : ∀ d ∈ Ideal.span (Set.range fun θ : 𝓞 E =>
      θ - RingOfIntegers.mapRingHom (starRingEnd E) θ),
      x * d ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨θ, rfl⟩ := hd
      exact hgen θ
    | zero => simp
    | add a b _ _ ha hb =>
      rw [mul_add]
      exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ c ha
  have h1 : (1 : 𝓞 E) ∈ Ideal.span (Set.range fun θ : 𝓞 E =>
      θ - RingOfIntegers.mapRingHom (starRingEnd E) θ) := by
    rw [hD]
    exact Submodule.mem_top
  simpa using key 1 h1

end GlobalTheory.UnramifiedConj
end

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_map_comap_of_le_conj_maximal_cmData : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (P Q : Ideal (𝓞 E)), Q.IsMaximal → P ≤ Q → P ≤ Q.comap (RingOfIntegers.mapRingHom (starRingEnd E)) → P ≤ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
  atlas_forward_decl GlobalTheory.UnramifiedConj.le_map_comap_of_le_conj
end

section
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_ideal_coprime_conj_mul_eq_spanSingleton :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
      Formalism.BasicNotions.CMData F E → ∀ (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 →
      ∀ N : 𝓞 E, N ≠ 0 → ∃ P : Ideal (𝓞 E), P ≠ ⊥ ∧
        P ⊔ P.comap (RingOfIntegers.mapRingHom (starRingEnd E)) = ⊤ ∧
        (∃ t : 𝓞 E, ∃ p ∈ P, t * N + p = 1) ∧
        ∃ α : E, (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c =
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) α := by
  intro F E _ _ _ _ _ _ hcm c hc N hN
  obtain ⟨a, hac, hQ, hp⟩ := GlobalTheory.T.exists_mem_fractionalIdeal_primitive_local_generator' F E hcm.deg2 c hc N hN

  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨p, hpm⟩ := Ideal.exists_maximal (𝓞 F)
    exact hp p hpm (Submodule.zero_mem _)

  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) a * c⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hc]
    exact mul_le_mul' (FractionalIdeal.spanSingleton_le_iff_mem.mpr hac) le_rfl
  obtain ⟨P, hP⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hPc : (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) a := by
    rw [hP, mul_assoc, inv_mul_cancel₀ hc, mul_one]

  have key : ∀ Q : Ideal (𝓞 E), P ≤ Q → a ∈ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
    intro Q hPQ
    rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← hPc]
    exact mul_le_mul' ((FractionalIdeal.coeIdeal_le_coeIdeal E).mpr hPQ) le_rfl
  have hσσ : ∀ x : 𝓞 E, RingOfIntegers.mapRingHom (starRingEnd E)
      (RingOfIntegers.mapRingHom (starRingEnd E) x) = x := by
    intro x
    ext
    simp
  refine ⟨P, ?_, ?_, ?_, a, hPc⟩
  · rintro rfl
    apply ha
    rw [FractionalIdeal.coeIdeal_bot, zero_mul, eq_comm,
      FractionalIdeal.spanSingleton_eq_zero_iff] at hPc
    exact hPc
  · by_contra htop
    obtain ⟨Q, hQm, hPQ⟩ := Ideal.exists_le_maximal _ htop
    have h1 : P ≤ Q := le_sup_left.trans hPQ
    have h2 : P ≤ Q.comap (RingOfIntegers.mapRingHom (starRingEnd E)) := by
      intro x hx
      apply hPQ (Ideal.mem_sup_right _)
      show RingOfIntegers.mapRingHom (starRingEnd E) (RingOfIntegers.mapRingHom (starRingEnd E) x) ∈ P
      rw [hσσ]
      exact hx
    have h3 := GlobalTheory.T.le_map_comap_of_le_conj_maximal_cmData F E hcm P Q hQm h1 h2
    have hpm : (Q.comap (algebraMap (𝓞 F) (𝓞 E))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
    exact hp _ hpm (key _ h3)
  · have htop : P ⊔ Ideal.span {N} = ⊤ := by
      by_contra htop
      obtain ⟨Q, hQm, hPQ⟩ := Ideal.exists_le_maximal _ htop
      exact hQ Q hQm (hPQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self N)))
        (key Q (le_sup_left.trans hPQ))
    have h1 : (1 : 𝓞 E) ∈ P ⊔ Ideal.span {N} := htop ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact ⟨t, y, hy, by rw [add_comm]; exact hyz⟩

end GlobalTheory
end

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_coprime_conj_mul_eq_spanSingleton' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ P : Ideal (𝓞 E), P ≠ ⊥ ∧ P ⊔ P.comap (RingOfIntegers.mapRingHom (starRingEnd E)) = ⊤ ∧ (∃ t : 𝓞 E, ∃ p ∈ P, t * N + p = 1) ∧ ∃ α : E, (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) α := by
  atlas_forward_decl GlobalTheory.exists_ideal_coprime_conj_mul_eq_spanSingleton
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.HypPrimVec

section
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem hconj (x y : S.V) : star (S.hT x y) = S.hT y x :=
  LinearMap.isSymm_def.mp S.herm x y

theorem mem_dual_iff (Λ : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ ↔ ∀ y ∈ Λ, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT y x := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]

theorem mem_of_dual {Λ : Submodule (𝓞 E) S.V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {x : S.V}
    (h : ∀ y ∈ Λ, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT y x) : x ∈ Λ := by
  have hx : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := (mem_dual_iff Λ x).2 h
  rwa [hU] at hx

theorem pair_mem {Λ : Submodule (𝓞 E) S.V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {x y : S.V}
    (hx : x ∈ Λ) (hy : y ∈ Λ) : ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT y x := by
  have hx' : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hU]; exact hx
  exact (mem_dual_iff Λ x).1 hx' y hy

end

theorem exists_primitive_norm_neg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], CMData F E → ∀ (S : HSpace E) (Λ : Submodule (𝓞 E) S.V), Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → (∃ x : 𝓞 E, (x : E) + star (x : E) = 1) → ∀ (e f : S.V) (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → S.hT e e = 0 → S.hT f f = 0 → S.hT e f = 1 → (∀ x ∈ c, x • e ∈ Λ) → (∀ y ∈ Λ, S.hT f y ∈ c) → ∀ T : ℕ, T ≠ 0 → ∃ z : S.V, z ∈ Submodule.span E {e, f} ∧ z ∈ Λ ∧ S.hT z z = -((T : ℕ) : E) ∧ ∀ γ : E, γ • z ∈ Λ → ∃ o : 𝓞 E, (o : E) = γ := by
  intro F E _ _ _ _ _ _ hcm S Λ hU hx e f c hc hee hff hef hce hfc T hT
  obtain ⟨x, hx⟩ := hx

  have hσ : ∀ r : 𝓞 E, ((RingOfIntegers.mapRingHom (starRingEnd E) r : 𝓞 E) : E) = star (r : E) :=
    fun r => rfl
  have hTne : (T : 𝓞 E) ≠ 0 := by
    intro h
    apply hT
    have h' := congrArg (fun r : 𝓞 E => (r : E)) h
    simpa using h'

  obtain ⟨P, hP0, hPP, ⟨t, p0, hp0, htp⟩, α, hα⟩ := GlobalTheory.T.exists_ideal_coprime_conj_mul_eq_spanSingleton' F E hcm c hc (T : 𝓞 E) hTne
  have htpE : (t : E) * (T : E) + (p0 : E) = 1 := by
    have h' := congrArg (fun r : 𝓞 E => (r : E)) htp
    simpa using h'

  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1
    (show (1 : 𝓞 E) ∈ P ⊔ P.comap (RingOfIntegers.mapRingHom (starRingEnd E)) by
      rw [hPP]; exact Submodule.mem_top)
  have hq' : RingOfIntegers.mapRingHom (starRingEnd E) q ∈ P := Ideal.mem_comap.1 hq
  have hpqE : (p : E) + (q : E) = 1 := by
    have h' := congrArg (fun r : 𝓞 E => (r : E)) hpq
    simpa using h'
  set w : 𝓞 E := p * x + RingOfIntegers.mapRingHom (starRingEnd E) q *
    RingOfIntegers.mapRingHom (starRingEnd E) x with hw
  have hwP : w ∈ P := P.add_mem (P.mul_mem_right _ hp) (P.mul_mem_right _ hq')
  have hwE : (w : E) + star (w : E) = 1 := by
    have e1 : (w : E) = (p : E) * x + star (q : E) * star (x : E) := by
      rw [hw]; push_cast; rfl
    have hs : star (p : E) + star (q : E) = 1 := by rw [← star_add, hpqE, star_one]
    rw [e1, star_add, star_mul', star_mul', star_star, star_star]
    linear_combination (x : E) * hpqE + star (x : E) * hs + hx

  have hPc : ∀ r ∈ P, ∀ s ∈ c, ∃ o : 𝓞 E, (o : E) * α = (r : E) * s := by
    intro r hr s hs
    have hm : (r : E) * s ∈ (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c :=
      FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩) hs
    rw [hα, FractionalIdeal.mem_spanSingleton] at hm
    obtain ⟨o, ho⟩ := hm
    exact ⟨o, by rw [← ho, Algebra.smul_def]⟩
  have hαc : α ∈ c := by
    have h1 : α ∈ (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
      rw [hα]; exact FractionalIdeal.mem_spanSingleton_self _ _
    have hle : (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c ≤ c :=
      FractionalIdeal.mul_le.2 fun i hi j hj => by
        obtain ⟨r, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
        rw [← Algebra.smul_def]
        exact (c : Submodule (𝓞 E) E).smul_mem r hj
    exact hle h1
  have hα0 : α ≠ 0 := by
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    obtain ⟨s, hs, hs0⟩ : ∃ s ∈ c, s ≠ 0 := by
      by_contra h
      push_neg at h
      apply hc
      ext y
      simp only [FractionalIdeal.mem_zero_iff]
      exact ⟨h y, fun hy => hy ▸ (c : Submodule (𝓞 E) E).zero_mem⟩
    obtain ⟨o, ho⟩ := hPc r hr s hs
    intro h0
    rw [h0, mul_zero] at ho
    have hr0' : (r : E) ≠ 0 := by exact_mod_cast hr0
    exact mul_ne_zero hr0' hs0 ho.symm
  have hfe : S.hT f e = 1 := by rw [← hconj e f, hef, star_one]

  set b : E := star (-(T : E) * (w : E) / α) with hb
  have h1 : star α * b = -(T : E) * star (w : E) := by
    rw [hb, ← star_mul', show α * (-(T : E) * (w : E) / α) = -(T : E) * w by field_simp,
      star_mul', star_neg, star_natCast]
  have h2 : star b * α = -(T : E) * (w : E) := by
    rw [hb, star_star]; field_simp
  refine ⟨α • e + b • f, ?_, ?_, ?_, ?_⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · refine Λ.add_mem (hce α hαc) (mem_of_dual hU fun y hy => ?_)
    obtain ⟨o, ho⟩ := hPc w hwP (S.hT f y) (hfc y hy)
    refine ⟨-(T : 𝓞 E) * RingOfIntegers.mapRingHom (starRingEnd E) o, ?_⟩
    have key : -(T : E) * w / α * S.hT f y = -(T : E) * o := by
      calc -(T : E) * w / α * S.hT f y = -(T : E) * ((w : E) * S.hT f y) / α := by ring
        _ = -(T : E) * ((o : E) * α) / α := by rw [ho]
        _ = -(T : E) * o := by field_simp
    rw [LinearMap.map_smul, ← hconj f y, smul_eq_mul, hb, ← star_mul', key, star_mul', star_neg,
      star_natCast]
    show ((-(T : 𝓞 E) * RingOfIntegers.mapRingHom (starRingEnd E) o : 𝓞 E) : E) = _
    push_cast
    rfl
  · simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      LinearMap.map_smul, smul_eq_mul, hee, hff, hef, hfe, mul_zero, mul_one, zero_add, add_zero,
      starRingEnd_apply]
    linear_combination h1 + h2 - (T : E) * hwE
  · intro γ hγ
    have hfz : S.hT f (γ • (α • e + b • f)) = γ * α := by
      simp only [map_add, LinearMap.map_smul, smul_eq_mul, hff, hfe, RingHom.id_apply]; ring
    have hγα : γ * α ∈ c := hfz ▸ hfc _ hγ
    obtain ⟨o1, ho1⟩ := hPc p0 hp0 _ hγα
    obtain ⟨o2, ho2⟩ := hPc w hwP _ hγα
    obtain ⟨o3, ho3⟩ := pair_mem hU hγ (hce α hαc)
    have E1 : (o1 : E) = p0 * γ := mul_right_cancel₀ hα0 (by rw [ho1]; ring)
    have E2 : (o2 : E) = w * γ := mul_right_cancel₀ hα0 (by rw [ho2]; ring)
    have E3 : (o3 : E) = -(T : E) * γ * star (w : E) := by
      have hez : S.hT (α • e) (γ • (α • e + b • f)) = γ * (star α * b) := by
        simp only [map_add, LinearMap.map_smulₛₗ, LinearMap.smul_apply, LinearMap.map_smul,
          smul_eq_mul, hee, hef, starRingEnd_apply, RingHom.id_apply]; ring
      rw [hez, h1] at ho3
      change (o3 : E) = _ at ho3
      rw [ho3]; ring
    refine ⟨o2 + (-t * o3 + RingOfIntegers.mapRingHom (starRingEnd E) w * o1), ?_⟩
    have hcast : ((o2 + (-t * o3 + RingOfIntegers.mapRingHom (starRingEnd E) w * o1) : 𝓞 E) : E) =
        (o2 : E) + (-(t : E) * o3 + star (w : E) * o1) := by
      push_cast; rfl
    rw [hcast]
    linear_combination E2 - (t : E) * E3 + star (w : E) * E1 + γ * star (w : E) * htpE + γ * hwE

end GlobalTheory.HypPrimVec
end

open NumberField IsDedekindDomain Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_vector_norm_neg_hyperbolicPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], CMData F E → ∀ (S : HSpace E) (Λ : Submodule (𝓞 E) S.V), Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → (∃ x : 𝓞 E, (x : E) + star (x : E) = 1) → ∀ (e f : S.V) (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → S.hT e e = 0 → S.hT f f = 0 → S.hT e f = 1 → (∀ x ∈ c, x • e ∈ Λ) → (∀ y ∈ Λ, S.hT f y ∈ c) → ∀ T : ℕ, T ≠ 0 → ∃ z : S.V, z ∈ Submodule.span E {e, f} ∧ z ∈ Λ ∧ S.hT z z = -((T : ℕ) : E) ∧ ∀ γ : E, γ • z ∈ Λ → ∃ o : 𝓞 E, (o : E) = γ := by
  atlas_forward_decl GlobalTheory.HypPrimVec.exists_primitive_norm_neg
end

section
open Formalism.BasicNotions Formalism.MainNotions.S
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoOrthHyp

open Matrix

theorem exists_norm_one {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (n : ℕ) (h : S.rank = n)
    (hn : 0 < n) (C : GL (Fin n) E)
    (hC : (C.1.map (starRingEnd E))ᵀ * C.1 = S.gram.reindex (finCongr h) (finCongr h)) :
    ∃ x : S.V, S.hT x x = 1 := by
  classical
  set e : Fin S.rank ≃ Fin n := finCongr h with he
  set M : Matrix (Fin n) (Fin n) E := ((C⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hM
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  refine ⟨∑ j : Fin n, M j i₀ • S.frame (e.symm j), ?_⟩
  have hCM : C.1 * M = 1 := by
    rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hstar : (C.1.map (starRingEnd E))ᵀ = C.1ᴴ := rfl
  have hprod : Mᴴ * S.gram.reindex e e * M = (C.1 * M)ᴴ * (C.1 * M) := by
    rw [← hC, hstar, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have key : (Mᴴ * S.gram.reindex e e * M) i₀ i₀ = 1 := by
    rw [hprod, hCM]
    simp
  rw [← key]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    HSpace.gram, starRingEnd_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem star_eq_hostConj (D : D7) (x : D.host.E) : starRingEnd D.host.E x = D.host.conj x := by
  have := D.host.isCMField_hostE
  obtain ⟨ψ⟩ := (inferInstance : Nonempty (D.host.E →+* ℂ))
  apply ψ.injective
  have h1 : ∀ y, ψ (D.host.conj y) = starRingEnd ℂ (ψ y) :=
    (D.host.der.conj_iff ψ D.host.conj).2 (MulEquiv.apply_symm_apply _ _)
  rw [h1]
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E ψ x

theorem exists_isotropic_orth_hyp : ∀ (D : D7), Formalism.L2.Forms.Forms0 D D.u₀ → ∃ w : (VS D).V, w ≠ 0 ∧ (VS D).hT w w = 0 ∧ ∀ i, (VS D).hT (D.sp.hypE i) w = 0 ∧ (VS D).hT (D.sp.hypF i) w = 0 := by
  intro D hF
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hi : (0 : ℕ) ≤ D.R.m := Nat.zero_le _
  obtain ⟨C, hC, -⟩ := hF.val0.de
  have hN : 0 < D.R.N 0 := by
    show 0 < D.R.k + 0 * (D.R.t + 1)
    have := D.R.m_add_three_le_k
    omega
  have hC' : (C.1.map (starRingEnd D.host.E))ᵀ * C.1 =
      (D.sp.X 0).gram.reindex (finCongr (Formalism.L2.Forms.rankN D 0 hi))
        (finCongr (Formalism.L2.Forms.rankN D 0 hi)) := hC
  obtain ⟨x, hx⟩ := exists_norm_one (D.sp.X 0) (D.R.N 0) (Formalism.L2.Forms.rankN D 0 hi) hN C hC'
  have hπ : (hF.atT.piU : D.host.E) * D.host.conj (hF.atT.piU : D.host.E) =
      ((D.mem D.u₀).A.T : D.host.E) := hF.atT.piU_norm
  have hT0 : ((D.mem D.u₀).A.T : D.host.E) ≠ 0 := by
    rw [← D.sp_T]
    exact_mod_cast D.sp.T_prime.ne_zero
  have hsym : ∀ a b : (VS D).V, (VS D).hT a b = 0 → (VS D).hT b a = 0 := by
    intro a b hab
    rw [← (VS D).herm.eq a b, hab, map_zero]
  have hvv : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x))
      (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x)) = ((D.mem D.u₀).A.T : D.host.E) := by
    rw [D.sp.iXY_isom 0 hm]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hx, mul_one, RingHom.id_apply,
      star_eq_hostConj]
    linear_combination hπ
  have hvz : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x)) D.sp.zm = 0 := D.sp.zm_orth _
  have hzv := hsym _ _ hvz
  have hzz : (VS D).hT D.sp.zm D.sp.zm = -((D.mem D.u₀).A.T : D.host.E) := by
    rw [D.sp.zm_norm, D.sp_T]
  refine ⟨D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x) + D.sp.zm, ?_, ?_, ?_⟩
  · intro h0
    have h1 : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x) + D.sp.zm) D.sp.zm = 0 := by
      rw [h0, map_zero, LinearMap.zero_apply]
    rw [map_add, LinearMap.add_apply, hvz, hzz, zero_add, neg_eq_zero] at h1
    exact hT0 h1
  · simp only [map_add, LinearMap.add_apply, hvv, hvz, hzv, hzz]
    ring
  · intro i
    constructor
    · rw [map_add, hsym _ _ (D.sp.hyp_orthX i _).1, hsym _ _ (D.sp.hyp_orthz i).1, add_zero]
    · rw [map_add, hsym _ _ (D.sp.hyp_orthX i _).2, hsym _ _ (D.sp.hyp_orthz i).2, add_zero]

end GlobalTheory.IsoOrthHyp
end

section
open Formalism.BasicNotions Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.St.Lat

theorem latExists_of_forms0 : ∀ D : D7, Formalism.L2.Forms.Forms0 D D.u₀ → LatExists D := by
  intro D hF
  refine GlobalTheory.St.Lat.latExists_of ?_ ?_ D ?_
  · exact GlobalTheory.T.exists_primitive_vector_norm_neg_hyperbolicPair
  · exact GlobalTheory.unramified_degree_one_of_ncard_placesOver
  · exact GlobalTheory.IsoOrthHyp.exists_isotropic_orth_hyp D hF

end GlobalTheory.St.Lat
end
