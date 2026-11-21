import Mathlib
import Formalism.UnipotentAdelicQuotients.ClassNumberFinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraToSpecialLinearEmbInjectiveHom
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteAdelicDoubleCosetsOfRationalSLSubgroup
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact

section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFiniteAdele_compact_closed_multiples : ∀ (F : Type) [Field F] [NumberField F], IsCompact {a : FiniteAdeleRing (𝓞 F) F | (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)} ∧ (∀ M : ℕ, 0 < M → IsClosed {a : FiniteAdeleRing (𝓞 F) F | ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ a = (M : FiniteAdeleRing (𝓞 F) F) * c}) ∧ (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ M : ℕ, 0 < M → ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ a = (M : FiniteAdeleRing (𝓞 F) F) * c) → a = 0) ∧ (∀ x : F, (∀ v, (algebraMap F (FiniteAdeleRing (𝓞 F) F) x : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) → ∃ y : 𝓞 F, x = y) ∧ (∀ a : FiniteAdeleRing (𝓞 F) F, ∃ M : ℕ, 0 < M ∧ (∀ v, (((M : FiniteAdeleRing (𝓞 F) F) * a) : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ IsReduced (FiniteAdeleRing (𝓞 F) F) := by
  first | exact @GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties | exact GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties | (intros; apply GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties <;> assumption)
end

section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

theorem isClosed_int_add_mul {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (O : Subring A) (M : ℕ) (hM : 0 < M) (hcl : IsClosed {a : A | ∃ c ∈ O, a = (M : A) * c}) :
    IsClosed {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} := by
  have key : {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} =
      ⋃ r : Fin M, (fun x => x - ((r : ℕ) : A)) ⁻¹' {a : A | ∃ c ∈ O, a = (M : A) * c} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨z, c, hc, rfl⟩
      have hMz : (0 : ℤ) < M := by exact_mod_cast hM
      have h0 : 0 ≤ z % (M : ℤ) := Int.emod_nonneg z hMz.ne'
      have h1 : z % (M : ℤ) < M := Int.emod_lt_of_pos z hMz
      have hdiv := congrArg (fun t : ℤ => (t : A)) (Int.emod_add_mul_ediv z M)
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hdiv
      refine ⟨⟨(z % M).toNat, by omega⟩, ((z / M : ℤ) : A) + c, add_mem (intCast_mem O _) hc, ?_⟩
      have hr : (((z % M).toNat : ℕ) : A) = ((z % M : ℤ) : A) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
      simp only [hr]
      linear_combination -hdiv
    · rintro ⟨r, c, hc, hx⟩
      refine ⟨((r : ℕ) : ℤ), c, hc, ?_⟩
      rw [Int.cast_natCast]
      linear_combination hx
  rw [key]
  exact isClosed_iUnion_of_finite fun r => hcl.preimage (continuous_id.sub continuous_const)

theorem exists_sum_of_approx {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (O : Subring A) (hO : IsCompact (O : Set A))
    (hcl : ∀ M : ℕ, 0 < M → IsClosed {a : A | ∃ c ∈ O, a = (M : A) * c})
    (hz : ∀ a : A, (∀ M : ℕ, 0 < M → ∃ c ∈ O, a = (M : A) * c) → a = 0)
    {β : Type} [Fintype β] (w : β → A) (a : A)
    (ha : ∀ M : ℕ, 0 < M → ∃ (z : β → ℤ) (c : A), c ∈ O ∧ a = ∑ i, (z i : A) * w i + (M : A) * c) :
    ∃ r : β → A, (∀ i, ∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : A), c ∈ O ∧ r i = (z : A) + (M : A) * c) ∧
      a = ∑ i, r i * w i := by
  classical
  have hSc : ∀ M : ℕ, 0 < M →
      IsClosed {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} :=
    fun M hM => isClosed_int_add_mul O M hM (hcl M hM)
  have hL : Continuous fun r : β → A => a - ∑ i, r i * w i :=
    continuous_const.sub (continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const)
  let t : ℕ → Set (β → A) := fun m =>
    (⋂ i, (fun r : β → A => r i) ⁻¹'
      {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + ((m + 1 : ℕ) : A) * c}) ∩
    (fun r : β → A => a - ∑ i, r i * w i) ⁻¹' {x : A | ∃ c ∈ O, x = ((m + 1 : ℕ) : A) * c}
  have htc : ∀ m, IsClosed (t m) := fun m =>
    (isClosed_iInter fun i => (hSc (m + 1) m.succ_pos).preimage (continuous_apply i)).inter
      ((hcl (m + 1) m.succ_pos).preimage hL)
  have hs : IsCompact (Set.univ.pi fun _ : β => (O : Set A)) := isCompact_univ_pi fun _ => hO
  have hne : ∀ u : Finset ℕ, ((Set.univ.pi fun _ : β => (O : Set A)) ∩ ⋂ m ∈ u, t m).Nonempty := by
    intro u
    have hNpos : 0 < ∏ m ∈ u, (m + 1) := Finset.prod_pos fun m _ => m.succ_pos
    obtain ⟨z, c, hc, hac⟩ := ha _ hNpos
    refine ⟨fun i => (z i : A), fun i _ => intCast_mem O (z i), ?_⟩
    simp only [Set.mem_iInter]
    intro m hm
    obtain ⟨k, hk⟩ : (m + 1) ∣ ∏ m ∈ u, (m + 1) := Finset.dvd_prod_of_mem _ hm
    rw [hk] at hac
    simp only [t, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
    refine ⟨fun i => ⟨z i, 0, zero_mem O, by ring⟩, (k : A) * c, mul_mem (natCast_mem O k) hc, ?_⟩
    push_cast at hac ⊢
    linear_combination hac
  obtain ⟨r, -, hr⟩ := hs.inter_iInter_nonempty t htc hne
  simp only [t, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] at hr
  have hpred : ∀ M : ℕ, 0 < M → ∃ m : ℕ, M = m + 1 := fun M hM => ⟨M - 1, by omega⟩
  refine ⟨r, fun i M hM => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ := hpred M hM
    exact (hr m).1 i
  · have h0 : a - ∑ i, r i * w i = 0 := hz _ fun M hM => by
      obtain ⟨m, rfl⟩ := hpred M hM
      exact (hr m).2
    exact sub_eq_zero.mp h0

private def intAdeles (F : Type) [Field F] [NumberField F] :
    Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  neg_mem' ha v := neg_mem (ha v)

theorem exists_sum_integralBasis : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) → ∃ r : β → FiniteAdeleRing (𝓞 F) F, (∀ i, (∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : FiniteAdeleRing (𝓞 F) F), (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ r i = (z : FiniteAdeleRing (𝓞 F) F) + (M : FiniteAdeleRing (𝓞 F) F) * c)) ∧ a = ∑ i, r i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F) := by
  intro F _ _ β _ ω a ha
  obtain ⟨hcomp, hclM, hzero, -, -, -⟩ := GlobalTheory.T.integralFiniteAdele_compact_closed_multiples F
  have hexp : ∀ x : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (x : F) =
      ∑ i, ((ω.repr x i : ℤ) : FiniteAdeleRing (𝓞 F) F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ω i : 𝓞 F) : F) := by
    intro x
    conv_lhs => rw [← ω.sum_repr x]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_sum, zsmul_eq_mul, map_mul, map_intCast]
  refine exists_sum_of_approx (intAdeles F) hcomp hclM hzero _ a ?_
  intro M hM
  obtain ⟨x, c, hc, hac⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F M hM).2 a ha
  refine ⟨fun i => ω.repr x i, c, hc, ?_⟩
  rw [hac, hexp, nsmul_eq_mul]

end GlobalTheory.ClassFin
end

section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.CoordDiv

variable (F : Type) [Field F] [NumberField F]

def intAdeles : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {c | ∀ v, c v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  mul_mem' := fun {a b} ha hb v => mul_mem (ha v) (hb v)
  one_mem' := fun v => one_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  add_mem' := fun {a b} ha hb v => add_mem (ha v) (hb v)
  zero_mem' := fun v => zero_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  neg_mem' := fun {a} ha v => neg_mem (ha v)

theorem algebraMap_mem (a : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ intAdeles F := by
  intro v
  rw [FiniteAdeleRing.algebraMap_apply, RingOfIntegers.coe_eq_algebraMap]
  exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v a

theorem exists_of_mem (k : F) (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) k ∈ intAdeles F) :
    ∃ a : 𝓞 F, (a : F) = k := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F k fun v => by
    have hv := h v
    rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    exact hv
  exact ⟨a, ha⟩

theorem dvd_of_eq (x : 𝓞 F) (N : ℕ) (hN : 0 < N) (e : FiniteAdeleRing (𝓞 F) F)
    (he : e ∈ intAdeles F)
    (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) (x : F) = (N : FiniteAdeleRing (𝓞 F) F) * e) :
    ∃ a : 𝓞 F, x = (N : 𝓞 F) * a := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'

  have hk : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((x : F) / N) = e := by
    rw [div_eq_mul_inv, map_mul, h, mul_comm, ← mul_assoc,
      ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul, inv_mul_cancel₀ hN',
      map_one, one_mul]
  obtain ⟨a, ha⟩ := exists_of_mem F _ (hk ▸ he)
  have hx : (x : F) = N * (a : F) := by
    rw [ha]
    field_simp
  exact ⟨a, by exact_mod_cast hx⟩

theorem int_dvd (z : ℤ) (N : ℕ) (a : 𝓞 F) (h : (z : 𝓞 F) = (N : 𝓞 F) * a) : (N : ℤ) ∣ z := by

  have h2 := congrArg (Algebra.norm ℤ) h
  rw [map_mul, ← eq_intCast (algebraMap ℤ (𝓞 F)) z,
    show (N : 𝓞 F) = algebraMap ℤ (𝓞 F) (N : ℤ) by simp, Algebra.norm_algebraMap,
    Algebra.norm_algebraMap] at h2
  exact (Int.pow_dvd_pow_iff Module.finrank_pos.ne').mp ⟨_, h2⟩

theorem coord_divisible : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)) (r : β → FiniteAdeleRing (𝓞 F) F) (N : ℕ), 0 < N → (∀ i, (∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : FiniteAdeleRing (𝓞 F) F), (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ r i = (z : FiniteAdeleRing (𝓞 F) F) + (M : FiniteAdeleRing (𝓞 F) F) * c)) → (∃ e : FiniteAdeleRing (𝓞 F) F, (∀ v, (e : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ ∑ i, r i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F) = (N : FiniteAdeleRing (𝓞 F) F) * e) → ∀ i, ∃ s : FiniteAdeleRing (𝓞 F) F, (∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : FiniteAdeleRing (𝓞 F) F), (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ s = (z : FiniteAdeleRing (𝓞 F) F) + (M : FiniteAdeleRing (𝓞 F) F) * c) ∧ r i = (N : FiniteAdeleRing (𝓞 F) F) * s := by
  intro F _ _ β _ ω r N hN hr hsum i
  obtain ⟨e, he, hsum⟩ := hsum
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'

  have hu : IsUnit (N : FiniteAdeleRing (𝓞 F) F) := by
    have := (isUnit_iff_ne_zero.mpr hN').map (algebraMap F (FiniteAdeleRing (𝓞 F) F))
    rwa [map_natCast] at this
  have hω : ∀ j, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ω j : 𝓞 F) : F) ∈ intAdeles F :=
    fun j => algebraMap_mem F (ω j)
  have hint : ∀ z : ℤ, (z : FiniteAdeleRing (𝓞 F) F) ∈ intAdeles F := fun z => intCast_mem _ z

  choose z c hc hrc using fun j => hr j N hN
  have hc' : ∀ j, c j ∈ intAdeles F := hc

  have hL : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((∑ j, z j • ω j : 𝓞 F)) : F) =
      ∑ j, (z j : FiniteAdeleRing (𝓞 F) F) * algebraMap F _ ((ω j : 𝓞 F) : F) := by
    rw [RingOfIntegers.coe_eq_algebraMap, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_zsmul, zsmul_eq_mul, RingOfIntegers.coe_eq_algebraMap]
  obtain ⟨a, ha⟩ := dvd_of_eq F (∑ j, z j • ω j) N hN
    (e - ∑ j, c j * algebraMap F _ ((ω j : 𝓞 F) : F))
    (sub_mem he (sum_mem fun j _ => mul_mem (hc' j) (hω j))) (by
      rw [hL, mul_sub, Finset.mul_sum, ← hsum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hrc j]
      ring)

  have hm : ∀ j, z j = N * ω.repr a j := by
    intro j
    have h1 := congrArg (fun y => ω.repr y j) ha
    have h2 : (N : 𝓞 F) * a = (N : ℤ) • a := by rw [zsmul_eq_mul]; push_cast; rfl
    simp only [ω.repr_sum_self, h2, map_zsmul, Finsupp.smul_apply, smul_eq_mul] at h1
    simpa using h1
  have key : ∀ j, r j = N * ((ω.repr a j : FiniteAdeleRing (𝓞 F) F) + c j) := by
    intro j
    rw [hrc j, hm j]
    push_cast
    ring
  refine ⟨(ω.repr a i : FiniteAdeleRing (𝓞 F) F) + c i, ?_, key i⟩
  intro M hM

  obtain ⟨z', c', hc'', hr'⟩ := hr i (M * N) (Nat.mul_pos hM hN)
  have hs : (ω.repr a i : FiniteAdeleRing (𝓞 F) F) + c i - M * c' ∈ intAdeles F :=
    sub_mem (add_mem (hint _) (hc' i)) (mul_mem (natCast_mem _ M) hc'')
  obtain ⟨a', ha'⟩ := dvd_of_eq F (z' : 𝓞 F) N hN _ hs (by
    have e1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((z' : 𝓞 F)) : F) =
        (z' : FiniteAdeleRing (𝓞 F) F) := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_intCast, map_intCast]
    have e2 : (z' : FiniteAdeleRing (𝓞 F) F) = r i - ((M * N : ℕ) : FiniteAdeleRing (𝓞 F) F) * c' := by
      rw [hr']
      ring
    rw [e1, e2, key i]
    push_cast
    ring)
  obtain ⟨t, ht⟩ := int_dvd F z' N a' ha'
  refine ⟨t, c', hc'', hu.mul_left_cancel ?_⟩
  rw [← key i, hr', ht]
  push_cast
  ring

end GlobalTheory.CoordDiv
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.AdeleFree

section Abstract

variable {A : Type} [CommRing A]

def intClosure (O : Subring A) : Subring A where
  carrier := {r | ∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : A), c ∈ O ∧ r = (z : A) + (M : A) * c}
  mul_mem' := by
    intro a b ha hb M hM
    obtain ⟨z, c, hc, rfl⟩ := ha M hM
    obtain ⟨z', c', hc', rfl⟩ := hb M hM
    refine ⟨z * z', z * c' + c * z' + M * (c * c'), ?_, by push_cast; ring⟩
    exact add_mem (add_mem (mul_mem (intCast_mem _ _) hc') (mul_mem hc (intCast_mem _ _)))
      (mul_mem (natCast_mem _ _) (mul_mem hc hc'))
  one_mem' := fun M _ => ⟨1, 0, zero_mem _, by simp⟩
  add_mem' := by
    intro a b ha hb M hM
    obtain ⟨z, c, hc, rfl⟩ := ha M hM
    obtain ⟨z', c', hc', rfl⟩ := hb M hM
    exact ⟨z + z', c + c', add_mem hc hc', by push_cast; ring⟩
  zero_mem' := fun M _ => ⟨0, 0, zero_mem _, by simp⟩
  neg_mem' := by
    intro a ha M hM
    obtain ⟨z, c, hc, rfl⟩ := ha M hM
    exact ⟨-z, -c, neg_mem hc, by push_cast; ring⟩

theorem intClosure_le (O : Subring A) {a : A} (ha : a ∈ intClosure O) : a ∈ O := by
  obtain ⟨z, c, hc, rfl⟩ := ha 1 one_pos
  exact add_mem (intCast_mem _ _) (by simpa using hc)

def ratSpan (Z : Subring A) : Subring A where
  carrier := {a | ∃ M : ℕ, 0 < M ∧ (M : A) * a ∈ Z}
  mul_mem' := by
    rintro a b ⟨M, hM, ha⟩ ⟨N, hN, hb⟩
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    have : ((M * N : ℕ) : A) * (a * b) = (M * a) * (N * b) := by push_cast; ring
    rw [this]; exact mul_mem ha hb
  one_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro a b ⟨M, hM, ha⟩ ⟨N, hN, hb⟩
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    have : ((M * N : ℕ) : A) * (a + b) = N * (M * a) + M * (N * b) := by push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem _ _) ha) (mul_mem (natCast_mem _ _) hb)
  zero_mem' := ⟨1, one_pos, by simp⟩
  neg_mem' := by
    rintro a ⟨M, hM, ha⟩
    exact ⟨M, hM, by rw [mul_neg]; exact neg_mem ha⟩

theorem mem_ratSpan {Z : Subring A} {a : A} (ha : a ∈ Z) : a ∈ ratSpan Z :=
  ⟨1, one_pos, by simpa using ha⟩

theorem den_mul (φ : ℚ →+* A) (q : ℚ) : (q.den : A) * φ q = (q.num : A) := by
  rw [← map_natCast φ q.den, ← map_mul, Rat.den_mul_eq_num, map_intCast]

theorem rat_mem (φ : ℚ →+* A) (Z : Subring A) (q : ℚ) : φ q ∈ ratSpan Z :=
  ⟨q.den, q.den_pos, by rw [den_mul]; exact intCast_mem _ _⟩

theorem inv_mul (φ : ℚ →+* A) {N : ℕ} (hN : 0 < N) : φ (N : ℚ)⁻¹ * (N : A) = 1 := by
  rw [← map_natCast φ N, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]

theorem cancel (φ : ℚ →+* A) {N : ℕ} (hN : 0 < N) {a b : A} (h : (N : A) * a = N * b) :
    a = b :=
  calc a = (φ (N : ℚ)⁻¹ * N) * a := by rw [inv_mul φ hN, one_mul]
    _ = φ (N : ℚ)⁻¹ * (N * a) := mul_assoc _ _ _
    _ = φ (N : ℚ)⁻¹ * (N * b) := by rw [h]
    _ = b := by rw [← mul_assoc, inv_mul φ hN, one_mul]

theorem mem_of_mul (φ : ℚ →+* A) (O : Subring A)
    (hint : ∀ (z : ℤ) (N : ℕ), 0 < N → ∀ e ∈ O, (z : A) = N * e → (N : ℤ) ∣ z)
    {N : ℕ} (hN : 0 < N) {c : A} (hc : c ∈ O) (h : (N : A) * c ∈ intClosure O) :
    c ∈ intClosure O := by
  intro M hM
  obtain ⟨z, d, hd, hzd⟩ := h (N * M) (Nat.mul_pos hN hM)
  have hz : (z : A) = N * (c - M * d) := by rw [mul_sub, hzd]; push_cast; ring
  obtain ⟨y, rfl⟩ := hint z N hN (c - M * d) (sub_mem hc (mul_mem (natCast_mem _ _) hd)) hz
  refine ⟨y, d, hd, cancel φ hN ?_⟩
  rw [hzd]; push_cast; ring

theorem exists_basis (φ : ℚ →+* A) (O : Subring A) [IsReduced A] {β : Type} [Fintype β]
    (w : β → A) (hw : ∀ i, w i ∈ O)
    (hint : ∀ (z : ℤ) (N : ℕ), 0 < N → ∀ e ∈ O, (z : A) = N * e → (N : ℤ) ∣ z)
    (h0 : ∀ a : A, (∀ M : ℕ, 0 < M → ∃ c, c ∈ O ∧ a = (M : A) * c) → a = 0)
    (hden : ∀ a : A, ∃ M : ℕ, 0 < M ∧ (M : A) * a ∈ O)
    (hspan : ∀ a ∈ O, ∃ r : β → A, (∀ i, r i ∈ intClosure O) ∧ a = ∑ i, r i * w i)
    (hdiv : ∀ (r : β → A) (N : ℕ), 0 < N → (∀ i, r i ∈ intClosure O) →
      (∃ e, e ∈ O ∧ ∑ i, r i * w i = (N : A) * e) →
        ∀ i, ∃ s, s ∈ intClosure O ∧ r i = (N : A) * s) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℚ R) (R₀ : Subring R) (_ : Algebra R A)
      (b : Module.Basis β R A), AdelicPair R R₀ ∧ IsReduced R ∧ (∀ i, b i = w i) ∧
        ∀ a : A, a ∈ O ↔ ∀ i, b.repr a i ∈ R₀ := by
  classical

  set Z := intClosure O with hZdef
  set R := ratSpan Z with hRdef
  have hZO : ∀ x ∈ Z, x ∈ O := fun x hx => intClosure_le O hx
  have hZR : ∀ x ∈ Z, x ∈ R := fun x hx => mem_ratSpan hx
  let φR : ℚ →+* R := φ.codRestrict R (rat_mem φ Z)
  let _ : Algebra ℚ R := φR.toAlgebra
  let _ : Algebra R A := (Subring.subtype R).toAlgebra
  have hsmul : ∀ (c : R) (x : A), c • x = (c : A) * x := fun _ _ => rfl
  let R₀ : Subring R := Z.comap (Subring.subtype R)
  have hmemR : ∀ c : R, ∃ M : ℕ, 0 < M ∧ (M : A) * c ∈ Z := fun c => c.2

  have hli : LinearIndependent R w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    choose M hM hMc using fun j => hmemR (c j)
    set K := ∏ j, M j with hKdef
    have hK : 0 < K := Finset.prod_pos fun j _ => hM j
    have hr : ∀ j, (K : A) * c j ∈ Z := by
      intro j
      have hsplit : (K : A) * c j = ((∏ k ∈ Finset.univ.erase j, M k : ℕ) : A) * ((M j : A) * c j) := by
        rw [← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
      rw [hsplit]
      exact mul_mem (natCast_mem _ _) (hMc j)
    have hc' : ∑ j, (c j : A) * w j = 0 := by simpa only [hsmul] using hc
    have hsum : ∑ j, ((K : A) * c j) * w j = 0 := by
      simp only [mul_assoc]
      rw [← Finset.mul_sum, hc', mul_zero]
    have hzero : (K : A) * c i = 0 := by
      apply h0
      intro N hN
      obtain ⟨s, hs, hrs⟩ := hdiv (fun j => (K : A) * c j) N hN hr
        ⟨0, zero_mem _, by rw [hsum, mul_zero]⟩ i
      exact ⟨s, hZO s hs, hrs⟩
    exact Subtype.ext (cancel φ hK (by rw [hzero]; simp))

  have hsp : ⊤ ≤ Submodule.span R (Set.range w) := by
    rintro a -
    obtain ⟨M, hM, hMa⟩ := hden a
    obtain ⟨r, hr, hra⟩ := hspan _ hMa
    have hmem : ∀ i, φ (M : ℚ)⁻¹ * r i ∈ R := fun i =>
      ⟨M, hM, by rw [← mul_assoc, mul_comm (M : A) (φ _), inv_mul φ hM, one_mul]; exact hr i⟩
    have ha : a = ∑ i, (⟨φ (M : ℚ)⁻¹ * r i, hmem i⟩ : R) • w i := by
      simp only [hsmul]
      apply cancel φ hM
      rw [hra, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← mul_assoc, mul_comm (M : A) (φ _), inv_mul φ hM, one_mul]
    rw [ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b : Module.Basis β R A := Module.Basis.mk hli hsp
  have hb : ∀ i, b i = w i := fun i => Module.Basis.mk_apply hli hsp i
  refine ⟨R, inferInstance, inferInstance, R₀, inferInstance, b, ?_, ?_, hb, ?_⟩
  ·
    refine ⟨?_, ?_⟩
    · intro q hq
      have hq' : φ q ∈ Z := hq
      obtain ⟨z, c, hc, hzc⟩ := hq' q.den q.den_pos
      have h1 : ((q.num - q.den * z : ℤ) : A) = (q.den : A) * ((q.den : A) * c) := by
        push_cast
        rw [← den_mul φ q, hzc]
        ring
      have h2 := hint _ q.den q.den_pos _ (mul_mem (natCast_mem _ _) hc) h1
      have h3 : (q.den : ℤ) ∣ q.num := by
        have h4 := dvd_add h2 (dvd_mul_right (q.den : ℤ) z)
        simpa using h4
      have h5 : q.den = 1 :=
        Nat.eq_one_of_dvd_coprimes q.reduced.symm dvd_rfl (Int.natCast_dvd.mp h3)
      exact ⟨q.num, ((Rat.den_eq_one_iff q).mp h5).symm⟩
    · intro M hM r
      obtain ⟨K, hK, hKr⟩ := hmemR r
      obtain ⟨z, c, hc, hzc⟩ := hKr (K * M) (Nat.mul_pos hK hM)
      have hcZ : c ∈ Z := by
        apply mem_of_mul φ O hint (Nat.mul_pos hK hM) hc
        have hkm : ((K * M : ℕ) : A) * c = (K : A) * r - z := by rw [hzc]; ring
        rw [hkm]
        exact sub_mem hKr (intCast_mem _ _)
      refine ⟨(z : ℚ) / K, ⟨c, hZR c hcZ⟩, hcZ, ?_⟩
      apply Subtype.ext
      have hk : (K : A) * φ ((z : ℚ) / K) = z := by
        rw [← map_natCast φ K, ← map_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hK.ne'),
          map_intCast]
      change (r : A) = φ ((z : ℚ) / K) + (M : A) * c
      apply cancel φ hK
      rw [hzc, mul_add, hk]
      push_cast
      ring
  · exact isReduced_of_injective (Subring.subtype R) Subtype.val_injective
  · intro a
    have hrep : a = ∑ i, (b.repr a i : A) * w i := by
      conv_lhs => rw [← b.sum_repr a]
      simp only [hsmul, hb]
    constructor
    · intro ha i
      obtain ⟨r, hr, hra⟩ := hspan a ha
      let c : β → R := fun j => ⟨r j, hZR _ (hr j)⟩
      have hdiff : ∑ j, (b.repr a j - c j) • b j = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, b.sum_repr]
        rw [sub_eq_zero]
        simp only [hsmul, hb]
        exact hra
      have h := Fintype.linearIndependent_iff.1 b.linearIndependent _ hdiff i
      rw [sub_eq_zero.1 h]
      exact hr i
    · intro h
      rw [hrep]
      exact Subring.sum_mem _ fun i _ => mul_mem (hZO _ (h i)) (hw i)

end Abstract

theorem finiteAdele_free : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)), ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℚ R) (R₀ : Subring R) (_ : Algebra R (FiniteAdeleRing (𝓞 F) F)) (b : Module.Basis β R (FiniteAdeleRing (𝓞 F) F)), AdelicPair R R₀ ∧ IsReduced R ∧ (∀ i, b i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F)) ∧ ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ↔ ∀ i, b.repr a i ∈ R₀ := by
  intro F _ _ β _ ω
  classical
  obtain ⟨-, -, hz0, -, hden, hred⟩ := GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F
  have : IsReduced (FiniteAdeleRing (𝓞 F) F) := hred
  let O : Subring (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.CoordDiv.intAdeles F
  have hint : ∀ (z : ℤ) (N : ℕ), 0 < N → ∀ e ∈ O,
      (z : FiniteAdeleRing (𝓞 F) F) = N * e → (N : ℤ) ∣ z := by
    intro z N hN e he h
    obtain ⟨a, ha⟩ := GlobalTheory.CoordDiv.dvd_of_eq F (z : 𝓞 F) N hN e he (by simpa using h)
    exact GlobalTheory.CoordDiv.int_dvd F z N a ha
  obtain ⟨R, i1, i2, R₀, i3, b, hP, hR, hb, hmem⟩ :=
    exists_basis ((algebraMap F (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap ℚ F)) O
      (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F))
      (fun i => GlobalTheory.CoordDiv.algebraMap_mem F (ω i)) hint (fun a ha => hz0 a ha) (fun a => hden a)
      (fun a ha => GlobalTheory.ClassFin.exists_sum_integralBasis F β ω a ha)
      (fun r N hN hr he => GlobalTheory.CoordDiv.coord_divisible F β ω r N hN hr he)
  exact ⟨R, i1, i2, R₀, i3, b, hP, hR, hb, fun a => hmem a⟩

end GlobalTheory.AdeleFree
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_pair_reduced_basis : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)), ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℚ R) (R₀ : Subring R) (_ : Algebra R (FiniteAdeleRing (𝓞 F) F)) (b : Module.Basis β R (FiniteAdeleRing (𝓞 F) F)), AdelicPair R R₀ ∧ IsReduced R ∧ (∀ i, b i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F)) ∧ ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ↔ ∀ i, b.repr a i ∈ R₀ := by
  atlas_forward_decl GlobalTheory.AdeleFree.finiteAdele_free
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem repr_algebraMap_of_basis_image (F β : Type) [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (x : F) (k : β) :
    b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k) := by
  have hq : ∀ q : ℚ, algebraMap F A (algebraMap ℚ F q) = algebraMap R A (algebraMap ℚ R q) := by
    intro q
    have h : (algebraMap F A).comp (algebraMap ℚ F) = (algebraMap R A).comp (algebraMap ℚ R) :=
      RingHom.ext_rat _ _
    exact RingHom.congr_fun h q
  have hx : algebraMap F A x = ∑ j, algebraMap ℚ R (ω.repr x j) • b j := by
    conv_lhs => rw [← ω.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul, hq, hb, Algebra.smul_def]
  rw [hx, b.repr_sum_self]

theorem coords_const_baseChange : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ x : F, (∀ k, b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k)) ∧ Algebra.leftMulMatrix b (algebraMap F A x) = (Algebra.leftMulMatrix ω x).map (algebraMap ℚ R) := by
  intro F β _ _ _ _ ω R A _ _ _ _ _ b hb x
  refine ⟨repr_algebraMap_of_basis_image F β ω R A b hb x, ?_⟩
  ext i j
  rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    hb j, ← map_mul, repr_algebraMap_of_basis_image F β ω R A b hb]

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_leftMulMatrix_const_baseChange : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ x : F, (∀ k, b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k)) ∧ Algebra.leftMulMatrix b (algebraMap F A x) = (Algebra.leftMulMatrix ω x).map (algebraMap ℚ R) := by
  atlas_forward_decl GlobalTheory.ClassFin.coords_const_baseChange
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem repr_algebraMap_of_basis_eq {F β : Type} [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (a : F) (k : β) :
    b.repr (algebraMap F A a) k = algebraMap ℚ R (ω.repr a k) := by
  have hq : ∀ q : ℚ, algebraMap F A (algebraMap ℚ F q) = algebraMap R A (algebraMap ℚ R q) :=
    fun q => DFunLike.congr_fun (RingHom.ext_rat ((algebraMap F A).comp (algebraMap ℚ F))
      ((algebraMap R A).comp (algebraMap ℚ R))) q
  have hsum : algebraMap F A a = ∑ i, algebraMap ℚ R (ω.repr a i) • b i := by
    conv_lhs => rw [← ω.sum_repr a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def (ω.repr a i) (ω i), map_mul, hq, hb,
      Algebra.smul_def (algebraMap ℚ R (ω.repr a i))]
  rw [hsum, b.repr_sum_self]

private theorem basis_repr_mul_of_basis_eq_algebraMap {F β : Type} [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (u v : A)
    (k : β) : b.repr (u * v) k =
      ∑ i, ∑ j, b.repr u i * b.repr v j * algebraMap ℚ R (ω.repr (ω i * ω j) k) := by
  have e : ∀ i j, b.repr ((b.repr u i • b i) * (b.repr v j • b j)) k
      = b.repr u i * b.repr v j * algebraMap ℚ R (ω.repr (ω i * ω j) k) := by
    intro i j
    rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul, hb i, hb j, ← map_mul,
      repr_algebraMap_of_basis_eq ω b hb]
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, e]
  exact Finset.sum_comm

theorem exists_coord_polynomial : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (τ : Type) (P : MvPolynomial τ F), ∃ Q : β → MvPolynomial (τ × β) ℚ, ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ (x : τ → A) (k : β), b.repr (MvPolynomial.aeval x P) k = MvPolynomial.aeval (fun p : τ × β => b.repr (x p.1) p.2) (Q k) := by
  intro F β _ _ _ _ ω τ P
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨fun k => MvPolynomial.C (ω.repr a k), ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, repr_algebraMap_of_basis_eq ω b hb]
  | add p q hp hq =>
    obtain ⟨Q1, h1⟩ := hp
    obtain ⟨Q2, h2⟩ := hq
    refine ⟨fun k => Q1 k + Q2 k, ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [map_add, map_add, Finsupp.add_apply, map_add, h1 R A b hb x k, h2 R A b hb x k]
  | mul_X p n hp =>
    obtain ⟨Q1, h1⟩ := hp
    refine ⟨fun k => ∑ i, ∑ j, Q1 i * MvPolynomial.X (n, j) *
      MvPolynomial.C (ω.repr (ω i * ω j) k), ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [map_mul, MvPolynomial.aeval_X, basis_repr_mul_of_basis_eq_algebraMap ω b hb]
    simp only [map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, h1 R A b hb x]

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_coord_polynomial_baseChange : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (τ : Type) (P : MvPolynomial τ F), ∃ Q : β → MvPolynomial (τ × β) ℚ, ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ (x : τ → A) (k : β), b.repr (MvPolynomial.aeval x P) k = MvPolynomial.aeval (fun p : τ × β => b.repr (x p.1) p.2) (Q k) := by
  atlas_forward_decl GlobalTheory.ClassFin.exists_coord_polynomial
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem res_mulVec_repr {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] (b : Module.Basis β R A) (g : Matrix κ κ A) (v : κ → A) :
    res b g *ᵥ (fun p : κ × β => b.repr (v p.1) p.2) = fun p : κ × β => b.repr ((g *ᵥ v) p.1) p.2 := by
  funext p
  simp only [Matrix.mulVec, dotProduct, res, Matrix.of_apply, Fintype.sum_prod_type, map_sum,
    Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (Algebra.leftMulMatrix_mulVec_repr b (g p.1 j) (v j)) p.2
  simpa [Matrix.mulVec, dotProduct] using h

theorem res_one_mul_injective_isUnit :
    ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), res b (1 : Matrix κ κ A) = 1 ∧ (∀ g h : Matrix κ κ A, res b (g * h) = res b g * res b h) ∧ Function.Injective (fun g : Matrix κ κ A => res b g) ∧ ∀ g : Matrix κ κ A, IsUnit (res b g).det → IsUnit g := by
  intro R A β κ _ _ _ _ _ _ _ b
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext ⟨i, k⟩ ⟨j, l⟩
    by_cases h : i = j
    · subst h
      simp [res, Matrix.one_apply]
    · simp [res, Matrix.one_apply, h]
  · intro g h
    ext ⟨i, k⟩ ⟨j, l⟩
    simp only [res, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, map_sum, map_mul,
      Matrix.sum_apply]
  · intro g h hgh
    ext i j
    apply Algebra.leftMulMatrix_injective b
    ext k l
    exact congrFun (congrFun hgh (i, k)) (j, l)
  · intro g hg
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro w
    have hs : Function.Surjective (res b g).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hg)
    obtain ⟨u, hu⟩ := hs (fun p : κ × β => b.repr (w p.1) p.2)
    refine ⟨fun i => b.equivFun.symm (fun k => u (i, k)), ?_⟩
    have h := res_mulVec_repr b g (fun i => b.equivFun.symm (fun k => u (i, k)))
    have hu' : (fun p : κ × β => b.repr (b.equivFun.symm (fun k => u (p.1, k))) p.2) = u := by
      funext p
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hu', hu] at h
    funext i
    apply b.repr.injective
    ext k
    exact (congrFun h (i, k)).symm

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictScalarsMatrixOfBasis_hom_injective_isUnit : ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), res b (1 : Matrix κ κ A) = 1 ∧ (∀ g h : Matrix κ κ A, res b (g * h) = res b g * res b h) ∧ Function.Injective (fun g : Matrix κ κ A => res b g) ∧ ∀ g : Matrix κ κ A, IsUnit (res b g).det → IsUnit g := by
  atlas_forward_decl GlobalTheory.ClassFin.res_one_mul_injective_isUnit
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.WeilEqs

noncomputable def coordOf {κ β R : Type} [Fintype β] [CommRing R] [Algebra ℚ R] (c : β → ℚ)
    (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R) (i j : κ) (k : β) : R :=
  ∑ l, y (Sum.inl (i, k)) (Sum.inl (j, l)) * algebraMap ℚ R (c l)

noncomputable def gen (ι : Type) : Matrix ι ι (MvPolynomial (ι × ι) ℚ) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

section
variable {κ β R : Type} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β] [CommRing R] [Algebra ℚ R]

omit [Fintype κ] [DecidableEq κ] [DecidableEq β] in
theorem aeval_coordOf (c : β → ℚ) (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R) (i j : κ) (k : β) :
    MvPolynomial.aeval (fun ij : ((κ × β) ⊕ Unit) × ((κ × β) ⊕ Unit) => y ij.1 ij.2)
      (coordOf c (gen ((κ × β) ⊕ Unit)) i j k) = coordOf c y i j k := by
  simp only [coordOf, gen, map_sum, map_mul, Matrix.of_apply, MvPolynomial.aeval_X, AlgHom.commutes]

theorem aeval_det (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R) :
    MvPolynomial.aeval (fun ij : ((κ × β) ⊕ Unit) × ((κ × β) ⊕ Unit) => y ij.1 ij.2)
      ((gen ((κ × β) ⊕ Unit)).toBlocks₁₁.det) = y.toBlocks₁₁.det := by
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp [gen, Matrix.toBlocks₁₁]

omit [Fintype κ] [DecidableEq κ] [DecidableEq β] in
theorem aeval_comp_coord (c : β → ℚ) (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R)
    (Q : MvPolynomial ((κ × κ) × β) ℚ) :
    MvPolynomial.aeval (fun ij : ((κ × β) ⊕ Unit) × ((κ × β) ⊕ Unit) => y ij.1 ij.2)
      (MvPolynomial.aeval (fun p : (κ × κ) × β => coordOf c (gen ((κ × β) ⊕ Unit)) p.1.1 p.1.2 p.2) Q) =
      MvPolynomial.aeval (fun p : (κ × κ) × β => coordOf c y p.1.1 p.1.2 p.2) Q := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp only [aeval_coordOf]

variable {A : Type} [CommRing A] [Algebra R A]

theorem sum_leftMul_one (b : Module.Basis β R A) (x : A) (k : β) :
    ∑ l, Algebra.leftMulMatrix b x k l * b.repr 1 l = b.repr x k := by
  have h := congrFun (Algebra.leftMulMatrix_mulVec_repr b x 1) k
  simpa [Matrix.mulVec, dotProduct] using h

theorem leftMul_expand (b : Module.Basis β R A) (x : A) (k l : β) :
    Algebra.leftMulMatrix b x k l = ∑ m, b.repr x m * Algebra.leftMulMatrix b (b m) k l := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end

theorem exists_equations : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), ∃ S' : Set (MvPolynomial (((Fin n × β) ⊕ Unit) × ((Fin n × β) ⊕ Unit)) ℚ), ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ y : Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) R, (∀ f ∈ S', ev f y = 0) ↔ ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) P = 0) ∧ y = emb b g := by
  intro F β _ _ _ _ ω n S
  choose Q hQ using fun P : MvPolynomial (Fin n × Fin n) F => GlobalTheory.T.exists_rational_coord_polynomial_baseChange F β ω (Fin n × Fin n) P
  let c : β → ℚ := fun l => ω.repr 1 l
  let X := gen ((Fin n × β) ⊕ Unit)
  refine ⟨{f | (∃ p u, f = X (Sum.inl p) (Sum.inr u)) ∨ (∃ p u, f = X (Sum.inr u) (Sum.inl p)) ∨
    (∃ i j k l, f = X (Sum.inl (i, k)) (Sum.inl (j, l)) -
      ∑ m, coordOf c X i j m * algebraMap ℚ _ (Algebra.leftMulMatrix ω (ω m) k l)) ∨
    f = X.toBlocks₁₁.det * X (Sum.inr ()) (Sum.inr ()) - 1 ∨
    ∃ P ∈ S, ∃ k, f = MvPolynomial.aeval
      (fun p : (Fin n × Fin n) × β => coordOf c X p.1.1 p.1.2 p.2) (Q P k)}, ?_⟩
  intro R A _ _ _ _ _ b hb y
  have hm := GlobalTheory.T.coords_leftMulMatrix_const_baseChange F β ω R A b hb
  obtain ⟨h1, hmul, -, hunit⟩ := GlobalTheory.T.restrictScalarsMatrixOfBasis_hom_injective_isUnit R A β (Fin n) b
  have hc : ∀ l, algebraMap ℚ R (c l) = b.repr 1 l := fun l => by
    have := (hm 1).1 l
    rw [map_one] at this
    exact this.symm
  have hL : ∀ m k l, algebraMap ℚ R (Algebra.leftMulMatrix ω (ω m) k l) =
      Algebra.leftMulMatrix b (b m) k l := fun m k l => by
    rw [hb m, (hm (ω m)).2, Matrix.map_apply]
  have hX : ∀ p q, MvPolynomial.aeval
      (fun ij : ((Fin n × β) ⊕ Unit) × ((Fin n × β) ⊕ Unit) => y ij.1 ij.2) (X p q) = y p q := fun p q => by
    simp [X, gen]
  have hinv : ∀ g : GL (Fin n) A, (res b (g : Matrix (Fin n) (Fin n) A)).det *
      (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det = 1 := fun g => by
    rw [← Matrix.det_mul, ← hmul, Units.mul_inv, h1, Matrix.det_one]
  have key : (∀ f ∈ {f | (∃ p u, f = X (Sum.inl p) (Sum.inr u)) ∨ (∃ p u, f = X (Sum.inr u) (Sum.inl p)) ∨
    (∃ i j k l, f = X (Sum.inl (i, k)) (Sum.inl (j, l)) -
      ∑ m, coordOf c X i j m * algebraMap ℚ _ (Algebra.leftMulMatrix ω (ω m) k l)) ∨
    f = X.toBlocks₁₁.det * X (Sum.inr ()) (Sum.inr ()) - 1 ∨
    ∃ P ∈ S, ∃ k, f = MvPolynomial.aeval
      (fun p : (Fin n × Fin n) × β => coordOf c X p.1.1 p.1.2 p.2) (Q P k)}, ev f y = 0) ↔
      ((∀ p u, y (Sum.inl p) (Sum.inr u) = 0) ∧ (∀ p u, y (Sum.inr u) (Sum.inl p) = 0) ∧
       (∀ i j k l, y (Sum.inl (i, k)) (Sum.inl (j, l)) =
          ∑ m, coordOf c y i j m * Algebra.leftMulMatrix b (b m) k l) ∧
       y.toBlocks₁₁.det * y (Sum.inr ()) (Sum.inr ()) = 1 ∧
       ∀ P ∈ S, ∀ k, MvPolynomial.aeval
          (fun p : (Fin n × Fin n) × β => coordOf c y p.1.1 p.1.2 p.2) (Q P k) = 0) := by
    have e3 : ∀ i j k l, ev (X (Sum.inl (i, k)) (Sum.inl (j, l)) -
        ∑ m, coordOf c X i j m * algebraMap ℚ _ (Algebra.leftMulMatrix ω (ω m) k l)) y =
        y (Sum.inl (i, k)) (Sum.inl (j, l)) -
          ∑ m, coordOf c y i j m * Algebra.leftMulMatrix b (b m) k l := fun i j k l => by
      simp only [ev, map_sub, map_sum, map_mul, hX, AlgHom.commutes, hL]
      simp only [X, aeval_coordOf]
    have e4 : ev (X.toBlocks₁₁.det * X (Sum.inr ()) (Sum.inr ()) - 1) y =
        y.toBlocks₁₁.det * y (Sum.inr ()) (Sum.inr ()) - 1 := by
      simp only [ev, map_sub, map_mul, hX, map_one]
      simp only [X, aeval_det]
    have e5 : ∀ P k, ev (MvPolynomial.aeval
        (fun p : (Fin n × Fin n) × β => coordOf c X p.1.1 p.1.2 p.2) (Q P k)) y =
        MvPolynomial.aeval (fun p : (Fin n × Fin n) × β => coordOf c y p.1.1 p.1.2 p.2) (Q P k) :=
      fun P k => aeval_comp_coord c y (Q P k)
    have e1 : ∀ p q, ev (X p q) y = y p q := hX
    constructor
    · intro h
      refine ⟨fun p u => ?_, fun p u => ?_, fun i j k l => ?_, ?_, fun P hP k => ?_⟩
      · rw [← e1]; exact h _ (Or.inl ⟨p, u, rfl⟩)
      · rw [← e1]; exact h _ (Or.inr (Or.inl ⟨p, u, rfl⟩))
      · rw [← sub_eq_zero, ← e3]; exact h _ (Or.inr (Or.inr (Or.inl ⟨i, j, k, l, rfl⟩)))
      · rw [← sub_eq_zero, ← e4]; exact h _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · rw [← e5]; exact h _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨P, hP, k, rfl⟩))))
    · rintro ⟨a1, a2, a3, a4, a5⟩ f (⟨p, u, rfl⟩ | ⟨p, u, rfl⟩ | ⟨i, j, k, l, rfl⟩ | rfl | ⟨P, hP, k, rfl⟩)
      · rw [e1, a1]
      · rw [e1, a2]
      · rw [e3, ← a3, sub_self]
      · rw [e4, a4, sub_self]
      · rw [e5, a5 P hP]
  rw [key]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5⟩
    let G : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => b.equivFun.symm (coordOf c y i j)
    have hG : ∀ i j k, b.repr (G i j) k = coordOf c y i j k := fun i j k => by
      have := congrFun (b.equivFun.apply_symm_apply (coordOf c y i j)) k
      rw [Module.Basis.equivFun_apply] at this
      exact this
    have hres : res b G = y.toBlocks₁₁ := by
      ext ⟨i, k⟩ ⟨j, l⟩
      simp only [res, Matrix.of_apply, Matrix.toBlocks₁₁]
      rw [a3, leftMul_expand]
      simp only [hG]
    have hu : IsUnit G := hunit G (by rw [hres]; exact IsUnit.of_mul_eq_one _ a4)
    obtain ⟨g, hg⟩ := hu
    refine ⟨g, fun P hP => ?_, ?_⟩
    · apply b.repr.injective
      ext k
      rw [hQ P R A b hb, hg]
      simp only [hG]
      simpa using a5 P hP k
    · have hi := hinv g
      rw [hg, hres] at hi
      have hcorner : y (Sum.inr ()) (Sum.inr ()) =
          (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det := by
        calc y (Sum.inr ()) (Sum.inr ()) = (y.toBlocks₁₁.det *
              (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det) * y (Sum.inr ()) (Sum.inr ()) := by
              rw [hi, one_mul]
          _ = (y.toBlocks₁₁.det * y (Sum.inr ()) (Sum.inr ())) *
              (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det := by ring
          _ = _ := by rw [a4, one_mul]
      ext (p | u) (q | v)
      · simp only [emb, Matrix.fromBlocks_apply₁₁, hg, hres, Matrix.toBlocks₁₁, Matrix.of_apply]
      · simp only [emb, Matrix.fromBlocks_apply₁₂, a1, Matrix.zero_apply]
      · simp only [emb, Matrix.fromBlocks_apply₂₁, a2, Matrix.zero_apply]
      · simp only [emb, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
        exact hcorner
  · rintro ⟨g, hg, rfl⟩
    have hco : ∀ i j k, coordOf c (emb b g) i j k = b.repr ((g : Matrix (Fin n) (Fin n) A) i j) k :=
      fun i j k => by
        simp only [coordOf, emb, Matrix.fromBlocks_apply₁₁, res, Matrix.of_apply, hc]
        exact sum_leftMul_one b _ k
    refine ⟨fun p u => ?_, fun p u => ?_, fun i j k l => ?_, ?_, fun P hP k => ?_⟩
    · simp [emb]
    · simp [emb]
    · simp only [hco]
      rw [← leftMul_expand]
      simp only [emb, Matrix.fromBlocks_apply₁₁, res, Matrix.of_apply]
    · simp only [emb, Matrix.toBlocks_fromBlocks₁₁, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
      exact hinv g
    · simp only [hco]
      rw [← hQ P R A b hb (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) k, hg P hP]
      simp

end GlobalTheory.ClassFin.WeilEqs
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_equations_weil_restriction : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), ∃ S' : Set (MvPolynomial (((Fin n × β) ⊕ Unit) × ((Fin n × β) ⊕ Unit)) ℚ), ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ y : Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) R, (∀ f ∈ S', ev f y = 0) ↔ ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) P = 0) ∧ y = emb b g := by
  atlas_forward_decl GlobalTheory.ClassFin.WeilEqs.exists_equations
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem mem_pts_zeroSet_of_isReduced :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S' : Set (MvPolynomial (ι × ι) ℚ)) (R : Type) [CommRing R]
      [Algebra ℚ R] (y : Matrix ι ι R),
      (y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R → ∀ f ∈ S', ev f y = 0) ∧
      (IsReduced R → (∀ f ∈ S', ev f y = 0) → y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R) := by
  intro ι _ _ S' R _ _ y
  refine ⟨fun hy f hf => hy f (fun g hg => hg f hf), fun hR hy f hf => ?_⟩
  have hrad : f ∈ (Ideal.span S').radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
      MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    have hx' := MvPolynomial.mem_zeroLocus_iff.1 hx
    exact hf (Matrix.of fun i j => x (i, j)) (fun p hp => hx' p (Ideal.subset_span hp))
  obtain ⟨n, hn⟩ := hrad
  have hle : Ideal.span S' ≤
      RingHom.ker (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => y ij.1 ij.2)) :=
    Ideal.span_le.2 fun p hp => hy p hp
  have h0 := hle hn
  rw [RingHom.mem_ker, map_pow] at h0
  exact IsReduced.eq_zero _ ⟨n, h0⟩

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S' : Set (MvPolynomial (ι × ι) ℚ)) (R : Type) [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R), (y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R → ∀ f ∈ S', ev f y = 0) ∧ (IsReduced R → (∀ f ∈ S', ev f y = 0) → y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R) := by
  atlas_forward_decl GlobalTheory.ClassFin.mem_pts_zeroSet_of_isReduced
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

theorem ev_map_complexAut {ι : Type} (f : MvPolynomial (ι × ι) ℚ)
    (g : Matrix ι ι ℂ) (σ : ℂ ≃+* ℂ) : ev f (g.map σ) = σ (ev f g) := by
  unfold ev
  have h := MvPolynomial.comp_aeval (f := fun ij : ι × ι => g ij.1 ij.2) (σ.toRingHom.toRatAlgHom)
  have h2 := DFunLike.congr_fun h f
  simp only [AlgHom.comp_apply, RingHom.toRatAlgHom_apply] at h2
  exact h2.symm

theorem exists_isQGroup_weilRestriction : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ Γ : Set (Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) ℂ), IsQGroup Γ ∧ ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → (∀ y ∈ pts Γ R, ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) ∧ y = emb b g) ∧ (IsReduced R → ∀ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) → emb b g ∈ pts Γ R) := by
  intro F β _ _ _ _ ω n S hS
  obtain ⟨S', hS'⟩ := GlobalTheory.T.exists_rational_equations_weil_restriction F β ω n S
  letI : Algebra F (ℂ ⊗[ℚ] F) := Algebra.TensorProduct.rightAlgebra
  have hb : ∀ i, Algebra.TensorProduct.basis ℂ ω i = algebraMap F (ℂ ⊗[ℚ] F) (ω i) := by
    intro i
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  have hC := hS' ℂ (ℂ ⊗[ℚ] F) (Algebra.TensorProduct.basis ℂ ω) hb
  obtain ⟨h1, hm, hi⟩ := hS (ℂ ⊗[ℚ] F)
  obtain ⟨e1, em, ed, -⟩ := GlobalTheory.T.glFreeAlgebraToSpecialLinearEmb_injective_hom ℂ (ℂ ⊗[ℚ] F) β (Fin n) (Algebra.TensorProduct.basis ℂ ω)
  refine ⟨{g | ∀ f ∈ S', ev f g = 0}, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact (hC 1).2 ⟨1, h1, e1.symm⟩
  · intro g hg h hh
    obtain ⟨g', hg', rfl⟩ := (hC g).1 hg
    obtain ⟨h', hh', rfl⟩ := (hC h).1 hh
    exact (hC _).2 ⟨g' * h', hm g' h' hg' hh', (em g' h').symm⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := (hC g).1 hg
    exact (hC _).2 ⟨g'⁻¹, hi g' hg', (ed g').2⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := (hC g).1 hg
    exact (ed g').1
  · intro σ g hg f hf
    rw [ev_map_complexAut, hg f hf, map_zero]
  · intro y hy
    exact (GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced _ S' ℂ y).1 hy
  · intro R A _ _ _ _ _ b hbb
    refine ⟨fun y hy => (hS' R A b hbb y).1 ((GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced _ S' R y).1 hy), fun hR g hg => ?_⟩
    exact (GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced _ S' R _).2 hR ((hS' R A b hbb _).2 ⟨g, hg, rfl⟩)

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isQGroup_weilRestriction_alt : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ Γ : Set (Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) ℂ), IsQGroup Γ ∧ ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → (∀ y ∈ pts Γ R, ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) ∧ y = emb b g) ∧ (IsReduced R → ∀ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) → emb b g ∈ pts Γ R) := by
  atlas_forward_decl GlobalTheory.ClassFin.exists_isQGroup_weilRestriction
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.EmbInt

theorem res_mul' {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (g h : Matrix κ κ A) :
    res b (g * h) = res b g * res b h := by
  ext p q
  simp only [res, Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
    Fintype.sum_prod_type]

theorem res_one' {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) :
    res b (1 : Matrix κ κ A) = 1 := by
  ext p q
  simp only [res, Matrix.of_apply, Matrix.one_apply]
  by_cases h : p.1 = q.1
  · rw [if_pos h, map_one, Matrix.one_apply]
    by_cases h' : p.2 = q.2
    · rw [if_pos h', if_pos (Prod.ext h h')]
    · rw [if_neg h', if_neg (fun e => h' (congrArg Prod.snd e))]
  · rw [if_neg h, map_zero, Matrix.zero_apply, if_neg (fun e => h (congrArg Prod.fst e))]

theorem repr_mem {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    (b : Module.Basis β R A) (R₀ : Subring R) (h1 : ∀ i, b.repr 1 i ∈ R₀) (x : A)
    (hx : ∀ p q, Algebra.leftMulMatrix b x p q ∈ R₀) (k : β) : b.repr x k ∈ R₀ := by

  have hsum : x = ∑ i, b.repr 1 i • (x * b i) := by
    conv_lhs => rw [← mul_one x, ← b.sum_repr 1]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
  have hk : b.repr x k = ∑ i, b.repr 1 i * Algebra.leftMulMatrix b x k i := by
    conv_lhs => rw [hsum]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, Algebra.leftMulMatrix_eq_repr_mul]
  rw [hk]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (h1 i) (hx k i)

theorem inv_mem {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (R₀ : Subring R)
    (M N : Matrix ι ι R) (hNM : N * M = 1) (hM : ∀ p q, M p q ∈ R₀) (hd : N.det ∈ R₀) (p q : ι) :
    N p q ∈ R₀ := by

  have hadj : N = N.det • M.adjugate := by
    have h1 : N * M * M.adjugate = M.adjugate := by rw [hNM, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h1
    have hd1 : N.det * M.det = 1 := by rw [← Matrix.det_mul, hNM, Matrix.det_one]
    rw [← h1, smul_smul, hd1, one_smul]

  let M' : Matrix ι ι R₀ := Matrix.of fun p q => ⟨M p q, hM p q⟩
  have hM' : R₀.subtype.mapMatrix M' = M := by ext; rfl
  have hA : M.adjugate p q = R₀.subtype (M'.adjugate p q) := by
    rw [← hM', ← RingHom.map_adjugate]; rfl
  rw [hadj, Matrix.smul_apply, smul_eq_mul, hA]
  exact Subring.mul_mem _ hd (M'.adjugate p q).2

theorem repr_map {F β : Type} [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F)
    {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A]
    (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (x : F) (k : β) :
    b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k) := by

  have hq : ∀ c : ℚ, algebraMap R A (algebraMap ℚ R c) = algebraMap F A (algebraMap ℚ F c) := fun c =>
    DFunLike.congr_fun (RingHom.ext_rat ((algebraMap R A).comp (algebraMap ℚ R))
      ((algebraMap F A).comp (algebraMap ℚ F))) c
  have hx : algebraMap F A x = ∑ i, algebraMap ℚ R (ω.repr x i) • b i := by
    conv_lhs => rw [← ω.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hq, hb]
  rw [hx, Module.Basis.repr_sum_self]

theorem res_map {F β : Type} [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F)
    {κ R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A]
    (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (g : Matrix κ κ F) :
    res b (g.map (algebraMap F A)) = (res ω g).map (algebraMap ℚ R) := by
  ext p q
  simp only [res, Matrix.of_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, hb,
    ← map_mul]
  exact repr_map ω b hb _ _

theorem emb_integral_and_rational : (∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (R₀ : Subring R) (u : GL κ A), (∀ i, b.repr 1 i ∈ R₀) → (∀ p q, emb b u p q ∈ R₀) → ∀ i j k, b.repr ((u : Matrix κ κ A) i j) k ∈ R₀ ∧ b.repr (((u⁻¹ : GL κ A) : Matrix κ κ A) i j) k ∈ R₀) ∧ ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (κ : Type) [Fintype κ] [DecidableEq κ] (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ γ : GL κ F, emb b (Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ) = (emb ω γ).map (algebraMap ℚ R) := by
  refine ⟨fun R A β κ _ _ _ _ _ _ _ b R₀ u h1 he i j k => ?_,
    fun F β _ _ _ _ ω κ _ _ R A _ _ _ _ _ b hb γ => ?_⟩
  ·

    have hres : ∀ p q, res b (u : Matrix κ κ A) p q ∈ R₀ := fun p q => by
      simpa [emb] using he (Sum.inl p) (Sum.inl q)
    have hdet : (res b ((u⁻¹ : GL κ A) : Matrix κ κ A)).det ∈ R₀ := by
      simpa [emb] using he (Sum.inr ()) (Sum.inr ())
    have hinv : res b ((u⁻¹ : GL κ A) : Matrix κ κ A) * res b (u : Matrix κ κ A) = 1 := by
      rw [← res_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, res_one']
    have hres' : ∀ p q, res b ((u⁻¹ : GL κ A) : Matrix κ κ A) p q ∈ R₀ :=
      fun p q => inv_mem R₀ _ _ hinv hres hdet p q
    exact ⟨repr_mem b R₀ h1 _ (fun p q => hres (i, p) (j, q)) k,
      repr_mem b R₀ h1 _ (fun p q => hres' (i, p) (j, q)) k⟩
  · have hc : ((Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ : GL κ A) :
        Matrix κ κ A) = (γ : Matrix κ κ F).map (algebraMap F A) := rfl
    have hc' : (((Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ)⁻¹ : GL κ A) :
        Matrix κ κ A) = ((γ⁻¹ : GL κ F) : Matrix κ κ F).map (algebraMap F A) := by
      rw [← map_inv]; rfl
    unfold emb
    rw [hc, hc', res_map ω b hb, res_map ω b hb, Matrix.fromBlocks_map]
    ext (x | x) (y | y) <;> simp [RingHom.map_det]

end GlobalTheory.ClassFin.EmbInt
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational : (∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (R₀ : Subring R) (u : GL κ A), (∀ i, b.repr 1 i ∈ R₀) → (∀ p q, emb b u p q ∈ R₀) → ∀ i j k, b.repr ((u : Matrix κ κ A) i j) k ∈ R₀ ∧ b.repr (((u⁻¹ : GL κ A) : Matrix κ κ A) i j) k ∈ R₀) ∧ ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (κ : Type) [Fintype κ] [DecidableEq κ] (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ γ : GL κ F, emb b (Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ) = (emb ω γ).map (algebraMap ℚ R) := by
  atlas_forward_decl GlobalTheory.ClassFin.EmbInt.emb_integral_and_rational
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

theorem classFinite_integralLevel : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ T : Finset (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), (∀ s ∈ T, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) ∧ ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) → ∃ γ : GL (Fin n) F, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((γ : GL (Fin n) (F)) : Matrix (Fin n) (Fin n) (F)) ij.1 ij.2) P = 0) ∧ ∃ s ∈ T, ∃ u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧ (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ x = Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ * s * u := by
  intro F _ _ n S hS
  classical

  obtain ⟨R, _, _, R₀, _, b, hAP, hred, hb, hint⟩ :=
    GlobalTheory.T.adelic_pair_reduced_basis F _ (NumberField.RingOfIntegers.basis F)
  obtain ⟨Γ, hΓ, hcorr⟩ := GlobalTheory.T.exists_isQGroup_weilRestriction_alt F _ (NumberField.integralBasis F) n S hS
  have hbF : ∀ i, b i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (NumberField.integralBasis F i) := by
    intro i
    rw [hb i, NumberField.integralBasis_apply]
  have hA := hcorr R (FiniteAdeleRing (𝓞 F) F) b hbF
  have hQ := hcorr ℚ F (NumberField.integralBasis F) (fun i => rfl)
  obtain ⟨T₀, hT₀, hdec⟩ := GlobalTheory.T.finiteAdelicDoubleCosets_of_rational_SL_subgroup _ Γ R R₀ hΓ hAP

  let lift : Matrix ((Fin n × _) ⊕ Unit) ((Fin n × _) ⊕ Unit) R → GL (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
    fun s => if h : ∃ g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F),
        (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n =>
          ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧
        s = GlobalTheory.ClassFin.emb b g then h.choose else 1
  have hlift : ∀ s ∈ pts Γ R, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n =>
      ((lift s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧
      s = GlobalTheory.ClassFin.emb b (lift s) := by
    intro s hs
    have h := hA.1 s hs
    simp only [lift, dif_pos h]
    exact h.choose_spec
  obtain ⟨hemb1, hembmul, -, hembinj⟩ := GlobalTheory.T.glFreeAlgebraToSpecialLinearEmb_injective_hom R (FiniteAdeleRing (𝓞 F) F) _ (Fin n) b
  refine ⟨T₀.image lift, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    exact (hlift s (hT₀ s hs)).1
  · intro x hx
    obtain ⟨γ₀, hγ₀, s, hs, u₀, hu₀, hu₀int, hx₀⟩ := hdec _ (hA.2 hred x hx)
    obtain ⟨γ, hγS, rfl⟩ := hQ.1 γ₀ hγ₀
    obtain ⟨u, huS, rfl⟩ := hA.1 u₀ hu₀
    obtain ⟨hsS, hsemb⟩ := hlift s (hT₀ s hs)
    have h1 : ∀ i, b.repr 1 i ∈ R₀ := by
      refine (hint 1).1 ?_
      intro v
      exact (HeightOneSpectrum.adicCompletionIntegers F v).one_mem
    have hunits := GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational.1 R _ _ (Fin n) b R₀ u h1 hu₀int
    refine ⟨γ, hγS, lift s, Finset.mem_image_of_mem lift hs, u, huS, ?_, ?_⟩
    · intro i j
      exact ⟨(hint _).2 (fun k => (hunits i j k).1), (hint _).2 (fun k => (hunits i j k).2)⟩
    · apply hembinj
      simp only [hembmul]
      rw [hx₀, ← hsemb, GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational.2 F _ (NumberField.integralBasis F) (Fin n) R _ b hbF γ]

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classNumber_finite_integralLevel_closedSubgroupGL : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ T : Finset (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), (∀ s ∈ T, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) ∧ ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) → ∃ γ : GL (Fin n) F, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((γ : GL (Fin n) (F)) : Matrix (Fin n) (Fin n) (F)) ij.1 ij.2) P = 0) ∧ ∃ s ∈ T, ∃ u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧ (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ x = Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ * s * u := by
  atlas_forward_decl GlobalTheory.ClassFin.classFinite_integralLevel
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.IntegralPointsCompact

theorem continuous_aeval_family {F A X σ : Type} [CommRing F] [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace X] (f : X → σ → A)
    (hf : ∀ s, Continuous fun x => f x s) (P : MvPolynomial σ F) :
    Continuous fun x => MvPolynomial.aeval (f x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p s hp => simp only [map_mul, MvPolynomial.aeval_X]; exact hp.mul (hf s)

theorem isClosed_of_equations {F A ι : Type} [CommRing F] [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [Fintype ι] [DecidableEq ι]
    (S : Set (MvPolynomial (ι × ι) F)) (H : Subgroup (GL ι A))
    (hH : ∀ g, g ∈ H ↔ ∀ P ∈ S, MvPolynomial.aeval
      (fun ij : ι × ι => ((g : GL ι A) : Matrix ι ι A) ij.1 ij.2) P = 0) :
    IsClosed (H : Set (GL ι A)) := by
  have e : (H : Set (GL ι A)) = ⋂ P ∈ S, {g : GL ι A | MvPolynomial.aeval
      (fun ij : ι × ι => (g : Matrix ι ι A) ij.1 ij.2) P = 0} := by
    ext g
    simp only [Set.mem_iInter, SetLike.mem_coe]
    exact hH g
  rw [e]
  refine isClosed_biInter fun P _ => isClosed_eq ?_ continuous_const
  exact continuous_aeval_family (fun (g : GL ι A) (ij : ι × ι) => (g : Matrix ι ι A) ij.1 ij.2)
    (fun s => Units.continuous_val.matrix_elem s.1 s.2) P

theorem isCompact_integral_points : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) (H : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))), (∀ g, g ∈ H ↔ (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) → IsCompact {u : H | (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v))} := by
  intro F _ _ n S H hH
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  have hK := GlobalTheory.GLIntegral.isCompact_glSub (ι := Fin n) (GlobalTheory.GLIntegral.intSubring F)
    (GlobalTheory.AdeleCocompact.isCompact_integral F)
  have hc := isClosed_of_equations S H hH
  have h := hc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  refine (congrArg IsCompact (Set.ext fun u => ?_)).mpr h
  exact ⟨fun hu => ⟨fun i j => (hu i j).1, fun i j => (hu i j).2⟩,
    fun hu i j => ⟨hu.1 i j, hu.2 i j⟩⟩

end GlobalTheory.IntegralPointsCompact
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_integralPoints_finiteAdelic_algebraicGroup : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) (H : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))), (∀ g, g ∈ H ↔ (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) → IsCompact {u : H | (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v))} := by
  atlas_forward_decl GlobalTheory.IntegralPointsCompact.isCompact_integral_points
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem compact_subset_finite_leftCosets (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (K : Set G) (hU : IsOpen (U : Set G))
    (hK : IsCompact K) : ∃ T : Finset G, ∀ k ∈ K, ∃ t ∈ T, ∃ u ∈ U, k = t * u := by
  obtain ⟨T, -, hT⟩ := hK.elim_nhds_subcover (fun t : G => (fun k => t⁻¹ * k) ⁻¹' (U : Set G))
    (fun t _ => (hU.preimage (by fun_prop)).mem_nhds (by simp))
  refine ⟨T, fun k hk => ?_⟩
  have := hT hk
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨t, ht, h⟩ := this
  exact ⟨t, ht, t⁻¹ * k, h, by simp⟩

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_meets_finitely_many_leftCosets_open : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G) (K : Set G), IsOpen (U : Set G) → IsCompact K → ∃ T : Finset G, ∀ k ∈ K, ∃ t ∈ T, ∃ u ∈ U, k = t * u := by
  atlas_forward_decl GlobalTheory.ClassFin.compact_subset_finite_leftCosets
end

section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem classNumberFinite_holds : HeckeCharacterZeroLocus.ClassNumberFinite := by
  classical
  intro F _ _ n S hS U hUo _
  obtain ⟨T₀, hT₀, hx⟩ := GlobalTheory.T.classNumber_finite_integralLevel_closedSubgroupGL F n S (fun B _ _ =>
    ⟨(hS B).1, fun g h hg hh => (hS B).2.1 g hg h hh, fun g hg => (hS B).2.2 g hg⟩)
  have hK := GlobalTheory.T.isCompact_integralPoints_finiteAdelic_algebraicGroup F n S (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))
    (fun g => Iff.rfl)
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.T.compact_meets_finitely_many_leftCosets_open _ U _ hUo hK
  refine ⟨Finset.image₂ (fun (s : T₀) (t : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) =>
    (⟨s.1, hT₀ s.1 s.2⟩ : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) * t) T₀.attach T₁, ?_⟩
  intro x
  obtain ⟨γ, hγ, s, hs, k, hk, hki, hxe⟩ := hx x.1 x.2
  obtain ⟨t, ht, u, hu, hke⟩ := hT₁ ⟨k, hk⟩ hki
  refine ⟨γ, hγ, _, Finset.mem_image₂_of_mem (Finset.mem_attach T₀ ⟨s, hs⟩) ht, u, hu, ?_⟩
  have hke' : k = t.1 * u.1 := congrArg Subtype.val hke
  rw [hxe, hke']
  simp only [Subgroup.coe_mul, mul_assoc]

end GlobalTheory
end
