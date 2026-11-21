import Formalism.HermitianCurvature.PrimeToDifferent

namespace Formalism.FourierDecayAlt.P.S6x6
open NumberField NumberField.IsCMField Module Formalism.FourierDecayAlt.S6
open scoped nonZeroDivisors

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem conj_conj (x : 𝓞 E) :
    ringOfIntegersComplexConj E (ringOfIntegersComplexConj E x) = x := by
  apply RingOfIntegers.ext
  simp [complexConj_apply_apply]


theorem dd_ne_zero : dd E ≠ 0 := by
  unfold dd
  rw [FractionalIdeal.coeIdeal_ne_zero]
  exact differentIdeal_ne_bot

theorem dd_le_one : dd E ≤ 1 := FractionalIdeal.coeIdeal_le_one


section LG

variable {E}

theorem locAt_add {L : Submodule ℤ E} (hL : IsFLattice E L)
    {P : Ideal (𝓞 (maximalRealSubfield E))} (hP : P.IsPrime) {x y : E}
    (hx : x ∈ locAt E P L) (hy : y ∈ locAt E P L) : x + y ∈ locAt E P L := by
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  refine ⟨a * b, fun h => (hP.mem_or_mem h).elim ha hb, ?_⟩
  have h1 := hL.1 b _ hax
  have h2 := hL.1 a _ hby
  have h3 : algebraMap (𝓞 (maximalRealSubfield E)) E (a * b) * (x + y) =
      algebraMap (𝓞 (maximalRealSubfield E)) E b * (algebraMap (𝓞 (maximalRealSubfield E)) E a * x) +
      algebraMap (𝓞 (maximalRealSubfield E)) E a * (algebraMap (𝓞 (maximalRealSubfield E)) E b * y) := by
    rw [map_mul]; ring
  rw [h3]; exact L.add_mem h1 h2

theorem locAt_zero (L : Submodule ℤ E) {P : Ideal (𝓞 (maximalRealSubfield E))} (hP : P.IsPrime) :
    (0 : E) ∈ locAt E P L :=
  ⟨1, fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h), by simp⟩

theorem locAt_sum {L : Submodule ℤ E} (hL : IsFLattice E L)
    {P : Ideal (𝓞 (maximalRealSubfield E))} (hP : P.IsPrime) {ι : Type*} (s : Finset ι) (f : ι → E)
    (h : ∀ i ∈ s, f i ∈ locAt E P L) : ∑ i ∈ s, f i ∈ locAt E P L :=
  Finset.sum_induction f (fun x => x ∈ locAt E P L) (fun _ _ hx hy => locAt_add hL hP hx hy)
    (locAt_zero L hP) h

def ann {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E) : Ideal (𝓞 (maximalRealSubfield E)) where
  carrier := {a | algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show algebraMap _ E (a + b) * t ∈ L
    rw [map_add, add_mul]; exact L.add_mem ha hb
  smul_mem' := fun c a ha => by
    show algebraMap _ E (c • a) * t ∈ L
    rw [smul_eq_mul, map_mul, mul_assoc]; exact hL.1 c _ ha

theorem mem_ann {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E)
    (a : 𝓞 (maximalRealSubfield E)) :
    a ∈ ann hL t ↔ algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L := Iff.rfl

theorem ann_ne_bot {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E) : ann hL t ≠ ⊥ := by
  obtain ⟨n, hn, hnt⟩ := hL.2 t
  intro h
  have h1 : (n : 𝓞 (maximalRealSubfield E)) ∈ ann hL t := by
    rw [mem_ann, map_natCast]; exact hnt
  rw [h, Ideal.mem_bot] at h1
  have : n = 0 := by exact_mod_cast h1
  omega

theorem exists_multiplier {L : Submodule ℤ E} (hL : IsFLattice E L)
    (P : Ideal (𝓞 (maximalRealSubfield E))) (hP : P.IsMaximal) (τ : E) :
    ∃ e : 𝓞 (maximalRealSubfield E),
      algebraMap (𝓞 (maximalRealSubfield E)) E e * τ - τ ∈ locAt E P L ∧
      ∀ Q : Ideal (𝓞 (maximalRealSubfield E)), Q.IsMaximal → Q ≠ P →
        algebraMap (𝓞 (maximalRealSubfield E)) E e * τ ∈ locAt E Q L := by
  have hfin : FiniteMultiplicity P (ann hL τ) :=
    FiniteMultiplicity.of_not_isUnit (fun h => hP.ne_top (Ideal.isUnit_iff.mp h)) (ann_ne_bot hL τ)
  obtain ⟨J, hJ, hPJ⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  generalize multiplicity P (ann hL τ) = k at hJ
  rw [Ideal.dvd_iff_le] at hPJ
  obtain ⟨b, hbJ, hbP⟩ := SetLike.not_le_iff_exists.mp hPJ
  have hcop : IsCoprime P J := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have h1 : P = P ⊔ J := hP.eq_of_le h le_sup_left
    exact hPJ (h1 ▸ le_sup_right)
  obtain ⟨u, hu, e, he, hue⟩ := Ideal.isCoprime_iff_exists.mp (hcop.pow_left (m := k))
  refine ⟨e, ⟨b, hbP, ?_⟩, ?_⟩
  · have h1 : u * b ∈ ann hL τ := hJ ▸ Ideal.mul_mem_mul hu hbJ
    rw [mem_ann] at h1
    have h2 : algebraMap (𝓞 (maximalRealSubfield E)) E b *
        (algebraMap (𝓞 (maximalRealSubfield E)) E e * τ - τ) =
        -(algebraMap (𝓞 (maximalRealSubfield E)) E (u * b) * τ) := by
      have h3 : algebraMap (𝓞 (maximalRealSubfield E)) E u +
          algebraMap (𝓞 (maximalRealSubfield E)) E e = 1 := by
        rw [← map_add, hue, map_one]
      rw [map_mul]
      linear_combination (algebraMap (𝓞 (maximalRealSubfield E)) E b * τ) * h3
    rw [h2]; exact L.neg_mem h1
  · intro Q hQ hQP
    have hnle : ¬ P ≤ Q := fun h => hQP (hP.eq_of_le hQ.ne_top h).symm
    obtain ⟨c, hcP, hcQ⟩ := SetLike.not_le_iff_exists.mp hnle
    refine ⟨c ^ k, fun h => hcQ (hQ.isPrime.mem_of_pow_mem _ h), ?_⟩
    have h1 : c ^ k * e ∈ ann hL τ := hJ ▸ Ideal.mul_mem_mul (Ideal.pow_mem_pow hcP k) he
    rw [mem_ann, map_mul, mul_assoc] at h1
    exact h1

theorem finite_bad {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E) :
    {P : Ideal (𝓞 (maximalRealSubfield E)) | P.IsMaximal ∧ t ∉ locAt E P L}.Finite := by
  obtain ⟨n, hn, hnt⟩ := hL.2 t
  have hn0 : (n : 𝓞 (maximalRealSubfield E)) ≠ 0 := by
    intro h
    have : n = 0 := by exact_mod_cast h
    omega
  have hI : Ideal.span {(n : 𝓞 (maximalRealSubfield E))} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hn0
  refine ((Ideal.finite_factors hI).image
    (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)) => v.asIdeal)).subset ?_
  rintro P ⟨hP, htP⟩
  have hnP : (n : 𝓞 (maximalRealSubfield E)) ∈ P := by
    by_contra h
    exact htP ⟨n, h, by rw [map_natCast]; exact hnt⟩
  have hPbot : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hnP
    exact hn0 hnP
  exact ⟨⟨P, hP.isPrime, hPbot⟩, by
    show P ∣ _
    rw [Ideal.dvd_span_singleton]; exact hnP, rfl⟩


theorem approx {L : Submodule ℤ E} (hL : IsFLattice E L)
    (S : Finset (Ideal (𝓞 (maximalRealSubfield E)))) (τ : Ideal (𝓞 (maximalRealSubfield E)) → E)
    (hS : ∀ P ∈ S, P.IsMaximal) :
    ∃ t : E, (∀ P ∈ S, t - τ P ∈ locAt E P L) ∧
      ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → P ∉ S → t ∈ locAt E P L := by
  classical
  have hex : ∀ P : Ideal (𝓞 (maximalRealSubfield E)), ∃ e : 𝓞 (maximalRealSubfield E),
      P.IsMaximal → (algebraMap (𝓞 (maximalRealSubfield E)) E e * τ P - τ P ∈ locAt E P L ∧
      ∀ Q : Ideal (𝓞 (maximalRealSubfield E)), Q.IsMaximal → Q ≠ P →
        algebraMap (𝓞 (maximalRealSubfield E)) E e * τ P ∈ locAt E Q L) := by
    intro P
    by_cases hP : P.IsMaximal
    · obtain ⟨e, he⟩ := exists_multiplier hL P hP (τ P)
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose e he using hex
  refine ⟨∑ P ∈ S, algebraMap (𝓞 (maximalRealSubfield E)) E (e P) * τ P, ?_, ?_⟩
  · intro P hPS
    rw [← Finset.add_sum_erase S _ hPS, add_sub_right_comm]
    refine locAt_add hL (hS P hPS).isPrime (he P (hS P hPS)).1 ?_
    refine locAt_sum hL (hS P hPS).isPrime _ _ fun Q hQ => ?_
    rw [Finset.mem_erase] at hQ
    exact (he Q (hS Q hQ.2)).2 P (hS P hPS) (Ne.symm hQ.1)
  · intro P hP hPS
    refine locAt_sum hL hP.isPrime _ _ fun Q hQ => ?_
    exact (he Q (hS Q hQ)).2 P hP (fun h => hPS (h ▸ hQ))

end LG

end Formalism.FourierDecayAlt.P.S6x6

namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6



end Formalism.FourierDecayAlt.P
