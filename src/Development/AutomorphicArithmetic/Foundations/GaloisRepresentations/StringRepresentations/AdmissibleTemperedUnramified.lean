module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.GaloisStatementWeakOfFull

@[expose] public section

noncomputable section

namespace UpperTheory.GalN

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At UpperTheory.Lit.Car

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

structure RelA {w : PlE H} (x y : A.LP w) : Prop where
  dim : A.lpDim x = A.lpDim y
  mono : A.mono0 y → A.mono0 x
  ine : A.mono0 y ∧ IneAb N A y → ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol x σ = A.inePol y σ

structure CuspA {w : PlE H} (x y : A.LP w) : Prop where
  rel : RelA N A x y
  one : A.lpDim y = 1 → x = y

variable {N A}

theorem RelA.refl {w : PlE H} (x : A.LP w) : RelA N A x x := ⟨rfl, id, fun _ _ _ => rfl⟩

private theorem commutator_le_self' {G : Type*} [Group G] (K : Subgroup G) : ⁅K, K⁆ ≤ K :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

theorem RelA.unr {w : PlE H} {x y : A.LP w} (h : RelA N A x y) (hy : A.unr y) : A.unr x := by
  obtain ⟨hm, hi⟩ := (A.unr_iff_ine y).mp hy
  refine (A.unr_iff_ine x).mpr ⟨h.mono hm, fun σ hσ => ?_⟩
  rw [h.ine ⟨hm, fun τ hτ => hi τ (commutator_le_self' _ hτ)⟩ σ hσ, hi σ hσ, h.dim]

private theorem eq_X_sub_one_pow_of_monic_mul_eq {p q : ℂ[X]} {n m : ℕ} (hp : p.Monic) (hpn : p.natDegree = n)
    (h : p * q = (X - 1) ^ (n + m)) : p = (X - 1) ^ n := by
  have hd : p ∣ (X - C 1) ^ (n + m) := ⟨q, by simpa using h.symm⟩
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C (1 : ℂ)) _).mp hd
  have he : p = (X - C 1) ^ i :=
    Polynomial.eq_of_monic_of_associated hp ((Polynomial.monic_X_sub_C 1).pow i) hi
  have hin : i = n := by
    rw [← hpn, he, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  subst hin
  simpa using he

theorem RelA.sum (hLP : TieLP N A) {w : PlE H} {x y x' y' : A.LP w} (h : RelA N A x y) (h' : RelA N A x' y') :
    RelA N A (A.lpSum x x') (A.lpSum y y') := by
  have hu1 : A.lpDim (A.lpUnr w {1}) = 1 := by
    rw [(A.lpUnr_spec w {1} (by simp)).2.2]
    simp
  have hmon : ∀ (a : A.LP w) σ, σ ∈ Ine (F := H.E) (N.plOm.1 w) →
      (A.inePol a σ).Monic ∧ (A.inePol a σ).natDegree = A.lpDim a := fun a σ hσ =>
    ((hLP w a a (A.lpUnr w {1}) (A.lpUnr w {1}) 0 hu1 hu1).2.2.2.2.2 σ hσ).1
  refine ⟨by rw [A.lpDim_sum, A.lpDim_sum, h.dim, h'.dim], fun hm => ?_, fun ⟨hm, hab⟩ σ hσ => ?_⟩
  · rw [A.monomial_sum_iff] at hm ⊢
    exact ⟨h.mono hm.1, h'.mono hm.2⟩
  · rw [A.monomial_sum_iff] at hm
    have key : ∀ τ ∈ ⁅Ine (F := H.E) (N.plOm.1 w), Ine (F := H.E) (N.plOm.1 w)⁆,
        A.inePol y τ = (X - 1) ^ A.lpDim y ∧ A.inePol y' τ = (X - 1) ^ A.lpDim y' := by
      intro τ hτ
      have hτI : τ ∈ Ine (F := H.E) (N.plOm.1 w) := commutator_le_self' _ hτ
      have e := hab τ hτ
      rw [A.inePol_sum, A.lpDim_sum] at e
      refine ⟨eq_X_sub_one_pow_of_monic_mul_eq (hmon y τ hτI).1 (hmon y τ hτI).2 e, ?_⟩
      rw [mul_comm, add_comm] at e
      exact eq_X_sub_one_pow_of_monic_mul_eq (hmon y' τ hτI).1 (hmon y' τ hτI).2 e
    rw [A.inePol_sum, A.inePol_sum, h.ine ⟨hm.1, fun τ hτ => (key τ hτ).1⟩ σ hσ,
      h'.ine ⟨hm.2, fun τ hτ => (key τ hτ).2⟩ σ hσ]

theorem RelA.char (hLP : TieLP N A) {w : PlE H} {x y : A.LP w} (h : RelA N A x y) (c : A.LP w) (hc : A.lpDim c = 1)
    (hu : A.unr c) : RelA N A (A.lpChar x c) (A.lpChar y c) := by
  have hpc : ∀ τ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol c τ = X - C 1 := by
    intro τ hτ
    rw [((A.unr_iff_ine c).mp hu).2 τ hτ, hc]
    simp
  have hch : ∀ (a : A.LP w) τ, τ ∈ Ine (F := H.E) (N.plOm.1 w) →
      A.inePol (A.lpChar a c) τ = A.inePol a τ := by
    intro a τ hτ
    rw [((hLP w a a c c 0 hc hc).2.2.2.2.2 τ hτ).2 1 (hpc τ hτ), Polynomial.scaleRoots_one]
  refine ⟨by rw [A.lpDim_char _ _ hc, A.lpDim_char _ _ hc, h.dim], fun hm => ?_,
    fun ⟨hm, hab⟩ σ hσ => ?_⟩
  · rw [A.monomial_char_iff _ _ hc] at hm ⊢
    exact h.mono hm
  · rw [A.monomial_char_iff _ _ hc] at hm
    have hab' : IneAb N A y := by
      intro τ hτ
      have hτI : τ ∈ Ine (F := H.E) (N.plOm.1 w) := commutator_le_self' _ hτ
      have e := hab τ hτ
      rw [hch y τ hτI, A.lpDim_char _ _ hc] at e
      exact e
    rw [hch x σ hσ, hch y σ hσ, h.ine ⟨hm, hab'⟩ σ hσ]

theorem CuspA.of_eq {w : PlE H} {x y : A.LP w} (e : x = y) : CuspA N A x y := by
  subst e
  exact ⟨RelA.refl x, fun _ => rfl⟩

theorem exists_inv_unr {w : PlE H} (k : A.LP w) (hk : A.lpDim k = 1) (hu : A.unr k) :
    ∃ k' : A.LP w, A.lpDim k' = 1 ∧ A.unr k' ∧ A.lpChar k k' = A.lpUnr w {1} ∧ A.lpChar k' k = A.lpUnr w {1} := by
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.mp ((A.frobEig_card k hu).trans hk)
  have hc0 : c ≠ 0 := fun h => A.frobEig_ne_zero k hu (by rw [hc, h]; exact Multiset.mem_singleton_self 0)
  obtain ⟨hu', hf', hd'⟩ := A.lpUnr_spec w {c⁻¹} (by simp [hc0, eq_comm])
  have hd1 : A.lpDim (A.lpUnr w {c⁻¹}) = 1 := by rw [hd']; simp
  refine ⟨A.lpUnr w {c⁻¹}, hd1, hu', ?_, ?_⟩
  · rw [A.unr_eq_lpUnr _ (A.unr_char _ _ hd1 hu hu'), A.frobEig_char _ _ c⁻¹ hu hu' hd1 hf', hc]
    simp [hc0]
  · rw [A.unr_eq_lpUnr _ (A.unr_char _ _ hk hu' hu), A.frobEig_char _ _ c hu' hu hk hc, hf']
    simp [hc0]

variable (N A)

variable {N A}

end UpperTheory.GalN
