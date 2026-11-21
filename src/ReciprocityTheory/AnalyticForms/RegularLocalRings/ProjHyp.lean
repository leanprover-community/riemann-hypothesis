import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjDehom
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LogResStC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypA
import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc

section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

section Loc

variable {σ : Type}

def kerPt (z : σ → ℂ) : Ideal (MvPolynomial σ ℂ) :=
  RingHom.ker (MvPolynomial.eval z : MvPolynomial σ ℂ →+* ℂ)

instance kerPt_isPrime (z : σ → ℂ) : (kerPt z).IsPrime :=
  RingHom.ker_isPrime _

def kerPtQ (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) : Ideal (MvPolynomial σ ℂ ⧸ I) :=
  (kerPt z).map (Ideal.Quotient.mk I)

theorem mk_mem_kerPtQ {I : Ideal (MvPolynomial σ ℂ)} {z : σ → ℂ} (hI : I ≤ kerPt z)
    (f : MvPolynomial σ ℂ) : Ideal.Quotient.mk I f ∈ kerPtQ I z ↔ f ∈ kerPt z :=
  Ideal.mem_quotient_iff_mem hI

theorem kerPtQ_isPrime {I : Ideal (MvPolynomial σ ℂ)} {z : σ → ℂ} (hI : I ≤ kerPt z) :
    (kerPtQ I z).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hI)

abbrev locQ (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) : Type :=
  Localization.AtPrime (kerPt z) ⧸
    Ideal.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (kerPt z))) I

theorem algebraMap_locQ_mk (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) (f : MvPolynomial σ ℂ) :
    algebraMap (MvPolynomial σ ℂ ⧸ I) (locQ I z) (Ideal.Quotient.mk I f) =
      algebraMap _ (locQ I z) f := by
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.mk_algebraMap]

theorem isLocalization_locQ {I : Ideal (MvPolynomial σ ℂ)} {z : σ → ℂ} (hI : I ≤ kerPt z) :
    letI := kerPtQ_isPrime hI; IsLocalization.AtPrime (locQ I z) (kerPtQ I z) := by
  let _ := kerPtQ_isPrime hI
  set P := kerPt z
  have hmem : ∀ f, Ideal.Quotient.mk I f ∈ (kerPtQ I z).primeCompl ↔ f ∈ P.primeCompl :=
    fun f => not_congr (mk_mem_kerPtQ hI f)
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [algebraMap_locQ_mk, ← Ideal.Quotient.mk_algebraMap]
    exact (IsLocalization.map_units (Localization.AtPrime P) (⟨f, (hmem f).1 hy⟩ : P.primeCompl)).map _
  · intro w
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj P.primeCompl s
    refine ⟨(Ideal.Quotient.mk I a, ⟨Ideal.Quotient.mk I b, (hmem b).2 b.2⟩), ?_⟩
    simp only [algebraMap_locQ_mk, ← Ideal.Quotient.mk_algebraMap, ← map_mul]
    exact congrArg _ hab
  · intro u v huv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [algebraMap_locQ_mk, algebraMap_locQ_mk, ← Ideal.Quotient.mk_algebraMap,
      ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, ← map_sub] at huv
    obtain ⟨⟨k, s⟩, hks⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (M := P.primeCompl) (S := Localization.AtPrime P)).1 huv
    rw [← map_mul, IsLocalization.eq_iff_exists P.primeCompl] at hks
    obtain ⟨c, hc⟩ := hks
    refine ⟨⟨Ideal.Quotient.mk I s, (hmem s).2 s.2⟩, ?_⟩
    have hc0 : (c : MvPolynomial σ ℂ) ≠ 0 := fun h => c.2 (h ▸ P.zero_mem)
    have hk : (a - b) * s = k := mul_left_cancel₀ hc0 hc
    show Ideal.Quotient.mk I s * Ideal.Quotient.mk I a = Ideal.Quotient.mk I s * Ideal.Quotient.mk I b
    rw [← sub_eq_zero, ← mul_sub, ← map_sub, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, mul_comm, hk]
    exact k.2

end Loc

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_closedPoint_stalk' {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (x : projX P hP) (hx : x ∈ (chartOpen hP p).1)
    (hc : IsClosed ({x} : Set (projX P hP))) :
    ∃ y : (Σ k, ι k) → ℂ, (∀ h ∈ chartIdeal P p, eval y h = 0) ∧
      (∀ q, val (toSpecC hP) (chartCoord hP p q) x hx = y q) ∧
      Nonempty ((projX P hP).presheaf.stalk x ≃+* locQ (chartIdeal P p) y) := by
  have hU : IsAffineOpen (chartOpen hP p).1 := (chartOpen hP p).2
  obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) (chartOpen hP p).1 x hx hc
  let e := gammaChart hP p
  let y : (Σ k, ι k) → ℂ := fun q => val (toSpecC hP) (chartCoord hP p q) x hx
  have hψ : φ.comp (e.symm.toRingHom.comp (Ideal.Quotient.mk (chartIdeal P p))) = eval y := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, eval_C]
      rw [gammaChart_symm_C, hφ, val_const (toSpecC hP) _ x hx hc]
    · intro q
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, eval_X]
      rw [hφ]
      rfl
  have hev : ∀ f, φ (e.symm (Ideal.Quotient.mk _ f)) = eval y f := fun f => RingHom.congr_fun hψ f
  have hzero : ∀ h ∈ chartIdeal P p, eval y h = 0 := by
    intro h hh
    rw [← hev, Ideal.Quotient.eq_zero_iff_mem.2 hh, map_zero, map_zero]
  have hI : chartIdeal P p ≤ kerPt y := fun h hh => (RingHom.mem_ker).2 (hzero h hh)
  refine ⟨y, hzero, fun q => rfl, ?_⟩
  let _ := TopCat.Presheaf.algebra_section_stalk (projX P hP).presheaf (⟨x, hx⟩ : (chartOpen hP p).1)
  have := hU.isLocalization_stalk ⟨x, hx⟩
  set Q := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let _ := kerPtQ_isPrime hI
  have hloc := isLocalization_locQ hI
  have hQ : ∀ a, a ∈ Q ↔ φ a = 0 := by
    intro a
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff ((projX P hP).presheaf.stalk x) Q, hφ,
      val_eq_zero_iff (toSpecC hP) a x hx hc, ← Scheme.germ_residue, CommRingCat.comp_apply]
    exact (IsLocalRing.residue_eq_zero_iff _).symm
  have key : ∀ f, e.symm (Ideal.Quotient.mk _ f) ∈ Q ↔
      Ideal.Quotient.mk (chartIdeal P p) f ∈ kerPtQ (chartIdeal P p) y := by
    intro f
    rw [hQ, hev, mk_mem_kerPtQ hI]
    rfl
  have H : Q.primeCompl.map e.toMonoidHom = (kerPtQ (chartIdeal P p) y).primeCompl := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      show e a ∉ kerPtQ _ y
      obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (e a)
      have ha' : a = e.symm (Ideal.Quotient.mk _ f) := by rw [hf, e.symm_apply_apply]
      rw [← hf, ← key f, ← ha']
      exact ha
    · intro hb
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨e.symm (Ideal.Quotient.mk _ f), ?_, e.apply_symm_apply _⟩
      show _ ∉ Q
      rw [key]
      exact hb
  exact ⟨IsLocalization.ringEquivOfRingEquiv ((projX P hP).presheaf.stalk x)
    (locQ (chartIdeal P p) y) e H⟩

end

end ReciprocityTheory.AnForm.R
end

section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_relevant_minimalPrime_of_chart {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : IsMultiHomogIdeal P) (hD : IsMultiHomogIdeal D) (p : (k : K) → ι k)
    (M : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hM : M ∈ (chartIdeal P p).minimalPrimes)
    (hDM : D ≤ M) :
    ∃ q ∈ P.minimalPrimes, IsRelevant q ∧ D ≤ q := by
  classical
  set R := MvPolynomial (Σ k, ι k) ℂ
  have hMp : M.IsPrime := hM.1.1
  have hcM : chartIdeal P p ≤ M := hM.1.2
  have hX1 : ∀ k, (X ⟨k, p k⟩ - 1 : R) ∈ M := fun k =>
    hcM (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
  have hXM : ∀ k, (X ⟨k, p k⟩ : R) ∉ M := fun k h =>
    hMp.ne_top ((Ideal.eq_top_iff_one _).mpr (by
      have := M.sub_mem h (hX1 k); simpa using this))
  obtain ⟨q, hq, hqM⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hcM : P ≤ M)
  have hqp : q.IsPrime := hq.1.1
  have hPq : P ≤ q := hq.1.2
  set s : R := ∏ k, X ⟨k, p k⟩
  have hsq : s ∉ q := by
    intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (p := q)).mp h
    exact hXM k (hqM hk)
  have hdis : Disjoint (Submonoid.powers s : Set R) ↑q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime s).mpr hsq
  let A := Localization.Away s
  have hu : ∀ k, IsUnit (algebraMap R A (X ⟨k, p k⟩)) := fun k =>
    isUnit_of_dvd_unit (map_dvd (algebraMap R A)
      (Finset.dvd_prod_of_mem (fun k => (X ⟨k, p k⟩ : R)) (Finset.mem_univ k)))
      (IsLocalization.Away.algebraMap_isUnit (S := A) s)
  let u : K → A := fun k => ((hu k).unit⁻¹ : Aˣ)
  have hu1 : ∀ k, u k * algebraMap R A (X ⟨k, p k⟩) = 1 := fun k => (hu k).val_inv_mul
  let σ : R →+* A := eval₂Hom (algebraMap ℂ A) (fun r => u r.1 * algebraMap R A (X r))
  have hσ : ∀ (f : R) (a : K → ℕ), IsMultiHomog f a →
      σ f = (∏ k, u k ^ a k) * algebraMap R A f := by
    intro f a hf
    show eval₂ (algebraMap ℂ A) (fun r => u r.1 * algebraMap R A (X r)) f = _
    rw [eval₂_smul_of_isMultiHomog' (algebraMap ℂ A) hf u (fun r => algebraMap R A (X r))]
    congr 1
    conv_rhs => rw [← eval₂_eta f, eval₂_comp_left]
    congr 1
  let Q : Ideal A := Ideal.map (algebraMap R A) q
  have hQp : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) A q hqp hdis
  have hQq : Q.comap (algebraMap R A) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers s) A hqp hdis
  let M' : Ideal R := Q.comap σ
  have : M'.IsPrime := Ideal.comap_isPrime σ Q

  have hs1 : IsUnit (Ideal.Quotient.mk M s) := by
    have : ∀ k, Ideal.Quotient.mk M (X ⟨k, p k⟩) = 1 := fun k => by
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk M), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]; exact hX1 k
    simp [s, map_prod, this]
  let φ : A →+* R ⧸ M := IsLocalization.Away.lift s hs1
  have hφa : ∀ x : R, φ (algebraMap R A x) = Ideal.Quotient.mk M x := fun x =>
    IsLocalization.Away.lift_eq s hs1 x
  have hφu : ∀ k, φ (u k) = 1 := fun k => by
    have h := congrArg φ (hu1 k)
    rw [map_mul, map_one, hφa] at h
    have hx : Ideal.Quotient.mk M (X ⟨k, p k⟩) = 1 := by
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk M), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]; exact hX1 k
    rw [hx, mul_one] at h; exact h
  have hφσ : φ.comp σ = Ideal.Quotient.mk M := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [σ, IsScalarTower.algebraMap_apply ℂ R A, hφa]; rfl
    · intro r
      simp [σ, hφa, hφu]
  have hM'M : M' ≤ M := by
    intro g hg
    have hQ : Q ≤ (⊥ : Ideal (R ⧸ M)).comap φ := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      simp only [Ideal.mem_comap, hφa, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
      exact hqM hx
    have h0 := hQ hg
    simp only [Ideal.mem_comap, Ideal.mem_bot] at h0
    have : Ideal.Quotient.mk M g = 0 := by rw [← hφσ]; exact h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

  have hcM' : chartIdeal P p ≤ M' := by
    refine sup_le ?_ ?_
    · obtain ⟨S, hS, hPS⟩ := hP
      rw [hPS, Ideal.span_le]
      intro f hfS
      obtain ⟨a, ha⟩ := hS f hfS
      show σ f ∈ Q
      rw [hσ f a ha]
      exact Q.mul_mem_left _ (Ideal.mem_map_of_mem _ (hPq (hPS ▸ Ideal.subset_span hfS)))
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      show σ _ ∈ Q
      have : σ (X ⟨k, p k⟩ - 1) = 0 := by
        have hσX : σ (X ⟨k, p k⟩) = u k * algebraMap R A (X ⟨k, p k⟩) := eval₂_X _ _ _
        rw [map_sub, map_one, hσX, hu1, sub_self]
      rw [this]; exact Q.zero_mem
  have hMM' : M ≤ M' := hM.2 ⟨inferInstance, hcM'⟩ hM'M
  refine ⟨q, hq, fun k => ⟨p k, fun h => hXM k (hqM h)⟩, ?_⟩
  obtain ⟨T, hT, hDT⟩ := hD
  rw [hDT, Ideal.span_le]
  intro f hfT
  obtain ⟨a, ha⟩ := hT f hfT
  have hfM' : σ f ∈ Q := hMM' (hDM (hDT ▸ Ideal.subset_span hfT))
  rw [hσ f a ha] at hfM'
  have hunit : IsUnit (∏ k, u k ^ a k) :=
    IsUnit.prod_univ_iff.mpr fun k => ((hu k).unit⁻¹).isUnit.pow _
  have : algebraMap R A f ∈ Q := by
    have := Q.mul_mem_left (hunit.unit⁻¹ : Aˣ).1 hfM'
    rwa [← mul_assoc, hunit.val_inv_mul, one_mul] at this
  rw [← hQq]; exact this

end

end ReciprocityTheory.AnForm.R
end

section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

open Classical in
theorem prod_X_chartUpd (p : (k : K) → ι k) (q : Σ k, ι k) :
    (∏ k, (X ⟨k, chartUpd p q k⟩ : MvPolynomial (Σ k, ι k) ℂ)) =
      (∏ k ∈ Finset.univ.erase q.1, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ)) * X q := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ q.1)]
  congr 1
  · refine Finset.prod_congr rfl fun k hk => ?_
    rw [chartUpd, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  · rw [chartUpd, Function.update_self]

open Classical in
theorem segre_rename_chartUpd (p : (k : K) → ι k) {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    segreMap (rename (chartUpd p) f) =
      (∏ k, (∏ j ∈ Finset.univ.erase k, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ a k) * f := by
  classical
  let c : K → MvPolynomial (Σ k, ι k) ℂ := fun k => ∏ j ∈ Finset.univ.erase k, X ⟨j, p j⟩
  let φ := (segreMap : MvPolynomial ((k : K) → ι k) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ).comp
    (rename (chartUpd p))
  have hX : ∀ q, φ (X q) = c q.1 * X q := by
    intro q
    simp only [φ, AlgHom.comp_apply, rename_X, segreMap, aeval_X]
    exact prod_X_chartUpd p q
  have hC : ∀ r : ℂ, φ (C r) = C r := fun r => by
    simp [φ, segreMap]
  have key : ∀ m ∈ f.support, φ (monomial m (coeff m f)) = (∏ k, c k ^ a k) * monomial m (coeff m f) := by
    intro m hm

    have hpow : (m.prod fun q e => c q.1 ^ e) = ∏ k, c k ^ a k := by
      rw [Finsupp.prod, Finset.prod_subset (Finset.subset_univ m.support)
        (fun q _ hq => by rw [(by simpa using hq : m q = 0), pow_zero])]
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ a k
      rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
    rw [monomial_eq, map_mul, map_finsuppProd]
    simp only [map_pow, hX, hC, mul_pow]
    rw [Finsupp.prod_mul, hpow]
    ring
  show φ f = _
  calc φ f = φ (∑ m ∈ f.support, monomial m (coeff m f)) := by rw [← f.as_sum]
    _ = ∑ m ∈ f.support, φ (monomial m (coeff m f)) := map_sum _ _ _
    _ = ∑ m ∈ f.support, (∏ k, c k ^ a k) * monomial m (coeff m f) := Finset.sum_congr rfl key
    _ = (∏ k, c k ^ a k) * f := by rw [← Finset.mul_sum, ← f.as_sum]

open Classical in
theorem mk_prod_chartUpd {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p p' : (k : K) → ι k) :
    Ideal.Quotient.mk (segreIdeal P) (∏ k, X (chartUpd p ⟨k, p' k⟩)) =
      Ideal.Quotient.mk (segreIdeal P) (X p' * X p ^ (Fintype.card K - 1)) := by
  classical
  let x : K → MvPolynomial (Σ k, ι k) ℂ := fun j => X ⟨j, p j⟩
  let c : K → MvPolynomial (Σ k, ι k) ℂ := fun k => ∏ j ∈ Finset.univ.erase k, x j
  have hseg : ∀ v : (k : K) → ι k, segreMap (X v : MvPolynomial ((k : K) → ι k) ℂ) =
      ∏ k, (X ⟨k, v k⟩ : MvPolynomial (Σ k, ι k) ℂ) := fun v => by
    simp [segreMap]
  have hne : (∏ j, x j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => X_ne_zero _
  have hn : Fintype.card K - 1 + 1 = Fintype.card K := Nat.sub_add_cancel Fintype.card_pos

  have hcprod : (∏ k, c k) = (∏ j, x j) ^ (Fintype.card K - 1) := by
    apply mul_right_cancel₀ hne
    rw [← pow_succ, hn, ← Finset.prod_mul_distrib]
    rw [Finset.prod_congr rfl fun k _ => Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
    rw [Finset.prod_const, Finset.card_univ]
  rw [Ideal.Quotient.eq, segreIdeal, Ideal.mem_comap, map_sub]
  have h1 : segreMap (∏ k, X (chartUpd p ⟨k, p' k⟩) : MvPolynomial ((k : K) → ι k) ℂ) =
      (∏ k, c k) * ∏ k, (X ⟨k, p' k⟩ : MvPolynomial (Σ k, ι k) ℂ) := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hseg]
    exact prod_X_chartUpd p ⟨k, p' k⟩
  have h2 : segreMap (X p' * X p ^ (Fintype.card K - 1) : MvPolynomial ((k : K) → ι k) ℂ) =
      (∏ k, (X ⟨k, p' k⟩ : MvPolynomial (Σ k, ι k) ℂ)) * (∏ j, x j) ^ (Fintype.card K - 1) := by
    rw [map_mul, map_pow, hseg, hseg]
  rw [h1, h2, hcprod, mul_comm, sub_self]
  exact P.zero_mem

section Dehom

variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)

theorem val_polyToAway_X (q : Σ k, ι k) :
    letI := segreGraded hP
    (polyToAway hP p (X q)).val = IsLocalization.mk' (Localization.Away (segreW P p))
      (segreW P (chartUpd p q)) (⟨segreW P p, Submonoid.mem_powers _⟩ : Submonoid.powers (segreW P p)) := by
  simp only [polyToAway, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
  unfold awayCoord
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  congr 1
  exact Subtype.ext (pow_one _)

theorem val_polyToAway_C (c : ℂ) :
    letI := segreGraded hP
    (polyToAway hP p (C c)).val =
      algebraMap _ (Localization.Away (segreW P p)) (Ideal.Quotient.mk (segreIdeal P) (C c)) := by
  simp only [polyToAway, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.comp_apply]
  rw [← Localization.mk_one_eq_algebraMap]
  first
  | rfl
  | (rw [← HomogeneousLocalization.algebraMap_apply]; rfl)
  | simp [HomogeneousLocalization.val_fromZeroRingHom, Localization.mk_one_eq_algebraMap,
      SetLike.GradeZero.coe_algebraMap, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]

theorem val_polyToAway_mul_pow {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    letI := segreGraded hP
    (polyToAway hP p f).val * algebraMap _ (Localization.Away (segreW P p)) (segreW P p) ^ (∑ k, a k) =
      algebraMap _ (Localization.Away (segreW P p))
        (Ideal.Quotient.mk (segreIdeal P) (rename (chartUpd p) f)) := by
  letI := segreGraded hP
  let W := algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (Localization.Away (segreW P p))
    (segreW P p)
  let ψ : MvPolynomial (Σ k, ι k) ℂ →+* Localization.Away (segreW P p) :=
    (algebraMap (HomogeneousLocalization.Away (segreGrading P) (segreW P p))
      (Localization.Away (segreW P p))).comp (polyToAway hP p)
  let τ : MvPolynomial (Σ k, ι k) ℂ →+* Localization.Away (segreW P p) :=
    (algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (Localization.Away (segreW P p))).comp
      ((Ideal.Quotient.mk (segreIdeal P)).comp (rename (chartUpd p)).toRingHom)
  have hψ : ∀ g, ψ g = (polyToAway hP p g).val := fun g => HomogeneousLocalization.algebraMap_apply _
  have hX : ∀ q, ψ (X q) * W = τ (X q) := by
    intro q
    have hs := IsLocalization.mk'_spec (Localization.Away (segreW P p)) (segreW P (chartUpd p q))
      (⟨segreW P p, Submonoid.mem_powers _⟩ : Submonoid.powers (segreW P p))
    rw [hψ, val_polyToAway_X hP p q]
    refine hs.trans ?_
    simp [τ]
  have hC : ∀ r, ψ (C r) = τ (C r) := fun r => by
    rw [hψ, val_polyToAway_C hP p r]
    simp [τ]
  have key : ∀ m ∈ f.support, ψ (monomial m (coeff m f)) * W ^ (∑ k, a k) =
      τ (monomial m (coeff m f)) := by
    intro m hm

    have hW : W ^ (∑ k, a k) = m.prod (fun _ e => W ^ e) := by
      rw [Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum, Fintype.sum_sigma]
      congr 1
      exact Finset.sum_congr rfl fun k _ => (hf m hm k).symm
    rw [hW, monomial_eq, map_mul, map_mul, map_finsuppProd, map_finsuppProd, mul_assoc,
      ← Finsupp.prod_mul]
    simp only [map_pow, ← mul_pow, hX, hC]
  show ψ f * W ^ (∑ k, a k) = τ f
  calc ψ f * W ^ (∑ k, a k) = (∑ m ∈ f.support, ψ (monomial m (coeff m f))) * W ^ (∑ k, a k) := by
        rw [← map_sum, ← f.as_sum]
    _ = ∑ m ∈ f.support, ψ (monomial m (coeff m f)) * W ^ (∑ k, a k) := Finset.sum_mul _ _ _
    _ = ∑ m ∈ f.support, τ (monomial m (coeff m f)) := Finset.sum_congr rfl key
    _ = τ f := by rw [← map_sum, ← f.as_sum]

theorem val_polyToAway_segre_mul_pow {g : MvPolynomial ((k : K) → ι k) ℂ} {d : ℕ}
    (hg : g.IsHomogeneous d) :
    letI := segreGraded hP
    (polyToAway hP p (segreMap g)).val * algebraMap _ (Localization.Away (segreW P p)) (segreW P p) ^ d =
      algebraMap _ (Localization.Away (segreW P p)) (Ideal.Quotient.mk (segreIdeal P) g) := by
  classical
  letI := segreGraded hP
  let W := algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (Localization.Away (segreW P p))
    (segreW P p)
  let ψ : MvPolynomial (Σ k, ι k) ℂ →+* Localization.Away (segreW P p) :=
    (algebraMap (HomogeneousLocalization.Away (segreGrading P) (segreW P p))
      (Localization.Away (segreW P p))).comp (polyToAway hP p)
  let σ' : MvPolynomial ((k : K) → ι k) ℂ →+* Localization.Away (segreW P p) :=
    (algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (Localization.Away (segreW P p))).comp
      (Ideal.Quotient.mk (segreIdeal P))
  let ψ' : MvPolynomial ((k : K) → ι k) ℂ →+* Localization.Away (segreW P p) :=
    ψ.comp (segreMap : MvPolynomial ((k : K) → ι k) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ).toRingHom
  have hψ : ∀ g, ψ g = (polyToAway hP p g).val := fun g => HomogeneousLocalization.algebraMap_apply _
  have hU : IsUnit W := IsLocalization.Away.algebraMap_isUnit _
  have hn : Fintype.card K - 1 + 1 = Fintype.card K := Nat.sub_add_cancel Fintype.card_pos

  have hXq : ∀ q : Σ k, ι k, ψ (X q) * W = σ' (X (chartUpd p q)) := by
    intro q
    have hs := IsLocalization.mk'_spec (Localization.Away (segreW P p)) (segreW P (chartUpd p q))
      (⟨segreW P p, Submonoid.mem_powers _⟩ : Submonoid.powers (segreW P p))
    rw [hψ, val_polyToAway_X hP p q]
    exact hs
  have hA : ∀ v : (k : K) → ι k, ψ' (X v) * W = σ' (X v) := by
    intro v
    apply (hU.pow (Fintype.card K - 1)).mul_right_cancel
    have e1 : ψ' (X v) * W * W ^ (Fintype.card K - 1) = ∏ k, (ψ (X ⟨k, v k⟩) * W) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_assoc, ← pow_succ', hn]
      simp [ψ', segreMap, map_prod]
    rw [e1, Finset.prod_congr rfl fun k _ => hXq ⟨k, v k⟩, ← map_prod]
    simp only [σ', RingHom.comp_apply]
    rw [mk_prod_chartUpd p v, map_mul, map_mul, map_pow, map_pow]
  have hC : ∀ r, ψ' (C r) = σ' (C r) := fun r => by
    have e : segreMap (C r : MvPolynomial ((k : K) → ι k) ℂ) = C r := by simp [segreMap]
    show ψ (segreMap (C r)) = σ' (C r)
    rw [e, hψ, val_polyToAway_C hP p r]
    rfl
  have key : ∀ m ∈ g.support, ψ' (monomial m (coeff m g)) * W ^ d = σ' (monomial m (coeff m g)) := by
    intro m hm
    have hdeg : ∑ v ∈ m.support, m v = d := by
      have h1 := hg (mem_support_iff.1 hm)
      simpa [Finsupp.weight_apply, Finsupp.sum] using h1
    have hW : W ^ d = m.prod (fun _ e => W ^ e) := by
      rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, hdeg]
    rw [hW, monomial_eq, map_mul, map_mul, map_finsuppProd, map_finsuppProd, mul_assoc,
      ← Finsupp.prod_mul]
    simp only [map_pow, ← mul_pow, hA, hC]
  show ψ' g * W ^ d = σ' g
  calc ψ' g * W ^ d = (∑ m ∈ g.support, ψ' (monomial m (coeff m g))) * W ^ d := by
        rw [← map_sum, ← g.as_sum]
    _ = ∑ m ∈ g.support, ψ' (monomial m (coeff m g)) * W ^ d := Finset.sum_mul _ _ _
    _ = ∑ m ∈ g.support, σ' (monomial m (coeff m g)) := Finset.sum_congr rfl key
    _ = σ' g := by rw [← map_sum, ← g.as_sum]

theorem away_eq_mk_of_val {N : ℕ} (n : MvPolynomial ((k : K) → ι k) ℂ) (hn : n.IsHomogeneous N)
    (a : letI := segreGraded hP; HomogeneousLocalization.Away (segreGrading P) (segreW P p))
    (h : letI := segreGraded hP; a.val * algebraMap _ (Localization.Away (segreW P p)) (segreW P p) ^ N =
      algebraMap _ _ (Ideal.Quotient.mk (segreIdeal P) n)) :
    letI := segreGraded hP
    a = HomogeneousLocalization.mk
      ({ deg := N
         num := ⟨Ideal.Quotient.mk _ n, n, (mem_homogeneousSubmodule N n).mpr hn, rfl⟩
         den := ⟨segreW P p ^ N, by simpa using SetLike.pow_mem_graded N (segreW_mem P p)⟩
         den_mem := ⟨N, rfl⟩ } :
        HomogeneousLocalization.NumDenSameDeg (segreGrading P) (Submonoid.powers (segreW P p))) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mk, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  simpa [map_pow] using h

end Dehom

theorem evaluation_eq_zero_iff_mem_primeIdealOf {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    X.evaluation U x hx s = 0 ↔ s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen]
  have e : x ∈ X.basicOpen s ↔ hU.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen s := by
    rw [← hU.fromSpec_preimage_basicOpen]
    change x ∈ X.basicOpen s ↔ hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen s
    rw [show hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) = x from hU.fromSpec_primeIdealOf ⟨x, hx⟩]
  rw [e, PrimeSpectrum.mem_basicOpen, not_not]

end

end ReciprocityTheory.AnForm.R
end

section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

instance isNoetherian_projX {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    IsNoetherian (projX P hP) :=
  (isNoetherian_iff_of_finite_iSup_eq_top (S := chartOpen hP) (iSup_chartOpen_eq_top hP)).mpr
    (isNoetherianRing_gammaChart hP)

theorem isReduced_projX {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hrad : P.IsRadical) : IsReduced (projX P hP) := by
  haveI : ∀ x : projX P hP, _root_.IsReduced ((projX P hP).presheaf.stalk x) := by
    intro x
    obtain ⟨p, hp⟩ := chartOpen_cover hP x
    have hU := (chartOpen hP p).2
    let x' : ((chartOpen hP p).1 : Set (projX P hP)) := ⟨x, hp⟩
    show _root_.IsReduced ((projX P hP).presheaf.stalk (x' : projX P hP))
    letI := TopCat.Presheaf.algebra_section_stalk (projX P hP).presheaf x'
    haveI := hU.isLocalization_stalk x'
    exact isReduced_localizationPreserves (hU.primeIdealOf x').asIdeal.primeCompl _
      (isReduced_gammaChart hP hrad p)
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

theorem qe_projX {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hQE : FinalTheorems.FinTypeQE) : FinalTheorems.QE (projX P hP) := by
  intro x
  obtain ⟨p, hp⟩ := chartOpen_cover hP x
  exact ⟨chartOpen hP p, hp, qeRing_gammaChart hP hQE p⟩

theorem fFinRes_projX {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    FinalTheorems.FFinRes (projX P hP) := by
  intro x p _ hchar
  obtain ⟨q, hq⟩ := chartOpen_cover hP x
  let f : ℂ →+* (projX P hP).residueField x :=
    ((projX P hP).residue x).hom.comp (((projX P hP).presheaf.germ (chartOpen hP q).1 x hq).hom.comp
      ((gammaChart hP q).symm.toRingHom.comp (algebraMap ℂ (chartRing P q))))
  exfalso
  have h1 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have h2 : f (p : ℂ) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero _ p
  exact h1 (f.injective (by rw [h2, map_zero]))

def projB (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    TopologicalSpace.Closeds (projX P hP) :=
  letI := segreGraded hP
  ⟨ProjectiveSpectrum.zeroLocus (segreGrading P) (Ideal.Quotient.mk (segreIdeal P) '' (segreIdeal D : Set _)),
    ProjectiveSpectrum.isClosed_zeroLocus _ _⟩

theorem mem_projB_iff {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hD : IsMultiHomogIdeal D) (p : (k : K) → ι k) (x : projX P hP) (hx : x ∈ (chartOpen hP p).1) :
    x ∈ projB P D hP ↔
      ∀ f ∈ D, (projX P hP).evaluation _ x hx ((gammaChart hP p).symm (Ideal.Quotient.mk _ f)) = 0 := by
  letI := segreGraded hP
  have hsec : ∀ f, (gammaChart hP p).symm (Ideal.Quotient.mk _ f) =
      Proj.awayToSection (segreGrading P) (segreW P p) (polyToAway hP p f) := fun f => rfl
  show (Ideal.Quotient.mk (segreIdeal P) '' (segreIdeal D : Set _)) ⊆
    (ProjectiveSpectrum.asHomogeneousIdeal (𝒜 := segreGrading P) x : Set _) ↔ _
  constructor
  · intro hx'
    obtain ⟨S, hS, rfl⟩ := hD
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, ha⟩ := hS f hf
      have hrn : rename (chartUpd p) f ∈ segreIdeal (Ideal.span S) := by
        show segreMap (rename (chartUpd p) f) ∈ Ideal.span S
        rw [segre_rename_chartUpd p ha]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span hf)
      have hhom := (isHomogeneous_of_isMultiHomog ha).rename_isHomogeneous (f := chartUpd p)
      rw [hsec, away_eq_mk_of_val hP p _ hhom _ (val_polyToAway_mul_pow hP p ha)]
      exact (evaluation_awayToSection_eq_zero_iff _ _ x hx _).mpr (hx' ⟨_, hrn, rfl⟩)
    | zero => simp
    | add f g _ _ h1 h2 => simp only [map_add, h1, h2, add_zero]
    | smul a f _ h1 => simp only [smul_eq_mul, map_mul, h1, mul_zero]
  · intro h g hg
    obtain ⟨g, hg, rfl⟩ := hg
    rw [← sum_homogeneousComponent g, map_sum]
    show _ ∈ (ProjectiveSpectrum.asHomogeneousIdeal (𝒜 := segreGrading P) x).toIdeal
    refine Ideal.sum_mem _ fun d _ => ?_
    have hgd : homogeneousComponent d g ∈ segreIdeal D :=
      homogeneousComponent_mem_of_mem (segreIdeal_isHomogeneous hD) hg d
    have hv := h _ hgd
    rw [hsec, away_eq_mk_of_val hP p _ (homogeneousComponent_isHomogeneous d g) _
      (val_polyToAway_segre_mul_pow hP p (homogeneousComponent_isHomogeneous d g))] at hv
    exact (evaluation_awayToSection_eq_zero_iff _ _ x hx _).mp hv

def ptIdealOf {σ : Type} (z : σ → ℂ) : Ideal (MvPolynomial σ ℂ) :=
  RingHom.ker (MvPolynomial.eval z : MvPolynomial σ ℂ →+* ℂ)

instance ptIdealOf_isPrime {σ : Type} (z : σ → ℂ) : (ptIdealOf z).IsPrime :=
  RingHom.ker_isPrime _

abbrev locAt {σ : Type} (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) : Type :=
  Localization.AtPrime (ptIdealOf z) ⧸
    Ideal.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z))) I

abbrev chartLocRing (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ) :
    Type :=
  locAt (chartIdeal P p) y

theorem exists_closedPoint_stalk {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (x : projX P hP) (hx : x ∈ (chartOpen hP p).1) (hc : IsClosed ({x} : Set (projX P hP))) :
    ∃ y : (Σ k, ι k) → ℂ, (∀ h ∈ chartIdeal P p, eval y h = 0) ∧
      (∀ q, val (toSpecC hP) (chartCoord hP p q) x hx = y q) ∧
      Nonempty ((projX P hP).presheaf.stalk x ≃+* chartLocRing P p y) := by
  exact exists_closedPoint_stalk' hP p x hx hc

theorem isClosed_sing {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hQE : FinalTheorems.FinTypeQE) : IsClosed (FinalTheorems.Sing (projX P hP)) := by
  have hopen := isOpen_regularLocus_of_cover (fun p => chartOpen hP p) (chartOpen_cover hP)
    (fun p => (qeRing_gammaChart hP hQE p).2.2 _)
  exact hopen.isClosed_compl

theorem sing_subset_projB {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hD : IsMultiHomogIdeal D) (hQE : FinalTheorems.FinTypeQE)
    (hsing : ∀ (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval y h = 0) →
      ¬ IsRegularLocalRing (chartLocRing P p y) → ∀ f ∈ D, eval y f = 0) :
    FinalTheorems.Sing (projX P hP) ⊆ (projB P D hP : Set (projX P hP)) := by
  intro x hx
  by_contra hxB
  have : JacobsonSpace (projX P hP) := LocallyOfFiniteType.jacobsonSpace (toSpecC hP)
  have hZ : IsLocallyClosed (FinalTheorems.Sing (projX P hP) ∩ (projB P D hP : Set (projX P hP))ᶜ) :=
    (isClosed_sing hP hQE).isLocallyClosed.inter (projB P D hP).isClosed.isOpen_compl.isLocallyClosed
  obtain ⟨c, ⟨hcS, hcB⟩, hcc⟩ := nonempty_inter_closedPoints
    (Z := FinalTheorems.Sing (projX P hP) ∩ (projB P D hP : Set (projX P hP))ᶜ) ⟨x, hx, hxB⟩ hZ
  obtain ⟨p, hp⟩ := chartOpen_cover hP c
  obtain ⟨y, hy, hval, ⟨e⟩⟩ := exists_closedPoint_stalk hP p c hp hcc
  have hreg : ¬ IsRegularLocalRing (chartLocRing P p y) := fun h =>
    hcS (IsRegularLocalRing.of_ringEquiv e.symm)
  have hDy := hsing p y hy hreg
  apply hcB
  rw [SetLike.mem_coe, mem_projB_iff hP hD p c hp]
  intro f hf
  rw [← val_eq_zero_iff (toSpecC hP) _ c hp hcc]
  obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) (chartOpen hP p).1 c hp hcc
  rw [← hφ, gammaChart_symm_mk, eval₂_comp_left]
  have h1 : φ.comp (constSec (toSpecC hP) (chartOpen hP p).1) = RingHom.id ℂ := by
    ext a; simp [hφ, val_const (toSpecC hP) _ c hp hcc]
  have h2 : (φ ∘ chartCoord hP p) = y := by
    funext q; simp [hφ, hval]
  rw [h1, h2]
  exact hDy f hf

theorem interior_projB {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hD : IsMultiHomogIdeal D) (hmin : ∀ q ∈ P.minimalPrimes, IsRelevant q → ¬ D ≤ q) :
    interior (projB P D hP : Set (projX P hP)) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨p, hp⟩ := chartOpen_cover hP x
  have hA : IsAffineOpen (chartOpen hP p).1 := (chartOpen hP p).2
  obtain ⟨𝔮, h𝔮min, h𝔮le⟩ :=
    Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ (hA.primeIdealOf ⟨x, hp⟩).asIdeal)
  have h𝔮p : 𝔮.IsPrime := h𝔮min.1.1
  let η : PrimeSpectrum Γ(projX P hP, (chartOpen hP p).1) := ⟨𝔮, h𝔮p⟩
  have hspec : hA.fromSpec η ⤳ x := by
    have h1 : η ⤳ hA.primeIdealOf ⟨x, hp⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp h𝔮le
    have h2 := h1.map (hA.fromSpec).continuous
    rwa [hA.fromSpec_primeIdealOf] at h2
  have hηO : hA.fromSpec η ∈ interior (projB P D hP : Set (projX P hP)) :=
    hspec.mem_open isOpen_interior hx
  have hηU : hA.fromSpec η ∈ (chartOpen hP p).1 := hA.range_fromSpec.le ⟨η, rfl⟩
  have hηB : hA.fromSpec η ∈ (projB P D hP : Set (projX P hP)) := interior_subset hηO
  rw [SetLike.mem_coe, mem_projB_iff hP hD p _ hηU] at hηB
  have hpη : hA.primeIdealOf ⟨hA.fromSpec η, hηU⟩ = η :=
    (hA.fromSpec).isOpenEmbedding.injective (hA.fromSpec_primeIdealOf ⟨hA.fromSpec η, hηU⟩)
  let θ : MvPolynomial (Σ k, ι k) ℂ →+* Γ(projX P hP, (chartOpen hP p).1) :=
    (gammaChart hP p).symm.toRingHom.comp (Ideal.Quotient.mk (chartIdeal P p))
  have hθs : Function.Surjective θ :=
    (gammaChart hP p).symm.surjective.comp Ideal.Quotient.mk_surjective
  have hθk : RingHom.ker θ = chartIdeal P p := by
    ext f
    simp [θ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have hDM : D ≤ 𝔮.comap θ := fun f hf => by
    have h1 := hηB f hf
    rw [evaluation_eq_zero_iff_mem_primeIdealOf hA _ hηU, hpη] at h1
    exact h1
  have hMmin : 𝔮.comap θ ∈ (chartIdeal P p).minimalPrimes := by
    refine ⟨⟨Ideal.comap_isPrime θ 𝔮, fun f hf => ?_⟩, fun J hJ hJM => ?_⟩
    · have : θ f = 0 := by rw [← RingHom.mem_ker, hθk]; exact hf
      show θ f ∈ 𝔮
      rw [this]; exact 𝔮.zero_mem
    · haveI := hJ.1
      have hk : RingHom.ker θ ≤ J := hθk ▸ hJ.2
      have hJ' : (J.map θ).IsPrime := Ideal.map_isPrime_of_surjective hθs hk
      have hle : J.map θ ≤ 𝔮 := Ideal.map_le_iff_le_comap.mpr hJM
      have h3 : 𝔮 ≤ J.map θ := h𝔮min.2 ⟨hJ', bot_le⟩ hle
      calc 𝔮.comap θ ≤ (J.map θ).comap θ := Ideal.comap_mono h3
        _ = J := by rw [Ideal.comap_map_of_surjective θ hθs, sup_eq_left]; exact le_trans (by
            rw [← RingHom.ker_eq_comap_bot]) hk
  obtain ⟨q, hq, hrel, hDq⟩ := exists_relevant_minimalPrime_of_chart hP hD p _ hMmin hDM
  exact hmin q hq hrel hDq

end

end ReciprocityTheory.AnForm.R
end
