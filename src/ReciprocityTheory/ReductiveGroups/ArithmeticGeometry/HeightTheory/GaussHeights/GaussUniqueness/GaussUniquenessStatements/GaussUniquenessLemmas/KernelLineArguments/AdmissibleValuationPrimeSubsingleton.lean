import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessLemmas.KernelLineArguments.ImgRSuccAbove

section
namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

theorem sImg_rel {Ω : Type} [Field Ω] {D N : ℕ} (jc : Fin (N + 1)) (b : Fin (N + 1) → Ω)
    (hb : b jc = 1) (i : Fin (D + 1)) (hi : i ≠ 0) :
    ∑ j, sImg (D := D) jc (fun k => b (jc.succAbove k)) (i, j) *
      algebraMap Ω (OmS Ω D N) (b j) = 0 := by
  rw [Fin.sum_univ_succAbove _ jc]
  simp only [sImg, GaussValuationUniqueness.sac_same, GaussValuationUniqueness.sac_succAbove, if_neg hi, hb, map_one,
    mul_one]
  simp only [IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
    MvPolynomial.algebraMap_eq, ← map_mul, ← map_sum, ← map_add, neg_add_cancel, map_zero]

noncomputable def eS {Ω : Type} [Field Ω] {D N : ℕ} (jc j0 : Fin (N + 1)) (x : Fin N → Ω) :
    SVar D N → OmS Ω D N :=
  Sum.elim (fun _ => sImg jc x (0, j0)) (fun ik => sImg jc x (ik.1, j0.succAbove ik.2))

section Fac

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

theorem sub_apply (y : vRing v) : (vRing v).subtype y = (y : Ω) := rfl

theorem sHom_factor (hv : IsTrivOn K v) (jc j0 : Fin (N + 1)) (x : Fin N → Ω)
    (a : Fin (N + 1) → Ω) (ha : ∀ j, a j ∈ vRing v) (ha0 : a j0 = 1)
    (hrel : ∀ i : Fin (D + 1), i ≠ 0 →
      ∑ j, sImg jc x (i, j) * algebraMap Ω (OmS Ω D N) (a j) = 0) (f : MvPolynomial (TVar D N) K) :
    sHom (K := K) jc x f = MvPolynomial.eval₂ ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype)
      (eS jc j0 x) (psiT v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩) f) := by
  have key : ((sHom (K := K) jc x : MvPolynomial (TVar D N) K →ₐ[K] OmS Ω D N) :
      MvPolynomial (TVar D N) K →+* OmS Ω D N) =
      (MvPolynomial.eval₂Hom ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype)
        (eS jc j0 x)).comp (psiT v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, sHom,
        MvPolynomial.aeval_C, psiT, MvPolynomial.eval₂Hom_C, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_C]
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
        IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
        MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
      rfl
    · rintro ⟨i, j⟩
      rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
      · by_cases hi : i = 0
        · subst hi
          simp [sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_same]
        · have h := hrel i hi
          rw [Fin.sum_univ_succAbove _ j, ha0, map_one, mul_one] at h
          simp [sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_same, hi, GaussValuationUniqueness.sub_apply]
          linear_combination h
      · simp [sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_succAbove]
  exact RingHom.congr_fun key f

end Fac

end GaussValuationUniqueness
end

section
namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

theorem not_inj_of_trdeg {F E : Type} [Field F] [Field E] [Algebra F E] {D N : ℕ} (S : Set E)
    (j0 : Fin (N + 1)) (ρ : Fin N → IntermediateField.adjoin F S) (hD : 1 ≤ D)
    (htr : Algebra.trdeg F (IntermediateField.adjoin F S) = ((D - 1 : ℕ) : Cardinal)) :
    ¬ Function.Injective (MvPolynomial.aeval (R := F) (imgR (D := D) j0 ρ)) := by
  intro hinj
  have hai : AlgebraicIndependent F (imgR (D := D) j0 ρ) := hinj
  have h1 := hai.cardinalMk_le_trdeg
  first
  | rw [← Algebra.trdeg_add_eq F (IntermediateField.adjoin F S)] at h1
  | rw [← trdeg_add_eq F (IntermediateField.adjoin F S)] at h1
  rw [htr, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id] at h1
  have hT : Fintype.card (TVar D N) = (D + 1) * (N + 1) := by simp [TVar]
  have hS : Fintype.card (SVar D N) = 1 + (D + 1) * N := by simp [SVar]
  rw [Cardinal.mk_fintype, Cardinal.mk_fintype, hT, hS] at h1
  norm_cast at h1
  rw [show (D + 1) * (N + 1) = (D + 1) * N + (D + 1) by ring] at h1
  generalize (D + 1) * N = P at h1
  omega

section Tr

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

noncomputable def gK (hv : IsTrivOn K v) :
    K →+* IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)) :=
  (IsLocalRing.residue _).comp ((RingHom.id K).codRestrict ((vRing v).comap (algebraMap K Ω))
    (fun x => by rw [ValuationSubring.mem_comap]; exact alg_mem v hv x))

theorem gK_surj (hv : IsTrivOn K v) : Function.Surjective (gK v hv) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  exact ⟨x.1, rfl⟩

end Tr

end GaussValuationUniqueness
end

section
namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

theorem ker_ne_bot (hv : IsTrivOn K v) (j0 : Fin (N + 1)) (a : Fin (N + 1) → Ω)
    (ha : ∀ j, a j ∈ vRing v) (hD : 1 ≤ D)
    (htr : letI := resAlg (F := K) v
      Algebra.trdeg (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)))
        (IntermediateField.adjoin (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)))
          {r | ∃ j, ∃ h : a j ∈ vRing v, r = IsLocalRing.residue (vRing v) ⟨_, h⟩}) =
        ((D - 1 : ℕ) : Cardinal)) :
    RingHom.ker (psiR (D := D) v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) ≠ ⊥ := by
  letI := resAlg (F := K) v
  intro hbot
  let S : Set (IsLocalRing.ResidueField (vRing v)) :=
    {r | ∃ j, ∃ h : a j ∈ vRing v, r = IsLocalRing.residue (vRing v) ⟨_, h⟩}
  let ρL : Fin N → IntermediateField.adjoin
      (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω))) S :=
    fun k => ⟨IsLocalRing.residue (vRing v) ⟨a (j0.succAbove k), ha _⟩,
      IntermediateField.subset_adjoin _ _ ⟨j0.succAbove k, ha _, rfl⟩⟩
  have hni := not_inj_of_trdeg (D := D) S j0 ρL hD htr
  rw [injective_iff_map_eq_zero] at hni
  push_neg at hni
  obtain ⟨G, hG0, hG⟩ := hni
  obtain ⟨f, rfl⟩ := MvPolynomial.map_surjective (gK v hv) (gK_surj v hv) G
  have hf : f ≠ 0 := by
    rintro rfl
    exact hG (map_zero _)
  have H : psiR (D := D) v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩) =
      (MvPolynomial.map (algebraMap (IntermediateField.adjoin
        (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω))) S)
        (IsLocalRing.ResidueField (vRing v)))).comp
        (((MvPolynomial.aeval (imgR (D := D) j0 ρL)).toRingHom).comp
          (MvPolynomial.map (gK v hv))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [psiR, psiT, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_apply]
      congr 1
    · intro t
      simp only [psiR, psiT, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
      rw [imgR_map, imgR_map]
      rfl
  have hmem : f ∈ RingHom.ker (psiR (D := D) v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) := by
    rw [RingHom.mem_ker, H]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hG0, map_zero]
  rw [hbot] at hmem
  exact hf (Ideal.mem_bot.mp hmem)

end GaussValuationUniqueness
end

section
namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0 NumberField

theorem admissibleValuation_prime_subsingleton {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
    {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT]
    {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
    [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))
    (d : Data K ι Ω WT A) : LeafSt.AdmissibleValuationPrimeUnique 𝒜 d := by
  intro hd _ c v hAdm hK p1 hp1 p2 hp2
  obtain ⟨hH1, w1, hw1, hv1⟩ := hp1
  obtain ⟨hH2, w2, hw2, hv2⟩ := hp2

  have hRC : d.ResCond c v (d.D - 1) := by
    rcases hAdm.2 with ⟨la, hla, _⟩ | ⟨_, hRC⟩
    · exfalso
      obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
      have h1 := (hla z).mpr hz
      have hK0 : ((z : 𝓞 K) : K) ≠ 0 := NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hz0
      rw [hK _ hK0] at h1
      exact lt_irrefl _ h1
    · exact hRC
  obtain ⟨_, j0, hj0, hnn, htr⟩ := hRC
  set a : Fin (d.N + 1) → Ω c := fun j => ratio (Ω := Ω c) (d.w j c) (d.w j0 c) with ha_def
  have ha : ∀ j, a j ∈ vRing v := fun j => (GaussValuationUniqueness.mem_vRing_iff v _).mpr (hnn j)
  have hQne := GaussValuationUniqueness.ker_ne_bot (D := d.D) v hK j0 a ha (by have := hd.D_ge; omega) htr
  set Q := RingHom.ker (GaussValuationUniqueness.psiR (D := d.D) v hK j0 (fun k => ⟨a (j0.succAbove k), ha _⟩))
    with hQ
  haveI : Q.IsPrime := RingHom.ker_isPrime _

  have hbase := hd.w_base c
  have hline := hd.finrank_one c d.wL
  set b : Fin (d.N + 1) → Ω c := fun j => ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) with hb_def
  have hα : ∀ j, d.w j c = b j • d.w (d.jc c) c := by
    intro j
    obtain ⟨α, hα⟩ := GaussValuationUniqueness.exists_smul_of_line hline (hd.w_mem j c) (hd.w_mem _ c) hbase
    rw [hb_def]
    simp only
    rw [GaussValuationUniqueness.ratio_eq_of hbase hα]
    exact hα
  have hb : b (d.jc c) = 1 := GaussValuationUniqueness.ratio_eq_of hbase (one_smul _ _).symm
  have hb0 : b j0 ≠ 0 := by
    intro h0
    apply hj0
    rw [hα j0, h0, zero_smul]
  have hab : ∀ j, a j = b j * (b j0)⁻¹ := by
    intro j
    apply GaussValuationUniqueness.ratio_eq_of hj0
    rw [hα j, hα j0, smul_smul, mul_assoc, inv_mul_cancel₀ hb0, mul_one]
  have ha0 : a j0 = 1 := by rw [hab, mul_inv_cancel₀ hb0]
  have hrel : ∀ i : Fin (d.D + 1), i ≠ 0 →
      ∑ j, sImg (D := d.D) (d.jc c) (d.x c) (i, j) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a j) = 0 := by
    intro i hi
    have rel : ∑ j, sImg (D := d.D) (d.jc c) (d.x c) (i, j) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (b j) = 0 := sImg_rel (d.jc c) b hb i hi
    simp_rw [hab, map_mul, ← mul_assoc]
    rw [← Finset.sum_mul, rel, zero_mul]

  have key : ∀ p, ∀ w ∈ d.GoodP c p, d.Wres c w = v → Q ≤ p := by
    intro p w hw hwv f hf
    have hOv := hw.1
    have hwv' : ∀ t : Ω c, w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) t) = v t := by
      intro t; rw [← hwv]; rfl
    have he : ∀ s, 0 ≤ w (GaussValuationUniqueness.eS (D := d.D) (d.jc c) j0 (d.x c) s) := by
      intro s
      rcases s with u | ik
      · have e1 : GaussValuationUniqueness.eS (D := d.D) (d.jc c) j0 (d.x c) (Sum.inl u) =
            d.sH c (MvPolynomial.X ((0, j0) : TVar d.D d.N)) := by
          simp [GaussValuationUniqueness.eS, Data.sH, sHom]
        rw [e1]; exact (hOv.2 _).1
      · have e1 : GaussValuationUniqueness.eS (D := d.D) (d.jc c) j0 (d.x c) (Sum.inr ik) =
            d.sH c (MvPolynomial.X ((ik.1, j0.succAbove ik.2) : TVar d.D d.N)) := by
          simp [GaussValuationUniqueness.eS, Data.sH, sHom]
        rw [e1]; exact (hOv.2 _).1
    have hq : MvPolynomial.map (IsLocalRing.residue (vRing v))
        (GaussValuationUniqueness.psiT (D := d.D) v hK j0 (fun k => ⟨a (j0.succAbove k), ha _⟩) f) = 0 :=
      RingHom.mem_ker.mp hf
    have hpos := GaussValuationUniqueness.pos_of_ker v hwv' _ he _ hq
    have hfac := GaussValuationUniqueness.sHom_factor v hK (d.jc c) j0 (d.x c) a ha ha0 hrel f
    rw [← hfac] at hpos
    exact (hOv.2 f).2.mp hpos
  haveI := hH1.1
  haveI := hH2.1
  have e1 := GaussValuationUniqueness.eq_of_le_ht hH1.2 hQne (key p1 w1 hw1 hv1)
  have e2 := GaussValuationUniqueness.eq_of_le_ht hH2.2 hQne (key p2 w2 hw2 hv2)
  rw [← e1, ← e2]

end GaussValuationUniqueness
end
