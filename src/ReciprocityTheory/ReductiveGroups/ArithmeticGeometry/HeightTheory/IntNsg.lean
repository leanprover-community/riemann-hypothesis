import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ComponentFormProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPts
import ReciprocityTheory.SemistableReduction.AevalIsWeightedHomogeneous
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HintIntOfBounds

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

theorem hint_zpow_split {F : Type*} [Field F] (x : F) (e : ℤ) :
    x ^ e = x ^ e.toNat / x ^ (-e).toNat := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg e <;> simp [zpow_neg]

theorem hint_fp_split {R Fr ι : Type*} [CommRing R] [Field Fr] [Algebra R Fr] (S : Set ι)
    (g : ι → R) (e : ι → ℤ) :
    ∃ s : Finset ι, (∀ p ∈ s, p ∈ S ∧ e p ≠ 0) ∧
      ∏ᶠ (p : ι) (_ : p ∈ S), algebraMap R Fr (g p) ^ e p =
        algebraMap R Fr (∏ p ∈ s, g p ^ (e p).toNat) /
          algebraMap R Fr (∏ p ∈ s, g p ^ (-e p).toNat) := by
  classical
  by_cases hfin : (Function.mulSupport fun p => ∏ᶠ (_ : p ∈ S), algebraMap R Fr (g p) ^ e p).Finite
  · refine ⟨hfin.toFinset, fun p hp => ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset, Function.mem_mulSupport] at hp
      by_cases hpS : p ∈ S
      · exact ⟨hpS, fun h0 => hp (by simp [hpS, h0])⟩
      · exact (hp (by simp [hpS])).elim
    · rw [finprod_eq_prod _ hfin, map_prod, map_prod, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Set.Finite.mem_toFinset, Function.mem_mulSupport] at hp
      have hpS : p ∈ S := by
        by_contra h
        exact hp (by simp [h])
      rw [finprod_eq_if, if_pos hpS, map_pow, map_pow]
      exact hint_zpow_split _ _
  · refine ⟨∅, by simp, ?_⟩
    rw [finprod_of_infinite_mulSupport hfin]
    simp

def HintMH {R : Type*} [CommSemiring R] {D n : ℕ} (q : MvPolynomial (Fin (D + 1) × Fin n) R) :
    Prop :=
  ∃ α : Fin (D + 1) → ℕ, α 0 = 0 ∧ IsMultiHomogeneous α q

theorem hintMH_one {R : Type*} [CommSemiring R] {D n : ℕ} :
    HintMH (1 : MvPolynomial (Fin (D + 1) × Fin n) R) := by
  refine ⟨0, rfl, fun s hs b => ?_⟩
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hs
  split_ifs at hs with h
  · subst h
    simp
  · exact absurd rfl hs

theorem hintMH_C_mul {R : Type*} [CommSemiring R] {D n : ℕ} (k : R)
    {q : MvPolynomial (Fin (D + 1) × Fin n) R} (hq : HintMH q) :
    HintMH (MvPolynomial.C k * q) := by
  obtain ⟨α, h0, hα⟩ := hq
  refine ⟨α, h0, fun s hs b => hα s ?_ b⟩
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hs
  exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hs)

theorem hintMH_mul {R : Type*} [CommSemiring R] {D n : ℕ}
    {q q' : MvPolynomial (Fin (D + 1) × Fin n) R} (hq : HintMH q) (hq' : HintMH q') :
    HintMH (q * q') := by
  classical
  obtain ⟨α, h0, hα⟩ := hq
  obtain ⟨α', h0', hα'⟩ := hq'
  refine ⟨α + α', by simp [h0, h0'], fun s hs b => ?_⟩
  open scoped Pointwise in
  have hsub : (q * q').support ⊆ q.support + q'.support := MvPolynomial.support_mul ..
  obtain ⟨a, ha, a', ha', rfl⟩ := Finset.mem_add.mp (hsub hs)
  simp [Finset.sum_add_distrib, hα a ha b, hα' a' ha' b]

theorem hintMH_pow {R : Type*} [CommSemiring R] {D n : ℕ}
    {q : MvPolynomial (Fin (D + 1) × Fin n) R} (hq : HintMH q) (m : ℕ) : HintMH (q ^ m) := by
  induction m with
  | zero =>
    rw [pow_zero]
    exact hintMH_one
  | succ k ih =>
    rw [pow_succ]
    exact hintMH_mul ih hq

theorem hintMH_prod {R ι : Type*} [CommSemiring R] {D n : ℕ} (s : Finset ι)
    (q : ι → MvPolynomial (Fin (D + 1) × Fin n) R) (m : ι → ℕ) (hq : ∀ p ∈ s, HintMH (q p)) :
    HintMH (∏ p ∈ s, q p ^ m p) := by
  exact Finset.prod_induction _ (fun x => HintMH x) (fun a b ha hb => hintMH_mul ha hb) hintMH_one
    (fun p hp => hintMH_pow (hq p hp) (m p))

theorem hintMH_map {K : Type*} [Field K] {D n : ℕ} {q : MvPolynomial (Fin (D + 1) × Fin n) K}
    (hq : HintMH q) (φ : K →+* ℂ) : HintMH (MvPolynomial.map φ q) := by
  obtain ⟨α, h0, hα⟩ := hq
  exact ⟨α, h0, fun s hs b => hα s (MvPolynomial.support_map_subset φ q hs) b⟩

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem hint_evT_eq (sg : K →+* ℂ) (t0 : Fin (d.N + 1) → ℂ)
    (z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1)) (q : KTp K d.D d.N) :
    d.evT sg t0 (d.tOf z) q = MvPolynomial.eval (hintPt t0 z) (MvPolynomial.map sg q) := by
  rw [MvPolynomial.eval_map]
  rfl

theorem hint_good_split (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (e : Ideal (KTp K d.D d.N) → ℤ)
    (he : ∀ p ∈ d.HtOne, e p ≠ 0 → ∃ w, w ∈ d.GoodP c p) :
    ∃ a b : KTp K d.D d.N, HintMH a ∧ HintMH b ∧
      ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ e p =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a / algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b := by
  obtain ⟨s, hs, heq⟩ := hint_fp_split (Fr := KTf K d.D d.N) d.HtOne d.gen e
  have hmh : ∀ p ∈ s, HintMH (d.gen p) := fun p hp => by
    obtain ⟨hp1, hp2⟩ := hs p hp
    exact ⟨_, by simp, (d.good_primes_properties hd h c).2.1 p hp1 (he p hp1 hp2)⟩
  exact ⟨_, _, hintMH_prod s _ _ hmh, hintMH_prod s _ _ hmh, heq⟩

theorem hint_good_of_ne (c : ι) (p : Ideal (KTp K d.D d.N)) {f : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ}
    (hp : (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p), f w) ≠ 0) :
    ∃ w, w ∈ d.GoodP c p := by
  by_contra hne
  push_neg at hne
  apply hp
  simp [hne]

theorem hint_log_finprod {α : Type*} (S : Set α) (hS : S.Finite) (f : α → ℂ)
    (hf : ∀ x ∈ S, f x ≠ 0) :
    ∑ᶠ (x : α) (_ : x ∈ S), Real.log ‖f x‖ = Real.log ‖∏ᶠ (x : α) (_ : x ∈ S), f x‖ := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finprod_mem_eq_finite_toFinset_prod _ hS, norm_prod,
    Real.log_prod]
  intro x hx
  rw [Set.Finite.mem_toFinset] at hx
  exact norm_ne_zero_iff.mpr (hf x hx)

theorem hint_intNorm (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (g : Ω c) (hg : g ≠ 0) :
    Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), Real.log ‖P g‖)
      (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.omS_finite hd h c).1
  obtain ⟨κ, hκ, hN⟩ := (d.norm_factorization hd h).1 c g hg
  obtain ⟨a, b, ha, hb, hsplit⟩ := d.hint_good_split hd h c _
    (fun p _ hp => d.hint_good_of_ne c p hp)
  rw [hsplit] at hN
  have hNm0 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) ≠ 0 :=
    Algebra.norm_ne_zero_iff.2 ((map_ne_zero_iff _ (algebraMap (Ω c) _).injective).2 hg)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero] at hN
    exact hNm0 hN
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero] at hN
    exact hNm0 hN
  set a' : KTp K d.D d.N := MvPolynomial.C κ * a with ha'
  have hkey : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a' := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb0
    rw [hN, ha', map_mul, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    field_simp
  have hmapb : MvPolynomial.map sg b ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective sg sg.injective)).2 hb0
  have hmapa : MvPolynomial.map sg a' ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective sg sg.injective)).2
      (mul_ne_zero (by simpa using hκ) ha0)
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  obtain ⟨βb, hβb0, hβb⟩ := hintMH_map hb sg
  obtain ⟨βa, hβa0, hβa⟩ := hintMH_map (hintMH_C_mul κ ha) sg
  have hIa := hint_logInt_tail hn hmapa hβa hβa0 0
  have hIb := hint_logInt_tail hn hmapb hβb hβb0 0
  refine (hIa.sub hIb).congr ?_
  filter_upwards [d.norm_at_sg hd h c sg, hint_ae_tail hn hmapb hβb hβb0 0] with z hz hbz
  obtain ⟨hfin, -, hcl1, -⟩ := hz
  have hbz' : d.evT sg 0 (d.tOf z) b ≠ 0 := by rw [hint_evT_eq]; exact hbz
  have hprod := hcl1 g a' b 0 hg hb0 hkey hbz'
  have hPg : ∀ P ∈ d.ST c sg (d.tOf z), P g ≠ 0 := fun P _ =>
    (map_ne_zero_iff P P.injective).2 hg
  have hprod0 : (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) ≠ 0 := by
    rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
    exact Finset.prod_ne_zero_iff.2 fun P hP => hPg P (hfin.mem_toFinset.1 hP)
  have haz : d.evT sg 0 (d.tOf z) a' ≠ 0 := by
    intro h0; rw [h0, zero_div] at hprod; exact hprod0 hprod.symm
  simp only [Pi.sub_apply]
  rw [hint_log_finprod _ hfin _ hPg, ← hprod, norm_div, Real.log_div (norm_ne_zero_iff.2 haz)
    (norm_ne_zero_iff.2 hbz'), hint_evT_eq, hint_evT_eq]

variable {d} in
theorem hint_line (hd : d.AxH 𝒜) {c : ι} {G : WT} {f g : A c} (hg : g ∈ 𝒜 c G) (hg0 : g ≠ 0)
    (hf : f ∈ 𝒜 c G) : f = ratio (Ω := Ω c) f g • g := by
  have h1 := hd.finrank_one c G
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨g, hg⟩ : 𝒜 c G) (by simpa using hg0)).mp h1
    ⟨f, hf⟩
  have hex : ∃ a : Ω c, f = a • g := ⟨a, by simpa using (congrArg Subtype.val ha).symm⟩
  unfold ratio
  rw [dif_pos hex]
  exact hex.choose_spec

variable {d} in
theorem hint_ratio_self (hd : d.AxH 𝒜) {c : ι} {G : WT} {g : A c} (hg : g ∈ 𝒜 c G)
    (hg0 : g ≠ 0) : ratio (Ω := Ω c) g g = 1 := by
  have hex : ∃ a : Ω c, g = a • g := ⟨1, (one_smul _ _).symm⟩
  unfold ratio
  rw [dif_pos hex]
  have h := hex.choose_spec
  have h2 : (hex.choose - 1) • g = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 hg0

noncomputable def hintU (c : ι) (P : Ω c →+* ℂ) : EuclideanSpace ℂ (Fin (d.N + 1)) :=
  WithLp.toLp 2 (fun j => P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)))

theorem hint_one_le_U (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) : 1 ≤ ‖d.hintU c P‖ := by
  have hr : ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w (d.jc c) c) = 1 :=
    hint_ratio_self hd (hd.w_mem _ c) (hd.w_base c)
  calc (1 : ℝ) = ‖(WithLp.ofLp (d.hintU c P)) (d.jc c)‖ := by simp [hintU, hr]
    _ ≤ ‖d.hintU c P‖ := PiLp.norm_apply_le _ _

theorem hint_nrm_w (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) (j : Fin (d.N + 1)) :
    d.nrm c d.wL (d.w j c) P =
      ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ * d.nrm c d.wL (d.w (d.jc c) c) P := by
  have hl := hint_line hd (hd.w_mem (d.jc c) c) (hd.w_base c) (hd.w_mem j c)
  by_cases h0 : ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = 0
  · conv_lhs => rw [hl, h0, zero_smul, hd.nrm_zero]
    simp [h0]
  · conv_lhs => rw [hl]
    exact hd.nrm_smul c P _ (hd.w_mem _ c) (hd.w_base c) h0

theorem hint_be_eq (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) :
    d.be c P = d.nrm c d.wL (d.w (d.jc c) c) P * ‖d.hintU c P‖ := by
  have hn : 0 ≤ d.nrm c d.wL (d.w (d.jc c) c) P := (hd.nrm_pos c P (hd.w_mem _ c) (hd.w_base c)).le
  have hs : ∑ j, d.nrm c d.wL (d.w j c) P ^ 2 =
      (∑ j, ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ ^ 2) *
        d.nrm c d.wL (d.w (d.jc c) c) P ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [hint_nrm_w d hd c P j, mul_pow]
  rw [Data.be, hs, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hn, mul_comm, EuclideanSpace.norm_eq]
  simp [hintU]

theorem hint_U_coord_ne (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) :
    (WithLp.ofLp (d.hintU c P) : Fin (d.N + 1) → ℂ) ≠ 0 := by
  intro h
  have := congrFun h (d.jc c)
  simp [hintU, hint_ratio_self hd (hd.w_mem _ c) (hd.w_base c)] at this

theorem hint_intU (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) :
    Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), Real.log ‖d.hintU c P‖)
      (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  obtain ⟨F, hF, hF0, hFmh, -, -⟩ := d.componentForm_properties hd h c
  obtain ⟨a, b, ha, hb, hsplit⟩ := d.hint_good_split hd h c
    (fun p => d.nPMM h c (d.w (d.jc c) c) p)
    (fun p _ hp => d.hint_good_of_ne c p
      (f := fun w => (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c)) hp)
  have hfZ : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F =
      Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b) := by
    rw [hF, ← hsplit]; rfl
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hF0 (hinj hfZ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hF0 (hinj hfZ)
  have hkey : Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F * b) := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb0
    rw [map_mul, hfZ]
    field_simp
  have hmi := MvPolynomial.map_injective (σ := TVar d.D d.N) sg sg.injective
  have hFc0 : MvPolynomial.map sg F ≠ 0 := (map_ne_zero_iff _ hmi).2 hF0
  have hac0 : MvPolynomial.map sg a ≠ 0 := (map_ne_zero_iff _ hmi).2 ha0
  have hbc0 : MvPolynomial.map sg b ≠ 0 := (map_ne_zero_iff _ hmi).2 hb0
  have hFcmh := isMultiHomogeneous_map_ring _ F hFmh sg
  obtain ⟨αa, hαa0, hαa⟩ := hintMH_map ha sg
  obtain ⟨αb, hαb0, hαb⟩ := hintMH_map hb sg
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  haveI := sphereMeasure_isProbability hn
  haveI := blockSphereMeasure_isProbability (B := d.D) hn
  have I1 := hint_fubini hn hFc0 hFcmh
  have I2 := hint_logInt_tail hn hac0 hαa hαa0 0
  have I3 := hint_logInt_tail hn hbc0 hαb hαb0 0
  refine (((I1.sub I2).add I3).add
    (integrable_const ((d.delc c : ℝ) * (harmonic d.N : ℝ) / 2))).congr ?_
  filter_upwards [d.norm_at_sg hd h c sg, hint_ae_tail hn hac0 hαa hαa0 0,
    hint_ae_tail hn hbc0 hαb hαb0 0] with z hz haz hbz
  obtain ⟨hfin, hcard, -, hcl2⟩ := hz
  set S := d.ST c sg (d.tOf z) with hS
  have hind : ∀ (q : MvPolynomial (Fin (d.D + 1) × Fin (d.N + 1)) ℂ) (α : Fin (d.D + 1) → ℕ),
      α 0 = 0 → IsMultiHomogeneous α q → ∀ t0 : Fin (d.N + 1) → ℂ,
      MvPolynomial.eval (hintPt t0 z) q = MvPolynomial.eval (hintPt 0 z) q := by
    intro q α h0 hq t0
    refine hint_eval_indep hq h0 _ _ ?_
    rintro ⟨i, j⟩ hi
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hi
    rfl
  have hlin : ∀ᵐ s ∂(sphereProb (d.N + 1)), ∀ P ∈ S,
      ∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j ≠ 0 :=
    (Filter.eventually_all_finite hfin).2 fun P _ => hint_lin_ae _ (d.hint_U_coord_ne hd c P)
  have hpt : ∀ᵐ s ∂(sphereProb (d.N + 1)),
      Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F)‖ =
        Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b)‖ +
          ∑ P ∈ hfin.toFinset,
            Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j‖ := by
    filter_upwards [hlin] with s hs
    have haz' : d.evT sg (spherePoint s) (d.tOf z) a ≠ 0 := by
      rw [hint_evT_eq, hind _ _ hαa0 hαa]; exact haz
    have hq := hcl2 (F * b) a (spherePoint s) ha0 hkey haz'
    rw [hint_evT_eq, hint_evT_eq, map_mul, map_mul, hind _ _ hαa0 hαa,
      hind (MvPolynomial.map sg b) _ hαb0 hαb] at hq
    have hL : ∀ P ∈ S, (∑ j, spherePoint s j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) ≠ 0 := by
      intro P hP
      have := hs P hP
      simpa [hintU, mul_comm] using this
    have hprod0 : (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S),
        ∑ j, spherePoint s j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) ≠ 0 := by
      rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
      exact Finset.prod_ne_zero_iff.2 fun P hP => hL P (hfin.mem_toFinset.1 hP)
    have hFz : MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F) ≠ 0 := by
      intro h0; rw [h0, zero_mul, zero_div] at hq; exact hprod0 hq.symm
    have heq : MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F) =
        MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a) *
          (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S),
            ∑ j, spherePoint s j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) /
          MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b) := by
      rw [← hq]; field_simp
    rw [heq, norm_div, norm_mul, Real.log_div (by simpa using mul_ne_zero haz hprod0)
      (norm_ne_zero_iff.2 hbz), Real.log_mul (norm_ne_zero_iff.2 haz)
      (norm_ne_zero_iff.2 hprod0), ← hint_log_finprod _ hfin _ hL,
      finsum_mem_eq_finite_toFinset_sum _ hfin]
    have : ∀ P ∈ hfin.toFinset, Real.log ‖∑ j, spherePoint s j *
        P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ =
        Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j‖ := by
      intro P _; simp [hintU, mul_comm]
    rw [Finset.sum_congr rfl this]; ring
  have hInt : ∀ P ∈ hfin.toFinset, Integrable (fun s : UnitSphereC (d.N + 1) =>
      Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j‖) (sphereProb (d.N + 1)) :=
    fun P _ => (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLinLog (d.N + 1) (d.hintU c P)
      (fun h0 => d.hint_U_coord_ne hd c P (by rw [h0]; rfl))).1
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [integral_congr_ae hpt, integral_add (integrable_const _) (integrable_finset_sum _ hInt),
    integral_const, integral_finset_sum _ hInt, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hval : ∀ P ∈ hfin.toFinset, ∫ s, Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j *
      spherePoint s j‖ ∂(sphereProb (d.N + 1)) = Real.log ‖d.hintU c P‖ - (harmonic d.N : ℝ) / 2 := by
    intro P _
    have := (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLinLog (d.N + 1) (d.hintU c P)
      (fun h0 => d.hint_U_coord_ne hd c P (by rw [h0]; rfl))).2
    simpa using this
  rw [Finset.sum_congr rfl hval, Finset.sum_sub_distrib, Finset.sum_const,
    ← Set.ncard_eq_toFinset_card _ hfin, hcard]
  simp only [probReal_univ, one_smul, nsmul_eq_mul]
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def hintSm (c : ι) (sg : K →+* ℂ) (φ : (Ω c →+* ℂ) → ℝ)
    (z : BlockSphere d.D (d.N + 1)) : ℝ :=
  ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), φ P

def HintIS (c : ι) (sg : K →+* ℂ) (φ : (Ω c →+* ℂ) → ℝ) : Prop :=
  Integrable (d.hintSm c sg φ) (blockSphereProb d.D (d.N + 1))

theorem hint_fs (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) :
    ∀ᵐ z ∂(blockSphereProb d.D (d.N + 1)), ∃ s : Finset (Ω c →+* ℂ), s.card = d.delc c ∧
      (∀ P ∈ s, P ∈ PT (Ω := Ω c) sg) ∧ ∀ φ, d.hintSm c sg φ z = ∑ P ∈ s, φ P := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  filter_upwards [d.norm_at_sg hd h c sg] with z hz
  obtain ⟨hfin, hcard, -, -⟩ := hz
  refine ⟨hfin.toFinset, ?_, fun P hP => (hfin.mem_toFinset.1 hP).1, fun φ => ?_⟩
  · rw [← hcard, Set.ncard_eq_toFinset_card _ hfin]
  · exact finsum_mem_eq_finite_toFinset_sum _ hfin

theorem hintIS_lin (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {sg : K →+* ℂ}
    {φ₁ φ₂ : (Ω c →+* ℂ) → ℝ} (h₁ : d.HintIS c sg φ₁) (h₂ : d.HintIS c sg φ₂) (a₁ a₂ b : ℝ) :
    d.HintIS c sg (fun P => a₁ * φ₁ P + a₂ * φ₂ P + b) := by
  have hfs := d.hint_fs hd h c sg
  haveI : IsFiniteMeasure (blockSphereProb d.D (d.N + 1)) := by
    unfold blockSphereProb; infer_instance
  unfold HintIS at *
  refine (((h₁.const_mul a₁).add (h₂.const_mul a₂)).add
    (integrable_const (b * (d.delc c : ℝ)))).congr ?_
  filter_upwards [hfs] with z hz
  obtain ⟨s, hs, -, hφ⟩ := hz
  simp only [Pi.add_apply, hφ, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, hs,
    nsmul_eq_mul]
  ring

theorem hintIS_congr (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {sg : K →+* ℂ}
    {φ ψ : (Ω c →+* ℂ) → ℝ} (hφ : d.HintIS c sg φ) (heq : ∀ P ∈ PT (Ω := Ω c) sg, φ P = ψ P) :
    d.HintIS c sg ψ := by
  unfold HintIS at *
  refine hφ.congr (Filter.Eventually.of_forall fun z => ?_)
  exact finsum_mem_congr rfl fun P hP => heq P hP.1

theorem hintIS_bounds (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {sg : K →+* ℂ}
    {φ ψ : (Ω c →+* ℂ) → ℝ}
    (hm : AEStronglyMeasurable (d.hintSm c sg φ) (blockSphereProb d.D (d.N + 1)))
    (hψ : d.HintIS c sg ψ) (hle : ∀ P ∈ PT (Ω := Ω c) sg, ψ P ≤ φ P) (B : ℝ)
    (hB : ∀ P ∈ PT (Ω := Ω c) sg, φ P ≤ B) : d.HintIS c sg φ := by
  have hfs := d.hint_fs hd h c sg
  haveI : IsFiniteMeasure (blockSphereProb d.D (d.N + 1)) := by
    unfold blockSphereProb; infer_instance
  unfold HintIS at *
  refine Integrable.mono' (hψ.abs.add (integrable_const |(d.delc c : ℝ) * B|)) hm ?_
  filter_upwards [hfs] with z hz
  obtain ⟨s, hs, hsP, hφ⟩ := hz
  have h1 : d.hintSm c sg ψ z ≤ d.hintSm c sg φ z := by
    rw [hφ, hφ]
    exact Finset.sum_le_sum fun P hP => hle P (hsP P hP)
  have h2 : d.hintSm c sg φ z ≤ (d.delc c : ℝ) * B := by
    rw [hφ, ← hs, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun P hP => hB P (hsP P hP)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [neg_abs_le (d.hintSm c sg ψ z), abs_nonneg ((d.delc c : ℝ) * B)]
  · linarith [le_abs_self ((d.delc c : ℝ) * B), abs_nonneg (d.hintSm c sg ψ z)]

theorem hint_bsp_smul : blockSphereProb d.D (d.N + 1) =
    (((volume : Measure (EuclideanSpace ℂ (Fin (d.N + 1)))).toSphere Set.univ)⁻¹ ^ d.D) •
      d.sphMeasure := by
  unfold blockSphereProb
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul, sphMeasure, Measure.pi_pi]
  simp only [sphereProb, ProbabilityTheory.cond_apply MeasurableSet.univ, Set.univ_inter,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem eq_ratio_smul_of_mem_graded {d' : Data K ι Ω WT A} (hd : d'.AxH 𝒜) {c : ι} {G : WT} {f e : A c}
    (he : e ∈ 𝒜 c G) (he0 : e ≠ 0) (hf : f ∈ 𝒜 c G) : f = ratio (Ω := Ω c) f e • e := by
  have hnz : (⟨e, he⟩ : 𝒜 c G) ≠ 0 := fun h0 => he0 (by simpa using congrArg Subtype.val h0)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e, he⟩ : 𝒜 c G) hnz).mp (hd.finrank_one c G) ⟨f, hf⟩
  have hex : ∃ a : Ω c, f = a • e := ⟨a, by simpa using (congrArg Subtype.val ha).symm⟩
  rw [ratio, dif_pos hex]
  exact hex.choose_spec

theorem hint_meas (hd : d.AxH 𝒜) (c : ι) (sg : K →+* ℂ) {G : WT} {f : A c} (hf : f ∈ 𝒜 c G)
    (hf0 : f ≠ 0) :
    AEStronglyMeasurable (d.hintSm c sg fun P => Real.log (d.nrm c G f P))
      (blockSphereProb d.D (d.N + 1)) := by
  rw [d.hint_bsp_smul]
  exact ((hd.a13 c sg hf hf0).smul_measure _).aestronglyMeasurable

variable {d} in
theorem hint_ratio_ne (hd : d.AxH 𝒜) {c : ι} {G : WT} {f e : A c} (he : e ∈ 𝒜 c G) (he0 : e ≠ 0)
    (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0) : ratio (Ω := Ω c) f e ≠ 0 := by
  intro h0
  have h1 := eq_ratio_smul_of_mem_graded hd he he0 hf
  rw [h0, zero_smul] at h1
  exact hf0 h1

theorem hint_log_line (hd : d.AxH 𝒜) {c : ι} {G : WT} {f e : A c} (he : e ∈ 𝒜 c G) (he0 : e ≠ 0)
    (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0) (P : Ω c →+* ℂ) :
    Real.log (d.nrm c G f P) = Real.log ‖P (ratio (Ω := Ω c) f e)‖ + Real.log (d.nrm c G e P) := by
  have hfe := eq_ratio_smul_of_mem_graded hd he he0 hf
  have hr := hint_ratio_ne hd he he0 hf hf0
  calc Real.log (d.nrm c G f P)
      = Real.log (d.nrm c G (ratio (Ω := Ω c) f e • e) P) := by rw [← hfe]
    _ = _ := by
      rw [hd.nrm_smul c P _ he he0 hr,
        Real.log_mul (norm_ne_zero_iff.mpr ((map_ne_zero P).mpr hr)) (hd.nrm_pos c P he he0).ne']

theorem hint_log_mul (hd : d.AxH 𝒜) {c : ι} {G G' : WT} {f g : A c} (hf : f ∈ 𝒜 c G)
    (hg : g ∈ 𝒜 c G') (hf0 : f ≠ 0) (hg0 : g ≠ 0) (P : Ω c →+* ℂ) :
    Real.log (d.nrm c (G + G') (f * g) P) =
      Real.log (d.nrm c G f P) + Real.log (d.nrm c G' g P) := by
  rw [hd.nrm_mul c P hf hg hf0 hg0,
    Real.log_mul (hd.nrm_pos c P hf hf0).ne' (hd.nrm_pos c P hg hg0).ne']

theorem hint_pow (hd : d.AxH 𝒜) {c : ι} {G : WT} {f : A c} (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0) :
    ∀ k : ℕ, 0 < k → f ^ k ∈ 𝒜 c (k • G) ∧ f ^ k ≠ 0 ∧
      ∀ P, Real.log (d.nrm c (k • G) (f ^ k) P) = k * Real.log (d.nrm c G f P) := by
  intro k hk
  haveI := hd.graded c
  induction k with
  | zero => exact absurd hk (lt_irrefl 0)
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨by simpa using hf, by simpa using hf0, fun P => by simp⟩
    · obtain ⟨h1, h2, h3⟩ := ih hn
      have hmem : f ^ (n + 1) ∈ 𝒜 c ((n + 1) • G) := by
        rw [pow_succ, succ_nsmul]; exact SetLike.mul_mem_graded h1 hf
      have hne : f ^ (n + 1) ≠ 0 := by
        rw [pow_succ]; exact hd.mul_ne_zero c h1 hf h2 hf0
      refine ⟨hmem, hne, fun P => ?_⟩
      rw [pow_succ, succ_nsmul, hd.nrm_mul c P h1 hf h2 hf0,
        Real.log_mul (hd.nrm_pos c P h1 h2).ne' (hd.nrm_pos c P hf hf0).ne', h3 P]
      push_cast
      ring

theorem hint_log_be (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) :
    Real.log (d.be c P) =
      Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) + Real.log ‖d.hintU c P‖ := by
  have he := hd.w_mem (d.jc c) c
  have he0 := hd.w_base c
  have key : ∀ j, d.nrm c d.wL (d.w j c) P =
      ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ * d.nrm c d.wL (d.w (d.jc c) c) P := by
    intro j
    by_cases hj : d.w j c = 0
    · have hr : ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = 0 := by
        have h1 := eq_ratio_smul_of_mem_graded hd he he0 (hd.w_mem j c)
        have h2 : ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c = 0 := by
          rw [← h1]; exact hj
        exact (smul_eq_zero.mp h2).resolve_right he0
      rw [hr, hj, hd.nrm_zero, map_zero, norm_zero, zero_mul]
    · rw [← hd.nrm_smul c P _ he he0 (hint_ratio_ne hd he he0 (hd.w_mem j c) hj),
        ← eq_ratio_smul_of_mem_graded hd he he0 (hd.w_mem j c)]
  have hsum : ∑ j, d.nrm c d.wL (d.w j c) P ^ 2 = d.nrm c d.wL (d.w (d.jc c) c) P ^ 2 *
      ∑ j, ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [key j]; ring
  have hU : ‖d.hintU c P‖ = Real.sqrt (∑ j, ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ ^ 2) := by
    simp [hintU, EuclideanSpace.norm_eq]
  have hUne : ‖d.hintU c P‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h0
    have h1 := congrArg (fun x => x (d.jc c)) h0
    exact hint_ratio_ne hd he he0 he he0 (by simpa [hintU] using h1)
  have hpos := hd.nrm_pos c P he he0
  rw [be, hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos.le, ← hU, Real.log_mul hpos.ne' hUne]

theorem hint_bdd (sg : K →+* ℂ) (c : ι) {G : WT} {f : ∀ c, A c}
    (hb : BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (f p.1) p.2)) :
    ∃ B, ∀ P ∈ PT (Ω := Ω c) sg, d.nrm c G (f c) P ≤ B := by
  obtain ⟨B, hB⟩ := hb
  exact ⟨B, fun P hP => hB ⟨⟨c, ⟨P, hP⟩⟩, rfl⟩⟩

theorem hint_log_le (hd : d.AxH 𝒜) {c : ι} {G : WT} {f : A c} (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0)
    {sg : K →+* ℂ} {B : ℝ} (hB : ∀ P ∈ PT (Ω := Ω c) sg, d.nrm c G f P ≤ B) :
    ∀ P ∈ PT (Ω := Ω c) sg, Real.log (d.nrm c G f P) ≤ Real.log B := fun P hP => Real.log_le_log (hd.nrm_pos c P hf hf0) (hB P hP)

theorem hint_thp_ne (hd : d.AxH 𝒜) (c : ι) : ∃ k, d.thp k c ≠ 0 := by
  by_contra hall
  push_neg at hall
  obtain ⟨e, he, -, h3⟩ := hd.a4
  obtain ⟨q, hq, p, hp⟩ := h3 1
  apply hq c
  have h4 := hp c
  rw [Pi.one_apply, mul_one] at h4
  rw [h4]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hr : ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c) = 0 := by
    rw [hall]
    have h1 := eq_ratio_smul_of_mem_graded hd (he c).1 (he c).2 (Submodule.zero_mem _)
    exact (smul_eq_zero.mp h1.symm).resolve_right (he c).2
  rw [hr, map_zero, mul_zero]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem hint_chain (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (c : ι) (sg : K →+* ℂ) :
    d.HintIS c sg (fun P => Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) ∧
    d.HintIS c sg (fun P => Real.log (d.nrm c d.wL (d.w (d.jc c) c) P)) ∧
    d.HintIS c sg (fun P => Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P)) ∧
    (∃ e, e ∈ 𝒜 c d.wF ∧ e ≠ 0 ∧ d.HintIS c sg (fun P => Real.log (d.nrm c d.wF e P))) ∧
    d.HintIS c sg (fun P => Real.log (d.nrm c d.G2 (d.ta2 c) P)) := by
  haveI := hd.graded c
  obtain ⟨Bw, hBw⟩ := d.hint_bdd sg c (f := d.w (d.jc c)) (hd.bdd sg d.wL _ (Or.inl
    ⟨by rw [hd.WW_span]; exact Submodule.subset_span ⟨_, rfl⟩, rfl⟩))
  obtain ⟨Be, hBe⟩ := d.hint_bdd sg c
    (hd.bdd sg (d.n1 • d.wde) d.et (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  obtain ⟨Bt, hBt⟩ := d.hint_bdd sg c
    (hd.bdd sg ((2 : ℕ) • d.G1) d.ta1 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  obtain ⟨B2, hB2⟩ := d.hint_bdd sg c
    (hd.bdd sg d.G2 d.ta2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
  obtain ⟨k, hk⟩ := d.hint_thp_ne hd c
  obtain ⟨Bh, hBh⟩ := d.hint_bdd sg c (f := d.thp k) (hd.bdd sg d.wF _ (Or.inr (Or.inl
    ⟨by rw [hd.Thp_span]; exact Submodule.subset_span ⟨k, rfl⟩, rfl⟩)))
  have hwm := hd.w_mem (d.jc c) c
  have hw0 := hd.w_base c
  have hem := hd.et_mem c
  have he0 := hd.et_ne c
  have htm := hd.firstSectionMem c
  have ht0 := hd.firstSectionNeZero c
  have h2m := hd.secondSectionMem c
  have h20 := hd.secondSectionNeZero c
  have hhm := hd.thp_mem k c
  have hn1 : 0 < d.n1 := Nat.mul_pos hd.i_ge hd.g_zero_ge_ask_sum
  have hi : (1 : ℝ) ≤ d.i := by exact_mod_cast hd.i_ge
  have hn1r : (d.n1 : ℝ) = d.i * d.g0 := by simp [Data.n1]
  have hn1r1 : (1 : ℝ) ≤ d.n1 := by exact_mod_cast hn1
  have hκ : (d.n1 : ℝ) * (d.cc / d.i) = d.g0 * d.cc := by
    rw [hn1r]; field_simp
  have hq : 1 ≤ 2 - 2 * d.cc * d.g0 := by linarith [hd.ccg0]
  have IU : d.HintIS c sg (fun P => Real.log ‖d.hintU c P‖) := d.hint_intU hd h c sg

  obtain ⟨ht1m, ht10, ht1l⟩ := d.hint_pow hd htm ht0 d.n1 hn1
  obtain ⟨he2m, he20, he2l⟩ := d.hint_pow hd hem he0 2 two_pos
  obtain ⟨hwpm, hwp0, hwpl⟩ := d.hint_pow hd hwm hw0 (2 * d.n1) (by omega)
  have hW1 : d.n1 • ((2 : ℕ) • d.G1) + (2 : ℕ) • (d.n1 • d.wde) = (2 * d.n1) • d.wL := by
    simp only [Data.G1, smul_sub, smul_smul, mul_comm d.n1 2]; abel
  have hf1m : d.ta1 c ^ d.n1 * d.et c ^ 2 ∈ 𝒜 c ((2 * d.n1) • d.wL) := by
    rw [← hW1]; exact SetLike.mul_mem_graded ht1m he2m
  have hf10 := hd.mul_ne_zero c ht1m he2m ht10 he20
  have Ir1 : d.HintIS c sg (fun P => Real.log ‖P (ratio (Ω := Ω c) (d.ta1 c ^ d.n1 * d.et c ^ 2)
      (d.w (d.jc c) c ^ (2 * d.n1)))‖) :=
    d.hint_intNorm hd h c sg _ (hint_ratio_ne hd hwpm hwp0 hf1m hf10)
  have E1 : ∀ P, (d.n1 : ℝ) * Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P) +
      2 * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) =
      Real.log ‖P (ratio (Ω := Ω c) (d.ta1 c ^ d.n1 * d.et c ^ 2)
        (d.w (d.jc c) c ^ (2 * d.n1)))‖ + 2 * d.n1 * Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) := by
    intro P
    have h1 := d.hint_log_mul hd ht1m he2m ht10 he20 P
    rw [hW1, ht1l, he2l] at h1
    have h2 := d.hint_log_line hd hwpm hwp0 hf1m hf10 P
    rw [hwpl] at h2
    push_cast at h1 h2
    linarith
  have I2 : ∀ P, -(Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) + Real.log ‖d.hintU c P‖) ≤
      d.tableLineDegreeFive * d.DF + d.cc / d.i * (-Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) +
        d.cc * d.tableLineDegreeTwo := by
    intro P; rw [← d.hint_log_be hd c P]; exact hI2be c P

  have Iet : d.HintIS c sg (fun P => Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) := by
    refine d.hintIS_bounds hd h (d.hint_meas hd c sg hem he0)
      (d.hintIS_lin hd h Ir1 IU (1 / (2 - 2 * d.cc * d.g0)) (-(2 * d.n1) / (2 - 2 * d.cc * d.g0))
        (-(d.n1 * Real.log Bt + 2 * d.n1 * (d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo)) /
          (2 - 2 * d.cc * d.g0))) (fun P hP => ?_) _ (d.hint_log_le hd hem he0 hBe)
    have e1 := E1 P
    have lt := d.hint_log_le hd htm ht0 hBt P hP
    have lt2 := mul_le_mul_of_nonneg_left lt (by positivity : (0 : ℝ) ≤ d.n1)
    have ib2 := mul_le_mul_of_nonneg_left (I2 P) (by positivity : (0 : ℝ) ≤ 2 * d.n1)
    have hκ' : (d.n1 : ℝ) * (d.cc / d.i) * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) =
        d.g0 * d.cc * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) := by rw [hκ]
    have hqp : (0 : ℝ) < 2 - 2 * d.cc * d.g0 := by linarith
    rw [← sub_nonneg]
    have : ∀ x y z : ℝ, 1 / (2 - 2 * d.cc * d.g0) * x + -(2 * d.n1) / (2 - 2 * d.cc * d.g0) * y +
        -z / (2 - 2 * d.cc * d.g0) = (x - 2 * d.n1 * y - z) / (2 - 2 * d.cc * d.g0) := by
      intro x y z; ring
    rw [this, sub_nonneg, div_le_iff₀ hqp]
    nlinarith

  have Iw : d.HintIS c sg (fun P => Real.log (d.nrm c d.wL (d.w (d.jc c) c) P)) := by
    refine d.hintIS_bounds hd h (d.hint_meas hd c sg hwm hw0)
      (d.hintIS_lin hd h Iet IU (d.cc / d.i) (-1) (-(d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo)))
      (fun P _ => ?_) _ (d.hint_log_le hd hwm hw0 hBw)
    have := I2 P
    linarith

  have It1 : d.HintIS c sg (fun P => Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P)) := by
    refine d.hintIS_bounds hd h (d.hint_meas hd c sg htm ht0)
      (d.hintIS_lin hd h Ir1 Iw (1 / d.n1) 2 (-(2 * Real.log Be) / d.n1)) (fun P hP => ?_) _
      (d.hint_log_le hd htm ht0 hBt)
    have e1 := E1 P
    have le := d.hint_log_le hd hem he0 hBe P hP
    have hnp : (0 : ℝ) < d.n1 := by linarith
    have : ∀ x y : ℝ, 1 / (d.n1 : ℝ) * x + 2 * y + -(2 * Real.log Be) / d.n1 =
        (x + 2 * d.n1 * y - 2 * Real.log Be) / d.n1 := by
      intro x y; field_simp; ring
    rw [this, div_le_iff₀ hnp]
    nlinarith

  obtain ⟨hwqm, hwq0, hwql⟩ := d.hint_pow hd hwm hw0 (d.D + 4) (by omega)
  have hW2 : d.wF + d.G2 = (d.D + 4) • d.wL := by rw [Data.G2]; abel
  have hf2m : d.thp k c * d.ta2 c ∈ 𝒜 c ((d.D + 4) • d.wL) := by
    rw [← hW2]; exact SetLike.mul_mem_graded hhm h2m
  have hf20 := hd.mul_ne_zero c hhm h2m hk h20
  have Ir2 : d.HintIS c sg (fun P => Real.log ‖P (ratio (Ω := Ω c) (d.thp k c * d.ta2 c)
      (d.w (d.jc c) c ^ (d.D + 4)))‖) :=
    d.hint_intNorm hd h c sg _ (hint_ratio_ne hd hwqm hwq0 hf2m hf20)
  have E2 : ∀ P, Real.log (d.nrm c d.wF (d.thp k c) P) + Real.log (d.nrm c d.G2 (d.ta2 c) P) =
      Real.log ‖P (ratio (Ω := Ω c) (d.thp k c * d.ta2 c) (d.w (d.jc c) c ^ (d.D + 4)))‖ +
        ((d.D + 4 : ℕ) : ℝ) * Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) := by
    intro P
    have h1 := d.hint_log_mul hd hhm h2m hk h20 P
    rw [hW2] at h1
    have h2 := d.hint_log_line hd hwqm hwq0 hf2m hf20 P
    rw [hwql] at h2
    linarith
  refine ⟨Iet, Iw, It1, ⟨d.thp k c, hhm, hk, ?_⟩, ?_⟩
  · refine d.hintIS_bounds hd h (d.hint_meas hd c sg hhm hk)
      (d.hintIS_lin hd h Ir2 Iw 1 ((d.D + 4 : ℕ) : ℝ) (-Real.log B2)) (fun P hP => ?_) _
      (d.hint_log_le hd hhm hk hBh)
    have e2 := E2 P
    have l2 := d.hint_log_le hd h2m h20 hB2 P hP
    linarith
  · refine d.hintIS_bounds hd h (d.hint_meas hd c sg h2m h20)
      (d.hintIS_lin hd h Ir2 Iw 1 ((d.D + 4 : ℕ) : ℝ) (-Real.log Bh)) (fun P hP => ?_) _
      (d.hint_log_le hd h2m h20 hB2)
    have e2 := E2 P
    have l2 := d.hint_log_le hd hhm hk hBh P hP
    linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

private theorem hintIS_log_nrm_of_mem_graded (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {sg : K →+* ℂ} {G : WT}
    {f e : A c} (he : e ∈ 𝒜 c G) (he0 : e ≠ 0) (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0)
    (hI : d.HintIS c sg (fun P => Real.log (d.nrm c G e P))) :
    d.HintIS c sg (fun P => Real.log (d.nrm c G f P)) := by
  have h1 := d.hint_intNorm hd h c sg (ratio (Ω := Ω c) f e) (d.hint_ratio_ne hd he he0 hf hf0)
  have h2 := d.hintIS_lin hd h (φ₁ := fun P => Real.log ‖P (ratio (Ω := Ω c) f e)‖) h1 hI 1 1 0
  refine d.hintIS_congr hd h (ψ := fun P => Real.log (d.nrm c G f P)) h2 ?_
  intro P _
  try dsimp only
  rw [d.hint_log_line hd he he0 hf hf0 P]
  ring

theorem int_Nsg (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (c : ι) (sg : K →+* ℂ) :
    (∀ (G : WT) (f : A c), G ∈ ({d.wL, d.n1 • d.wde, (2 : ℕ) • d.G1, d.wF, d.G2} : Set WT) →
      f ∈ 𝒜 c G → f ≠ 0 →
      MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
          Real.log (d.nrm c G f P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) ∧
    (∀ f : A c, f ∈ 𝒜 c d.wL → f ≠ 0 →
      MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
          Real.log (d.nrm c d.wL f P / d.be c P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) := by
  obtain ⟨h_et, h_w, h_ta1, ⟨e, he, he0, h_e⟩, h_ta2⟩ := d.hint_chain hd h hI2be c sg
  have hL : ∀ f : A c, f ∈ 𝒜 c d.wL → f ≠ 0 →
      d.HintIS c sg (fun P => Real.log (d.nrm c d.wL f P)) :=
    fun f hf hf0 => hintIS_log_nrm_of_mem_graded d hd h (hd.w_mem (d.jc c) c) (hd.w_base c) hf hf0 h_w
  refine ⟨fun G f hG hf hf0 => ?_, fun f hf hf0 => ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hG
    rcases hG with rfl | rfl | rfl | rfl | rfl
    · exact hL f hf hf0
    · exact hintIS_log_nrm_of_mem_graded d hd h (hd.et_mem c) (hd.et_ne c) hf hf0 h_et
    · exact hintIS_log_nrm_of_mem_graded d hd h (hd.firstSectionMem c) (hd.firstSectionNeZero c) hf hf0 h_ta1
    · exact hintIS_log_nrm_of_mem_graded d hd h he he0 hf hf0 h_e
    · exact hintIS_log_nrm_of_mem_graded d hd h (hd.secondSectionMem c) (hd.secondSectionNeZero c) hf hf0 h_ta2
  · have h3 := d.hintIS_lin hd h (hL f hf hf0) h_w 1 (-1) 0
    have h4 := d.hintIS_lin hd h (φ₂ := fun P => Real.log ‖d.hintU c P‖) h3
      (d.hint_intU hd h c sg) 1 (-1) 0
    refine d.hintIS_congr hd h (ψ := fun P => Real.log (d.nrm c d.wL f P / d.be c P)) h4 ?_
    intro P _
    try dsimp only
    have hpos := hd.nrm_pos c P hf hf0
    have hw := hd.nrm_pos c P (hd.w_mem (d.jc c) c) (hd.w_base c)
    have hU := d.hint_one_le_U hd c P
    have hbe : d.be c P ≠ 0 := by
      rw [d.hint_be_eq hd c P]
      exact (mul_pos hw (lt_of_lt_of_le one_pos hU)).ne'
    rw [Real.log_div hpos.ne' hbe, d.hint_log_be hd c P]
    ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
