import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IntNsg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDA

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def translatedForm (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) : KTp K d.D d.N :=
  MvPolynomial.aeval (fun v : TVar d.D d.N =>
    if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v) F

noncomputable def localHeightAtPrime (h : d.S1) (f : ∀ c, A c) (c : ι)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
    (d.fze h c w : ℝ) * (d.ordMM c (d.Wres c w) (f c) : ℝ)

noncomputable def localHeightAtEmbedding (f : ∀ c, A c) (c : ι) (sg : K →+* ℂ) : ℝ :=
  ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
    -Real.log (d.nrm c d.wL (f c) P / d.be c P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))

def heightSubstitutionCondition (h : d.S1) (x : Fin (d.N + 1) → K) (c : ι) (F : KTp K d.D d.N) (κ : K) : Prop :=
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F * algebraMap K (KTf K d.D d.N) κ *
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
        (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c))) =
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.translatedForm x F) *
      Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)

theorem ratio_eq_of_eq_smul_field {Ω' V : Type*} [Field Ω'] [AddCommGroup V] [Module Ω' V] {f g : V}
    (hg : g ≠ 0) {a : Ω'} (hf : f = a • g) : ratio (Ω := Ω') f g = a := by
  classical
  have h : ∃ b : Ω', f = b • g := ⟨a, hf⟩
  unfold ratio
  rw [dif_pos h]
  exact smul_left_injective Ω' hg (h.choose_spec.symm.trans hf)

theorem eq_ratio_base_smul (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) :
    f = ratio (Ω := Ω c) f (d.w (d.jc c) c) • d.w (d.jc c) c := by
  have hw := hd.w_mem (d.jc c) c
  have hw0 := hd.w_base c
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨_, hw⟩ : 𝒜 c d.wL)
    (by simpa using hw0)).1 (hd.finrank_one c d.wL) ⟨f, hf⟩
  have hfa : f = a • d.w (d.jc c) c := by
    have h1 := congrArg Subtype.val ha
    simp only [SetLike.val_smul] at h1
    exact h1.symm
  rw [ratio_eq_of_eq_smul_field hw0 hfa]
  exact hfa

theorem ratio_base_ne_zero (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    ratio (Ω := Ω c) f (d.w (d.jc c) c) ≠ 0 := by
  intro h0
  apply hf0
  rw [d.eq_ratio_base_smul hd c hf, h0, zero_smul]

theorem linearCombination_mem_section (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) : d.wx x c ∈ 𝒜 c d.wL := by
  haveI := hd.tower c
  unfold wx
  rw [Finset.sum_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Pi.smul_apply, ← algebraMap_smul (Ω c) (x j)]
  exact Submodule.smul_mem _ _ (hd.w_mem j c)

theorem ord_eq_valuation_ratio_base_add (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (hv : d.admitted c v)
    {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    ((d.ord c v d.wL f : ℤ) : WithTop ℤ) =
      v (ratio (Ω := Ω c) f (d.w (d.jc c) c)) + (d.ord c v d.wL (d.w (d.jc c) c) : WithTop ℤ) := by
  have hfa := d.eq_ratio_base_smul hd c hf
  have ha := d.ratio_base_ne_zero hd c hf hf0
  conv_lhs => rw [hfa]
  exact hd.ord_smul c v hv _ (hd.w_mem _ c) (hd.w_base c) ha

theorem eq_ratio_smul_of_mem (hd : d.AxH 𝒜) (c : ι) {f g : A c} (hf : f ∈ 𝒜 c d.wL) (hg : g ∈ 𝒜 c d.wL)
    (hg0 : g ≠ 0) : f = ratio (Ω := Ω c) f g • g := by
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨_, hg⟩ : 𝒜 c d.wL)
    (by simpa using hg0)).1 (hd.finrank_one c d.wL) ⟨f, hf⟩
  have hfa : f = a • g := by
    have h1 := congrArg Subtype.val ha
    simp only [SetLike.val_smul] at h1
    exact h1.symm
  rw [ratio_eq_of_eq_smul_field hg0 hfa]
  exact hfa

theorem ratio_ne_zero_of_ne_zero (hd : d.AxH 𝒜) (c : ι) {f g : A c} (hf : f ∈ 𝒜 c d.wL) (hg : g ∈ 𝒜 c d.wL)
    (hg0 : g ≠ 0) (hf0 : f ≠ 0) : ratio (Ω := Ω c) f g ≠ 0 := by
  intro h0
  apply hf0
  rw [d.eq_ratio_smul_of_mem hd c hf hg hg0, h0, zero_smul]

theorem ord_eq_valuation_ratio_add (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (hv : d.admitted c v)
    {f g : A c} (hf : f ∈ 𝒜 c d.wL) (hg : g ∈ 𝒜 c d.wL) (hg0 : g ≠ 0) (hf0 : f ≠ 0) :
    ((d.ord c v d.wL f : ℤ) : WithTop ℤ) =
      v (ratio (Ω := Ω c) f g) + (d.ord c v d.wL g : WithTop ℤ) := by
  have hfa := d.eq_ratio_smul_of_mem hd c hf hg hg0
  have ha := d.ratio_ne_zero_of_ne_zero hd c hf hg hg0 hf0
  conv_lhs => rw [hfa]
  exact hd.ord_smul c v hv _ hg hg0 ha

theorem ratio_mul_ratio_height (hd : d.AxH 𝒜) (c : ι) {f g e : A c} (hf : f ∈ 𝒜 c d.wL)
    (hg : g ∈ 𝒜 c d.wL) (he : e ∈ 𝒜 c d.wL) (hg0 : g ≠ 0) (he0 : e ≠ 0) :
    ratio (Ω := Ω c) f e = ratio (Ω := Ω c) f g * ratio (Ω := Ω c) g e := by
  have h1 := d.eq_ratio_smul_of_mem hd c hf hg hg0
  have h2 := d.eq_ratio_smul_of_mem hd c hg he he0
  apply ratio_eq_of_eq_smul_field he0
  rw [mul_smul, ← h2, ← h1]

theorem coe_untopD_of_ne_top {v : WithTop ℤ} (hv : v ≠ ⊤) : ((v.untopD 0 : ℤ) : WithTop ℤ) = v := by
  obtain ⟨x, rfl⟩ := WithTop.ne_top_iff_exists.1 hv
  rw [WithTop.untopD_coe]

theorem ordMinMax_eq_ratio_untop_sub (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (hv : d.admitted c v)
    (j0 : Fin (d.N + 1)) (hj0 : d.w j0 c ≠ 0)
    (hint : ∀ j, 0 ≤ v (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)))
    {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.ordMM c v f = (v (ratio (Ω := Ω c) f (d.w (d.jc c) c))).untopD 0 -
      (v (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c))).untopD 0 := by
  have key : ∀ {g : A c}, g ∈ 𝒜 c d.wL → g ≠ 0 → d.ord c v d.wL g =
      (v (ratio (Ω := Ω c) g (d.w (d.jc c) c))).untopD 0 + d.ord c v d.wL (d.w (d.jc c) c) := by
    intro g hg hg0
    have h := d.ord_eq_valuation_ratio_base_add hd c v hv hg hg0
    have hne : v (ratio (Ω := Ω c) g (d.w (d.jc c) c)) ≠ ⊤ := by
      rw [Ne, AddValuation.top_iff]
      exact d.ratio_base_ne_zero hd c hg hg0
    rw [← coe_untopD_of_ne_top hne, ← WithTop.coe_add] at h
    exact WithTop.coe_inj.1 h
  have hinf : (⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)) = d.ord c v d.wL (d.w j0 c) := by
    apply le_antisymm
    · exact ciInf_le (Set.finite_range _).bddBelow (⟨j0, hj0⟩ : {j // d.w j c ≠ 0})
    · haveI : Nonempty {j // d.w j c ≠ 0} := ⟨⟨j0, hj0⟩⟩
      refine le_ciInf fun j => ?_
      have h := d.ord_eq_valuation_ratio_add hd c v hv (hd.w_mem j.1 c) (hd.w_mem j0 c) hj0 j.2
      have hnn := hint j.1
      have hne : v (ratio (Ω := Ω c) (d.w j.1 c) (d.w j0 c)) ≠ ⊤ := by
        rw [Ne, AddValuation.top_iff]
        exact d.ratio_ne_zero_of_ne_zero hd c (hd.w_mem j.1 c) (hd.w_mem j0 c) hj0 j.2
      rw [← coe_untopD_of_ne_top hne, ← WithTop.coe_add] at h
      have h' := WithTop.coe_inj.1 h
      rw [← coe_untopD_of_ne_top hne] at hnn
      have h0 : 0 ≤ (v (ratio (Ω := Ω c) (d.w j.1 c) (d.w j0 c))).untopD 0 := by exact_mod_cast hnn
      omega
  unfold ordMM
  rw [hinf, key hf hf0, key (hd.w_mem j0 c) hj0]
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem gen_ne_zero_of_htOne {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) : d.gen p ≠ 0 := by
  intro h0
  exact d.x4v4_gen_ne hp (by rw [h0, map_zero])

theorem valuation_genericRatio_eq_restriction (hd : d.AxH 𝒜) (c : ι) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
    (j0 : Fin (d.N + 1)) (hj0 : d.w j0 c ≠ 0)
    (hunit : w (∑ j, d.sH c (MvPolynomial.X (0, j)) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0) :
    w (d.rationalBaseRow c) = d.Wres c w (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) := by
  have hg : d.w (d.jc c) c ≠ 0 := hd.w_base c
  have e0 : d.w j0 c = ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) • d.w (d.jc c) c :=
    d.x4v4_eq_smul hd c (hd.w_mem j0 c)
  have hr00 : ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) ≠ 0 := by
    intro h0
    apply hj0
    rw [e0, h0, zero_smul]
  have key : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) =
      ratio (Ω := Ω c) (d.w j c) (d.w j0 c) * ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) := by
    intro j
    have ej : d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c :=
      d.x4v4_eq_smul hd c (hd.w_mem j c)
    have hrj : ratio (Ω := Ω c) (d.w j c) (d.w j0 c) =
        ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) := by
      apply x4v4_ratio_spec hj0
      calc d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c := ej
        _ = (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) *
              ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) • d.w (d.jc c) c := by
            rw [div_mul_cancel₀ _ hr00]
        _ = (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) •
              (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) • d.w (d.jc c) c) := by
            rw [smul_smul]
        _ = _ := by rw [← e0]
    rw [hrj, div_mul_cancel₀ _ hr00]
  have hsum : d.rationalBaseRow c = (∑ j, d.sH c (MvPolynomial.X (0, j)) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) := by
    unfold Data.rationalBaseRow
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [key j, map_mul, mul_assoc]
  rw [hsum, AddValuation.map_mul, hunit, zero_add]
  first
    | rfl
    | simp [Data.Wres, AddValuation.comap_apply]

theorem ordMinMax_at_good_place (hd : d.AxH 𝒜) (c : ι) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
    (hv : d.admitted c (d.Wres c w)) (j0 : Fin (d.N + 1)) (hj0 : d.w j0 c ≠ 0)
    (hint : ∀ j, 0 ≤ d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)))
    (hunit : w (∑ j, d.sH c (MvPolynomial.X (0, j)) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0)
    {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.ordMM c (d.Wres c w) f =
      (w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) f (d.w (d.jc c) c)))).untopD 0 -
        (w (d.rationalBaseRow c)).untopD 0 := by
  rw [d.ordMinMax_eq_ratio_untop_sub hd c _ hv j0 hj0 hint hf hf0, d.valuation_genericRatio_eq_restriction hd c w j0 hj0 hunit]
  rfl

theorem exists_ne_zero_of_finsum_mem_ne_zero' {α M : Type*} [AddCommMonoid M] {s : Set α} {f : α → M}
    (h : ∑ᶠ i ∈ s, f i ≠ 0) : ∃ i ∈ s, f i ≠ 0 := by
  by_contra hne
  push_neg at hne
  exact h (by rw [finsum_mem_congr rfl hne, finsum_mem_zero])



theorem multiplicity_split_finsum (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.nPMM h c f p =
      (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)))) +
      d.nPMM h c (d.w (d.jc c) c) p := by
  exact d.x4v4_split hd h c hp hf hf0

theorem algebraMap_gen_ne_zero {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := fun h => d.gen_ne_zero_of_htOne hp
  ((IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)) (h.trans (map_zero _).symm))

theorem substituted_factorization_exists (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ∃ κ : K, κ ≠ 0 ∧ d.heightSubstitutionCondition h x c F κ := by
  set a := ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) with ha_def
  have hmem := d.linearCombination_mem_section hd x c
  have ha : a ≠ 0 := d.ratio_base_ne_zero hd c hmem (hx c)
  obtain ⟨κ1, hκ1, e1⟩ := d.SpecialFibreFactorization hd h c F hF x (hx c)
  obtain ⟨κ3, hκ3, e3⟩ := (d.norm_factorization hd h).1 c a ha
  set na : Ideal (KTp K d.D d.N) → ℤ := fun p =>
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w a) with hna
  have hsplit : ∀ p ∈ d.HtOne, d.nPMM h c (d.wx x c) p = na p + d.nPMM h c (d.w (d.jc c) c) p :=
    fun p hp => d.multiplicity_split_finsum hd h c hp hmem (hx c)
  have hyne : algebraMap (Ω c) (OmS (Ω c) d.D d.N) a ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (Ω c) (OmS (Ω c) d.D d.N)).injective).mpr ha
  have hSa := ((d.norm_by_places hd h c).2 _ hyne).1
  have hSj := (d.good_primes_properties hd h c).2.2.2 _ (hd.w_mem _ c) (hd.w_base c)
  set g : Ideal (KTp K d.D d.N) → KTf K d.D d.N := fun p =>
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) with hg
  have hfa : (d.HtOne ∩ Function.mulSupport fun p => g p ^ na p).Finite := by
    refine hSa.subset fun p hp => ⟨hp.1, ?_⟩
    have hn : na p ≠ 0 := by
      intro h0; apply hp.2; simp only [h0, zpow_zero]
    obtain ⟨w, hw, hne⟩ := exists_ne_zero_of_finsum_mem_ne_zero' hn
    refine ⟨w, hw.1, fun h0 => hne ?_⟩
    show (d.fze h c w : ℤ) * WithTop.untopD 0 (w _) = 0
    rw [h0]; simp
  have hfj : (d.HtOne ∩ Function.mulSupport fun p => g p ^ d.nPMM h c (d.w (d.jc c) c) p).Finite := by
    refine hSj.subset fun p hp => ⟨hp.1, ?_⟩
    intro h0; apply hp.2; simp only [h0, zpow_zero]
  have hprod : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), g p ^ d.nPMM h c (d.wx x c) p) =
      (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), g p ^ na p) *
        ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), g p ^ d.nPMM h c (d.w (d.jc c) c) p := by
    rw [← finprod_mem_mul_distrib' hfa hfj]
    refine finprod_mem_congr rfl fun p hp => ?_
    rw [hsplit p hp, zpow_add₀ (d.algebraMap_gen_ne_zero hp)]
  refine ⟨κ1 / κ3, div_ne_zero hκ1 hκ3, ?_⟩
  unfold heightSubstitutionCondition translatedForm
  rw [hF, e1, e3, hprod]
  unfold fZ
  have h3 : algebraMap K (KTf K d.D d.N) κ3 ≠ 0 := (map_ne_zero _).mpr hκ3
  rw [map_div₀]
  simp only [hg, hna]
  field_simp

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField ReciprocityTheory.MultiplicativeHeights

theorem isMultiHomogeneous_mul' {R : Type*} [CommSemiring R] {B n : ℕ} {a a' : Fin B → ℕ}
    {f g : MvPolynomial (Fin B × Fin n) R} (hf : IsMultiHomogeneous a f)
    (hg : IsMultiHomogeneous a' g) : IsMultiHomogeneous (a + a') (f * g) := by
  classical
  unfold IsMultiHomogeneous at *
  intro s hs b
  obtain ⟨s1, hs1, s2, hs2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hs)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf s1 hs1 b, hg s2 hs2 b]

theorem isMultiHomogeneous_one {R : Type*} [CommSemiring R] {B n : ℕ} :
    IsMultiHomogeneous (0 : Fin B → ℕ) (1 : MvPolynomial (Fin B × Fin n) R) := by
  classical
  unfold IsMultiHomogeneous
  intro s hs b
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hs
  split_ifs at hs with h
  · subst h
    simp
  · exact absurd rfl hs

theorem height_one_eq_zero {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) :
    h0 (1 : MvPolynomial (Fin B × Fin n) K) = 0 := by
  classical
  first
    | simp [h0, gaussAbs, blockSphereMean]
    | simp [h0, gaussAbs, blockSphereMean, MvPolynomial.support_one]

theorem height_pow_multiHomogeneous {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n)
    {g : MvPolynomial (Fin B × Fin n) K} {a : Fin B → ℕ} (hg0 : g ≠ 0)
    (hg : IsMultiHomogeneous a g) (e : ℕ) :
    g ^ e ≠ 0 ∧ IsMultiHomogeneous (e • a) (g ^ e) ∧ h0 (g ^ e) = e * h0 g := by
  induction e with
  | zero => simp [height_one_eq_zero hn, isMultiHomogeneous_one]
  | succ e ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨pow_ne_zero _ hg0, ?_, ?_⟩
    · rw [pow_succ, succ_nsmul]; exact isMultiHomogeneous_mul' h2 hg
    · rw [pow_succ, (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K B n _ _ _ _ hn h1 hg0 h2 hg).1, h3]
      push_cast; ring

theorem height_prod_pow_multiHomogeneous {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) {ι' : Type*}
    (T : Finset ι') (g : ι' → MvPolynomial (Fin B × Fin n) K) (e : ι' → ℕ)
    (hg : ∀ i ∈ T, g i ≠ 0 ∧ ∃ a, IsMultiHomogeneous a (g i)) :
    (∏ i ∈ T, g i ^ e i) ≠ 0 ∧ (∃ a, IsMultiHomogeneous a (∏ i ∈ T, g i ^ e i)) ∧
      h0 (∏ i ∈ T, g i ^ e i) = ∑ i ∈ T, (e i : ℝ) * h0 (g i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [height_one_eq_zero hn]; exact ⟨0, isMultiHomogeneous_one⟩
  | insert q T hq ih =>
    obtain ⟨h1, ⟨a1, h2⟩, h3⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    obtain ⟨hq0, aq, hqa⟩ := hg q (Finset.mem_insert_self q T)
    obtain ⟨p1, p2, p3⟩ := height_pow_multiHomogeneous hn hq0 hqa (e q)
    rw [Finset.prod_insert hq, Finset.sum_insert hq]
    refine ⟨mul_ne_zero p1 h1, ⟨_, isMultiHomogeneous_mul' p2 h2⟩, ?_⟩
    rw [(ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K B n _ _ _ _ hn p1 h1 p2 h2).1, p3, h3]

namespace Data

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

variable (d : Data K ι Ω WT A)

private lemma ratio_eq_of_eq_smul' {Ω' V : Type*} [Field Ω'] [AddCommGroup V] [Module Ω' V] {f g : V} {a : Ω'}
    (hg : g ≠ 0) (h : f = a • g) : ratio f g = a := by
  have hex : ∃ b : Ω', f = b • g := ⟨a, h⟩
  unfold ratio
  rw [dif_pos hex]
  have hc := hex.choose_spec
  exact smul_left_injective Ω' hg (hc.symm.trans h)

theorem ratio_linearCombination_expand (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) :
    ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) =
      ∑ j, algebraMap K (Ω c) (x j) * ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) := by
  haveI := hd.tower c
  have hg : d.w (d.jc c) c ≠ 0 := hd.w_base c
  have hspan : ∀ f ∈ 𝒜 c d.wL, ∃ a : Ω c, f = a • d.w (d.jc c) c := by
    intro f hf
    have hne : (⟨d.w (d.jc c) c, hd.w_mem _ c⟩ : 𝒜 c d.wL) ≠ 0 := by
      intro h0
      exact hg (congrArg Subtype.val h0)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp (hd.finrank_one c d.wL) ⟨f, hf⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  choose r hr using fun j => hspan (d.w j c) (hd.w_mem j c)
  have hrat : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = r j := fun j => ratio_eq_of_eq_smul' hg (hr j)
  simp only [hrat]
  apply ratio_eq_of_eq_smul' hg
  rw [Finset.sum_smul]
  unfold Data.wx
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.smul_apply, mul_smul, algebraMap_smul]
  conv_lhs => rw [hr j]

theorem untopD_le_untopD {u v : WithTop ℤ} (hu : u ≠ ⊤) (hv : v ≠ ⊤) (h : u ≤ v) :
    u.untopD 0 ≤ v.untopD 0 := by
  lift u to ℤ using hu
  lift v to ℤ using hv
  simpa using h

theorem ordMinMax_nonneg (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K) (c : ι)
    (hx : d.wx x c ≠ 0) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.GoodP c p) :
    0 ≤ d.ordMM c (d.Wres c w) (d.wx x c) := by
  rcases d.PlaceTrivialOrPositive hd h c p hp w hw.1 with htr | ⟨hA, htriv, j0, hj0, hint, _⟩
  · obtain ⟨a, ha, hne⟩ := hw.2
    exact absurd (htr a ha) hne
  have hmem := d.linearCombination_mem_section hd x c
  rw [d.ordMinMax_eq_ratio_untop_sub hd c _ hA j0 hj0 hint hmem hx, sub_nonneg]
  set v := d.Wres c w
  have hb := hd.w_base c
  have hm := hd.w_mem (d.jc c) c
  apply untopD_le_untopD (hA.1.1 _ (d.ratio_base_ne_zero hd c (hd.w_mem j0 c) hj0))
    (hA.1.1 _ (d.ratio_base_ne_zero hd c hmem hx))
  rw [d.ratio_linearCombination_expand hd x c]
  apply AddValuation.map_le_sum
  intro j _
  by_cases hxj : x j = 0
  · rw [hxj, map_zero, zero_mul, v.map_zero]; exact le_top
  rw [v.map_mul, htriv _ hxj, zero_add,
    d.ratio_mul_ratio_height hd c (hd.w_mem j c) (hd.w_mem j0 c) hm hj0 hb, v.map_mul]
  exact le_add_of_nonneg_left (hint j)

theorem multiplicity_nonneg (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K) (c : ι)
    (hx : d.wx x c ≠ 0) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    0 ≤ d.nPMM h c (d.wx x c) p := by
  unfold Data.nPMM
  apply finsum_nonneg
  intro w
  apply finsum_nonneg
  intro hw
  refine mul_nonneg ?_ (d.ordMinMax_nonneg hd h x c hx hp hw)
  first
    | positivity
    | exact Nat.cast_nonneg _

theorem height_substituted_eq_finsum (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    d.translatedForm x F ≠ 0 ∧
    ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.nPMM h c (d.wx x c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) =
      ReciprocityTheory.MultiplicativeHeights.h0 (d.translatedForm x F) := by
  classical
  have hmem := d.linearCombination_mem_section hd x c
  obtain ⟨κ1, hκ1, e1⟩ := d.SpecialFibreFactorization hd h c F hF x (hx c)
  have hS := (d.good_primes_properties hd h c).2.2.2 _ hmem (hx c)
  set T := hS.toFinset
  set n : Ideal (KTp K d.D d.N) → ℤ := fun p => d.nPMM h c (d.wx x c) p with hn
  have hT : ∀ p, p ∈ T ↔ p ∈ d.HtOne ∧ n p ≠ 0 := fun p => by rw [Set.Finite.mem_toFinset]; rfl
  have hgood : ∀ p ∈ T, d.gen p ≠ 0 ∧ ∃ a, IsMultiHomogeneous a (d.gen p) := by
    intro p hpT
    obtain ⟨hp, hnp⟩ := (hT p).mp hpT
    refine ⟨d.gen_ne_zero_of_htOne hp, _, (d.good_primes_properties hd h c).2.1 p hp ?_⟩
    obtain ⟨w, hw, _⟩ := exists_ne_zero_of_finsum_mem_ne_zero' hnp
    exact ⟨w, hw⟩
  set e : Ideal (KTp K d.D d.N) → ℕ := fun p => (n p).toNat with he
  have hne : ∀ p ∈ d.HtOne, n p = (e p : ℤ) := fun p hp =>
    (Int.toNat_of_nonneg (d.multiplicity_nonneg hd h x c (hx c) hp)).symm
  obtain ⟨P0, ⟨aP, hPm⟩, hPh⟩ := height_prod_pow_multiHomogeneous (K := K) (Nat.succ_pos d.N) T (fun p => d.gen p) e hgood
  have hprod : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ n p) =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (∏ p ∈ T, d.gen p ^ e p) := by
    rw [finprod_mem_eq_prod_of_inter_mulSupport_eq _ (t := T), map_prod]
    · refine Finset.prod_congr rfl fun p hpT => ?_
      rw [hne p ((hT p).mp hpT).1, zpow_natCast, map_pow]
    · ext p
      simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.mem_coe, hT]
      constructor
      · rintro ⟨hp, h1⟩
        refine ⟨⟨hp, fun h0 => h1 ?_⟩, h1⟩
        rw [h0, zpow_zero]
      · rintro ⟨⟨hp, _⟩, h1⟩; exact ⟨hp, h1⟩
  have hFx : d.translatedForm x F = MvPolynomial.C κ1 * ∏ p ∈ T, d.gen p ^ e p := by
    apply IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
    unfold translatedForm
    rw [e1, hprod, map_mul, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N)]
  refine ⟨by rw [hFx]; exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr hκ1) P0, ?_⟩
  rw [hFx, (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K (d.D + 1) (d.N + 1) aP aP _ _ (Nat.succ_pos _) P0 P0 hPm hPm).2
    κ1 hκ1, hPh]
  rw [finsum_mem_eq_sum_of_inter_support_eq _ (t := T)]
  · refine Finset.sum_congr rfl fun p hpT => ?_
    rw [show ((d.nPMM h c (d.wx x c) p : ℤ) : ℝ) = ((e p : ℤ) : ℝ) from
      congrArg _ (hne p ((hT p).mp hpT).1)]
    simp
  · ext p
    simp only [Set.mem_inter_iff, Function.mem_support, Finset.mem_coe, hT]
    constructor
    · rintro ⟨hp, h1⟩
      refine ⟨⟨hp, fun h0 => h1 ?_⟩, h1⟩
      simp only [hn] at h0; rw [h0]; simp
    · rintro ⟨⟨hp, _⟩, h1⟩; exact ⟨hp, h1⟩

theorem fZ_and_substituted_ne_zero (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    F ≠ 0 ∧ d.translatedForm x F ≠ 0 := by
  have hne := (d.height_substituted_eq_finsum hd h x hx c F hF).1
  refine ⟨fun h0 => hne ?_, hne⟩
  rw [h0]
  first
    | simp [Data.translatedForm]
    | exact map_zero _

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

theorem eval_substituted_eq_eval_update (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) (sg : K →+* ℂ)
    (y : Fin (d.D + 1) × Fin (d.N + 1) → ℂ) :
    MvPolynomial.eval y (MvPolynomial.map sg (d.translatedForm x F)) =
      MvPolynomial.eval (fun v => if v.1 = 0 then sg (x v.2) else y v) (MvPolynomial.map sg F) := by
  unfold translatedForm
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.map_X, MvPolynomial.eval_X]
    congr 1
    by_cases hv : v.1 = 0 <;> simp [hv]

theorem eval_substituted_shift_invariant (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) (sg : K →+* ℂ)
    (t0 : Fin (d.N + 1) → ℂ) (z : BlockSphere d.D (d.N + 1)) :
    MvPolynomial.eval (hintPt t0 z) (MvPolynomial.map sg (d.translatedForm x F)) =
      MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F)) := by
  rw [eval_substituted_eq_eval_update, eval_substituted_eq_eval_update]
  refine congrArg (fun y => MvPolynomial.eval y (MvPolynomial.map sg F)) (funext fun v => ?_)
  by_cases hv : v.1 = 0
  · simp only [hv, ↓reduceIte]
  · simp only [hv, ↓reduceIte]
    obtain ⟨a, b⟩ := v
    cases a using Fin.cases with
    | zero => exact absurd rfl hv
    | succ i => rfl

theorem sphereMean_substituted_eq_integral (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) (sg : K →+* ℂ) :
    blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg (d.translatedForm x F)) =
      ∫ z, Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F))‖
        ∂(blockSphereProb d.D (d.N + 1)) := by
  have hpt : ∀ z : BlockSphere (d.D + 1) (d.N + 1),
      MvPolynomial.eval (blockPoint z) (MvPolynomial.map sg (d.translatedForm x F)) =
        MvPolynomial.eval (hintPt 0 (Fin.tail z)) (MvPolynomial.map sg (d.translatedForm x F)) := by
    intro z
    rw [← eval_substituted_shift_invariant d x F sg (spherePoint (z 0)) (Fin.tail z)]
    refine congrArg (fun y => MvPolynomial.eval y (MvPolynomial.map sg (d.translatedForm x F)))
      (funext fun v => ?_)
    obtain ⟨a, b⟩ := v
    cases a using Fin.cases with
    | zero => rfl
    | succ i => rfl
  have key : ∀ g : (Fin d.D → UnitSphereC (d.N + 1)) → ℝ,
      ∫ z, g (Fin.tail z) ∂(Measure.pi fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) =
        ∫ w, g w ∂(Measure.pi fun _ : Fin d.D => sphereProb (d.N + 1)) := by
    intro g
    haveI hpr : IsProbabilityMeasure (sphereProb (d.N + 1)) :=
      ReciprocityTheory.MultiplicativeHeights.isProbabilityMeasure_sphereProb (Nat.succ_pos _)
    haveI hfin : IsFiniteMeasure (sphereProb (d.N + 1)) :=
      ⟨by rw [MeasureTheory.measure_univ]; exact ENNReal.one_lt_top⟩
    haveI hsf : SigmaFinite (sphereProb (d.N + 1)) :=
      @MeasureTheory.IsFiniteMeasure.toSigmaFinite _ _ _ hfin
    haveI hsf' : ∀ i : Fin (d.D + 1), SigmaFinite ((fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) i) :=
      fun _ => hsf
    have hmp := MeasureTheory.measurePreserving_piFinSuccAbove
      (fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) 0
    calc ∫ z, g (Fin.tail z) ∂(Measure.pi fun _ : Fin (d.D + 1) => sphereProb (d.N + 1))
        = ∫ z, (fun p : UnitSphereC (d.N + 1) × (Fin d.D → UnitSphereC (d.N + 1)) => g p.2)
            (MeasurableEquiv.piFinSuccAbove (fun _ => UnitSphereC (d.N + 1)) 0 z)
            ∂(Measure.pi fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) := by
          congr 1
      _ = ∫ p, g p.2 ∂((sphereProb (d.N + 1)).prod
            (Measure.pi fun _ : Fin d.D => sphereProb (d.N + 1))) :=
          hmp.integral_comp' (fun p : UnitSphereC (d.N + 1) × (Fin d.D → UnitSphereC (d.N + 1)) => g p.2)
      _ = ∫ w, g w ∂(Measure.pi fun _ : Fin d.D => sphereProb (d.N + 1)) := by
          rw [MeasureTheory.integral_fun_snd]
          simp
  unfold blockSphereMean blockSphereProb
  simp_rw [hpt]
  exact key (fun w => Real.log ‖MvPolynomial.eval (hintPt 0 w) (MvPolynomial.map sg (d.translatedForm x F))‖)

theorem sphereMean_fubini {F : MvPolynomial (Fin (d.D + 1) × Fin (d.N + 1)) ℂ} {a : Fin (d.D + 1) → ℕ}
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    blockSphereMean (d.D + 1) (d.N + 1) F =
      ∫ z, (∫ s, Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) F‖ ∂(sphereProb (d.N + 1)))
        ∂(blockSphereProb d.D (d.N + 1)) := by
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  haveI := sphereMeasure_isProbability hn
  haveI := blockSphereMeasure_isProbability (B := d.D) hn
  set G : UnitSphereC (d.N + 1) × BlockSphere d.D (d.N + 1) → ℝ :=
    fun p => Real.log ‖MvPolynomial.eval (hintPt (spherePoint p.1) p.2) F‖ with hG
  have hmp := hint_mpSplit d.D (d.N + 1) hn
  have hint : Integrable G ((sphereProb (d.N + 1)).prod (blockSphereProb d.D (d.N + 1))) := by
    rw [← hmp.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d.D + 1) => UnitSphereC (d.N + 1)) 0).measurableEmbedding]
    refine (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable (d.D + 1) (d.N + 1) a F hF0 hF).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply, hG]
    rw [hint_blockPoint_eq]
    rfl
  rw [← integral_prod_symm G hint]
  unfold blockSphereMean
  rw [← hmp.integral_comp
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d.D + 1) => UnitSphereC (d.N + 1)) 0).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [hG]
  rw [hint_blockPoint_eq]
  rfl

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

theorem archimedean_local_height_term (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N) (κ : K) (hκ : κ ≠ 0)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (hFne : F ≠ 0) (hs : d.heightSubstitutionCondition h x c F κ) (sg : K →+* ℂ) :
    d.localHeightAtEmbedding (d.wx x) c sg =
      blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg F) -
        blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg (d.translatedForm x F)) +
        Real.log ‖sg κ‖ + d.delc c * (harmonic d.N : ℝ) / 2 := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.omS_finite hd h c).1
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  haveI := sphereMeasure_isProbability hn
  haveI := blockSphereMeasure_isProbability (B := d.D) hn
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  set ra := ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) with hra
  have hmem := d.linearCombination_mem_section hd x c
  have hra0 : ra ≠ 0 := d.ratio_base_ne_zero hd c hmem (hx c)

  obtain ⟨κ3, hκ3, hN⟩ := (d.norm_factorization hd h).1 c ra hra0
  obtain ⟨a1, b1, ha1, hb1, hsplit1⟩ := d.hint_good_split hd h c _
    (fun p _ hp => d.hint_good_of_ne c p hp)
  rw [hsplit1] at hN
  have hNm0 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) ≠ 0 :=
    Algebra.norm_ne_zero_iff.2 ((map_ne_zero_iff _ (algebraMap (Ω c) _).injective).2 hra0)
  have hb10 : b1 ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero] at hN
    exact hNm0 hN
  have ha10 : a1 ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero] at hN
    exact hNm0 hN
  set a1' : KTp K d.D d.N := MvPolynomial.C κ3 * a1 with ha1'
  have hkey1 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a1' := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb10
    rw [hN, ha1', map_mul, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    field_simp

  obtain ⟨F', hF', hF'0, hFmh, -, -⟩ := d.componentForm_properties hd h c
  have hFF : F' = F := hinj (hF'.trans hF.symm)
  subst hFF
  obtain ⟨a2, b2, ha2, hb2, hsplit2⟩ := d.hint_good_split hd h c
    (fun p => d.nPMM h c (d.w (d.jc c) c) p)
    (fun p _ hp => d.hint_good_of_ne c p
      (f := fun w => (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c)) hp)
  have hfZ : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F' =
      Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2 /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b2) := by
    rw [hF, ← hsplit2]; rfl
  have hb20 : b2 ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hFne (hinj hfZ)
  have ha20 : a2 ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hFne (hinj hfZ)
  have hkey2 : Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2 =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F' * b2) := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b2 ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb20
    rw [map_mul, hfZ]
    field_simp

  have hpoly : MvPolynomial.C κ * a1' * a2 = d.translatedForm x F' * b2 * b1 := by
    apply mul_left_cancel₀ hFne
    apply hinj
    have hs' := hs
    unfold heightSubstitutionCondition at hs'
    rw [map_mul] at hkey2
    have hCk : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C κ) =
        algebraMap K (KTf K d.D d.N) κ := by
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    simp only [map_mul, hCk]
    linear_combination (-(algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F' *
        algebraMap K (KTf K d.D d.N) κ * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2)) * hkey1 +
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2) * hs' +
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.translatedForm x F') *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1) * hkey2

  have hmi := MvPolynomial.map_injective (σ := TVar d.D d.N) sg sg.injective
  have hFc0 : MvPolynomial.map sg F' ≠ 0 := (map_ne_zero_iff _ hmi).2 hFne
  have ha1c : MvPolynomial.map sg a1' ≠ 0 :=
    (map_ne_zero_iff _ hmi).2 (mul_ne_zero (by simpa using hκ3) ha10)
  have hb1c : MvPolynomial.map sg b1 ≠ 0 := (map_ne_zero_iff _ hmi).2 hb10
  have ha2c : MvPolynomial.map sg a2 ≠ 0 := (map_ne_zero_iff _ hmi).2 ha20
  have hb2c : MvPolynomial.map sg b2 ≠ 0 := (map_ne_zero_iff _ hmi).2 hb20
  have hFcmh := isMultiHomogeneous_map_ring _ F' hFmh sg
  obtain ⟨αa1, hαa10, hαa1⟩ := hintMH_map (hintMH_C_mul κ3 ha1) sg
  obtain ⟨αb1, hαb10, hαb1⟩ := hintMH_map hb1 sg
  obtain ⟨αa2, hαa20, hαa2⟩ := hintMH_map ha2 sg
  obtain ⟨αb2, hαb20, hαb2⟩ := hintMH_map hb2 sg
  have I1 := hint_fubini hn hFc0 hFcmh
  have Ia1 := hint_logInt_tail hn ha1c hαa1 hαa10 0
  have Ib1 := hint_logInt_tail hn hb1c hαb1 hαb10 0
  have Ia2 := hint_logInt_tail hn ha2c hαa2 hαa20 0
  have Ib2 := hint_logInt_tail hn hb2c hαb2 hαb20 0
  have hind : ∀ (z : BlockSphere d.D (d.N + 1))
      (q : MvPolynomial (Fin (d.D + 1) × Fin (d.N + 1)) ℂ) (α : Fin (d.D + 1) → ℕ),
      α 0 = 0 → IsMultiHomogeneous α q → ∀ t0 : Fin (d.N + 1) → ℂ,
      MvPolynomial.eval (hintPt t0 z) q = MvPolynomial.eval (hintPt 0 z) q := by
    intro z q α h0 hq t0
    refine hint_eval_indep hq h0 _ _ ?_
    rintro ⟨i, j⟩ hi
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hi
    rfl

  have hpt : ∀ᵐ z ∂(blockSphereProb d.D (d.N + 1)),
      (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => spherePoint (z i) j)),
        -Real.log (d.nrm c d.wL (d.wx x c) P / d.be c P)) =
        (∫ s, Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F')‖
            ∂(sphereProb (d.N + 1))) -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F'))‖ +
          Real.log ‖sg κ‖ + d.delc c * (harmonic d.N : ℝ) / 2 ∧
      Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F'))‖ =
        Real.log ‖sg κ‖ + Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a1')‖ +
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b2)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b1)‖ := by
    filter_upwards [d.norm_at_sg hd h c sg, hint_ae_tail hn hb1c hαb1 hαb10 0,
      hint_ae_tail hn hb2c hαb2 hαb20 0, hint_ae_tail hn ha2c hαa2 hαa20 0] with z hz hb1z hb2z ha2z
    obtain ⟨hfin, hcard, hcl1, hcl2⟩ := hz
    set S := d.ST c sg (d.tOf z) with hS
    have hpe := congrArg (fun q => MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg q)) hpoly
    simp only [map_mul, MvPolynomial.map_C, MvPolynomial.eval_C] at hpe

    have hb1z' : d.evT sg 0 (d.tOf z) b1 ≠ 0 := by rw [hint_evT_eq]; exact hb1z
    have hprod1 := hcl1 ra a1' b1 0 hra0 hb10 hkey1 hb1z'
    have hPra : ∀ P ∈ S, P ra ≠ 0 := fun P _ => (map_ne_zero_iff P P.injective).2 hra0
    have hprod0 : (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S), P ra) ≠ 0 := by
      rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
      exact Finset.prod_ne_zero_iff.2 fun P hP => hPra P (hfin.mem_toFinset.1 hP)
    have ha1z : d.evT sg 0 (d.tOf z) a1' ≠ 0 := by
      intro h0; rw [h0, zero_div] at hprod1; exact hprod0 hprod1.symm
    rw [hint_evT_eq, hint_evT_eq] at hprod1
    rw [hint_evT_eq] at ha1z
    have hsum1 : ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S), Real.log ‖P ra‖ =
        Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a1')‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b1)‖ := by
      rw [hint_log_finprod _ hfin _ hPra, ← hprod1, norm_div,
        Real.log_div (norm_ne_zero_iff.2 ha1z) (norm_ne_zero_iff.2 hb1z)]

    have hsk : sg κ ≠ 0 := (map_ne_zero sg).2 hκ
    have hlhs0 : sg κ * MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a1') *
        MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hsk ha1z) ha2z
    rw [hpe] at hlhs0
    have hFXz : MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F')) ≠ 0 := by
      intro h0; apply hlhs0; rw [h0]; ring
    have hlogFX : Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F'))‖ =
        Real.log ‖sg κ‖ + Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a1')‖ +
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b2)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b1)‖ := by
      have hl := congrArg (fun w : ℂ => Real.log ‖w‖) hpe
      simp only [norm_mul] at hl
      rw [Real.log_mul (by positivity) (norm_ne_zero_iff.2 ha2z),
        Real.log_mul (norm_ne_zero_iff.2 hsk) (norm_ne_zero_iff.2 ha1z),
        Real.log_mul (by positivity) (norm_ne_zero_iff.2 hb1z),
        Real.log_mul (norm_ne_zero_iff.2 hFXz) (norm_ne_zero_iff.2 hb2z)] at hl
      linarith
    refine ⟨?_, hlogFX⟩

    have hlin : ∀ᵐ s ∂(sphereProb (d.N + 1)), ∀ P ∈ S,
        ∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j ≠ 0 :=
      (Filter.eventually_all_finite hfin).2 fun P _ => hint_lin_ae _ (d.hint_U_coord_ne hd c P)
    have hptU : ∀ᵐ s ∂(sphereProb (d.N + 1)),
        Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F')‖ =
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2)‖ -
            Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b2)‖ +
            ∑ P ∈ hfin.toFinset,
              Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j‖ := by
      filter_upwards [hlin] with s hs
      have haz' : d.evT sg (spherePoint s) (d.tOf z) a2 ≠ 0 := by
        rw [hint_evT_eq, hind z _ _ hαa20 hαa2]; exact ha2z
      have hq := hcl2 (F' * b2) a2 (spherePoint s) ha20 hkey2 haz'
      rw [hint_evT_eq, hint_evT_eq, map_mul, map_mul, hind z _ _ hαa20 hαa2,
        hind z (MvPolynomial.map sg b2) _ hαb20 hαb2] at hq
      have hL : ∀ P ∈ S, (∑ j, spherePoint s j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) ≠ 0 := by
        intro P hP
        have := hs P hP
        simpa [hintU, mul_comm] using this
      have hprod0' : (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S),
          ∑ j, spherePoint s j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) ≠ 0 := by
        rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
        exact Finset.prod_ne_zero_iff.2 fun P hP => hL P (hfin.mem_toFinset.1 hP)
      have heq : MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F') =
          MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2) *
            (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S),
              ∑ j, spherePoint s j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) /
            MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b2) := by
        rw [← hq]; field_simp
      rw [heq, norm_div, norm_mul, Real.log_div (by simpa using mul_ne_zero ha2z hprod0')
        (norm_ne_zero_iff.2 hb2z), Real.log_mul (norm_ne_zero_iff.2 ha2z)
        (norm_ne_zero_iff.2 hprod0'), ← hint_log_finprod _ hfin _ hL,
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
    have hval : ∀ P ∈ hfin.toFinset, ∫ s, Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j *
        spherePoint s j‖ ∂(sphereProb (d.N + 1)) = Real.log ‖d.hintU c P‖ - (harmonic d.N : ℝ) / 2 := by
      intro P _
      have := (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLinLog (d.N + 1) (d.hintU c P)
        (fun h0 => d.hint_U_coord_ne hd c P (by rw [h0]; rfl))).2
      simpa using this
    have hintS : ∫ s, Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F')‖
        ∂(sphereProb (d.N + 1)) =
        Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b2)‖ +
          ∑ P ∈ hfin.toFinset, Real.log ‖d.hintU c P‖ - d.delc c * (harmonic d.N : ℝ) / 2 := by
      rw [integral_congr_ae hptU, integral_add (integrable_const _) (integrable_finset_sum _ hInt),
        integral_const, integral_finset_sum _ hInt, Finset.sum_congr rfl hval, Finset.sum_sub_distrib,
        Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hfin, hcard]
      simp only [probReal_univ, one_smul, nsmul_eq_mul]
      ring

    have hPe : ∀ P : Ω c →+* ℂ, -Real.log (d.nrm c d.wL (d.wx x c) P / d.be c P) =
        Real.log ‖d.hintU c P‖ - Real.log ‖P ra‖ := by
      intro P
      have hw := d.eq_ratio_base_smul hd c hmem
      have hn1 : d.nrm c d.wL (d.wx x c) P = ‖P ra‖ * d.nrm c d.wL (d.w (d.jc c) c) P := by
        conv_lhs => rw [hw]
        exact hd.nrm_smul c P _ (hd.w_mem _ c) (hd.w_base c) hra0
      have hpos := hd.nrm_pos c P (hd.w_mem _ c) (hd.w_base c)
      have hU := d.hint_one_le_U hd c P
      rw [hn1, d.hint_be_eq hd c P, mul_comm ‖P ra‖, mul_div_mul_left _ _ hpos.ne',
        Real.log_div (norm_ne_zero_iff.2 ((map_ne_zero P).2 hra0)) (by linarith)]
      ring
    change ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S), -Real.log (d.nrm c d.wL (d.wx x c) P / d.be c P) = _
    have hsum1' : ∑ P ∈ hfin.toFinset, Real.log ‖P ra‖ =
        Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a1')‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b1)‖ := by
      rw [← finsum_mem_eq_finite_toFinset_sum _ hfin]; exact hsum1
    rw [finsum_mem_congr rfl fun P _ => hPe P, finsum_mem_eq_finite_toFinset_sum _ hfin,
      Finset.sum_sub_distrib, hsum1', hintS, hlogFX]
    ring

  have IFX : Integrable (fun z : BlockSphere d.D (d.N + 1) =>
      Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F'))‖)
      (blockSphereProb d.D (d.N + 1)) := by
    refine (((((integrable_const (Real.log ‖sg κ‖)).add Ia1).add Ia2).sub Ib2).sub Ib1).congr ?_
    filter_upwards [hpt] with z hz
    rw [hz.2]; rfl
  unfold localHeightAtEmbedding
  rw [integral_congr_ae (hpt.mono fun z hz => hz.1)]
  rw [integral_add ?_ (integrable_const _), integral_add ?_ (integrable_const _),
    integral_sub I1 IFX, integral_const, integral_const, d.sphereMean_fubini hFc0 hFcmh, d.sphereMean_substituted_eq_integral]
  · simp only [probReal_univ, one_smul]
  · exact I1.sub IFX
  · exact (I1.sub IFX).add (integrable_const _)

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

theorem finite_local_height_term (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N) (κ : K) (hκ : κ ≠ 0)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (hFne : F ≠ 0) (hFx : d.translatedForm x F ≠ 0) (hs : d.heightSubstitutionCondition h x c F κ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    d.localHeightAtPrime h (d.wx x) c la * logNorm la =
      Real.log (gaussAbs (FinitePlace.mk la) F) -
        Real.log (gaussAbs (FinitePlace.mk la) (d.translatedForm x F)) +
        Real.log (FinitePlace.mk la κ) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.omS_finite hd h c).1
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  haveI := sphereMeasure_isProbability hn
  haveI := blockSphereMeasure_isProbability (B := d.D) hn
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  set ra := ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) with hra
  have hmem := d.linearCombination_mem_section hd x c
  have hra0 : ra ≠ 0 := d.ratio_base_ne_zero hd c hmem (hx c)

  obtain ⟨κ3, hκ3, hN⟩ := (d.norm_factorization hd h).1 c ra hra0
  obtain ⟨a1, b1, ha1, hb1, hsplit1⟩ := d.hint_good_split hd h c _
    (fun p _ hp => d.hint_good_of_ne c p hp)
  rw [hsplit1] at hN
  have hNm0 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) ≠ 0 :=
    Algebra.norm_ne_zero_iff.2 ((map_ne_zero_iff _ (algebraMap (Ω c) _).injective).2 hra0)
  have hb10 : b1 ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero] at hN
    exact hNm0 hN
  have ha10 : a1 ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero] at hN
    exact hNm0 hN
  set a1' : KTp K d.D d.N := MvPolynomial.C κ3 * a1 with ha1'
  have hkey1 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a1' := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb10
    rw [hN, ha1', map_mul, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    field_simp

  obtain ⟨F', hF', hF'0, hFmh, -, -⟩ := d.componentForm_properties hd h c
  have hFF : F' = F := hinj (hF'.trans hF.symm)
  subst hFF
  obtain ⟨a2, b2, ha2, hb2, hsplit2⟩ := d.hint_good_split hd h c
    (fun p => d.nPMM h c (d.w (d.jc c) c) p)
    (fun p _ hp => d.hint_good_of_ne c p
      (f := fun w => (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c)) hp)
  have hfZ : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F' =
      Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2 /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b2) := by
    rw [hF, ← hsplit2]; rfl
  have hb20 : b2 ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hFne (hinj hfZ)
  have ha20 : a2 ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hFne (hinj hfZ)
  have hkey2 : Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2 =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F' * b2) := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b2 ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb20
    rw [map_mul, hfZ]
    field_simp

  have hpoly : MvPolynomial.C κ * a1' * a2 = d.translatedForm x F' * b2 * b1 := by
    apply mul_left_cancel₀ hFne
    apply hinj
    have hs' := hs
    unfold heightSubstitutionCondition at hs'
    rw [map_mul] at hkey2
    have hCk : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C κ) =
        algebraMap K (KTf K d.D d.N) κ := by
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    simp only [map_mul, hCk]
    linear_combination (-(algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F' *
        algebraMap K (KTf K d.D d.N) κ * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2)) * hkey1 +
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2) * hs' +
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.translatedForm x F') *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1) * hkey2

  have hfin := (d.places_over_la hd h la c).1
  have hZ : ∀ w ∈ d.PlOver la c, d.ordMM c (d.Wres c w) (d.wx x c) =
      (w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra)).untopD 0 - (w (d.rationalBaseRow c)).untopD 0 := by
    intro w hw
    obtain ⟨hv, -, j0, hj0, hint, hunit⟩ := d.admissible_over_prime hd h la c w hw
    exact d.ordMinMax_at_good_place hd c w hv j0 hj0 hint hunit hmem (hx c)
  have hNla : d.localHeightAtPrime h (d.wx x) c la =
      (d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) : ℝ) - (d.nLa h c la (d.rationalBaseRow c) : ℝ) := by
    unfold localHeightAtPrime nLa
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hZ w (hfin.mem_toFinset.1 hw)]; push_cast; ring

  have ha1'0 : a1' ≠ 0 := mul_ne_zero (by simpa using hκ3) ha10
  have hraS : algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (Ω c) _).injective).2 hra0
  have hw0 : d.rationalBaseRow c ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero, zero_mul] at hkey2
    exact mul_ne_zero hFne hb20 (hinj (hkey2.symm.trans (map_zero _).symm))
  have p1 := d.pf_fin hd h c _ hraS a1' b1 ha1'0 hb10 hkey1 la
  have p2 := d.pf_fin hd h c _ hw0 (F' * b2) a2 (mul_ne_zero hFne hb20) ha20 hkey2 la

  set v := FinitePlace.mk la with hv
  have hg := congrArg (gaussAbs v) hpoly
  rw [gauss_abs_mul v _ _ (mul_ne_zero (by simpa using hκ) ha1'0) ha20,
    gauss_abs_mul v _ _ (by simpa using hκ) ha1'0, HeightMultiplicativity.gaussAbs_C,
    gauss_abs_mul v _ _ (mul_ne_zero hFx hb20) hb10,
    gauss_abs_mul v _ _ hFx hb20] at hg
  have hl := congrArg Real.log hg
  have hk0 : 0 < v κ := (FinitePlace.pos_iff).2 hκ
  have q1 := gauss_abs_pos_of_ne_zero v a1' ha1'0
  have q2 := gauss_abs_pos_of_ne_zero v a2 ha20
  have q3 := gauss_abs_pos_of_ne_zero v _ hFx
  have q4 := gauss_abs_pos_of_ne_zero v b2 hb20
  have q5 := gauss_abs_pos_of_ne_zero v b1 hb10
  have q6 := gauss_abs_pos_of_ne_zero v F' hFne
  rw [Real.log_mul (by positivity) q2.ne', Real.log_mul hk0.ne' q1.ne',
    Real.log_mul (by positivity) q5.ne', Real.log_mul q3.ne' q4.ne'] at hl
  rw [gauss_abs_mul v _ _ hFne hb20, Real.log_mul q6.ne' q4.ne'] at p2
  rw [hNla]
  linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

theorem finsum_finset_sum_comm' {α β : Type*} (s : Finset β) (f : β → α → ℝ)
    (hf : ∀ b ∈ s, (Function.support (f b)).Finite) :
    ∑ᶠ a, ∑ b ∈ s, f b a = ∑ b ∈ s, ∑ᶠ a, f b a := by
  first
    | exact finsum_sum_comm s (fun a b => f b a) hf
    | (classical
       induction s using Finset.induction_on with
       | empty => simp
       | insert b s hb ih =>
         simp only [Finset.sum_insert hb]
         rw [finsum_add_distrib (hf b (Finset.mem_insert_self b s))
           ((s.finite_toSet.biUnion fun b' hb' => hf b' (Finset.mem_insert_of_mem hb')).subset
             (Function.support_finset_sum)), ih fun b' hb' => hf b' (Finset.mem_insert_of_mem hb')])

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem height_decomposition_local_terms (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    (Function.support fun la => d.localHeightAtPrime h (d.wx x) c la * logNorm la).Finite ∧
    (∑ᶠ la, d.localHeightAtPrime h (d.wx x) c la * logNorm la) / (Module.finrank ℚ K : ℝ) +
      meanK (d.localHeightAtEmbedding (d.wx x) c) +
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.nPMM h c (d.wx x c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) =
      ReciprocityTheory.MultiplicativeHeights.h0 F + d.delc c * (harmonic d.N : ℝ) / 2 := by
  obtain ⟨hFne, hFx⟩ := d.fZ_and_substituted_ne_zero hd h x hx c F hF
  obtain ⟨κ, hκ, hs⟩ := d.substituted_factorization_exists hd h x hx c F hF
  have hfin := d.finite_local_height_term hd h x hx c F κ hκ hF hFne hFx hs
  have harch := d.archimedean_local_height_term hd h x hx c F κ hκ hF hFne hs
  rw [(d.height_substituted_eq_finsum hd h x hx c F hF).2]
  set G : FinitePlace K → ℝ := fun v => Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v F) -
    Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v (d.translatedForm x F)) + Real.log (v κ) with hG
  have hg : (fun la => d.localHeightAtPrime h (d.wx x) c la * logNorm la) =
      fun la => G (FinitePlace.equivHeightOneSpectrum.symm la) := by
    funext la; rw [hfin la]; rfl
  have s1 := ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite F hFne
  have s2 := ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite _ hFx
  have s3 : (Function.support fun v : FinitePlace K => Real.log (v κ)).Finite := by
    refine (FinitePlace.hasFiniteMulSupport hκ).subset fun v hv => ?_
    intro h1; apply hv; simp only; rw [show v κ = 1 from h1, Real.log_one]
  have sG : (Function.support G).Finite := ((s1.union s2).union s3).subset (by
    intro v hv; by_contra hn; apply hv
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    simp only [hG, hn.1.1, hn.1.2, hn.2]; ring)
  have hsumG : ∑ᶠ la, d.localHeightAtPrime h (d.wx x) c la * logNorm la = ∑ᶠ v, G v := by
    rw [hg]; exact finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
  refine ⟨?_, ?_⟩
  · rw [hg]
    exact (sG.image FinitePlace.equivHeightOneSpectrum).subset (by
      intro la hla; exact ⟨FinitePlace.equivHeightOneSpectrum.symm la, hla, by simp⟩)
  rw [hsumG, hG, finsum_add_distrib ((s1.union s2).subset (Function.support_sub _ _)) s3,
    finsum_sub_distrib s1 s2]
  have hpf : (∑ᶠ v : FinitePlace K, Real.log (v κ)) + ∑ σ : K →+* ℂ, Real.log ‖σ κ‖ = 0 := by
    classical
    have hm := FinitePlace.hasFiniteMulSupport hκ
    set U := hm.toFinset
    have hsub1 : Function.mulSupport (fun v : FinitePlace K => v κ) ⊆ U := by
      intro v hv; exact hm.mem_toFinset.mpr hv
    have hsub2 : Function.support (fun v : FinitePlace K => Real.log (v κ)) ⊆ U := by
      intro v hv; apply hsub1; intro h1; apply hv; simp only; rw [show v κ = 1 from h1, Real.log_one]
    have hprod := FinitePlace.prod_eq_inv_abs_norm hκ
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub1] at hprod
    rw [finsum_eq_sum_of_support_subset _ hsub2, ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq κ hκ,
      ← Real.log_prod fun v _ => (FinitePlace.pos_iff.mpr hκ).ne', hprod]
    push_cast
    rw [Real.log_inv]; ring
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    rw [NumberField.Embeddings.card]
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold meanK ReciprocityTheory.MultiplicativeHeights.h0
  simp_rw [harch]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hcard]
  field_simp
  linarith [hpf]

theorem height_minMax_eq_sum_heights (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) :
    d.HgtMM h (d.wx x) = ∑ c, ReciprocityTheory.MultiplicativeHeights.h0 (F c) + d.del * (harmonic d.N : ℝ) / 2 := by
  have hc := fun c => d.height_decomposition_local_terms hd h hI2be x hx c (F c) (hF c)
  have hla : ∀ la, d.NlaMM h (d.wx x) la * logNorm la = ∑ c, d.localHeightAtPrime h (d.wx x) c la * logNorm la := by
    intro la
    simp only [NlaMM, localHeightAtPrime, Finset.sum_mul]
  have hsg : d.NsgMM (d.wx x) = fun sg => ∑ c, d.localHeightAtEmbedding (d.wx x) c sg := by
    funext sg
    rfl
  have hmean : meanK (fun sg => ∑ c, d.localHeightAtEmbedding (d.wx x) c sg) = ∑ c, meanK (d.localHeightAtEmbedding (d.wx x) c) := by
    simp only [meanK, Finset.sum_div]
    rw [Finset.sum_comm]
  unfold HgtMM mahlerMeasureHeight
  simp only [hla]
  rw [finsum_finset_sum_comm' Finset.univ (fun c la => d.localHeightAtPrime h (d.wx x) c la * logNorm la) (fun c _ => (hc c).1)]
  rw [hsg, hmean, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun c _ => (hc c).2, Finset.sum_add_distrib]
  simp only [del, Nat.cast_sum, Finset.sum_mul, Finset.sum_div]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem HeightMinMaxFormula (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) :
    d.HgtMM h (d.wx x) = ∑ c, ReciprocityTheory.MultiplicativeHeights.h0 (F c) + d.del * (harmonic d.N : ℝ) / 2 :=
  d.height_minMax_eq_sum_heights hd h hI2be x hx F hF

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
