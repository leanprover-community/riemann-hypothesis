import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IntNsg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormByPlaces
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FsumEqSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HPlaces

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem AH_smul (hd : d.AxH 𝒜) (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ)
    (Nr : ∀ c, A c → (Ω c →+* ℂ) → ℝ) (ta : ∀ c, A c) (a : ∀ c, Ω c) (ha : ∀ c, a c ≠ 0)
    (hOs : ∀ c v, d.admitted c v →
      ((O c v (a c • ta c) : ℤ) : WithTop ℤ) = v (a c) + (O c v (ta c) : WithTop ℤ))
    (hOf : ∀ c, {v | d.admitted c v ∧ O c v (ta c) ≠ 0}.Finite)
    (hOf' : ∀ c, {v | d.admitted c v ∧ O c v (a c • ta c) ≠ 0}.Finite)
    (hPf : ∀ c, {p | p ∈ d.HtOne ∧ d.anP h O c (ta c) p ≠ 0}.Finite)
    (hNs : ∀ c P, Nr c (a c • ta c) P = ‖P (a c)‖ * Nr c (ta c) P)
    (hN0 : ∀ c P, Nr c (ta c) P ≠ 0)
    (hI : ∀ c sg, Integrable (d.aI Nr c (ta c) sg) (blockSphereProb d.D (d.N + 1)))
    (hI' : ∀ c sg, Integrable (d.aI Nr c (a c • ta c) sg) (blockSphereProb d.D (d.N + 1))) :
    d.AH h O Nr (fun c => a c • ta c) = d.AH h O Nr ta := by
  set U := ⋃ c, ({la : HeightOneSpectrum (𝓞 K) | ∃ w ∈ d.PlOver la c, O c (d.Wres c w) (ta c) ≠ 0} ∪
    {la : HeightOneSpectrum (𝓞 K) | ∃ w ∈ d.PlOver la c, O c (d.Wres c w) (a c • ta c) ≠ 0}) with hUdef
  have hU : U.Finite := Set.finite_iUnion fun c =>
    (d.la_fin hd h c (fun v => O c v (ta c)) (hOf c)).union (d.la_fin hd h c (fun v => O c v (a c • ta c)) (hOf' c))
  have e1 : ∑ᶠ la, d.aNla h O ta la * logNorm la = ∑ la ∈ hU.toFinset, d.aNla h O ta la * logNorm la := by
    apply finsum_eq_sum_of_support_subset
    intro la hla
    rw [Set.Finite.coe_toFinset]
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 (d.aNla_supp hd h O ta (Function.support_mul_subset_left _ _ hla))
    exact Set.mem_iUnion.2 ⟨c, Or.inl hc⟩
  have e2 : ∑ᶠ la, d.aNla h O (fun c => a c • ta c) la * logNorm la =
      ∑ la ∈ hU.toFinset, d.aNla h O (fun c => a c • ta c) la * logNorm la := by
    apply finsum_eq_sum_of_support_subset
    intro la hla
    rw [Set.Finite.coe_toFinset]
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1
      (d.aNla_supp hd h O (fun c => a c • ta c) (Function.support_mul_subset_left _ _ hla))
    exact Set.mem_iUnion.2 ⟨c, Or.inr hc⟩
  have e3 : ∀ c, ∑ᶠ la, (d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a c)) : ℝ) * logNorm la =
      ∑ la ∈ hU.toFinset, (d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a c)) : ℝ) * logNorm la := by
    intro c
    apply finsum_eq_sum_of_support_subset
    intro la hla
    rw [Set.Finite.coe_toFinset]
    have hla' : la ∈ Function.support
        (fun la => d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a c))) := by
      intro h0; apply hla; simp only at h0 ⊢; rw [h0]; simp
    exact Set.mem_iUnion.2 ⟨c, d.nLa_supp hd h O c (ta c) (a c) (ha c) (hOs c) hla'⟩
  have hla : ∑ᶠ la, d.aNla h O (fun c => a c • ta c) la * logNorm la =
      ∑ᶠ la, d.aNla h O ta la * logNorm la +
        ∑ c, ∑ᶠ la, (d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a c)) : ℝ) * logNorm la := by
    rw [e1, e2, Finset.sum_congr rfl fun c _ => e3 c, Finset.sum_comm, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro la _
    rw [d.aNla_smul hd h O ta a ha hOs la, add_mul, Finset.sum_mul]
  have hP : ∀ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      (d.anP h O c (a c • ta c) p : ℝ) * h0 (d.gen p) =
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), (d.anP h O c (ta c) p : ℝ) * h0 (d.gen p) +
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), (d.nPa h c p (a c) : ℝ) * h0 (d.gen p) := by
    intro c
    rw [finsum_mem_congr rfl (fun p hp => by
      rw [d.usage₆ hd h O c (ta c) (a c) (ha c) (hOs c) hp, Int.cast_add, add_mul])]
    apply finsum_mem_add_distrib'
    · refine (hPf c).subset ?_
      rintro p ⟨hp, hp0⟩
      exact ⟨hp, fun h0' => hp0 (by simp only; rw [h0']; simp)⟩
    · refine (d.nPa_support hd h c (a c) (ha c)).subset ?_
      rintro p ⟨hp, hp0⟩
      exact ⟨hp, fun h0' => hp0 (by simp only; rw [h0']; simp)⟩
  have hS : (fun sg => ∑ c, ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
      -Real.log (Nr c (a c • ta c) P)) ∂(blockSphereProb d.D (d.N + 1))) =
      fun sg => (∑ c, ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
        -Real.log (Nr c (ta c) P)) ∂(blockSphereProb d.D (d.N + 1))) -
        ∑ c, ∫ z, d.lsum c sg (a c) z ∂(blockSphereProb d.D (d.N + 1)) := by
    funext sg
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ =>
      d.nsg_smul hd h Nr c (ta c) (a c) (ha c) (hNs c) (hN0 c) sg (hI c sg) (hI' c sg)
  have hpf := fun c => d.pf hd h c (a c) (ha c)
  unfold AH
  rw [hla, hS, meanK_sub, Finset.sum_congr rfl fun c _ => hP c, Finset.sum_add_distrib]
  simp only [meanK_sum]
  rw [← Finset.sum_congr rfl fun c _ => hpf c, Finset.sum_add_distrib, add_div, Finset.sum_div]
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

def IntOK (G : WT) (ta : ∀ c, A c) : Prop :=
  ∀ c sg, Integrable (d.aI (fun c f P => d.nrm c G f P) c (ta c) sg) (blockSphereProb d.D (d.N + 1))

theorem meanK_add (F G : (K →+* ℂ) → ℝ) : meanK (fun sg => F sg + G sg) = meanK F + meanK G := by
  first
    | (simp only [meanK, Finset.sum_add_distrib, add_div])
    | (unfold meanK; rw [Finset.sum_add_distrib, add_div])
    | (simp [meanK, Finset.sum_add_distrib, add_div])

theorem aI_mul_ae (hd : d.AxH 𝒜) (h : d.S1) {G G' : WT} (c : ι) {f g : A c}
    (hf : f ∈ 𝒜 c G) (hg : g ∈ 𝒜 c G') (hf0 : f ≠ 0) (hg0 : g ≠ 0) (sg : K →+* ℂ) :
    d.aI (fun c f P => d.nrm c (G + G') f P) c (f * g) sg =ᵐ[blockSphereProb d.D (d.N + 1)]
      fun z => d.aI (fun c f P => d.nrm c G f P) c f sg z + d.aI (fun c f P => d.nrm c G' f P) c g sg z := by
  filter_upwards [d.norm_at_sg hd h c sg] with z hz
  unfold aI
  rw [finsum_mem_eq_finite_toFinset_sum _ hz.1, finsum_mem_eq_finite_toFinset_sum _ hz.1,
    finsum_mem_eq_finite_toFinset_sum _ hz.1, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro P _
  dsimp only
  rw [hd.nrm_mul c P hf hg hf0 hg0, Real.log_mul (hd.nrm_pos c P hf hf0).ne' (hd.nrm_pos c P hg hg0).ne']

theorem Hgt_mul (hd : d.AxH 𝒜) (h : d.S1) (G G' : WT) (f g : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c G ∧ f c ≠ 0) (hg : ∀ c, g c ∈ 𝒜 c G' ∧ g c ≠ 0)
    (hIf : d.IntOK G f) (hIg : d.IntOK G' g) :
    d.IntOK (G + G') (f * g) ∧ d.Hgt h (G + G') (f * g) = d.Hgt h G f + d.Hgt h G' g := by
  have hae := fun c sg => d.aI_mul_ae hd h c (hf c).1 (hg c).1 (hf c).2 (hg c).2 sg
  have hI : d.IntOK (G + G') (f * g) := fun c sg => ((hIf c sg).add (hIg c sg)).congr (hae c sg).symm
  refine ⟨hI, ?_⟩

  have hOf := fun c => hd.a3' c (hf c).1 (hf c).2
  have hOg := fun c => hd.a3' c (hg c).1 (hg c).2
  have hla : ∀ la, d.aNla h (fun c v x => d.ord c v (G + G') x) (f * g) la =
      d.aNla h (fun c v x => d.ord c v G x) f la + d.aNla h (fun c v x => d.ord c v G' x) g la := by
    intro la
    unfold aNla
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    have hfin := (d.places_over_la hd h la c).1
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    have hv := (d.admissible_over_prime hd h la c w hw).1
    rw [Pi.mul_apply]
    dsimp only
    rw [hd.ord_mul c _ hv (hf c).1 (hg c).1 (hf c).2 (hg c).2]
    push_cast; ring
  have hsf : (Function.support fun la => d.aNla h (fun c v x => d.ord c v G x) f la * logNorm la).Finite :=
    (Set.finite_iUnion fun c => d.la_fin hd h c (fun v => d.ord c v G (f c)) (hOf c)).subset
    ((Function.support_mul_subset_left _ _).trans (d.aNla_supp hd h (fun c v x => d.ord c v G x) f))
  have hsg : (Function.support fun la => d.aNla h (fun c v x => d.ord c v G' x) g la * logNorm la).Finite :=
    (Set.finite_iUnion fun c => d.la_fin hd h c (fun v => d.ord c v G' (g c)) (hOg c)).subset
    ((Function.support_mul_subset_left (fun la => d.aNla h (fun c v x => d.ord c v G' x) g la)
      logNorm).trans (d.aNla_supp hd h (fun c v x => d.ord c v G' x) g))
  have hN : ∑ᶠ la, d.aNla h (fun c v x => d.ord c v (G + G') x) (f * g) la * logNorm la =
      ∑ᶠ la, d.aNla h (fun c v x => d.ord c v G x) f la * logNorm la +
      ∑ᶠ la, d.aNla h (fun c v x => d.ord c v G' x) g la * logNorm la := by
    rw [← finsum_add_distrib hsf hsg]
    exact finsum_congr fun la => by rw [hla, add_mul]

  have hS : ∀ sg c, ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
      -Real.log (d.nrm c (G + G') ((f * g) c) P)) ∂(blockSphereProb d.D (d.N + 1)) =
      ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
        -Real.log (d.nrm c G (f c) P)) ∂(blockSphereProb d.D (d.N + 1)) +
      ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
        -Real.log (d.nrm c G' (g c) P)) ∂(blockSphereProb d.D (d.N + 1)) := by
    intro sg c
    have e1 := d.neg_aI (fun c f P => d.nrm c (G + G') f P) c ((f * g) c) sg
    have e2 := d.neg_aI (fun c f P => d.nrm c G f P) c (f c) sg
    have e3 := d.neg_aI (fun c f P => d.nrm c G' f P) c (g c) sg
    simp_rw [e1, e2, e3]
    rw [integral_neg, integral_neg, integral_neg, Pi.mul_apply, integral_congr_ae (hae c sg),
      integral_add (hIf c sg) (hIg c sg)]
    ring

  have hP : ∀ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      (d.anP h (fun c v x => d.ord c v (G + G') x) c ((f * g) c) p : ℝ) * h0 (d.gen p) =
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.anP h (fun c v x => d.ord c v G x) c (f c) p : ℝ) * h0 (d.gen p) +
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.anP h (fun c v x => d.ord c v G' x) c (g c) p : ℝ) * h0 (d.gen p) := by
    intro c
    rw [finsum_mem_congr rfl (fun p hp => by
      rw [show d.anP h (fun c v x => d.ord c v (G + G') x) c ((f * g) c) p =
          d.anP h (fun c v x => d.ord c v G x) c (f c) p + d.anP h (fun c v x => d.ord c v G' x) c (g c) p from by
        have hfin := d.goodP_finite' hd h c hp
        unfold anP
        rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
          finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro w hw
        rw [Set.Finite.mem_toFinset] at hw
        rw [Pi.mul_apply]
        dsimp only
        rw [hd.ord_mul c _ (d.admissible_of_good_valuation hd h c hp hw) (hf c).1 (hg c).1 (hf c).2 (hg c).2]
        ring, Int.cast_add, add_mul])]
    apply finsum_mem_add_distrib'
    · refine ((d.good_primes_properties hd h c).2.2.1 G (f c) (hf c).1 (hf c).2).subset ?_
      rintro p ⟨hp, hp0⟩
      exact ⟨hp, fun h0' => hp0 (by simp only; rw [show d.anP h _ c (f c) p = d.nP h c G (f c) p from rfl, h0']; simp)⟩
    · refine ((d.good_primes_properties hd h c).2.2.1 G' (g c) (hg c).1 (hg c).2).subset ?_
      rintro p ⟨hp, hp0⟩
      exact ⟨hp, fun h0' => hp0 (by simp only; rw [show d.anP h _ c (g c) p = d.nP h c G' (g c) p from rfl, h0']; simp)⟩
  rw [d.Hgt_eq_AH, d.Hgt_eq_AH, d.Hgt_eq_AH]
  unfold AH
  rw [hN]
  simp only [hS, Finset.sum_add_distrib, meanK_add, hP]
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

theorem h0_zero : ReciprocityTheory.MultiplicativeHeights.h0 (0 : KTp K d.D d.N) = 0 := by
  simp [ReciprocityTheory.MultiplicativeHeights.h0, ReciprocityTheory.MultiplicativeHeights.gaussAbs, ReciprocityTheory.MultiplicativeHeights.blockSphereMean]

theorem lr_nonneg : (0 : ℝ) ≤ Real.log (d.N + 1 : ℕ) + 1 / 2 := by
  have h := Real.log_natCast_nonneg (d.N + 1)
  linarith

theorem logHeight_generator_lower_bound (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (hg : ∃ w, w ∈ d.GoodP c p) :
    -((d.D : ℝ) * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) ≤ ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) := by
  by_cases h0 : d.gen p = 0
  · rw [h0, d.h0_zero]
    have : d.dg 0 = 0 := by simp [dg]
    rw [this]; simp
  · have hm := (d.good_primes_properties hd h c).2.1 p hp hg
    have := ReciprocityTheory.MultiplicativeHeights.Closed.sphere_height_lower_bound K (d.D + 1) (d.N + 1) _ (d.gen p) (Nat.succ_pos _) h0 hm
    rw [Fin.sum_univ_succ] at this
    simp only [Fin.succ_ne_zero, if_false, if_true, Nat.cast_zero, zero_mul, zero_add,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    convert this using 2
    ring

theorem multiplicity_mul_logHeight_le (hd : d.AxH 𝒜) (h : d.S1) (hF1d : d.TrivialPlaceHyp) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) :
    (d.Ep h c p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) ≤
      d.cc / d.i * d.nP h c (d.n1 • d.wde) (d.et c) p * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) +
        d.D * (Real.log (d.N + 1 : ℕ) + 1 / 2) * (d.cc / d.i) *
          (d.nP h c (d.n1 • d.wde) (d.et c) p * d.dg (d.gen p)) := by
  by_cases hg : ∃ w, w ∈ d.GoodP c p
  · have hL := d.logHeight_generator_lower_bound hd h c hp hg
    have hE0 : (0 : ℝ) ≤ d.Ep h c p := by exact_mod_cast d.Ep_nonneg hd h c hp
    have hE := d.Ep_le hd h hF1d c hp
    have hn0 : (0 : ℝ) ≤ d.nP h c (d.n1 • d.wde) (d.et c) p := by
      exact_mod_cast d.nP_nonneg hd h c hp _ _ fun v hv => hd.ord_nonneg_et c v hv
    have hi : (0 : ℝ) ≤ d.cc / d.i := div_nonneg hd.cc_nonneg (Nat.cast_nonneg _)
    have hE' : (d.Ep h c p : ℝ) ≤ d.cc / d.i * d.nP h c (d.n1 • d.wde) (d.et c) p := by
      have : d.cc / (2 * d.i) = (d.cc / d.i) / 2 := by ring
      rw [this] at hE; nlinarith
    have hlr := d.lr_nonneg
    have hX : (0 : ℝ) ≤ d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2) := by positivity
    set r := d.cc / d.i * (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) - d.Ep h c p
    have hr0 : 0 ≤ r := by linarith
    have hrle : r ≤ d.cc / d.i * (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) := by linarith
    have k1 : -(r * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p)) ≤ r * (d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) := by
      nlinarith
    have k2 : r * (d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) ≤
        d.cc / d.i * (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) *
          (d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) :=
      mul_le_mul_of_nonneg_right hrle hX
    have : (d.Ep h c p : ℝ) = d.cc / d.i * d.nP h c (d.n1 • d.wde) (d.et c) p - r := by ring
    rw [this]
    nlinarith
  · push_neg at hg
    have hG : d.GoodP c p = ∅ := Set.eq_empty_iff_forall_notMem.mpr hg
    have e1 : d.Ep h c p = 0 := by unfold Ep; rw [hG]; simp
    have e2 : d.nP h c (d.n1 • d.wde) (d.et c) p = 0 := by unfold nP; rw [hG]; simp
    rw [e1, e2]; simp

theorem logHeight_section_bound (hd : d.AxH 𝒜) (h : d.S1) (hF1d : d.TrivialPlaceHyp) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) :
    d.h0f h d.wL f ≤ d.mahlerMeasureHeight h f + d.cc / d.i * d.h0f h (d.n1 • d.wde) d.et +
      d.D * (Real.log (d.N + 1 : ℕ) + 1 / 2) * (d.cc / d.i) * (d.aG h (d.n1 • d.wde) d.et : ℝ) := by
  classical
  unfold h0f mahlerMeasureHeight aG
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  have x2 := d.good_primes_properties hd h c
  have hfin : {p | p ∈ d.HtOne ∧ (d.nP h c d.wL (f c) p ≠ 0 ∨ d.nPMM h c (f c) p ≠ 0 ∨
      d.Ep h c p ≠ 0 ∨ d.nP h c (d.n1 • d.wde) (d.et c) p ≠ 0)}.Finite := by
    refine (((x2.2.2.1 _ _ (hf c).1 (hf c).2).union (x2.2.2.2 _ (hf c).1 (hf c).2)).union
      ((d.Ep_ne hd h c _ (hf c).1 (hf c).2).union
        (x2.2.2.1 _ _ (hd.et_mem c) (hd.et_ne c)))).subset ?_
    rintro p ⟨hp, h1 | h1 | h1 | h1⟩
    · exact Or.inl (Or.inl ⟨hp, h1⟩)
    · exact Or.inl (Or.inr ⟨hp, h1⟩)
    · exact Or.inr (Or.inl ⟨hp, h1⟩)
    · exact Or.inr (Or.inr ⟨hp, h1⟩)
  set S := hfin.toFinset
  have mem : ∀ p, p ∈ d.HtOne → (d.nP h c d.wL (f c) p ≠ 0 ∨ d.nPMM h c (f c) p ≠ 0 ∨
      d.Ep h c p ≠ 0 ∨ d.nP h c (d.n1 • d.wde) (d.et c) p ≠ 0) → p ∈ S := fun p hp h1 => by
    simp only [S, Set.Finite.mem_toFinset]; exact ⟨hp, h1⟩
  rw [fsum_eq_sum _ S (fun p => (d.nP h c d.wL (f c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p))
      (fun p hp h0 => mem p hp (Or.inl fun e => h0 (by simp [e]))),
    fsum_eq_sum _ S (fun p => (d.nPMM h c (f c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p))
      (fun p hp h0 => mem p hp (Or.inr (Or.inl fun e => h0 (by simp [e])))),
    fsum_eq_sum _ S (fun p => (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p))
      (fun p hp h0 => mem p hp (Or.inr (Or.inr (Or.inr fun e => h0 (by simp [e]))))),
    fsum_eq_sum _ S (fun p => d.nP h c (d.n1 • d.wde) (d.et c) p * (d.dg (d.gen p) : ℤ))
      (fun p hp h0 => mem p hp (Or.inr (Or.inr (Or.inr fun e => h0 (by simp [e])))))]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases hp : p ∈ d.HtOne
  · simp only [Set.indicator_of_mem hp]
    have e := d.nP_split hd h c hp (f c)
    have k := d.multiplicity_mul_logHeight_le hd h hF1d c hp
    rw [e]; push_cast
    push_cast at k
    linarith
  · simp [Set.indicator_of_notMem hp]

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

open MeasureTheory

theorem be_pos (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) : 0 < d.be c P := by
  unfold Data.be
  apply Real.sqrt_pos.mpr
  have h1 := hd.nrm_pos c P (hd.w_mem (d.jc c) c) (hd.w_base c)
  exact lt_of_lt_of_le (pow_pos h1 2)
    (Finset.single_le_sum (f := fun j => d.nrm c d.wL (d.w j c) P ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ (d.jc c)))

theorem fneg {α : Type*} (s : Set α) (g : α → ℝ) : ∑ᶠ x ∈ s, -g x = -∑ᶠ x ∈ s, g x := by
  simp only [finsum_neg_distrib]

theorem integral_le_of_ae_le_affine {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (F1 F2 F3 : X → ℝ) (C r : ℝ) (I1 : Integrable F1 μ) (I2 : Integrable F2 μ) (I3 : Integrable F3 μ)
    (hle : ∀ᵐ x ∂μ, F1 x ≤ F2 x + C + r * F3 x) :
    ∫ x, F1 x ∂μ ≤ ∫ x, F2 x ∂μ + C + r * ∫ x, F3 x ∂μ := by
  have hC : Integrable (fun _ : X => C) μ := integrable_const C
  have h2C : Integrable (fun x => F2 x + C) μ := I2.add hC
  have hI : Integrable (fun x => F2 x + C + r * F3 x) μ := h2C.add (I3.const_mul r)
  calc ∫ x, F1 x ∂μ ≤ ∫ x, (F2 x + C + r * F3 x) ∂μ := integral_mono_ae I1 hI hle
    _ = ∫ x, F2 x ∂μ + C + r * ∫ x, F3 x ∂μ := by
      rw [integral_add h2C (I3.const_mul r), integral_const_mul, integral_add I2 hC]
      simp

theorem int_neg (c : ι) (sg : K →+* ℂ) (g : (Ω c →+* ℂ) → ℝ)
    (hI : Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)), g P)
      (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) :
    Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)), -g P)
      (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  exact hI.neg.congr (ae_of_all _ fun z => by simp only [Pi.neg_apply, fneg])

theorem sg_one (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) (c : ι) (sg : K →+* ℂ) :
    ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
      -Real.log (d.nrm c d.wL (f c) P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) ≤
    ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
      -Real.log (d.nrm c d.wL (f c) P / d.be c P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) +
    d.delc c * (d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo) + d.cc / d.i *
    ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
      -Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  haveI := ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_isProbability (B := d.D) (Nat.succ_pos d.N)
  have hint := d.int_Nsg hd h hI2be c sg
  have I1 := d.int_neg c sg (fun P => Real.log (d.nrm c d.wL (f c) P))
    (hint.1 d.wL (f c) (by simp) (hf c).1 (hf c).2)
  have I2 := d.int_neg c sg (fun P => Real.log (d.nrm c d.wL (f c) P / d.be c P))
    (hint.2 (f c) (hf c).1 (hf c).2)
  have I3 := d.int_neg c sg (fun P => Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P))
    (hint.1 (d.n1 • d.wde) (d.et c) (by simp) (hd.et_mem c) (hd.et_ne c))
  set κ := d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo
  refine integral_le_of_ae_le_affine _ _ _ _ _ _ I1 I2 I3 ?_
  filter_upwards [d.norm_at_sg hd h c sg] with z hz
  obtain ⟨hfin0, hcard0, -, -⟩ := hz
  have hfin : (d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)).Finite := hfin0
  have hcard : (d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)).ncard = d.delc c := hcard0
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [Set.ncard_eq_toFinset_card _ hfin] at hcard
  have e : (d.delc c : ℝ) * κ = ∑ P ∈ hfin.toFinset, κ := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  rw [e, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun P _ => ?_
  have hn := hd.nrm_pos c P (hf c).1 (hf c).2
  have hb := d.be_pos hd c P
  have hI := hI2be c P
  rw [Real.log_div hn.ne' hb.ne']
  simp only [κ]
  linarith

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

theorem logNorm_nonneg (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : 0 ≤ logNorm la := by
  unfold logNorm
  exact Real.log_natCast_nonneg _

theorem over_unique {c : ι} (v : AddValuation (Ω c) (WithTop ℤ)) :
    {la : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | IsOver (K := K) v la}.Subsingleton := by
  intro la1 h1 la2 h2
  have h1' : IsOver (K := K) v la1 := h1
  have h2' : IsOver (K := K) v la2 := h2
  apply IsDedekindDomain.HeightOneSpectrum.ext
  ext a
  exact (h1' a).symm.trans (h2' a)

theorem NlaG_nonneg (hd : d.AxH 𝒜) (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    0 ≤ d.NlaG h (d.n1 • d.wde) d.et la :=
  Finset.sum_nonneg fun c _ => finsum_nonneg fun w => finsum_nonneg fun hw =>
    mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hd.ord_nonneg_et c _ (d.admissible_over_prime hd h la c w hw).1)

theorem Nla_le (hd : d.AxH 𝒜) (h : d.S1) (hH1 : d.FinitePlaceHyp) (f : ∀ c, A c)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    d.NlaG h d.wL f la ≤ d.NlaMM h f la + d.del * d.nu la +
      d.cc / d.i * d.NlaG h (d.n1 • d.wde) d.et la := by
  have hnn := d.NlaG_nonneg hd h la
  have hi : (0 : ℝ) ≤ d.cc / d.i := div_nonneg hd.cc_nonneg (Nat.cast_nonneg _)
  suffices key : d.NlaG h d.wL f la ≤ d.NlaMM h f la + d.del * d.nu la +
      d.cc / (2 * d.i) * d.NlaG h (d.n1 • d.wde) d.et la by
    have : d.cc / (2 * d.i) * d.NlaG h (d.n1 • d.wde) d.et la ≤ d.cc / d.i * d.NlaG h (d.n1 • d.wde) d.et la := by
      have : d.cc / (2 * d.i) = (d.cc / d.i) / 2 := by ring
      rw [this]; nlinarith
    linarith
  unfold NlaG NlaMM del
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  have hfin := (d.places_over_la hd h la c).1
  have hsum := (d.places_over_la hd h la c).2
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum ⊢
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsumR : (d.delc c : ℝ) = ∑ w ∈ hfin.toFinset, (d.fze h c w : ℝ) * (ramIdx (K := K) (d.Wres c w) la : ℝ) := by
    have e := congrArg (fun z : ℤ => (z : ℝ)) hsum
    push_cast at e
    linarith
  rw [hsumR, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  have hs := d.admissible_over_prime hd h la c w hw
  have h3 := hH1.2.2.2 c (d.Wres c w) la hs.1 hs.2.1
  have hf : (0 : ℝ) ≤ d.fze h c w := Nat.cast_nonneg _
  unfold ordMM
  push_cast
  have e : ((⨅ j : {j // d.w j c ≠ 0}, d.ord c (d.Wres c w) d.wL (d.w j c) : ℤ) : ℝ) =
    (d.Emin c (d.Wres c w) : ℝ) := rfl
  rw [e] at h3 ⊢
  nlinarith [mul_le_mul_of_nonneg_left h3 hf]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem exists_smul_eq (hd : d.AxH 𝒜) {c : ι} {G : WT} {f g : A c} (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0)
    (hg : g ∈ 𝒜 c G) (hg0 : g ≠ 0) : ∃ a : Ω c, a ≠ 0 ∧ a • f = g := by
  have h1 := hd.finrank_one c G
  have hne : (⟨f, hf⟩ : 𝒜 c G) ≠ 0 := by
    rwa [Ne, Submodule.mk_eq_zero]
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 h1 ⟨g, hg⟩
  have ha' : a • f = g := congrArg Subtype.val ha
  refine ⟨a, ?_, ha'⟩
  rintro rfl
  exact hg0 (by rw [← ha', zero_smul])

theorem Hgt_indep (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (ta ta' : ∀ c, A c)
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) (hta' : ∀ c, ta' c ∈ 𝒜 c G ∧ ta' c ≠ 0)
    (hI : d.IntOK G ta) (hI' : d.IntOK G ta') : d.Hgt h G ta = d.Hgt h G ta' := by
  choose a ha hae using fun c => d.exists_smul_eq hd (hta c).1 (hta c).2 (hta' c).1 (hta' c).2
  have he : ta' = fun c => a c • ta c := funext fun c => (hae c).symm
  subst he
  rw [d.Hgt_eq_AH, d.Hgt_eq_AH]
  refine (d.AH_smul hd h _ _ ta a ha (fun c v hv => hd.ord_smul c v hv (a c) (hta c).1 (hta c).2 (ha c))
    (fun c => hd.a3' c (hta c).1 (hta c).2) (fun c => hd.a3' c (hta' c).1 (hta' c).2)
    (fun c => (d.good_primes_properties hd h c).2.2.1 G (ta c) (hta c).1 (hta c).2)
    (fun c P => hd.nrm_smul c P (a c) (hta c).1 (hta c).2 (ha c))
    (fun c P => (hd.nrm_pos c P (hta c).1 (hta c).2).ne') hI hI').symm

theorem Hgt_pow (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c G ∧ f c ≠ 0) (hI : d.IntOK G f) (n : ℕ) :
    (∀ c, (f ^ (n + 1)) c ∈ 𝒜 c ((n + 1) • G) ∧ (f ^ (n + 1)) c ≠ 0) ∧
      d.IntOK ((n + 1) • G) (f ^ (n + 1)) ∧
      d.Hgt h ((n + 1) • G) (f ^ (n + 1)) = ((n + 1 : ℕ) : ℝ) * d.Hgt h G f := by
  induction n with
  | zero =>
    refine ⟨fun c => ?_, ?_, ?_⟩ <;>
      simp only [zero_add, pow_one, one_smul, one_nsmul, Nat.cast_one, one_mul]
    · exact hf c
    · exact hI
  | succ n ih =>
    obtain ⟨hm, hI', hH⟩ := ih
    have hmem : ∀ c, (f ^ (n + 1 + 1)) c ∈ 𝒜 c ((n + 1 + 1) • G) ∧ (f ^ (n + 1 + 1)) c ≠ 0 := by
      intro c
      haveI := hd.graded c
      rw [pow_succ, succ_nsmul, Pi.mul_apply]
      exact ⟨SetLike.GradedMul.mul_mem (hm c).1 (hf c).1,
        hd.mul_ne_zero c (hm c).1 (hf c).1 (hm c).2 (hf c).2⟩
    obtain ⟨hI2, hH2⟩ := d.Hgt_mul hd h ((n + 1) • G) G (f ^ (n + 1)) f hm hf hI' hI
    rw [← pow_succ, ← succ_nsmul] at hI2 hH2
    refine ⟨hmem, hI2, ?_⟩
    rw [hH2, hH]
    push_cast
    ring

theorem Hgt_pow' (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c G ∧ f c ≠ 0) (hI : d.IntOK G f) (n : ℕ) (hn : 0 < n) :
    (∀ c, (f ^ n) c ∈ 𝒜 c (n • G) ∧ (f ^ n) c ≠ 0) ∧ d.IntOK (n • G) (f ^ n) ∧
      d.Hgt h (n • G) (f ^ n) = (n : ℝ) * d.Hgt h G f := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact d.Hgt_pow hd h G f hf hI m

theorem wx_mem (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) : d.wx x c ∈ 𝒜 c d.wL := by
  haveI := hd.tower c
  rw [Data.wx, Finset.sum_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Pi.smul_apply, ← algebraMap_smul (Ω c) (x j) (d.w j c)]
  exact Submodule.smul_mem _ _ (hd.w_mem j c)

theorem intOK_of (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (G : WT)
    (hG : G ∈ ({d.wL, d.n1 • d.wde, (2 : ℕ) • d.G1, d.wF, d.G2} : Set WT)) (ta : ∀ c, A c)
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) : d.IntOK G ta :=
  fun c sg => (d.int_Nsg hd h hI2be c sg).1 G (ta c) hG (hta c).1 (hta c).2

theorem weight_double_eq_scaled_line : d.n1 • ((2 : ℕ) • d.G1) + (2 : ℕ) • (d.n1 • d.wde) = (2 * d.n1) • d.wL := by
  simp only [Data.G1, smul_sub, smul_smul]
  rw [mul_comm d.n1 2]
  exact sub_add_cancel _ _

theorem weight_sum_eq_scaled_line : d.wF + d.G2 = (d.D + 4) • d.wL := by
  simp only [Data.G2]
  abel

theorem degree_multiplier_pos (hd : d.AxH 𝒜) : 0 < d.n1 := Nat.mul_pos hd.i_ge hd.g_zero_ge_ask_sum

theorem h_ind' (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) :
    (∀ (G : WT) (ta ta' : ∀ c, A c),
      G ∈ ({d.wL, d.n1 • d.wde, (2 : ℕ) • d.G1, d.wF, d.G2} : Set WT) →
      (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) → (∀ c, ta' c ∈ 𝒜 c G ∧ ta' c ≠ 0) →
      d.Hgt h G ta = d.Hgt h G ta') ∧
    (∀ f f' : ∀ c, A c, (∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) → (∀ c, f' c ∈ 𝒜 c d.wL ∧ f' c ≠ 0) →
      d.HgtMM h f = d.HgtMM h f') ∧
    (∀ x : Fin (d.N + 1) → K, (∀ c, d.wx x c ≠ 0) →
      (d.n1 : ℝ) * d.Hgt h ((2 : ℕ) • d.G1) d.ta1 + 2 * d.Hgt h (d.n1 • d.wde) d.et =
        2 * d.n1 * d.Hgt h d.wL (d.wx x)) ∧
    (∀ (x : Fin (d.N + 1) → K) (ta' : ∀ c, A c), (∀ c, d.wx x c ≠ 0) →
      (∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) →
      d.Hgt h d.wF ta' + d.Hgt h d.G2 d.ta2 = (d.D + 4) * d.Hgt h d.wL (d.wx x)) := by
  have hmemS : ∀ G, G ∈ ({d.wL, d.n1 • d.wde, (2 : ℕ) • d.G1, d.wF, d.G2} : Set WT) → True :=
    fun _ _ => trivial
  refine ⟨fun G ta ta' hG hta hta' => d.Hgt_indep hd h G ta ta' hta hta'
      (d.intOK_of hd h hI2be G hG ta hta) (d.intOK_of hd h hI2be G hG ta' hta'), ?_, ?_, ?_⟩
  · intro f f' hf hf'
    choose a ha hae using fun c => d.exists_smul_eq hd (hf c).1 (hf c).2 (hf' c).1 (hf' c).2
    have he : f' = fun c => a c • f c := funext fun c => (hae c).symm
    subst he
    have hbe : ∀ c P, d.be c P ≠ 0 := fun c P => by
      rw [d.hint_be_eq hd c P]
      exact (mul_pos (hd.nrm_pos c P (hd.w_mem (d.jc c) c) (hd.w_base c))
        (by linarith [d.hint_one_le_U hd c P])).ne'
    have hOs : ∀ c v, d.admitted c v →
        ((d.ordMM c v (a c • f c) : ℤ) : WithTop ℤ) = v (a c) + (d.ordMM c v (f c) : WithTop ℤ) := by
      intro c v hv
      have e := hd.ord_smul c v hv (a c) (hf c).1 (hf c).2 (ha c)
      have hvt : v (a c) ≠ ⊤ := by rw [Ne, AddValuation.top_iff]; exact ha c
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hvt
      rw [← hk] at e ⊢
      unfold ordMM
      norm_cast at e ⊢
      omega
    have hOfin : ∀ c (g : A c), g ∈ 𝒜 c d.wL → g ≠ 0 →
        {v | d.admitted c v ∧ d.ordMM c v g ≠ 0}.Finite := by
      intro c g hg hg0
      refine ((hd.a3' c hg hg0).union (Set.finite_iUnion fun j : {j // d.w j c ≠ 0} =>
        hd.a3' c (hd.w_mem j.1 c) j.2)).subset ?_
      rintro v ⟨hv, hne⟩
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists, not_and,
        not_not] at hcon
      apply hne
      have hne' : Nonempty {j // d.w j c ≠ 0} := ⟨⟨d.jc c, hd.w_base c⟩⟩
      unfold ordMM
      rw [hcon.1 hv]
      have : (fun j : {j // d.w j c ≠ 0} => d.ord c v d.wL (d.w j c)) = fun _ => 0 :=
        funext fun j => hcon.2 j hv
      rw [this, ciInf_const]; rfl
    have hsm : ∀ c, a c • f c ∈ 𝒜 c d.wL ∧ a c • f c ≠ 0 := fun c =>
      ⟨Submodule.smul_mem _ _ (hf c).1, smul_ne_zero (ha c) (hf c).2⟩
    rw [d.HgtMM_eq_AH, d.HgtMM_eq_AH]
    refine (d.AH_smul hd h (fun c v g => d.ordMM c v g) (fun c g P => d.nrm c d.wL g P / d.be c P) f a ha hOs (fun c => hOfin c _ (hf c).1 (hf c).2)
      (fun c => hOfin c _ (hsm c).1 (hsm c).2)
      (fun c => (d.good_primes_properties hd h c).2.2.2 (f c) (hf c).1 (hf c).2)
      (fun c P => by
        rw [hd.nrm_smul c P (a c) (hf c).1 (hf c).2 (ha c), mul_div_assoc])
      (fun c P => div_ne_zero (hd.nrm_pos c P (hf c).1 (hf c).2).ne' (hbe c P))
      (fun c sg => (d.int_Nsg hd h hI2be c sg).2 (f c) (hf c).1 (hf c).2)
      (fun c sg => (d.int_Nsg hd h hI2be c sg).2 _ (hsm c).1 (hsm c).2)).symm
  · intro x hx
    have hw : ∀ c, d.wx x c ∈ 𝒜 c d.wL ∧ d.wx x c ≠ 0 := fun c => ⟨d.wx_mem hd x c, hx c⟩
    have hIw := d.intOK_of hd h hI2be d.wL (by simp) _ hw
    have hn1 := d.degree_multiplier_pos hd
    have ht1 : ∀ c, d.ta1 c ∈ 𝒜 c ((2 : ℕ) • d.G1) ∧ d.ta1 c ≠ 0 := fun c => ⟨hd.firstSectionMem c, hd.firstSectionNeZero c⟩
    have het : ∀ c, d.et c ∈ 𝒜 c (d.n1 • d.wde) ∧ d.et c ≠ 0 := fun c => ⟨hd.et_mem c, hd.et_ne c⟩
    obtain ⟨m1, I1, H1⟩ := d.Hgt_pow' hd h _ d.ta1 ht1 (d.intOK_of hd h hI2be _ (by simp) _ ht1) d.n1 hn1
    obtain ⟨m2, I2, H2⟩ := d.Hgt_pow' hd h _ d.et het (d.intOK_of hd h hI2be _ (by simp) _ het) 2 two_pos
    obtain ⟨m3, I3, H3⟩ := d.Hgt_pow' hd h _ _ hw hIw (2 * d.n1) (by omega)
    obtain ⟨I4, H4⟩ := d.Hgt_mul hd h _ _ _ _ m1 m2 I1 I2
    have m4 : ∀ c, (d.ta1 ^ d.n1 * d.et ^ 2) c ∈ 𝒜 c (d.n1 • ((2 : ℕ) • d.G1) + (2 : ℕ) • (d.n1 • d.wde)) ∧
        (d.ta1 ^ d.n1 * d.et ^ 2) c ≠ 0 := fun c => by
      have := hd.graded c
      rw [Pi.mul_apply]
      exact ⟨SetLike.mul_mem_graded (m1 c).1 (m2 c).1, hd.mul_ne_zero c (m1 c).1 (m2 c).1 (m1 c).2 (m2 c).2⟩
    rw [d.weight_double_eq_scaled_line] at I4 H4 m4
    have := d.Hgt_indep hd h _ _ _ m4 m3 I4 I3
    rw [H4, H1, H2, H3] at this
    push_cast at this
    linarith
  · intro x ta' hx hta'
    have hw : ∀ c, d.wx x c ∈ 𝒜 c d.wL ∧ d.wx x c ≠ 0 := fun c => ⟨d.wx_mem hd x c, hx c⟩
    have hIw := d.intOK_of hd h hI2be d.wL (by simp) _ hw
    have ht2 : ∀ c, d.ta2 c ∈ 𝒜 c d.G2 ∧ d.ta2 c ≠ 0 := fun c => ⟨hd.secondSectionMem c, hd.secondSectionNeZero c⟩
    obtain ⟨m3, I3, H3⟩ := d.Hgt_pow' hd h _ _ hw hIw (d.D + 4) (by omega)
    obtain ⟨I4, H4⟩ := d.Hgt_mul hd h _ _ _ _ hta' ht2 (d.intOK_of hd h hI2be _ (by simp) _ hta')
      (d.intOK_of hd h hI2be _ (by simp) _ ht2)
    have m4 : ∀ c, (ta' * d.ta2) c ∈ 𝒜 c (d.wF + d.G2) ∧ (ta' * d.ta2) c ≠ 0 := fun c => by
      have := hd.graded c
      rw [Pi.mul_apply]
      exact ⟨SetLike.mul_mem_graded (hta' c).1 (ht2 c).1,
        hd.mul_ne_zero c (hta' c).1 (ht2 c).1 (hta' c).2 (ht2 c).2⟩
    rw [d.weight_sum_eq_scaled_line] at I4 H4 m4
    have := d.Hgt_indep hd h _ _ _ m4 m3 I4 I3
    rw [H4, H3] at this
    push_cast at this
    linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights MeasureTheory IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem four_sg (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (ta : ∀ c, A c)
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) (sg : K →+* ℂ)
    (hbdd : BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (ta p.1) p.2))
    (c : ι) (hint : Integrable (fun z : BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => spherePoint (z i) j)),
          Real.log (d.nrm c G (ta c) P)) (blockSphereProb d.D (d.N + 1))) :
    -((d.delc c : ℝ) * Real.log (d.supN sg G ta)) ≤
      ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => spherePoint (z i) j)),
        -Real.log (d.nrm c G (ta c) P)) ∂(blockSphereProb d.D (d.N + 1)) := by
  have := blockSphereMeasure_isProbability (B := d.D) (Nat.succ_pos d.N)
  have I2 := d.int_neg c sg (fun P => Real.log (d.nrm c G (ta c) P)) hint
  have k := integral_le_of_ae_le_affine (blockSphereProb d.D (d.N + 1)) (fun _ => (0 : ℝ)) _ _
    ((d.delc c : ℝ) * Real.log (d.supN sg G ta)) 0 (integrable_const 0) I2 I2 ?_
  · simp only [integral_zero, zero_mul, add_zero] at k
    linarith
  filter_upwards [d.norm_at_sg hd h c sg] with z hz
  obtain ⟨hfin0, hcard0, -, -⟩ := hz
  have hfin : (d.ST c sg (fun i j => spherePoint (z i) j)).Finite := hfin0
  have hcard : (d.ST c sg (fun i j => spherePoint (z i) j)).ncard = d.delc c := hcard0
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [Set.ncard_eq_toFinset_card _ hfin] at hcard
  have e : (d.delc c : ℝ) * Real.log (d.supN sg G ta) =
      ∑ P ∈ hfin.toFinset, Real.log (d.supN sg G ta) := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  rw [e, zero_mul, add_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_nonneg fun P hP => ?_
  rw [Set.Finite.mem_toFinset] at hP
  have hn := hd.nrm_pos c P (hta c).1 (hta c).2
  have hle : d.nrm c G (ta c) P ≤ d.supN sg G ta :=
    le_ciSup (f := fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (ta p.1) p.2) hbdd ⟨c, ⟨P, hP.1⟩⟩
  have := Real.log_le_log hn hle
  linarith

theorem sum_mult_logHeight_lower (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (c : ι) (f : A c) (hf : f ∈ 𝒜 c G)
    (hf0 : f ≠ 0) (hord : ∀ v, d.admitted c v → 0 ≤ d.ord c v G f) :
    -((d.D : ℝ) * (((∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nP h c G f p * (d.dg (d.gen p) : ℤ) : ℤ)) : ℝ) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) ≤
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), (d.nP h c G f p : ℝ) * h0 (d.gen p) := by
  classical
  have hfin := (d.good_primes_properties hd h c).2.2.1 G f hf hf0
  set S := hfin.toFinset
  have mem : ∀ p, p ∈ d.HtOne → d.nP h c G f p ≠ 0 → p ∈ S := fun p hp h1 => by
    simp only [S, Set.Finite.mem_toFinset]; exact ⟨hp, h1⟩
  rw [fsum_eq_sum _ S (fun p => d.nP h c G f p * (d.dg (d.gen p) : ℤ))
      (fun p hp h0 => mem p hp fun e => h0 (by simp [e])),
    fsum_eq_sum _ S (fun p => (d.nP h c G f p : ℝ) * h0 (d.gen p))
      (fun p hp h0 => mem p hp fun e => h0 (by simp [e]))]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases hp : p ∈ d.HtOne
  · simp only [Set.indicator_of_mem hp]
    by_cases hg : ∃ w, w ∈ d.GoodP c p
    · have hL := d.logHeight_generator_lower_bound hd h c hp hg
      have hn0 : (0 : ℝ) ≤ d.nP h c G f p := by exact_mod_cast d.nP_nonneg hd h c hp G f hord
      push_cast at hL ⊢
      nlinarith [mul_le_mul_of_nonneg_left hL hn0]
    · push_neg at hg
      have hG : d.GoodP c p = ∅ := Set.eq_empty_iff_forall_notMem.mpr hg
      have e2 : d.nP h c G f p = 0 := by unfold nP; rw [hG]; simp
      rw [e2]; simp
  · simp [Set.indicator_of_notMem hp]

theorem h_four' (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (ta : ∀ c, A c)
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0)
    (hord : ∀ c (v : AddValuation (Ω c) (WithTop ℤ)), d.admitted c v → 0 ≤ d.ord c v G (ta c))
    (hbdd : ∀ sg : K →+* ℂ, BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (ta p.1) p.2))
    (hint : ∀ (c : ι) (sg : K →+* ℂ), MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
          Real.log (d.nrm c G (ta c) P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) :
    -(d.del * meanK (fun sg => Real.log (d.supN sg G ta))) -
        d.D * d.aG h G ta * (Real.log (d.N + 1 : ℕ) + 1 / 2) ≤ d.Hgt h G ta ∧
      (∑ᶠ la, d.NlaG h G ta la * logNorm la) / (Module.finrank ℚ K : ℝ) ≤
        d.Hgt h G ta + d.del * meanK (fun sg => Real.log (d.supN sg G ta)) +
          d.D * d.aG h G ta * (Real.log (d.N + 1 : ℕ) + 1 / 2) := by

  have hA : 0 ≤ (∑ᶠ la, d.NlaG h G ta la * logNorm la) / (Module.finrank ℚ K : ℝ) := by
    refine div_nonneg (finsum_nonneg fun la => mul_nonneg ?_ (logNorm_nonneg la)) (Nat.cast_nonneg _)
    exact Finset.sum_nonneg fun c _ => finsum_nonneg fun w => finsum_nonneg fun hw =>
      mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hord c _ (d.admissible_over_prime hd h la c w hw).1)

  have hB : -(d.del * meanK (fun sg => Real.log (d.supN sg G ta))) ≤ meanK (d.Nsg G ta) := by
    unfold meanK
    rw [← mul_div_assoc, ← neg_div, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun sg _ => ?_) (Nat.cast_nonneg _)
    unfold Nsg del
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun c _ => d.four_sg hd h G ta hta sg (hbdd sg) c (hint c sg)

  have hC : -((d.D : ℝ) * d.aG h G ta * (Real.log (d.N + 1 : ℕ) + 1 / 2)) ≤ d.h0f h G ta := by
    unfold aG h0f
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun c _ => ?_
    have k := d.sum_mult_logHeight_lower hd h G c (ta c) (hta c).1 (hta c).2 (fun v hv => hord c v hv)
    push_cast at k
    exact k
  have hH : d.Hgt h G ta = (∑ᶠ la, d.NlaG h G ta la * logNorm la) / (Module.finrank ℚ K : ℝ) +
      meanK (d.Nsg G ta) + d.h0f h G ta := rfl
  constructor
  · rw [hH]; linarith
  · rw [hH]; linarith

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

theorem h_ind (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) :
    (∀ (G : WT) (ta ta' : ∀ c, A c),
      G ∈ ({d.wL, d.n1 • d.wde, (2 : ℕ) • d.G1, d.wF, d.G2} : Set WT) →
      (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) → (∀ c, ta' c ∈ 𝒜 c G ∧ ta' c ≠ 0) →
      d.Hgt h G ta = d.Hgt h G ta') ∧
    (∀ f f' : ∀ c, A c, (∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) → (∀ c, f' c ∈ 𝒜 c d.wL ∧ f' c ≠ 0) →
      d.HgtMM h f = d.HgtMM h f') ∧
    (∀ x : Fin (d.N + 1) → K, (∀ c, d.wx x c ≠ 0) →
      (d.n1 : ℝ) * d.Hgt h ((2 : ℕ) • d.G1) d.ta1 + 2 * d.Hgt h (d.n1 • d.wde) d.et =
        2 * d.n1 * d.Hgt h d.wL (d.wx x)) ∧
    (∀ (x : Fin (d.N + 1) → K) (ta' : ∀ c, A c), (∀ c, d.wx x c ≠ 0) →
      (∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) →
      d.Hgt h d.wF ta' + d.Hgt h d.G2 d.ta2 = (d.D + 4) * d.Hgt h d.wL (d.wx x)) := by
  exact d.h_ind' hd h hI2be

theorem h_four (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (ta : ∀ c, A c)
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0)
    (hord : ∀ c (v : AddValuation (Ω c) (WithTop ℤ)), d.admitted c v → 0 ≤ d.ord c v G (ta c))
    (hbdd : ∀ sg : K →+* ℂ, BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (ta p.1) p.2))
    (hint : ∀ (c : ι) (sg : K →+* ℂ), MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
          Real.log (d.nrm c G (ta c) P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) :
    -(d.del * meanK (fun sg => Real.log (d.supN sg G ta))) -
        d.D * d.aG h G ta * (Real.log (d.N + 1 : ℕ) + 1 / 2) ≤ d.Hgt h G ta ∧
      (∑ᶠ la, d.NlaG h G ta la * logNorm la) / (Module.finrank ℚ K : ℝ) ≤
        d.Hgt h G ta + d.del * meanK (fun sg => Real.log (d.supN sg G ta)) +
          d.D * d.aG h G ta * (Real.log (d.N + 1 : ℕ) + 1 / 2) := by
  exact d.h_four' hd h G ta hta hord hbdd hint

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
