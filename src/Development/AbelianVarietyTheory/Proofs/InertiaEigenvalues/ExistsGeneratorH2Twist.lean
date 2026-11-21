import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCocyclesQuotientPowSmulModule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import BuildAid.ForwardExisting

section
open ReciprocityTheory.ChartRestriction.T2

namespace GlobalTheory

theorem isPrecomplete_of_compact_isAdic {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] (I : Ideal O) (h : IsAdic I) : IsPrecomplete I O := by
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := exists_clusterPt_of_compactSpace (Filter.map f Filter.atTop)
  refine ⟨L, fun n => ?_⟩
  have hopen : IsOpen ((I ^ n : Ideal O) : Set O) := (isAdic_iff.mp h).1 n
  have hclosed : IsClosed ((I ^ n : Ideal O) : Set O) :=
    AddSubgroup.isClosed_of_isOpen (I ^ n).toAddSubgroup hopen
  have hc : IsClosed {x : O | f n - x ∈ I ^ n} :=
    hclosed.preimage (f := fun x => f n - x) (continuous_const.sub continuous_id)
  have hmem : {x : O | f n - x ∈ I ^ n} ∈ Filter.map f Filter.atTop := by
    rw [Filter.mem_map]
    filter_upwards [Filter.eventually_ge_atTop n] with k hk
    have := hf hk
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    exact this
  have hLm : L ∈ {x : O | f n - x ∈ I ^ n} := by
    rw [← hc.closure_eq]
    exact mem_closure_iff_clusterPt.mpr (hL.mono (Filter.le_principal_iff.mpr hmem))
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  exact hLm

theorem isAdicComplete_of_padicCoeff {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] (h : PadicCoeff p O) : IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  haveI := h.ring
  haveI := h.compact
  haveI := isPrecomplete_of_compact_isAdic _ h.adic
  haveI : IsHausdorff (IsLocalRing.maximalIdeal O) O := inferInstance
  exact ⟨⟩

end GlobalTheory
end

section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_of_padicCoeff' : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], PadicCoeff p O → IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  atlas_forward_decl GlobalTheory.isAdicComplete_of_padicCoeff
end

section
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory

theorem padicInt_ringHom_continuous_of_padicCoeff : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O], PadicCoeff p O → ∀ φ : ℤ_[p] →+* O, Continuous φ := by
  intro p _ O _ _ _ _ hO φ
  haveI := hO.ring
  refine continuous_of_continuousAt_zero φ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := (isAdic_iff.mp hO.adic).2 s hs
  have hball : Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ))) ∈ nhds (0 : ℤ_[p]) := by
    apply Metric.closedBall_mem_nhds
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  refine Filter.mem_map.mpr (Filter.mem_of_superset hball ?_)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, PadicInt.norm_le_pow_iff_mem_span_pow] at hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  apply hn
  show φ (a * (p : ℤ_[p]) ^ n) ∈ ((IsLocalRing.maximalIdeal O) ^ n : Ideal O)
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hO.p_mem n)

end GlobalTheory
end

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_ringHom_continuous_of_padicCoeff' : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], PadicCoeff p O → ∀ φ : ℤ_[p] →+* O, Continuous φ := by
  atlas_forward_decl GlobalTheory.padicInt_ringHom_continuous_of_padicCoeff
end

section
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.CycImage

theorem cyc_eq_image : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G], PadicCoeff p O → ∀ (φ : ℤ_[p] →+* O) (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ g : G, ((ε g : Oˣ) : O) = φ ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) : ℤ_[p]ˣ) : ℤ_[p]) := by
  intro p _ K O _ _ _ _ G _ _ hO φ i ε hε g
  set c : ℤ_[p] := ((cyclotomicCharacter (PadicAlgCl p) p
    (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) : ℤ_[p]ˣ) : ℤ_[p]) with hcdef
  have key : ∀ n : ℕ, ((ε g : Oˣ) : O) - φ c ∈ Ideal.span {(p : O) ^ n} := by
    intro n
    obtain ⟨ζ, hζ⟩ : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ (p ^ n) :=
      HasEnoughRootsOfUnity.exists_primitiveRoot _ _
    obtain ⟨a, ha, hmem⟩ := hε (i g) n ζ hζ.pow_eq_one
    have hcar : ((carry i ε (i g) : Oˣ) : O) = ((ε g : Oˣ) : O) := by
      simp only [carry, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
      congr 2
      exact i.symm_apply_apply g
    rw [hcar] at hmem
    have hsp := cyclotomicCharacter.spec (L := PadicAlgCl p) p (n := n)
      (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) ζ hζ.pow_eq_one
    have h1 : (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) ζ = (i g) ζ := rfl
    rw [h1, ha] at hsp
    set v : ℕ := (PadicInt.toZModPow n c).val with hv
    have hmod : a ≡ v [MOD p ^ n] := by
      have hne : ζ ≠ 0 := hζ.ne_zero (NeZero.ne _)
      have hz : ζ ^ ((a : ℤ) - (v : ℤ)) = 1 := by
        rw [zpow_sub₀ hne, zpow_natCast, zpow_natCast, hsp, div_self (pow_ne_zero _ hne)]
      have hd := (hζ.zpow_eq_one_iff_dvd _).1 hz
      exact (Nat.modEq_iff_dvd.2 (by
        have : ((p ^ n : ℕ) : ℤ) ∣ -((a : ℤ) - (v : ℤ)) := (dvd_neg).2 (by exact_mod_cast hd)
        simpa using this))
    have hc : c - (v : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, hv,
        ZMod.natCast_zmod_val, sub_self]
    have hφ : φ c - (v : O) ∈ Ideal.span {(p : O) ^ n} := by
      have := Ideal.mem_map_of_mem φ hc
      rw [Ideal.map_span, Set.image_singleton] at this
      simpa using this
    have hav : (a : O) - (v : O) ∈ Ideal.span {(p : O) ^ n} := by
      rw [Ideal.mem_span_singleton]
      have hd : ((p ^ n : ℕ) : ℤ) ∣ (v : ℤ) - (a : ℤ) := (Nat.modEq_iff_dvd.1 hmod)
      obtain ⟨k, hk⟩ := hd
      refine ⟨-(k : O), ?_⟩
      have hk' : ((v : ℤ) : O) - ((a : ℤ) : O) = (((p ^ n : ℕ) : ℤ) : O) * (k : O) := by
        rw [← Int.cast_sub, hk, Int.cast_mul]
      push_cast at hk'
      linear_combination -hk'
    have hsum : ((ε g : Oˣ) : O) - φ c =
        ((((ε g : Oˣ) : O) - a) + ((a : O) - v)) - (φ c - v) := by ring
    rw [hsum]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hmem hav) hφ
  have hbot : ((ε g : Oˣ) : O) - φ c ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal O) ^ n := by
    refine Ideal.mem_iInf.2 fun n => ?_
    have h := key n
    have hle : Ideal.span {(p : O) ^ n} ≤ (IsLocalRing.maximalIdeal O) ^ n := by
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem _).2 hO.p_mem) n
    exact hle h
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top, Ideal.mem_bot] at hbot
  exact sub_eq_zero.1 hbot

end GlobalTheory.CycImage
end
end

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_cyclotomicCharacter_of_isCyc : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G], PadicCoeff p O → ∀ (φ : ℤ_[p] →+* O) (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ g : G, ((ε g : Oˣ) : O) = φ ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) : ℤ_[p]ˣ) : ℤ_[p]) := by
  atlas_forward_decl GlobalTheory.CycImage.cyc_eq_image
end

section
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory.PadicH2SeparatedDVR

open GlobalTheory.LocDualInt

theorem discrete_quot {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (P : Submodule O O) (hP : IsOpen (P : Set O)) : DiscreteTopology (O ⧸ P) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P q
  have hq := (Submodule.isOpenQuotientMap_mkQ P).isQuotientMap
  rw [← hq.isOpen_preimage]
  have : (P.mkQ ⁻¹' {Submodule.Quotient.mk x}) = (fun y => y - x) ⁻¹' (P : Set O) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Submodule.mkQ_apply, SetLike.mem_coe]
    exact Submodule.Quotient.eq P
  rw [this]
  exact hP.preimage (continuous_sub_right x)

theorem continuous_mk {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (P : Submodule O O) : Continuous (Submodule.Quotient.mk : O → O ⧸ P) :=
  (Submodule.isOpenQuotientMap_mkQ P).continuous

theorem d1_mk {O : Type} [CommRing O] {G : Type} [Group G] (ε : G →* Oˣ) (ϖ : O) (n : ℕ)
    (b : G → O) :
    d1 (quotRep (twist ε O) ϖ n) (fun g => Submodule.Quotient.mk (b g)) =
      fun p => Submodule.Quotient.mk (d1 (twist ε O) b p) := by
  funext p
  show quotRep (twist ε O) ϖ n p.1 (Submodule.Quotient.mk (b p.2)) - Submodule.Quotient.mk (b (p.1 * p.2))
      + Submodule.Quotient.mk (b p.1) = Submodule.Quotient.mk ((twist ε O) p.1 (b p.2) - b (p.1 * p.2) + b p.1)
  rw [quotRep_mk, Submodule.Quotient.mk_add, Submodule.Quotient.mk_sub]

theorem separated_dvr_second_cohomology_mem : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ) (ϖ : O), (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → (∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((powSub (M := O) ϖ n : Submodule O O) : Set O) ⊆ U) → (∀ n : ℕ, (Z1 (quotRep (twist ε O) ϖ n) : Set (G → O ⧸ powSub (M := O) ϖ n)).Finite) → ∀ (w : G × G → O), w ∈ Z2 (twist ε O) → (∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧ ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) = Submodule.Quotient.mk (w (g, h))) → w ∈ B2 (twist ε O) := by
  intro O _ _ _ _ _ _ _ G _ _ ε ϖ hopen hbasis hfin w hw hmod
  haveI hdisc : ∀ n : ℕ, DiscreteTopology (O ⧸ powSub (M := O) ϖ n) := fun n => discrete_quot _ (hopen n)
  let α : ∀ s : ℕ, Set (G → O ⧸ powSub (M := O) ϖ s) := fun s =>
    {β | Continuous β ∧ d1 (quotRep (twist ε O) ϖ s) β = fun p => Submodule.Quotient.mk (w p)}
  have hα : ∀ s, (α s).Finite := by
    intro s
    rcases Set.eq_empty_or_nonempty (α s) with h | ⟨c, hc⟩
    · rw [h]; exact Set.finite_empty
    refine ((hfin s).image (fun f => f + c)).subset ?_
    rintro β ⟨hβ, hd⟩
    refine ⟨β - c, ⟨hβ.sub hc.1, fun g h => ?_⟩, by simp⟩
    have e : d1 (quotRep (twist ε O) ϖ s) (β - c) (g, h) = 0 := by
      rw [map_sub, hd, hc.2, sub_self]; rfl
    have e2 : quotRep (twist ε O) ϖ s g ((β - c) h) - (β - c) (g * h) + (β - c) g = 0 := e
    have : (β - c) g + quotRep (twist ε O) ϖ s g ((β - c) h) - (β - c) (g * h) = 0 := by
      rw [← e2]; abel
    exact (sub_eq_zero.1 this).symm
  let T : ℕ → Set (G → O) := fun r =>
    ⋂ s, ⋂ (_ : s ≤ r), (fun (b : G → O) g =>
      (Submodule.Quotient.mk (b g) : O ⧸ powSub (M := O) ϖ s)) ⁻¹' α s
  have hcl : ∀ r, IsClosed (T r) := fun r =>
    isClosed_iInter fun s => isClosed_iInter fun _ => (hα s).isClosed.preimage
      (continuous_pi fun g => (continuous_mk _).comp (continuous_apply g))
  have hne : ∀ r, (T r).Nonempty := by
    intro r
    obtain ⟨β, hβc, hβ⟩ := hmod r
    refine ⟨fun g => qlift (β g), Set.mem_iInter₂.2 fun s hs => ⟨?_, ?_⟩⟩
    · have e : (fun g => (Submodule.Quotient.mk (qlift (β g)) : O ⧸ powSub (M := O) ϖ s)) =
          fun g => Submodule.factor (powSub_anti (M := O) ϖ hs) (β g) := by
        funext g
        conv_rhs => rw [← mk_qlift (β g)]
        rfl
      show Continuous (fun g => (Submodule.Quotient.mk (qlift (β g)) : O ⧸ powSub (M := O) ϖ s))
      rw [e]
      exact (continuous_factor ϖ hs).comp hβc
    · rw [d1_mk]
      funext p
      have h1 : (Submodule.Quotient.mk (d1 (twist ε O) (fun g => qlift (β g)) p) :
          O ⧸ powSub (M := O) ϖ r) = Submodule.Quotient.mk (w p) := by
        rw [← congrFun (d1_mk ε ϖ r (fun g => qlift (β g))) p]
        have : (fun g => (Submodule.Quotient.mk (qlift (β g)) : O ⧸ powSub (M := O) ϖ r)) = β :=
          funext fun g => mk_qlift _
        rw [this]
        exact hβ p.1 p.2
      rw [Submodule.Quotient.eq] at h1 ⊢
      exact powSub_anti ϖ hs h1
  have hdec : ∀ r, T (r + 1) ⊆ T r := fun r b hb =>
    Set.mem_iInter₂.2 fun s hs => Set.mem_iInter₂.1 hb s (hs.trans (Nat.le_succ r))
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hcl 0).isCompact hcl
  have hb' : ∀ s, (fun g => (Submodule.Quotient.mk (b g) : O ⧸ powSub (M := O) ϖ s)) ∈ α s :=
    fun s => Set.mem_iInter₂.1 (Set.mem_iInter.1 hb s) s le_rfl
  have hbc : Continuous b := by
    rw [continuous_iff_continuousAt]
    intro x V hV
    have hW : (fun u => u + b x) ⁻¹' V ∈ nhds (0 : O) := by
      apply (continuous_add_const (b x)).continuousAt.preimage_mem_nhds
      simpa using hV
    obtain ⟨n, hn⟩ := hbasis _ hW
    have hloc : {y | (Submodule.Quotient.mk (b y) : O ⧸ powSub (M := O) ϖ n) =
        Submodule.Quotient.mk (b x)} ∈ nhds x :=
      ((isOpen_discrete {(Submodule.Quotient.mk (b x) : O ⧸ powSub (M := O) ϖ n)}).preimage
        (hb' n).1).mem_nhds rfl
    show b ⁻¹' V ∈ nhds x
    refine Filter.mem_of_superset hloc fun y hy => ?_
    have hy' : b y - b x ∈ powSub (M := O) ϖ n := (Submodule.Quotient.eq _).1 hy
    have := hn hy'
    simpa using this
  refine ⟨b, hbc, ?_⟩
  funext p
  have hall : ∀ n : ℕ, d1 (twist ε O) b p - w p ∈ powSub (M := O) ϖ n := by
    intro n
    have := congrFun (hb' n).2 p
    rw [d1_mk] at this
    exact (Submodule.Quotient.eq _).1 this
  by_contra hne'
  have hd : d1 (twist ε O) b p - w p ≠ 0 := sub_ne_zero.2 hne'
  obtain ⟨n, hn⟩ := hbasis _ (isOpen_compl_singleton.mem_nhds (Ne.symm hd))
  exact hn (hall n) rfl

end GlobalTheory.PadicH2SeparatedDVR
end

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoCocycle_mem_coboundaries_of_mod_uniformizer_pow : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ) (ϖ : O), (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → (∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((powSub (M := O) ϖ n : Submodule O O) : Set O) ⊆ U) → (∀ n : ℕ, (Z1 (quotRep (twist ε O) ϖ n) : Set (G → O ⧸ powSub (M := O) ϖ n)).Finite) → ∀ (w : G × G → O), w ∈ Z2 (twist ε O) → (∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧ ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) = Submodule.Quotient.mk (w (g, h))) → w ∈ B2 (twist ε O) := by
  atlas_forward_decl GlobalTheory.PadicH2SeparatedDVR.separated_dvr_second_cohomology_mem
end

section
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory.UnifSpan

open GlobalTheory.TateTop

private theorem quotRep_twist_apply {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {G : Type} [Group G] (ε : G →* Oˣ) (ϖ : O) (n : ℕ) (g : G) (q : O ⧸ powSub (M := O) ϖ n) :
    quotRep (twist ε O) ϖ n g q = ((ε g : Oˣ) : O) • q := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [quotRep_mk, twist_apply, Submodule.Quotient.mk_smul]

private theorem factor_quotRep_of_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {G : Type} [Group G] (ε : G →* Oˣ) (ϖ : O) {m n : ℕ} (hmn : m ≤ n) (g : G)
    (q : O ⧸ powSub (M := O) ϖ n) :
    Submodule.factor (powSub_anti (M := O) ϖ hmn) (quotRep (twist ε O) ϖ n g q) =
      quotRep (twist ε O) ϖ m g (Submodule.factor (powSub_anti (M := O) ϖ hmn) q) := by
  rw [quotRep_twist_apply, quotRep_twist_apply]
  exact map_smul _ _ _

theorem span_mod_pow {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O]
    {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p])
    (hgen : ∀ r, GlobalTheory.TateTop.Gen χ r c) (φ : ℤ_[p] →+* O) (ε : G →* Oˣ)
    (hε : ∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) (ϖ : O) (hϖ : Irreducible ϖ)
    (hp : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (hopen : ∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O))
    (w : G × G → O) (hw : w ∈ Z2 (twist ε O)) :
    ∃ a : O, ∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧
      ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) =
        Submodule.Quotient.mk (w (g, h) - a * φ (c (g, h))) := by
  classical
  have hwZ := (mem_cocycles2 (twist ε O) w).mp hw

  have hp' := hp
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.mem_span_singleton] at hp'
  obtain ⟨t, ht⟩ := hp'

  have hdisc : ∀ n : ℕ, DiscreteTopology (O ⧸ powSub (M := O) ϖ n) := fun n =>
    QuotientAddGroup.discreteTopology (N := (powSub (M := O) ϖ n).toAddSubgroup) (hopen n)

  let S : ℕ → Set O := fun n => {a | ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧
      ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) =
        Submodule.Quotient.mk (w (g, h) - a * φ (c (g, h)))}

  have hne : ∀ n, (S n).Nonempty := by
    intro n
    have := hdisc n
    letI : Module ℤ_[p] (O ⧸ powSub (M := O) ϖ n) := Module.compHom _ φ
    have hsm : ∀ (s : ℤ_[p]) (q : O ⧸ powSub (M := O) ϖ n), s • q = φ s • q := fun _ _ => rfl
    have : CompactSpace (O ⧸ powSub (M := O) ϖ n) := by
      refine ⟨?_⟩
      rw [← (Submodule.mkQ_surjective (powSub (M := O) ϖ n)).range_eq]
      exact isCompact_range (Submodule.continuous_mkQ _)
    have : Finite (O ⧸ powSub (M := O) ϖ n) := finite_of_compact_of_discrete
    have hkill : ∀ m : O ⧸ powSub (M := O) ϖ n, ((p : ℤ_[p]) ^ n) • m = 0 := by
      intro m
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      rw [hsm, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_powSub]
      refine ⟨t ^ n * x, ?_⟩
      rw [map_pow, map_natCast, ht, smul_eq_mul, smul_eq_mul]
      ring
    obtain ⟨-, hex, -⟩ := hgen n (O ⧸ powSub (M := O) ϖ n) hkill
    have hz : IsCoc χ (fun q : G × G => (Submodule.Quotient.mk (w q) : O ⧸ powSub (M := O) ϖ n)) := by
      refine ⟨(IsLocallyConstant.iff_continuous _).mpr ((Submodule.continuous_mkQ _).comp hwZ.1),
        fun g h k => ?_⟩
      have e := hwZ.2 g h k
      rw [twist_apply, hε g] at e
      rw [hsm, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub,
        ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_sub, e, Submodule.Quotient.mk_zero]
    obtain ⟨x, b, hb, hzb⟩ := hex _ hz
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨a, b, hb.continuous, fun g h => ?_⟩
    have e := hzb (g, h)
    simp only [cob, hsm] at e
    rw [d1_apply, quotRep_twist_apply, hε g, Submodule.Quotient.mk_sub, e,
      show a * φ (c (g, h)) = φ (c (g, h)) • a from mul_comm _ _, Submodule.Quotient.mk_smul]
    abel

  have hanti : ∀ n, S (n + 1) ⊆ S n := by
    intro n a ha
    obtain ⟨b, hb, hd⟩ := ha
    refine ⟨fun g => Submodule.factor (powSub_anti (M := O) ϖ (Nat.le_succ n)) (b g),
      (continuous_factor ϖ (Nat.le_succ n)).comp hb, fun g h => ?_⟩
    have e := hd g h
    rw [d1_apply] at e
    rw [d1_apply, ← factor_quotRep_of_le ε ϖ (Nat.le_succ n), ← map_sub, ← map_add, e]
    exact Submodule.factor_mk _ _

  have hclosed : ∀ n, IsClosed (S n) := by
    intro n
    have := hdisc n
    have hpre : S n = (powSub (M := O) ϖ n).mkQ ⁻¹' ((powSub (M := O) ϖ n).mkQ '' S n) := by
      refine (Set.subset_preimage_image _ _).antisymm ?_
      rintro a' ⟨a, ⟨b, hb, hd⟩, hmk⟩
      refine ⟨b, hb, fun g h => ?_⟩
      rw [hd g h, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub]
      congr 1
      rw [Submodule.Quotient.eq]
      have hmk' : Submodule.Quotient.mk (p := powSub (M := O) ϖ n) a =
          Submodule.Quotient.mk a' := hmk
      have hd' := Submodule.smul_mem _ (φ (c (g, h))) ((Submodule.Quotient.eq _).mp hmk')
      rw [smul_eq_mul] at hd'
      convert hd' using 1
      ring
    rw [hpre]
    exact (isClosed_discrete _).preimage (Submodule.continuous_mkQ _)

  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hanti hne
    (hclosed 0).isCompact hclosed
  exact ⟨a, fun n => Set.mem_iInter.mp ha n⟩

end GlobalTheory.UnifSpan
end

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoCocycle_fundamental_multiple_mod_pow : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p]), (∀ r, GlobalTheory.TateTop.Gen χ r c) → ∀ (φ : ℤ_[p] →+* O) (ε : G →* Oˣ), (∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) → ∀ (ϖ : O), Irreducible ϖ → (p : O) ∈ IsLocalRing.maximalIdeal O → (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → ∀ (w : G × G → O), w ∈ Z2 (twist ε O) → ∃ a : O, ∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧ ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) = Submodule.Quotient.mk (w (g, h) - a * φ (c (g, h))) := by
  atlas_forward_decl GlobalTheory.UnifSpan.span_mod_pow
end

section
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory.TateNat

theorem free_inj : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p]), (∀ r, GlobalTheory.TateTop.Gen χ r c) → ∀ (φ : ℤ_[p] →+* O) (ε : G →* Oˣ), (∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) → ∀ (ϖ : O), Irreducible ϖ → (p : O) ∈ IsLocalRing.maximalIdeal O → (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → ∀ (a : O) (f : G → O), Continuous f → (∀ g h : G, d1 (twist ε O) f (g, h) = a * φ (c (g, h))) → a = 0 := by
  intro p _ O _ _ _ _ _ _ G _ _ χ c hgen φ ε hεφ ϖ hϖ hp hopen a f hf hd
  have key : ∀ n : ℕ, a ∈ (powSub (M := O) ϖ n : Submodule O O) := by
    intro n
    set N : Submodule O O := powSub (M := O) ϖ n with hN
    letI : Module ℤ_[p] (O ⧸ N) := Module.compHom (O ⧸ N) φ
    have hs : ∀ (t : ℤ_[p]) (x : O), t • (Submodule.Quotient.mk x : O ⧸ N) =
        Submodule.Quotient.mk (φ t * x) := fun t x => by
      show (φ t) • (Submodule.Quotient.mk x : O ⧸ N) = _
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul]
    haveI : Finite (O ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N.toAddSubgroup (hopen n)
    have hM : ∀ m : O ⧸ N, (p : ℤ_[p]) ^ n • m = 0 := by
      intro m
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        rw [hs, Submodule.Quotient.mk_eq_zero, map_pow, map_natCast]
        rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
        obtain ⟨u, hu⟩ := hp
        refine mem_powSub.2 ⟨u ^ n * x, ?_⟩
        rw [hu, smul_eq_mul, mul_pow]
        ring
    have hlc : IsLocallyConstant (fun g => (Submodule.Quotient.mk (f g) : O ⧸ N)) := by
      intro s
      have ho : IsOpen ((Submodule.Quotient.mk : O → O ⧸ N) ⁻¹' s) := by
        rw [isOpen_iff_forall_mem_open]
        intro x hx
        refine ⟨(fun y => y - x) ⁻¹' (N : Set O), fun y hy => ?_,
          (hopen n).preimage (continuous_id.sub continuous_const), ?_⟩
        · have e : (Submodule.Quotient.mk y : O ⧸ N) = Submodule.Quotient.mk x :=
            (Submodule.Quotient.eq N).2 hy
          show (Submodule.Quotient.mk y : O ⧸ N) ∈ s
          rw [e]
          exact hx
        · show x - x ∈ N
          rw [sub_self]
          exact N.zero_mem
      exact ho.preimage hf
    have h3 := ((hgen n) (O ⧸ N) hM).2.2 (Submodule.Quotient.mk a)
      (fun g => Submodule.Quotient.mk (f g)) hlc fun q => by
        obtain ⟨g, h⟩ := q
        have e := hd g h
        simp only [d1_apply] at e
        change (ε g : O) • f h - f (g * h) + f g = a * φ (c (g, h)) at e
        rw [smul_eq_mul, hεφ] at e
        simp only [GlobalTheory.TateTop.cob, hs]
        rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]
        congr 1
        linear_combination -e
    exact (Submodule.Quotient.mk_eq_zero N).1 h3
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal O)
    (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hmem : a ∈ ⨅ i, (IsLocalRing.maximalIdeal O) ^ i := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    obtain ⟨y, hy⟩ := mem_powSub.1 (key i)
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← hy, smul_eq_mul]
    exact dvd_mul_right _ _
  rw [hbot] at hmem
  exact (Submodule.mem_bot O).1 hmem

end GlobalTheory.TateNat
end

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamentalTwoCocycle_multiple_not_coboundary : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p]), (∀ r, GlobalTheory.TateTop.Gen χ r c) → ∀ (φ : ℤ_[p] →+* O) (ε : G →* Oˣ), (∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) → ∀ (ϖ : O), Irreducible ϖ → (p : O) ∈ IsLocalRing.maximalIdeal O → (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → ∀ (a : O) (f : G → O), Continuous f → (∀ g h : G, d1 (twist ε O) f (g, h) = a * φ (c (g, h))) → a = 0 := by
  atlas_forward_decl GlobalTheory.TateNat.free_inj
end

section
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.FreeTwistH2

theorem powSub_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) (n : ℕ) :
    ((powSub (M := O) ϖ n : Submodule O O) : Set O) = ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := by
  ext x
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, SetLike.mem_coe, SetLike.mem_coe,
    mem_powSub, Ideal.mem_span_singleton']
  simp only [smul_eq_mul, mul_comm]

theorem powSub_open_basis {p : ℕ} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] (hO : PadicCoeff p O) {ϖ : O} (hϖ : Irreducible ϖ) :
    (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) ∧
      ∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((powSub (M := O) ϖ n : Submodule O O) : Set O) ⊆ U := by
  haveI := hO.ring
  obtain ⟨h1, h2⟩ := (isAdic_iff).1 hO.adic
  refine ⟨fun n => ?_, fun U hU => ?_⟩
  · rw [powSub_eq hϖ]; exact h1 n
  · obtain ⟨n, hn⟩ := h2 U hU
    exact ⟨n, by rw [powSub_eq hϖ]; exact hn⟩

theorem exists_free_H2_twist : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O]
    {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K →
    PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) →
    ∃ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) := by
  intro p _ K O _ _ _ _ _ G _ _ hT hK hO i ε hε
  haveI := hO.compact
  haveI := hO.t2
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hopen, hbasis⟩ := powSub_open_basis hO hϖ
  haveI := GlobalTheory.T.isAdicComplete_of_padicCoeff' hO
  have hd : ∀ n : ℕ, ringChar (O ⧸ IsLocalRing.maximalIdeal O ^ n) ∣ p ^ n := fun n => by
    apply ringChar.dvd
    rw [← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)),
      Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow hO.p_mem n
  let φ : ℤ_[p] →+* O := IsAdicComplete.liftRingHom (IsLocalRing.maximalIdeal O)
    (fun n => (ZMod.castHom (hd n) (O ⧸ IsLocalRing.maximalIdeal O ^ n)).comp (PadicInt.toZModPow n))
    (fun {m n} hle => by
      rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
      congr 1
      exact RingHom.ext_zmod _ _)
  have hφ : Continuous φ := GlobalTheory.T.padicInt_ringHom_continuous_of_padicCoeff' hO φ
  let χZ : Formalism.GaloisCohomology.GK p K →* ℤ_[p]ˣ := (cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p))
  have hχc : Continuous fun g => (χZ g : ℤ_[p]) :=
    Units.continuous_val.comp (cyclotomicCharacter.continuous p K (PadicAlgCl p))
  obtain ⟨c, hc⟩ := GlobalTheory.TateTop.exists_gen_all hχc fun r => by
    have : NeZero (p ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    exact GlobalTheory.TateTop.exists_gen hχc
      (hT p K hK (r + 1) (ZMod (p ^ (r + 1))) (ReciprocityTheory.Gal.charRep (GlobalTheory.Cyc.TwistLift.redChar χZ (r + 1)))
        (Nat.succ_pos _) (GlobalTheory.Cyc.TwistLift.contAction_charRep _
          ((GlobalTheory.PadicH2Separated.continuous_reduction _).comp hχc))).1
      fun M _ _ _ _ _ rho hrho => (hT p K hK (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2
  let e : G ≃* Formalism.GaloisCohomology.GK p K := i.toMulEquiv
  have he : Continuous e := i.continuous
  have he' : Continuous e.symm := i.symm.continuous
  let χ : G →* ℤ_[p]ˣ := χZ.comp e.toMonoidHom
  let cG : G × G → ℤ_[p] := fun q => c (e q.1, e q.2)
  have hcG : ∀ r, GlobalTheory.TateTop.Gen χ r cG := fun r => (hc r).transport e he he'
  have hεφ : ∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p]) := fun g => GlobalTheory.T.eq_cyclotomicCharacter_of_isCyc hO φ i hε g
  have hχGc : Continuous fun g => (χ g : ℤ_[p]) := hχc.comp he
  have hεc : Continuous fun g => ((ε g : Oˣ) : O) := by
    simp_rw [hεφ]
    exact hφ.comp hχGc
  have hcont : ContAction (twist ε O) := by
    show Continuous fun q : G × O => twist ε O q.1 q.2
    simp only [twist_apply, smul_eq_mul]
    exact (hεc.comp continuous_fst).mul continuous_snd
  have hfin := fun n => GlobalTheory.T.finite_cocycles_quotient_pow_smul_of_isOpen hT hK hO.p_mem i (twist ε O) hcont ϖ hϖ hopen n
  have hG := fun r => GlobalTheory.GenSpan.gen_zmod (hcG r)
  have hcc : Continuous cG :=
    GlobalTheory.PadicH2Separated.continuous_of_reductions cG fun s => (hG (s + 1)).1.1.continuous
  have hcoc : ∀ g h k, (χ g : ℤ_[p]) * cG (h, k) - cG (g * h, k) + cG (g, h * k) - cG (g, h) = 0 := by
    intro g h k
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    simpa only [map_sub, map_add, map_mul, map_zero] using (hG n).1.2 g h k
  let z0 : G × G → O := fun q => φ (cG q)
  have hz0 : z0 ∈ Z2 (twist ε O) := by
    refine (mem_cocycles2 _ _).2 ⟨hφ.comp hcc, fun g h k => ?_⟩
    simp only [twist_apply, smul_eq_mul, z0, hεφ]
    rw [← map_mul, ← map_sub, ← map_add, ← map_sub, hcoc, map_zero]
  let Z : H2 (twist ε O) := Submodule.Quotient.mk ⟨z0, hz0⟩
  refine ⟨Z, fun a b hab => ?_, fun y => ?_⟩
  · have h0 : (a - b) • Z = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.2 hab
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨f, hf, hfd⟩ := (separated_dvr_second_cohomology_mem _ _).1 h0
    refine sub_eq_zero.1 (GlobalTheory.T.fundamentalTwoCocycle_multiple_not_coboundary χ cG hcG φ ε hεφ ϖ hϖ hO.p_mem hopen (a - b) f hf
      fun g h => ?_)
    have e1 := congrFun hfd (g, h)
    rw [e1]
    rfl
  · induction y using Submodule.Quotient.induction_on with
    | H w =>
      obtain ⟨a, ha⟩ := GlobalTheory.T.twoCocycle_fundamental_multiple_mod_pow χ cG hcG φ ε hεφ ϖ hϖ hO.p_mem hopen w.1 w.2
      refine ⟨a, ?_⟩
      show a • Z = Submodule.Quotient.mk w
      rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq]
      show (w.1 - a • z0) ∈ B2 (twist ε O)
      refine GlobalTheory.T.twoCocycle_mem_coboundaries_of_mod_uniformizer_pow ε ϖ hopen hbasis hfin _
        (sub_mem w.2 (Submodule.smul_mem _ a hz0)) fun n => ?_
      obtain ⟨b, hb, hbd⟩ := ha n
      exact ⟨b, hb, fun g h => by rw [hbd]; rfl⟩

end GlobalTheory.FreeTwistH2
end
end

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_H2_twist : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∃ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) := by
  atlas_forward_decl GlobalTheory.FreeTwistH2.exists_free_H2_twist
end
