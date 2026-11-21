import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.ShortIsot
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsProj
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.IwasawaBase
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.FiniteDimensionalFromLinearForms
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdelClassFin
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.DensRat
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.SecondOrderExpAtInfinitePlace
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.LocalPointData
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.HeightBoundSetup
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceCoveringDivisor

section
open Matrix MeasureTheory NumberField Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S Formalism.L2.SG.ProjRows Formalism.L2.SG.RowsDef Formalism.L2.SG.Pf Formalism.MainNotions.LeviCoordinates

theorem dense_bdd {X : Type} [MeasurableSpace X] (μ : Measure X) :
    Dense {F : Lp ℂ 2 μ | ∃ M : ℝ, ∀ᵐ x ∂μ, ‖(F : X → ℂ) x‖ ≤ M} := by
  refine (Lp.simpleFunc.dense (E := ℂ) (μ := μ) (p := 2) (by simp)).mono fun F hF => ?_
  let f : Lp.simpleFunc ℂ 2 μ := ⟨F, hF⟩
  obtain ⟨M, hM⟩ := (Lp.simpleFunc.toSimpleFunc f).exists_forall_norm_le
  refine ⟨M, ?_⟩
  filter_upwards [Lp.simpleFunc.toSimpleFunc_eq_toFun f] with x hx
  rw [show (F : X → ℂ) x = Lp.simpleFunc.toSimpleFunc f x from hx.symm]
  exact hM x

theorem rowsFinDim_of (hCore : Core) (hFin : FiniteDimensionalFromLinearForms) (hCA : CuspAdel) (hD : GFDisc) (hLev : LevelOf)
    (hCR : ConvRep) (hRC : RepOfConv) : RowsFinDim := by
  intro I μf _ _ fund hfund R hR e Re hlc hsupp hRe H _ _ _ σ dv w hU _ hF hw hL T hT
  have : LocallyCompactSpace I.Gf := gf_locallyCompact I
  have : T2Space I.Gf := finite_adeles_group_t2 I
  have : SecondCountableTopology I.Gf := rr_secondCountable I μf
  have hright : (I.muA μf).IsMulRightInvariant := Formalism.L2.S.S7.IwasawaBase.muA_right I μf
  have : (I.muA μf).IsHaarMeasure := by
    have h1 : (I.muA μf).IsOpenPosMeasure := by unfold AutInst.muA; infer_instance
    have h2 : (I.muA μf).IsMulLeftInvariant := rr_muA_left I μf
    have h3 : IsLocallyFiniteMeasure (I.muA μf) := by unfold AutInst.muA; infer_instance
    exact {}
  have hlf : IsLocallyFiniteMeasure μf := inferInstance
  let X : Formalism.MainNotions.BridgeLemma.CData :=
    { I := I, b := 0, lam := 0, g := 0, g₀ := 0, e := e, H := fun _ => ℂ, σ := fun _ _ => 0, w := 0,
      Hs := ℂ, σs := fun _ => 0, tens := fun _ => 0, μf := μf, fund := fund, R := R, Re := Re, h := 0 }
  have hd : RegData X := ⟨‹_›, hfund, hR⟩
  have hu : UnimodA X := hright
  obtain ⟨hmul, -, hiso, -⟩ := adelic_regular_rep_unitary_continuous X hd hu hlf
  have hmeas := regular_rep_coeff_measurable X hd hu
  set ph := phInf I σ w dv with hph
  have hphI : Integrable ph (muInf I) := phInf_int I hL
  have hconv := phInf_conv I hU hF hw
  have hφ₀ : Integrable (fun p : I.GA => ph p.1 * e p.2) (I.muA μf) := hphI.mul_prod hRe.1
  have hpr := prod_op_eq (muInf I) μf R hmul hiso (fun x y => (hmeas x y).aestronglyMeasurable) ph e hφ₀ T Re hT hRe.2
  have hRT : I.IsRConv μf fund R (fun p => ph p.1 * e p.2) (Re.comp T) := ⟨hφ₀, fun x y => (hpr x y).2.symm⟩
  obtain ⟨Kp, hKo, hKc, hKe⟩ := hLev I e hlc hsupp
  have hK0 : μf Kp ≠ 0 := (hKo.measure_pos μf ⟨1, Kp.one_mem⟩).ne'
  have hK1 : μf Kp ≠ ∞ := hKc.measure_lt_top.ne
  have hind : Integrable ((Kp : Set I.Gf).indicator fun _ => (((μf Kp).toReal⁻¹ : ℝ) : ℂ)) μf :=
    (integrable_indicator_iff hKo.measurableSet).2 (integrableOn_const hK1)
  have hφ : Integrable (phK I μf ph Kp) (I.muA μf) := hphI.mul_prod hind
  have hφφ₀ : ∀ z : I.GA, ∫ y, phK I μf ph Kp y * (ph (y⁻¹ * z).1 * e (y⁻¹ * z).2) ∂(I.muA μf) = ph z.1 * e z.2 := by
    intro z
    have e1 : (fun y : I.GA => phK I μf ph Kp y * (ph (y⁻¹ * z).1 * e (y⁻¹ * z).2)) = fun y =>
        (ph y.1 * ph (y.1⁻¹ * z.1)) *
          (Kp : Set I.Gf).indicator (fun _ => (((μf Kp).toReal⁻¹ : ℝ) : ℂ) * e z.2) y.2 := by
      funext y
      by_cases hy : y.2 ∈ Kp
      · have hy' : y.2 ∈ (Kp : Set I.Gf) := hy
        simp only [phK, Set.indicator_of_mem hy', Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
          hKe _ (Kp.inv_mem hy)]
        ring
      · have hy' : y.2 ∉ (Kp : Set I.Gf) := hy
        simp only [phK, Set.indicator_of_notMem hy', mul_zero, zero_mul]
    rw [e1]
    refine (integral_prod_mul (μ := muInf I) (ν := μf) (fun g => ph g * ph (g⁻¹ * z.1)) _).trans ?_
    rw [hconv, integral_indicator_const _ hKo.measurableSet, Measure.real, Complex.real_smul, ← mul_assoc ((μf Kp).toReal : ℂ),
      ← Complex.ofReal_mul, mul_inv_cancel₀ (ENNReal.toReal_pos hK0 hK1).ne', Complex.ofReal_one, one_mul]
  have hFD := rr_isFD (rr_FD_of I μf fund hfund)
  have hO : IsClopen {g : I.GA | g.2 ∈ Kp} :=
    IsClopen.preimage (s := (Kp : Set I.Gf)) ⟨Kp.isClosed_of_isOpen hKo, hKo⟩ continuous_snd
  have hdet := hCore I.GA (I.muA μf) (rr_GF I) fund hFD (fun C hC => hD I C hC) (phK I μf ph Kp) _ hφ hO
    (fun y hy => by
      have hy' : y.2 ∉ (Kp : Set I.Gf) := hy
      simp only [phK, Set.indicator_of_notMem hy', mul_zero])
    (hCA I μf (rr_GF I) rfl Kp hKo hKc ph hphI hconv)
  refine hFin I.GA (I.muA μf) (rr_GF I) fund _ hφ hdet _ ?_
  rintro _ ⟨F₀, rfl⟩
  refine map_mem_closure (f := Re.comp T) (Re.comp T).continuous (dense_bdd _ F₀) fun F hFb => ?_
  obtain ⟨s, hs, hsb, hsi, hae⟩ := hCR I μf fund hfund R hR _ _ hRT F hFb
  exact ⟨_, hRC I.GA (I.muA μf) (rr_GF I) _ _ s hφ hφ₀ hφφ₀ hs hsb hsi, hae⟩

end CompanionTheory.D.gk.RF
end
end

section
open MeasureTheory Topology Filter Set
open scoped ENNReal Pointwise

noncomputable section

namespace CompanionTheory.D.gk.RF

theorem Disc.countable {G : Type} [Group G] [TopologicalSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
    {Λ : Subgroup G} (h : Disc Λ) : Countable Λ := by
  have : (Λ : Set G).Countable := by
    have e : (Λ : Set G) = ⋃ n, compactCovering G n ∩ Λ := by rw [← iUnion_inter, iUnion_compactCovering, univ_inter]
    rw [e]
    exact countable_iUnion fun n => (h _ (isCompact_compactCovering G n)).countable
  exact this.to_subtype

theorem Disc.exists_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] {Λ : Subgroup G} (h : Disc Λ) :
    ∃ O ∈ 𝓝 (1 : G), ∀ a ∈ O, ∀ b ∈ O, a * b⁻¹ ∈ Λ → a = b := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hcl : IsClosed ((K ∩ Λ) \ {1}) := ((h K hK).subset sdiff_subset).isClosed
  have hW : K ∩ ((K ∩ Λ) \ {1})ᶜ ∈ 𝓝 (1 : G) := inter_mem hK1 (hcl.isOpen_compl.mem_nhds fun h => h.2 rfl)
  obtain ⟨O, hO, hOW⟩ := exists_nhds_split_inv hW
  refine ⟨O, hO, fun a ha b hb hab => ?_⟩
  have := hOW a ha b hb
  rw [div_eq_mul_inv] at this
  by_contra hne
  exact this.2 ⟨⟨this.1, hab⟩, fun e => hne (mul_inv_eq_one.1 e)⟩

theorem fundamental_domain_inclusion : FundIn := by
  classical
  intro N _ _ _ _ _ _ _ _ Λ hd V hV hcov
  obtain ⟨O, hO, hinj⟩ := hd.exists_nhds
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.countable_cover_nhds
    (f := fun p : N => interior ((fun x => x * p⁻¹) ⁻¹' O)) fun p =>
      interior_mem_nhds.2 ((continuous_id.mul continuous_const).continuousAt.preimage_mem_nhds (by simpa using hO))
  have hTne : T.Nonempty := by
    have : (1 : N) ∈ ⋃ x ∈ T, interior ((fun y => y * x⁻¹) ⁻¹' O) := hT ▸ mem_univ _
    obtain ⟨p, hp, -⟩ := mem_iUnion₂.1 this
    exact ⟨p, hp⟩
  obtain ⟨p, rfl⟩ := hTc.exists_eq_range hTne
  let W : ℕ → Set N := fun i => V ∩ interior ((fun x => x * (p i)⁻¹) ⁻¹' O)
  have hWo : ∀ i, IsOpen (W i) := fun i => hV.inter isOpen_interior
  let S : ℕ → Set N := fun i => {m | ∃ l ∈ Λ, l * m ∈ W i}
  have hSo : ∀ i, IsOpen (S i) := fun i => by
    have : S i = ⋃ l ∈ Λ, (fun m => l * m) ⁻¹' W i := by ext m; simp [S]
    rw [this]
    exact isOpen_biUnion fun l _ => (hWo i).preimage (continuous_const.mul continuous_id)
  have hSi : ∀ i, ∀ l ∈ Λ, ∀ m, l * m ∈ S i ↔ m ∈ S i := fun i l hl m =>
    ⟨fun ⟨l', hl', h⟩ => ⟨l' * l, Λ.mul_mem hl' hl, by rwa [mul_assoc]⟩,
      fun ⟨l', hl', h⟩ => ⟨l' * l⁻¹, Λ.mul_mem hl' (Λ.inv_mem hl), by simpa [mul_assoc] using h⟩⟩
  have hex : ∀ m, ∃ i, m ∈ S i := fun m => by
    obtain ⟨l, hl, hlm⟩ := hcov m
    have : l * m ∈ ⋃ x ∈ range p, interior ((fun y => y * x⁻¹) ⁻¹' O) := hT ▸ mem_univ _
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := mem_iUnion₂.1 this
    exact ⟨i, l, hl, hlm, hi⟩
  refine ⟨⋃ i, W i \ ⋃ j < i, S j, MeasurableSet.iUnion fun i => (hWo i).measurableSet.diff
    (isOpen_biUnion fun j _ => hSo j).measurableSet, iUnion_subset fun i => sdiff_subset.trans inter_subset_left,
    fun m => ?_⟩
  have key : ∀ l : Λ, ∀ i, (l : N) * m ∈ W i \ ⋃ j < i, S j → i = Nat.find (hex m) := fun l i h => by
    refine ((Nat.find_eq_iff (hex m)).2 ⟨⟨l, l.2, h.1⟩, fun j hj hm => h.2 ?_⟩).symm
    exact mem_iUnion₂.2 ⟨j, hj, (hSi j l l.2 m).2 hm⟩
  obtain ⟨l, hl, hlm⟩ := Nat.find_spec (hex m)
  refine ⟨⟨l, hl⟩, mem_iUnion.2 ⟨_, hlm, fun h => ?_⟩, fun l' hl' => ?_⟩
  · obtain ⟨j, hj, hm⟩ := mem_iUnion₂.1 h
    exact Nat.find_min (hex m) hj ((hSi j l hl m).1 hm)
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hl'
    obtain rfl := key l' i hi
    have a1 := mem_preimage.1 (interior_subset hi.1.2)
    have a2 := mem_preimage.1 (interior_subset hlm.2)
    have := hinj _ a1 _ a2 (by
      simpa [mul_assoc] using Λ.mul_mem l'.2 (Λ.inv_mem hl))
    exact Subtype.ext (mul_right_cancel (mul_right_cancel this))

theorem averaging_of_fundamental_domain : FundIn → Avg := by
  intro hF G _ _ _ _ _ _ _ _ N Λ hN hle hd V hV hVc hcov
  have : LocallyCompactSpace N := hN.locallyCompactSpace
  have : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  let Λ' : Subgroup N := Λ.subgroupOf N
  have hd' : Disc Λ' := fun C hC =>
    ((hd _ (hC.image continuous_subtype_val)).preimage Subtype.val_injective.injOn).subset
      fun x hx => ⟨mem_image_of_mem _ hx.1, hx.2⟩
  have := hd'.countable
  obtain ⟨D, hDm, hDV, hD⟩ := hF N Λ' hd' (Subtype.val ⁻¹' V) (hV.preimage continuous_subtype_val) fun m => by
    obtain ⟨l, hl, h⟩ := hcov m m.2
    exact ⟨⟨l, hle hl⟩, hl, h⟩
  let μ : Measure N := Measure.haar
  have hFD : ∀ g : N, IsFundamentalDomain Λ' ((fun x => x * g) ⁻¹' D) μ := fun g =>
    IsFundamentalDomain.mk' (measurable_mul_const g hDm).nullMeasurableSet fun m => by
      simpa [Subgroup.smul_def, mul_assoc] using hD (m * g)
  have hFD1 : IsFundamentalDomain Λ' D μ := by simpa using hFD 1
  have hfin : μ D ≠ ∞ := ((measure_mono (hDV.trans (preimage_mono subset_closure))).trans_lt
    (hN.isClosedEmbedding_subtypeVal.isCompact_preimage hVc).measure_lt_top).ne
  have hpos : μ D ≠ 0 := hFD1.measure_ne_zero (NeZero.ne μ)
  have hR : ∀ g : N, μ.map (fun x => x * g) = μ := fun g => by
    have h1 := Measure.isMulLeftInvariant_eq_smul (μ.map fun x => x * g) μ
    have h2 := congrArg (fun m : Measure N => m D) h1
    simp only [Measure.map_apply (measurable_mul_const g) hDm, Measure.smul_apply] at h2
    rw [(hFD g).measure_eq hFD1, ENNReal.smul_def, smul_eq_mul] at h2
    have h3 : ((μ.map fun x => x * g).haarScalarFactor μ : ℝ≥0∞) = 1 :=
      (ENNReal.mul_left_inj hpos hfin).1 (h2.symm.trans (one_mul _).symm)
    rw [h1, show (μ.map fun x => x * g).haarScalarFactor μ = 1 by exact_mod_cast h3, one_smul]
  have hE : MeasurableEmbedding (Subtype.val : N → G) := MeasurableEmbedding.subtype_coe hN.measurableSet
  have hP : IsProbabilityMeasure ((μ D)⁻¹ • μ.restrict D) :=
    ⟨by rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]⟩
  refine ⟨((μ D)⁻¹ • μ.restrict D).map Subtype.val, Measure.isProbabilityMeasure_map hE.measurable.aemeasurable,
    hE.ae_map_iff.2 (Measure.ae_smul_measure ((ae_restrict_mem hDm).mono fun x hx => hDV hx) _),
    fun u _ hu m₀ hm₀ y => ?_⟩
  rw [hE.integral_map, hE.integral_map, integral_smul_measure, integral_smul_measure]
  congr 1
  let g : N := ⟨m₀, hm₀⟩
  have hmp : MeasurePreserving (fun x : N => x * g⁻¹) μ μ := ⟨measurable_mul_const _, hR _⟩
  rw [← (hFD g⁻¹).setIntegral_eq hFD1 (f := fun m : N => u (m * y)) fun l x => by
      show u (((l : N) : G) * x * y) = _
      rw [mul_assoc]; exact hu _ l.2 _,
    ← hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight g⁻¹) (fun m : N => u (m * (m₀ * y))) D]
  congr 1
  funext x
  simp [g]

theorem parabolic_subgroup_decomposition : ParPi := by
  intro ι _ _ G _ _ _ i₀ N a Ht P
  refine ⟨(continuous_mulSingle i₀).comp P.cont, fun s t => by rw [P.add, Pi.mulSingle_mul], ?_,
    P.hcont.comp (continuous_apply i₀), ?_, fun t g => by simp [P.ha], ?_, fun U hU => ?_⟩
  · rintro t _ ⟨m, hm, rfl⟩
    refine ⟨_, P.norm t m hm, ?_⟩
    simp [Pi.mulSingle_mul, Pi.mulSingle_inv]
  · rintro _ ⟨m, hm, rfl⟩ g
    simp [P.hN m hm]
  · obtain ⟨c, hc, hb⟩ := P.bd
    exact ⟨fun y => c (y i₀), hc.comp (continuous_apply i₀), fun x y => hb _ _⟩
  · obtain ⟨τ, hτ, h⟩ := P.small (Pi.mulSingle i₀ ⁻¹' U)
      ((continuous_mulSingle i₀).continuousAt.preimage_mem_nhds (by simpa using hU))
    refine ⟨τ, hτ, fun t ht x => ?_⟩
    obtain ⟨m, hm, hx⟩ := h t ht (x i₀)
    refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
    refine (congrArg (· ∈ U) ?_).mpr (mem_preimage.1 hx)
    funext i
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [Pi.mulSingle_eq_of_ne hi]

end CompanionTheory.D.gk.RF
end
end

section
open MeasureTheory Topology Filter Set Matrix NumberField
open scoped ENNReal Pointwise InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S Formalism.L2.SG.ProjRows Formalism.MainNotions.LeviCoordinates

theorem exists_GF (I : AutInst) (x : I.Gf) (hx : x ∈ PI.AdelClassFin.GFf I) : ∃ g : I.Ginf, (g, x) ∈ I.GFset := by
  obtain ⟨γ, hγ, h⟩ := hx
  exact ⟨fun v => Formalism.L2.S.S7.DensRat.ratReal I γ hγ v, γ, hγ, fun _ => rfl, h⟩

theorem adelic_cusp_of_infinite_cusp : CuspInf → CongK → CuspAdel := by
  intro hCI hCK I μf _ _ Γ hΓ Kp hKo hKc ph hph hconv U hU
  have : SecondCountableTopology I.Gf := rr_secondCountable I μf
  have : (I.muA μf).IsMulLeftInvariant := rr_muA_left I μf
  have : T2Space I.Gf := Formalism.L2.SG.Pf.finite_adeles_group_t2 I
  have hmem : ∀ {g : I.GA}, g ∈ I.GFset → g ∈ Γ := fun h => by rw [← SetLike.mem_coe, hΓ]; exact h
  obtain ⟨S, hS⟩ := _root_.adelic_class_set_finite I Kp hKo
  have hU' : (fun g : I.Ginf => ((g, 1) : I.GA)) ⁻¹' U ∈ 𝓝 1 :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds hU
  have hs : ∀ s : I.Gf, ∃ M : ℕ, 1 ≤ M ∧ ∀ g ∈ GamSet I M, ∃ x, s⁻¹ * x * s ∈ Kp ∧ (g, x) ∈ I.GFset := fun s =>
    hCK I ((fun x => s⁻¹ * x * s) ⁻¹' Kp) ((hKo.preimage (by fun_prop)).mem_nhds (by simp))
  choose M hM hMK using hs
  choose C hC hCy using fun s => hCI I (M s) (hM s) ph hph hconv _ hU'
  refine ⟨⋃ s ∈ S, C s ×ˢ ((fun k => s * k) '' Kp), S.isCompact_biUnion fun s _ =>
    (hC s).prod (hKc.image (continuous_const.mul continuous_id)), fun x => ?_⟩
  obtain ⟨γf, hγf, s, hsS, k, hk, hx⟩ := hS x.2
  obtain ⟨g₀, hg₀⟩ := exists_GF I γf hγf
  obtain ⟨y, hxe⟩ : ∃ y : I.Ginf, x = (g₀, γf) * (y, s * k) :=
    ⟨g₀⁻¹ * x.1, Prod.ext (by simp) (by simp [hx, mul_assoc])⟩
  generalize ((g₀, γf) : I.GA) = γ₀ at hxe hg₀
  rcases hCy s y with ⟨γ, hγ, hγy⟩ | ⟨ν, hν, hνU, hv⟩
  · obtain ⟨xf, hxf, hGF⟩ := hMK s γ hγ
    refine Or.inl ⟨(γ, xf) * γ₀⁻¹, Γ.mul_mem (hmem hGF) (Γ.inv_mem (hmem hg₀)), mem_iUnion₂.2 ⟨s, hsS, ?_⟩⟩
    rw [hxe, mul_assoc, inv_mul_cancel_left]
    exact ⟨hγy, s⁻¹ * xf * s * k, Kp.mul_mem hxf hk, by simp [mul_assoc]⟩
  right
  let j : I.Ginf → I.GA := fun m => γ₀ * (m, 1) * γ₀⁻¹
  have hjE : MeasurableEmbedding j :=
    (measurableEmbedding_mulRight γ₀⁻¹).comp ((measurableEmbedding_mulLeft γ₀).comp
      (measurableEmbedding_prod_mk_right 1))
  refine ⟨ν.map j, Measure.isProbabilityMeasure_map hjE.measurable.aemeasurable, hjE.ae_map_iff.2 (hνU.mono fun m hm => ?_),
    fun h hh z hz => ?_⟩
  · have : x⁻¹ * j m * x = (y⁻¹ * m * y, 1) := by
      rw [hxe]
      refine Prod.ext ?_ ?_ <;> simp [j, mul_assoc]
    rw [this]
    exact hm
  have hK0 : μf Kp ≠ 0 := (hKo.measure_pos μf ⟨1, Kp.one_mem⟩).ne'
  have hK1 : μf Kp ≠ ∞ := hKc.measure_lt_top.ne
  obtain ⟨hhc, B, hB⟩ := hh.1
  have hright : ∀ k ∈ Kp, ∀ g f, h (g, f * k) = h (g, f) := fun k hk g f => by
    rw [hh.2.2 (g, f * k), hh.2.2 (g, f),
      ← integral_mul_left_eq_self (fun w => phK I μf ph Kp w * h ((g, f) * w)) ((1, k) : I.GA)]
    congr 1
    funext w
    have e1 : phK I μf ph Kp ((1, k) * w) = phK I μf ph Kp w := by
      simp only [phK, Prod.fst_mul, Prod.snd_mul, one_mul]
      congr 1
      by_cases hw : w.2 ∈ Kp
      · rw [indicator_of_mem (show w.2 ∈ (Kp : Set I.Gf) from hw),
          indicator_of_mem (show k * w.2 ∈ (Kp : Set I.Gf) from Kp.mul_mem hk hw)]
      · rw [indicator_of_notMem (show w.2 ∉ (Kp : Set I.Gf) from hw), indicator_of_notMem
          (show k * w.2 ∉ (Kp : Set I.Gf) from fun h => hw ((Kp.mul_mem_cancel_left hk).1 h))]
    rw [e1, ← mul_assoc ((g, f) : I.GA), show ((g, f) : I.GA) * (1, k) = (g, f * k) by simp]
  have hind : Integrable ((Kp : Set I.Gf).indicator fun _ => (((μf Kp).toReal⁻¹ : ℝ) : ℂ)) μf :=
    (integrable_indicator_iff hKo.measurableSet).2 (integrableOn_const hK1)
  have h0 := hv (fun g => h (g, s)) ⟨hhc.comp (by fun_prop), B, fun _ => hB _⟩
    (fun γ hγ g => by
      obtain ⟨xf, hxf, hGF⟩ := hMK s γ hγ
      have := hh.2.1 _ (hmem hGF) (g, s)
      rw [Prod.mk_mul_mk, show xf * s = s * (s⁻¹ * xf * s) by group, hright _ hxf] at this
      exact this)
    (fun g => by
      have e1 : (fun w : I.GA => phK I μf ph Kp w * h ((g, s) * w)) = fun w => (ph w.1 * h (g * w.1, s)) *
          (Kp : Set I.Gf).indicator (fun _ => (((μf Kp).toReal⁻¹ : ℝ) : ℂ)) w.2 := by
        funext w
        by_cases hw : w.2 ∈ Kp
        · have : h ((g, s) * w) = h (g * w.1, s) := hright _ hw _ _
          rw [this, phK]; ring
        · simp only [phK, indicator_of_notMem (show w.2 ∉ (Kp : Set I.Gf) from hw), mul_zero, zero_mul]
      rw [hh.2.2 (g, s), e1]
      refine (integral_prod_mul (μ := muInf I) (ν := μf) (fun z => ph z * h (g * z, s)) _).trans ?_
      rw [integral_indicator_const _ hKo.measurableSet, Measure.real, Complex.real_smul, ← Complex.ofReal_mul,
        mul_inv_cancel₀ (ENNReal.toReal_pos hK0 hK1).ne', Complex.ofReal_one, mul_one]) (y * z.1)
  rw [hjE.integral_map, ← h0]
  congr 1
  funext m
  have : j m * x * z = γ₀ * (m * (y * z.1), s * (k * z.2)) := by
    rw [hxe]
    refine Prod.ext ?_ ?_ <;> simp [j, mul_assoc]
  rw [this, hh.2.1 _ (hmem hg₀), hright _ (Kp.mul_mem hk hz)]

theorem convolution_operator_representation : ConvRep := by
  intro I μf _ _ fund hfund R hR φ₀ T hT Fv ⟨M, hM⟩
  have : SecondCountableTopology I.Gf := rr_secondCountable I μf
  have : (I.muA μf).IsMulLeftInvariant := rr_muA_left I μf
  have : (I.muA μf).IsMulRightInvariant := Formalism.L2.S.S7.IwasawaBase.muA_right I μf
  have : SigmaFinite (I.muA μf) := rr_muA_sigmaFinite I μf
  set μ := I.muA μf
  have hFD := rr_FD_of I μf fund hfund
  obtain ⟨r, hrm, hr⟩ := rr_exists_meas_rep hFD
  let f₀ := (Lp.aestronglyMeasurable Fv).mk
  have hf₀ : Measurable f₀ := (Lp.aestronglyMeasurable Fv).stronglyMeasurable_mk.measurable
  let f : I.GA → ℂ := {x | ‖f₀ x‖ ≤ M}.indicator f₀
  have hf : Measurable f := hf₀.indicator (measurableSet_le hf₀.norm measurable_const)
  have hfb : ∀ x, ‖f x‖ ≤ |M| := fun x => by
    by_cases hx : x ∈ {x | ‖f₀ x‖ ≤ M}
    · rw [show f x = f₀ x from indicator_of_mem hx _]; exact hx.trans (le_abs_self M)
    · rw [show f x = 0 from indicator_of_notMem hx _, norm_zero]; exact abs_nonneg M
  have hfe : ∀ᵐ x ∂μ, x ∈ fund → (Fv : I.GA → ℂ) x = f x := by
    rw [← ae_restrict_iff' hfund.1]
    filter_upwards [hM, (Lp.aestronglyMeasurable Fv).ae_eq_mk] with x h1 h2
    rw [show f x = f₀ x from indicator_of_mem (show x ∈ {x | ‖f₀ x‖ ≤ M} from (congrArg norm h2).ge.trans h1) _]
    exact h2
  have hN : ∀ᵐ x ∂μ, x ∉ rr_N (rr_GF I) fund := compl_mem_ae_iff.2 (rr_N_null hFD)
  have hrep : ∀ x, x ∉ rr_N (rr_GF I) fund → I.rep fund x = r x := fun x hx => by
    obtain ⟨γ, h1, h2, h3⟩ := hr x
    rw [h2]; exact rr_rep_eq hFD hx h1 h3
  have hse : ∀ᵐ x ∂μ, I.ext Fv x = f (r x) := by
    have h1 : ∀ᵐ x ∂μ, ∀ γ : rr_GF I, (γ : I.GA) * x ∈ fund → (Fv : I.GA → ℂ) (γ * x) = f (γ * x) :=
      ae_all_iff.2 fun γ => (measurePreserving_mul_left μ (γ : I.GA)).quasiMeasurePreserving.ae hfe
    filter_upwards [h1, hN] with x a b
    obtain ⟨γ, h1, h2, h3⟩ := hr x
    show (Fv : I.GA → ℂ) (I.rep fund x) = _
    rw [hrep x b, h2]
    exact a ⟨γ, h1⟩ h3
  have hs : Measurable fun x => f (r x) := hf.comp hrm
  refine ⟨fun x => f (r x), hs, ⟨_, fun _ => hfb _⟩, fun γ hγ => ?_, ?_⟩
  · filter_upwards [hN] with x hx
    rw [← hrep x hx, ← hrep _ (rr_N_smul (Γ := rr_GF I) hγ hx)]
    exact congrArg f (rr_rep_smul hFD hγ hx)
  have hm2 : Measurable fun p : I.GA × I.GA => f (r (p.1 * p.2)) := hs.comp measurable_mul
  have hI : ∀ A : Set I.GA, (μ.restrict fund) A < ∞ →
      Integrable (fun p : I.GA × I.GA => φ₀ p.2 * f (r (p.1 * p.2))) (((μ.restrict fund).restrict A).prod μ) :=
    fun A hA => by
      have : IsFiniteMeasure ((μ.restrict fund).restrict A) := ⟨by rwa [Measure.restrict_apply_univ]⟩
      exact (hT.1.comp_snd _).mul_bdd hm2.aestronglyMeasurable (Eventually.of_forall fun _ => hfb _)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ hA => integrableOn_Lp_of_measure_ne_top _ one_le_two hA.ne)
    (fun A _ hA => (hI A hA).integral_prod_left) fun A hAm hA => ?_
  rw [← L2.inner_indicatorConstLp_one hAm hA.ne, hT.2, integral_integral_swap (hI A hA)]
  congr 1
  funext y
  rw [L2.inner_indicatorConstLp_one, integral_const_mul]
  congr 1
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hR y Fv, ae_restrict_of_ae ((measurePreserving_mul_right μ y).quasiMeasurePreserving.ae hse)]
    with x a b
  rw [a, b]

end CompanionTheory.D.gk.RF
end
end

section
open MeasureTheory Topology Filter Set Matrix NumberField
open scoped ENNReal Pointwise

noncomputable section

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S Formalism.L2.SG.ProjRows Formalism.MainNotions.LeviCoordinates

theorem cuspidal_at_infinity_of : Sel → Avg → NWSub → RealPar → ParPi → Transp → GamSub → GeoInf → CuspInf := by
  classical
  intro hSel hAvg hNW hRP hPi hT hGam hGeo I M hM ph hph hconv U hU
  obtain ⟨K, hKn, hKU, hK⟩ := local_compact_nhds hU
  obtain ⟨C, hC, hy⟩ := hGeo I M hM (interior K) (interior_mem_nhds.2 hKn)
  refine ⟨C, hC, fun y => (hy y).imp_right ?_⟩
  rintro ⟨W, hW0, hWi, hcov⟩
  obtain ⟨-, -, -, hperp, hne, -⟩ := hT I
  have hiso : ∀ v, Isot (Formalism.REAL.Jm (I.ε v)) (Wv I W v) := fun v => by
    unfold Isot
    rw [← hperp]
    exact Submodule.span_mono (image_mono hWi)
  choose Nv hNv using fun v => (hNW _ _ _ (hiso v)).2
  let N : Subgroup I.Ginf := Subgroup.pi univ Nv
  have hNm : ∀ g, g ∈ N ↔ g ∈ NInf I W := fun g => by
    simp only [N, Subgroup.mem_pi, mem_univ, forall_true_left, NInf, mem_ofPred_eq, ← hNv, SetLike.mem_coe]
  have hNc : IsClosed (N : Set I.Ginf) := by
    rw [Subgroup.coe_pi]
    exact isClosed_set_pi fun v _ => by rw [hNv]; exact (hNW _ _ _ (hiso v)).1
  obtain ⟨Γ, hΓ, hΓd⟩ := hGam I M
  have hc : Continuous fun m : I.Ginf => y⁻¹ * m * y := by fun_prop
  have hcK : IsCompact ((fun m : I.Ginf => y⁻¹ * m * y) ⁻¹' K) :=
    (((Homeomorph.mulLeft y⁻¹).trans (Homeomorph.mulRight y)).isCompact_preimage).2 hK
  obtain ⟨ν, hν, hνV, hinv⟩ := hAvg I.Ginf N (Γ ⊓ N) hNc inf_le_right
    (fun B hB => (hΓd B hB).subset fun x hx => ⟨hx.1, hx.2.1⟩) ((fun m => y⁻¹ * m * y) ⁻¹' interior K)
    (isOpen_interior.preimage hc)
    (hcK.of_isClosed_subset isClosed_closure (closure_minimal (preimage_mono interior_subset) hcK.isClosed))
    fun m hm => by
      obtain ⟨γ, hγ, hγN, h⟩ := hcov m ((hNm m).1 hm)
      exact ⟨γ, ⟨hΓ.ge hγ, (hNm γ).2 hγN⟩, h⟩
  refine ⟨ν, hν, hνV.mono fun m hm => hKU (interior_subset hm), fun u hu huΓ hrep x => ?_⟩
  obtain ⟨huc, B, hB⟩ := id hu
  have hc2 : Continuous fun p : I.Ginf × I.Ginf => u (p.1 * p.2) := huc.comp continuous_mul
  let F : I.Ginf → ℂ := fun x => ∫ m, u (m * x) ∂ν
  have hFb : BC F := ⟨continuous_of_dominated (bound := fun _ => B)
      (fun x => (hc2.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (fun x => Eventually.of_forall fun _ => hB _) (integrable_const _)
      (Eventually.of_forall fun m => hc2.comp (continuous_const.prodMk continuous_id)),
    B, fun x => by simpa using norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall fun m => hB (m * x))⟩
  have hFN : LInv N F := fun m hm x => hinv u hu (fun γ hγ => huΓ γ (by rw [← hΓ]; exact hγ.1)) m hm x
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  obtain ⟨a, Ht, P⟩ := hRP _ _ _ (hne v₀ W hW0) (hiso v₀) (Nv v₀) (hNv v₀)
  have h0 := hSel I.Ginf (muInf I) ph hph hconv _ _ _ (hPi _ _ v₀ _ a Ht P) F hFb (by
    rintro _ ⟨m, hm, rfl⟩
    refine hFN _ fun v _ => ?_
    by_cases hv : v = v₀
    · subst hv; simpa using hm
    · simp [Pi.mulSingle_eq_of_ne hv]) x
  have hI : Integrable (fun p : I.Ginf × I.Ginf => ph p.2 * u (p.1 * x * p.2)) (ν.prod (muInf I)) :=
    (hph.comp_snd ν).mul_bdd
      (huc.comp (by fun_prop) : Continuous fun p : I.Ginf × I.Ginf => u (p.1 * x * p.2)).aestronglyMeasurable
      (Eventually.of_forall fun _ => hB _)
  rw [← h0, integral_congr_ae (Eventually.of_forall fun m => hrep (m * x)), integral_integral_swap hI]
  simp only [F, integral_const_mul, mul_assoc]

theorem level_structure_of : LevelOf := by
  intro I e hlc hs
  let K : Subgroup I.Gf := (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype
  have hK : IsCompact (K : Set I.Gf) := PI.WAU.maximal_compact_isCompact I
  have hKo : IsOpen (K : Set I.Gf) := Formalism.L2.SG.Pf.kset_open I
  let Kp : Subgroup I.Gf :=
    { carrier := {k | k ∈ K ∧ ∀ x, e (k * x) = e x}
      mul_mem' := fun ha hb => ⟨K.mul_mem ha.1 hb.1, fun x => by rw [mul_assoc, ha.2, hb.2]⟩
      one_mem' := ⟨K.one_mem, fun x => by rw [one_mul]⟩
      inv_mem' := fun {k} hk => ⟨K.inv_mem hk.1, fun x => by rw [← hk.2 (k⁻¹ * x), mul_inv_cancel_left]⟩ }
  have h1 : ∀ᶠ k in 𝓝 (1 : I.Gf), ∀ x ∈ (K : Set I.Gf), e (k * x) = e x := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have a1 := (hlc.comp_continuous (continuous_mul (M := I.Gf))).eventually_eq (1, x)
    have a2 := (hlc.comp_continuous (continuous_snd (X := I.Gf))).eventually_eq (1, x)
    filter_upwards [a1, a2] with p h1 h2
    simp only [Function.comp_apply, one_mul] at h1 h2
    rw [h1, h2]
  have hop : IsOpen (Kp : Set I.Gf) := by
    refine Kp.isOpen_of_mem_nhds (g := 1) ?_
    filter_upwards [h1, hKo.mem_nhds K.one_mem] with k hk hkK
    refine ⟨hkK, fun x => ?_⟩
    by_cases hx : x ∈ K
    · exact hk x hx
    · have a1 : e x = 0 := by by_contra h; exact hx (hs x h)
      have a2 : e (k * x) = 0 := by by_contra h; exact hx ((K.mul_mem_cancel_left hkK).1 (hs _ h))
      rw [a1, a2]
  exact ⟨Kp, hop, hK.of_isClosed_subset (Kp.isClosed_of_isOpen hop) fun k hk => hk.1, fun k hk => hk.2⟩

end CompanionTheory.D.gk.RF
end
end

section
open Matrix NumberField Topology
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.RF.PE

open Formalism.MainNotions.S

theorem exists_extend {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ] (S : Submodule ℤ Λ)
    (hS : ∀ (m : ℤ) x, m • x ∈ S → m = 0 ∨ x ∈ S) (f : S →ₗ[ℤ] ℤ) : ∃ g : Λ →ₗ[ℤ] ℤ, ∀ x : S, g x = f x := by
  have : Module.IsTorsionFree ℤ (Λ ⧸ S) := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    obtain ⟨x, rfl⟩ := S.mkQ_surjective m
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    exact (hS r x h).imp_right fun h' => (Submodule.Quotient.mk_eq_zero _).2 h'
  have : Module.Free ℤ (Λ ⧸ S) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property S.mkQ LinearMap.id S.mkQ_surjective
  have hr : ∀ x, (LinearMap.id - s ∘ₗ S.mkQ : Λ →ₗ[ℤ] Λ) x ∈ S := fun x => by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub, LinearMap.comp_apply,
      ← LinearMap.comp_apply S.mkQ s, hs]
    simp
  refine ⟨f ∘ₗ LinearMap.codRestrict S _ hr, fun x => congrArg f (Subtype.ext ?_)⟩
  show (x : Λ) - s (S.mkQ x) = x
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 x.2, map_zero, sub_zero]

theorem dual_rep (E : Type) [Field E] [NumberField E] (n : ℕ) : ∃ D : ℕ, 1 ≤ D ∧ ∀ g : (Fin n → 𝓞 E) →ₗ[ℤ] ℤ,
    ∃ c : Fin n → E, (∀ j, IsIntegral ℤ ((D : E) * c j)) ∧
      ∀ u, (g u : ℚ) = Algebra.trace ℚ E (c ⬝ᵥ fun j => (u j : E)) := by
  classical
  obtain ⟨D, hD, hDi⟩ := exists_den (integralBasis E).traceDual
  refine ⟨D, hD, fun g => ⟨fun j => ∑ k, (g (Pi.single j (RingOfIntegers.basis E k)) : E) * (integralBasis E).traceDual k,
    fun j => ?_, fun u => ?_⟩⟩
  · rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun k _ => ?_
    rw [mul_left_comm]
    exact (isIntegral_intCast _).mul (hDi k)
  · let c : Fin n → E := fun j => ∑ k, (g (Pi.single j (RingOfIntegers.basis E k)) : E) * (integralBasis E).traceDual k
    let A : (Fin n → 𝓞 E) →ₗ[ℤ] ℚ := Algebra.linearMap ℤ ℚ ∘ₗ g
    let B : (Fin n → 𝓞 E) →ₗ[ℤ] ℚ := AddMonoidHom.toIntLinearMap
      { toFun := fun u => Algebra.trace ℚ E (c ⬝ᵥ fun j => (u j : E))
        map_zero' := by simp [dotProduct]
        map_add' := fun u u' => by
          rw [← map_add, ← dotProduct_add]
          congr 2 }
    have hAB : A = B := LinearMap.pi_ext' fun j => (RingOfIntegers.basis E).ext fun k => by
      show ((g (Pi.single j (RingOfIntegers.basis E k)) : ℤ) : ℚ) =
        Algebra.trace ℚ E (c ⬝ᵥ fun i => ((Pi.single j (RingOfIntegers.basis E k) : Fin n → 𝓞 E) i : E))
      rw [dotProduct, Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp),
        Pi.single_eq_same, Finset.sum_mul, map_sum, Finset.sum_eq_single k (fun l _ hl => ?_) (by simp)]
      · rw [mul_assoc, ← zsmul_eq_mul, map_zsmul, show ((RingOfIntegers.basis E k : 𝓞 E) : E) = integralBasis E k from
          (integralBasis_apply E k).symm, Module.Basis.trace_traceDual_mul]
        simp
      · rw [mul_assoc, ← zsmul_eq_mul, map_zsmul, show ((RingOfIntegers.basis E k : 𝓞 E) : E) = integralBasis E k from
          (integralBasis_apply E k).symm, mul_comm, Module.Basis.trace_mul_traceDual, if_neg (Ne.symm hl), smul_zero]
    exact LinearMap.congr_fun hAB u

variable (I : AutInst)

theorem span_phi (hs : ∀ v (a : I.E), I.φ v (star a) = star (I.φ v a)) :
    Submodule.span ℝ (Set.range fun k => fun v => I.φ v (integralBasis I.E k)) = ⊤ := by
  classical
  refine LinearIndependent.span_eq_top_of_card_eq_finrank' (Fintype.linearIndependent_iff.2 fun r hr j => ?_) ?_
  · have h1 : ∀ k, r k * (if k = j then 1 else 0) =
        ∑ v, 2 * ((r k : ℂ) * I.φ v (integralBasis I.E k) * I.φ v ((integralBasis I.E).traceDual j)).re := fun k => by
      have := trace_eq I hs (integralBasis I.E k * (integralBasis I.E).traceDual j)
      rw [Module.Basis.trace_mul_traceDual] at this
      simp only [mul_assoc, Complex.re_ofReal_mul, ← map_mul, mul_left_comm (2 : ℝ), ← Finset.mul_sum, ← this]
      split_ifs <;> simp
    have h2 := Finset.sum_congr (rfl : Finset.univ = _) fun k _ => h1 k
    rw [Finset.sum_comm] at h2
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    rw [h2]
    refine Finset.sum_eq_zero fun v _ => ?_
    have h3 := congrFun hr v
    simp only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul, Pi.zero_apply] at h3
    rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.sum_mul, h3]
    simp
  · rw [← Module.finrank_eq_card_basis (integralBasis I.E), ← Embeddings.card I.E ℂ,
      ← Fintype.card_of_bijective (emb_bij I hs), Module.finrank_pi_fintype, Fintype.card_prod]
    simp

theorem atV_smul (v : InfinitePlace I.F) (a : I.E) (u : Fin I.n → I.E) : atV I v (a • u) = I.φ v a • atV I v u := by
  unfold atV
  rw [← mulVec_smul]
  congr 1
  funext i
  simp

theorem atV_add (v : InfinitePlace I.F) (u u' : Fin I.n → I.E) : atV I v (u + u') = atV I v u + atV I v u' := by
  unfold atV
  rw [← mulVec_add]
  congr 1
  funext i
  simp

theorem mem_span_int (hs : ∀ v (a : I.E), I.φ v (star a) = star (I.φ v a)) (W : Submodule I.E (Fin I.n → I.E))
    (b : InfinitePlace I.F → Fin I.n → ℂ) (hb : ∀ v, b v ∈ Wv I W v) :
    b ∈ Submodule.span ℝ {x : InfinitePlace I.F → Fin I.n → ℂ | ∃ u ∈ IntV I, u ∈ W ∧ x = fun v => atV I v u} := by
  classical
  rw [← Finset.univ_sum_single b]
  refine Submodule.sum_mem _ fun v _ => ?_
  have key : ∀ x ∈ Wv I W v, ∀ β : ℂ, (Pi.single v (β • x) : InfinitePlace I.F → Fin I.n → ℂ) ∈ Submodule.span ℝ
      {x : InfinitePlace I.F → Fin I.n → ℂ | ∃ u ∈ IntV I, u ∈ W ∧ x = fun v => atV I v u} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      intro β
      obtain ⟨c, hc, hci⟩ := exists_den w
      have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
      let L : (InfinitePlace I.F → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) :=
        { toFun := fun γ v' => γ v' • atV I v' ((c : I.E) • w)
          map_add' := fun _ _ => funext fun v' => add_smul _ _ _
          map_smul' := fun r γ => funext fun v' => smul_assoc r (γ v') _ }
      have e : (Pi.single v (β • atV I v w) : InfinitePlace I.F → Fin I.n → ℂ) = L (Pi.single v (β / c)) := by
        funext v'
        by_cases h : v' = v
        · subst h
          show _ = (Pi.single v' (β / c) : InfinitePlace I.F → ℂ) v' • atV I v' ((c : I.E) • w)
          rw [Pi.single_eq_same, Pi.single_eq_same, atV_smul, map_natCast, smul_smul, div_mul_cancel₀ _ hc0]
        · show _ = (Pi.single v (β / c) : InfinitePlace I.F → ℂ) v' • atV I v' ((c : I.E) • w)
          rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, zero_smul]
      rw [e]
      have h1 : (Pi.single v (β / c) : InfinitePlace I.F → ℂ) ∈ Submodule.span ℝ
          (Set.range fun k => fun v => I.φ v (integralBasis I.E k)) := by rw [span_phi I hs]; trivial
      refine Submodule.span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span L h1)
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨integralBasis I.E k • (c : I.E) • w, fun i => ?_, W.smul_mem _ (W.smul_mem _ hw),
        funext fun v' => (atV_smul I v' _ _).symm⟩
      rw [integralBasis_apply]
      exact (RingOfIntegers.basis I.E k).2.mul (hci i)
    | zero => intro β; simp
    | add x y _ _ ihx ihy => intro β; rw [smul_add, Pi.single_add]; exact Submodule.add_mem _ (ihx β) (ihy β)
    | smul a x _ ih => intro β; rw [smul_smul]; exact ih _
  simpa using key _ (hb v) 1

theorem Jm_mulVec {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) (i : Fin n) :
    (Formalism.REAL.Jm ε *ᵥ x) i = (if ε i then 1 else -1) * x i := mulVec_diagonal _ _ _

theorem mem_of_perp_perp {n : ℕ} (ε : Fin n → Bool) (S : Submodule ℂ (Fin n → ℂ)) {x : Fin n → ℂ}
    (hx : ∀ b ∈ perp (Formalism.REAL.Jm ε) S, hf (Formalism.REAL.Jm ε) x b = 0) : x ∈ S := by
  classical
  by_contra h
  obtain ⟨l, hl, hS⟩ := Submodule.exists_le_ker_of_notMem h
  have e : ∀ s, hf (Formalism.REAL.Jm ε) s (Formalism.REAL.Jm ε *ᵥ fun i => star (l (Pi.single i 1))) = star (l s) := fun s => by
    rw [LinearMap.pi_apply_eq_sum_univ l s, star_sum, hf, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Jm_mulVec, Jm_mulVec, smul_eq_mul, star_mul', Pi.star_apply]
    have : (fun j => if i = j then (1 : ℂ) else 0) = Pi.single i 1 := by
      funext j; simp [Pi.single_apply, eq_comm]
    rw [this]
    split_ifs <;> ring
  have := hx _ fun w hw => by rw [e, show l w = 0 from hS hw, star_zero]
  rw [e] at this
  exact hl (star_eq_zero.1 this)

abbrev VR : Type := PiLp 2 fun _ : InfinitePlace I.F × Fin I.n => ℂ

def toV : (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] VR I where
  toFun b := WithLp.toLp 2 fun p => b p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem norm_le_toV (b : InfinitePlace I.F → Fin I.n → ℂ) : ‖b‖ ≤ ‖toV I b‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    PiLp.norm_apply_le (toV I b) (v, i)

theorem inner_toV (a b : InfinitePlace I.F → Fin I.n → ℂ) :
    ⟪toV I fun v => Formalism.REAL.Jm (I.ε v) *ᵥ a v, toV I b⟫_ℝ = ∑ v, (hf (Formalism.REAL.Jm (I.ε v)) (a v) (b v)).re := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [hf, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ⟪(Formalism.REAL.Jm (I.ε v) *ᵥ a v) i, b v i⟫_ℝ = _
  rw [Complex.inner, Jm_mulVec, Jm_mulVec]
  congr 1
  split_ifs <;> simp [mul_comm]

end CompanionTheory.D.gk.RF.PE

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S PE

set_option maxHeartbeats 800000 in
theorem covolume_orthogonal_complement : Transp → CovPerp := by
  classical
  intro hT I
  obtain ⟨hJ, hs, hh, hperp, -, -, -, -⟩ := hT I
  obtain ⟨D, hD, hdual⟩ := dual_rep I.E I.n
  obtain ⟨c₁, hc₁, hcJ⟩ := exists_den fun p : Fin I.n × Fin I.n => I.J⁻¹ p.1 p.2
  set c : ℕ := D * c₁ with hc
  have hc0 : (0 : ℝ) < c := by have : 0 < c := by positivity
                               exact_mod_cast this
  refine ⟨(Module.finrank ℝ (VR I) + 1) * c, by positivity, fun y W ρ t ht hρ hcov hlong b hb => ?_⟩
  let Λ : (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) :=
    { toFun := fun b v => uMat (y v)⁻¹ *ᵥ b v
      map_add' := fun _ _ => funext fun v => mulVec_add _ _ _
      map_smul' := fun r _ => funext fun v => mulVec_smul _ r _ }
  let co : (Fin I.n → 𝓞 I.E) → Fin I.n → I.E := fun u i => u i
  let ι : (Fin I.n → 𝓞 I.E) →ₗ[ℤ] VR I := AddMonoidHom.toIntLinearMap (AddMonoidHom.mk'
    (fun u => toV I (vecAt I y (co u))) fun u u' => by
      rw [← map_add]
      congr 1
      funext v
      rw [show co (u + u') = co u + co u' from rfl]
      simp only [vecAt, atV_add, mulVec_add, Pi.add_apply])
  have hι : ∀ u, ι u = toV I (vecAt I y (co u)) := fun _ => rfl
  let S : Submodule ℤ (Fin I.n → 𝓞 I.E) :=
    { carrier := {u | co u ∈ perp I.J W}
      add_mem' := fun ha hb => (perp I.J W).add_mem ha hb
      zero_mem' := (perp I.J W).zero_mem
      smul_mem' := fun m u hu => by
        have : co (m • u) = (m : I.E) • co u := funext fun i => by simp [co]
        show co (m • u) ∈ perp I.J W
        rw [this]; exact Submodule.smul_mem _ _ hu }
  let X : Submodule ℝ (VR I) := Submodule.span ℝ (S.map ι : Set (VR I))
  let M : Submodule ℤ X := (S.map ι).comap (X.subtype.restrictScalars ℤ)
  have hXP : ∀ b : InfinitePlace I.F → Fin I.n → ℂ, (∀ v, b v ∈ Wv I (perp I.J W) v) → toV I (Λ b) ∈ X := fun b hb => by
    refine Submodule.span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span (toV I ∘ₗ Λ) (mem_span_int I hs _ b hb))
    rintro _ ⟨_, ⟨u, hu, huW, rfl⟩, rfl⟩
    exact ⟨fun i => ⟨u i, hu i⟩, huW, rfl⟩
  have hdisc : DiscreteTopology M := by
    refine discreteTopology_of_isOpen_singleton_zero
      (isOpen_singleton_of_finite_mem_nhds 0 (Metric.closedBall_mem_nhds _ one_pos) ?_)
    set K : ℝ := ∑ v, ∑ i, ∑ j, ‖(I.P v * uMat (y v)) i j‖
    have hf1 : {u : Fin I.n → 𝓞 I.E | ∀ i, ∀ v, ‖I.φ v (u i)‖ ≤ K}.Finite :=
      Set.Finite.pi' (t := fun _ : Fin I.n => {a : 𝓞 I.E | ∀ v, ‖I.φ v a‖ ≤ K}) fun _ =>
        ((finite_bdd I hs K).preimage (f := fun a : 𝓞 I.E => (a : I.E)) RingOfIntegers.coe_injective.injOn).subset
          fun a ha => ⟨a.2, ha⟩
    refine Set.Finite.of_finite_image (f := fun m : M => ((m : X) : VR I)) ((hf1.image ι).subset ?_)
      (Subtype.val_injective.comp Subtype.val_injective).injOn
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨u, -, hu⟩ := m.2
    refine ⟨u, fun i v => ?_, hu⟩
    have h1 : ‖vecAt I y (co u)‖ ≤ 1 := (norm_le_toV I _).trans (by
      rw [← hι, hu]; exact mem_closedBall_zero_iff.1 hm)
    have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
    have e : (I.P v * uMat (y v)) *ᵥ vecAt I y (co u) v = fun i => I.φ v (u i) := by
      simp only [vecAt, atV, mulVec_mulVec]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (uMat (y v)), uMat_mul_inv, Matrix.one_mul,
        Matrix.mul_nonsing_inv _ hP, one_mulVec]
    rw [← congrFun e i, mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun j _ => ?_)
      ((Finset.single_le_sum (f := fun i => ∑ j, ‖(I.P v * uMat (y v)) i j‖) (fun _ _ => by positivity)
        (Finset.mem_univ i)).trans (Finset.single_le_sum (f := fun v => ∑ i, ∑ j, ‖(I.P v * uMat (y v)) i j‖)
          (fun _ _ => by positivity) (Finset.mem_univ v))))
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ v).trans h1))
  have hJu : IsUnit I.J.det := I.J_det.isUnit
  obtain ⟨m, ⟨u, huS, hu⟩, hm⟩ := PI.Tr2.coverDiv X M hdisc Submodule.span_span_coe_preimage (t / c)
    (by positivity) (fun z hz hz0 => by
      have hX : ∀ u ∈ S, ι u ∈ X := fun u hu => Submodule.subset_span ⟨u, hu, rfl⟩
      let F : S →ₗ[ℤ] ℝ := ((innerₛₗ ℝ (z : VR I)).restrictScalars ℤ) ∘ₗ ι ∘ₗ S.subtype
      have hF : ∀ u, F u ∈ LinearMap.range (Algebra.linearMap ℤ ℝ) := fun u => by
        obtain ⟨k, hk⟩ := hz ⟨ι u, hX u u.2⟩ ⟨u, u.2, rfl⟩
        exact ⟨k, by rw [real_inner_comm] at hk; exact hk.symm⟩
      let e := LinearEquiv.ofInjective (Algebra.linearMap ℤ ℝ) (Int.cast_injective (α := ℝ))
      obtain ⟨g, hg⟩ := exists_extend S (fun k x hx => by
        by_cases hk : k = 0
        · exact Or.inl hk
        · have e1 : co (k • x) = (k : I.E) • co x := funext fun i => by simp [co]
          have h1 : co (k • x) ∈ perp I.J W := hx
          rw [e1] at h1
          have hk' : (k : I.E) ≠ 0 := Int.cast_ne_zero.2 hk
          have h2 : co x ∈ perp I.J W := ((perp I.J W).smul_mem_iff hk').1 h1
          exact Or.inr h2)
        (e.symm.toLinearMap ∘ₗ F.codRestrict _ hF)
      have hgF : ∀ u : S, (g u : ℝ) = ⟪(z : VR I), ι u⟫_ℝ := fun u => by
        rw [hg]
        exact congrArg Subtype.val (e.apply_symm_apply (F.codRestrict _ hF u))
      obtain ⟨cv, hcv, hgc⟩ := hdual g
      set u₀ : Fin I.n → I.E := star (cv ᵥ* I.J⁻¹) with hu₀
      have hu₀f : ∀ u, hf I.J u₀ u = cv ⬝ᵥ u := fun u => by
        rw [hf, hu₀, star_star, dotProduct_mulVec, vecMul_vecMul, Matrix.nonsing_inv_mul _ hJu, vecMul_one]
      have hu₀i : (c : I.E) • u₀ ∈ IntV I := fun i => by
        have : ((c : I.E) • u₀) i = star (∑ j, ((D : I.E) * cv j) * ((c₁ : I.E) * I.J⁻¹ j i)) := by
          rw [Pi.smul_apply, smul_eq_mul, hu₀, Pi.star_apply, ← star_natCast (R := I.E) c, ← star_mul', vecMul,
            dotProduct, Finset.mul_sum, hc]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          push_cast; ring
        rw [this]
        exact isIntegral_star (IsIntegral.sum _ fun j _ => (hcv j).mul (hcJ (j, i)))
      let q : VR I := toV I fun v => Formalism.REAL.Jm (I.ε v) *ᵥ ((2 : ℂ) • vecAt I y u₀ v)
      have hq : ∀ u : S, ⟪q, ι u⟫_ℝ = ⟪(z : VR I), ι u⟫_ℝ := fun u => by
        rw [← hgF, hι, inner_toV]
        have h1 := congrArg (fun r : ℚ => (r : ℝ)) (hgc u)
        simp only [Rat.cast_intCast] at h1
        rw [h1, trace_eq I hs, ← hu₀f]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← hh, ← hf_uMat (y v)⁻¹ (atV I v u₀)]
        simp only [hf, star_smul, smul_dotProduct, vecAt]
        simp [co]
      have hqX : ∀ x ∈ X, ⟪q - z, x⟫_ℝ = 0 := fun x hx => by
        induction hx using Submodule.span_induction with
        | mem x hx => obtain ⟨u, hu, rfl⟩ := hx; rw [inner_sub_left, hq ⟨u, hu⟩, sub_self]
        | zero => simp
        | add _ _ _ _ h1 h2 => rw [inner_add_right, h1, h2, add_zero]
        | smul a _ _ h1 => rw [inner_smul_right, h1, mul_zero]
      have hu₀W : (c : I.E) • u₀ ∉ W := fun hW => hz0 (by
        have hW' : u₀ ∈ W := (W.smul_mem_iff (s := (c : I.E)) (by exact_mod_cast hc0.ne')).1 hW
        have h1 : ∀ x ∈ X, ⟪(z : VR I), x⟫_ℝ = 0 := fun x hx => by
          induction hx using Submodule.span_induction with
          | mem x hx =>
            obtain ⟨u, hu, rfl⟩ := hx
            have h2 := hgc u
            rw [← hu₀f, show hf I.J u₀ _ = 0 from hu u₀ hW', map_zero] at h2
            rw [← hgF ⟨u, hu⟩, show g u = 0 by exact_mod_cast h2, Int.cast_zero]
          | zero => simp
          | add _ _ _ _ h1 h2 => rw [inner_add_right, h1, h2, add_zero]
          | smul a _ _ h1 => rw [inner_smul_right, h1, mul_zero]
        exact Subtype.ext (inner_self_eq_zero.1 (h1 _ z.2)))

      let zJ : InfinitePlace I.F → Fin I.n → ℂ := fun v => Formalism.REAL.Jm (I.ε v) *ᵥ fun i => (z : VR I) (v, i)
      let a : InfinitePlace I.F → Fin I.n → ℂ := fun v => (2 : ℂ) • vecAt I y u₀ v - zJ v
      have hqa : q - z = toV I fun v => Formalism.REAL.Jm (I.ε v) *ᵥ a v := PiLp.ext fun p => by
        show (Formalism.REAL.Jm (I.ε p.1) *ᵥ ((2 : ℂ) • vecAt I y u₀ p.1)) p.2 - (z : VR I) p =
          (Formalism.REAL.Jm (I.ε p.1) *ᵥ a p.1) p.2
        simp only [a, zJ, Jm_mulVec, Pi.sub_apply]
        split_ifs <;> ring
      have haW : ∀ v, uMat (y v) *ᵥ a v ∈ Wv I W v := fun v => mem_of_perp_perp _ _ fun b' hb' => by
        rw [← hperp] at hb'
        have h1 : ∀ β : ℂ, (hf (Formalism.REAL.Jm (I.ε v)) (a v) (β • uMat (y v)⁻¹ *ᵥ b')).re = 0 := fun β => by
          have h2 := hqX _ (hXP (Pi.single v (β • b')) fun v' => by
            by_cases h : v' = v
            · subst h; rw [Pi.single_eq_same]; exact Submodule.smul_mem _ _ hb'
            · rw [Pi.single_eq_of_ne h]; exact Submodule.zero_mem _)
          rw [hqa, inner_toV, Finset.sum_eq_single v (fun v' _ h => by
            simp [Λ, Pi.single_eq_of_ne h, hf]) (by simp)] at h2
          simpa only [Λ, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same, mulVec_smul] using h2
        rw [← hf_uMat (y v)⁻¹, mulVec_mulVec, uMat_inv_mul, one_mulVec]
        have h3 := h1 1
        have h4 := h1 Complex.I
        simp only [hf, mulVec_smul, dotProduct_smul, smul_eq_mul, one_mul, Complex.I_mul_re, neg_eq_zero] at h3 h4
        exact Complex.ext h3 h4
      obtain ⟨u', hu'i, hu'W, hu'⟩ := hcov (fun v => ((c : ℂ) / 2) • uMat (y v) *ᵥ a v) fun v =>
        Submodule.smul_mem _ _ (haW v)
      have h5 := hlong ((c : I.E) • u₀ - u') (fun i => (hu₀i i).sub (hu'i i))
        fun h => hu₀W (by simpa using W.add_mem h hu'W)
      have e5 : vecAt I y ((c : I.E) • u₀ - u') = ((fun v => uMat (y v)⁻¹ *ᵥ ((c : ℂ) / 2) • uMat (y v) *ᵥ a v) -
          vecAt I y u') + ((c : ℂ) / 2) • zJ := by
        funext v
        have : (c : I.E) • u₀ - u' = (c : I.E) • u₀ + (-1 : I.E) • u' := by simp [sub_eq_add_neg]
        simp only [this, vecAt, atV_add, atV_smul, mulVec_add, mulVec_smul, mulVec_mulVec, uMat_inv_mul, one_mulVec,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply, a, map_natCast, map_neg, map_one]
        module
      have h6 : ‖zJ‖ ≤ ‖z‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v =>
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
          simp only [zJ, Jm_mulVec, norm_mul]
          have : ‖(if I.ε v i = true then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp
          rw [this, one_mul]
          exact PiLp.norm_apply_le (z : VR I) (v, i)
      rw [e5] at h5
      have h7 := h5.trans (norm_add_le_of_le hu' (norm_smul_le _ _))
      rw [norm_div, Complex.norm_natCast, Complex.norm_two] at h7
      rw [div_le_iff₀ hc0]
      nlinarith [mul_le_mul_of_nonneg_left h6 hc0.le]) ⟨_, hXP b hb⟩
  refine ⟨co u, fun i => (u i).2, huS, ?_⟩
  refine (norm_le_toV I _).trans (le_trans (le_of_eq ?_) (hm.trans ?_))
  · rw [map_sub, ← hι, hu]; rfl
  · have h1 : (Module.finrank ℝ X : ℝ) ≤ Module.finrank ℝ (VR I) := by exact_mod_cast X.finrank_le
    rw [div_le_div_iff₀ (by positivity) ht, mul_assoc, mul_left_comm (c : ℝ), mul_div_cancel₀ _ hc0.ne']
    nlinarith [(Nat.cast_nonneg (Module.finrank ℝ X) : (0 : ℝ) ≤ _)]

end CompanionTheory.D.gk.RF
end
end

section
open Matrix Topology Filter
open scoped ComplexOrder

noncomputable section

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S Formalism.REAL

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {W : Submodule ℂ (Fin n → ℂ)}

def Sc (J : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) (l m : ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ w ∈ W, g *ᵥ w = l • w) ∧ (∀ z ∈ perp J W, g *ᵥ z - z ∈ W) ∧ ∀ z, g *ᵥ z - m • z ∈ perp J W

theorem lowers_iff {g : Matrix (Fin n) (Fin n) ℂ} : Lowers J W (g - 1) ↔ Sc J W 1 1 g := by
  simp only [Lowers, Sc, sub_mulVec, one_mulVec, one_smul, sub_eq_zero]

theorem Sc.mul (hW : Isot J W) {l m l' m' : ℂ} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : Sc J W l m g)
    (hh : Sc J W l' m' h) : Sc J W (l * l') (m * m') (g * h) := by
  have gW : ∀ w ∈ W, g *ᵥ w ∈ W := fun w hw => by rw [hg.1 w hw]; exact W.smul_mem _ hw
  have gP : ∀ z ∈ perp J W, g *ᵥ z ∈ perp J W := fun z hz => by
    simpa using (perp J W).add_mem (hW (hg.2.1 z hz)) hz
  refine ⟨fun w hw => ?_, fun z hz => ?_, fun z => ?_⟩
  · rw [← mulVec_mulVec, hh.1 w hw, mulVec_smul, hg.1 w hw, smul_smul, mul_comm]
  · have := W.add_mem (gW _ (hh.2.1 z hz)) (hg.2.1 z hz)
    rwa [mulVec_sub, sub_add_sub_cancel, mulVec_mulVec] at this
  · have := (perp J W).add_mem (gP _ (hh.2.2 z)) ((perp J W).smul_mem m' (hg.2.2 z))
    rwa [mulVec_sub, mulVec_smul, smul_sub, sub_add_sub_cancel, mulVec_mulVec, smul_smul, mul_comm m'] at this

theorem Sc.inv (hW : Isot J W) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : Sc J W 1 1 g) (e : h * g = 1) :
    Sc J W 1 1 h := by
  have e' : ∀ z, h *ᵥ (g *ᵥ z) = z := fun z => by rw [mulVec_mulVec, e, one_mulVec]
  have h1 : ∀ w ∈ W, h *ᵥ w = w := fun w hw => by
    have := e' w
    rwa [hg.1 w hw, one_smul] at this
  have h0 : ∀ z, h *ᵥ z - z = -(h *ᵥ (g *ᵥ z - z)) := fun z => by rw [mulVec_sub, e', neg_sub]
  have h2 : ∀ z ∈ perp J W, h *ᵥ z - z ∈ W := fun z hz => by
    rw [h0, h1 _ (hg.2.1 z hz)]; exact W.neg_mem (hg.2.1 z hz)
  refine ⟨fun w hw => by rw [h1 w hw, one_smul], h2, fun z => ?_⟩
  have h3 := hg.2.2 z
  rw [one_smul] at h3 ⊢
  rw [h0]
  simpa using (perp J W).neg_mem ((perp J W).add_mem (hW (h2 _ h3)) h3)

theorem uMat_mul {ε : Fin n → Bool} (g h : UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_inv_mulF {ε : Fin n → Bool} (g : UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel]; rfl

theorem uMat_mul_invF {ε : Fin n → Bool} (g : UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel]; rfl

theorem continuous_uMat {ε : Fin n → Bool} : Continuous (uMat : UJ ε → _) := (isClosedEmbeddingMatrix n ε).1.continuous

theorem unipotent_radical_subgroup : NWSub := by
  intro n ε W hW
  constructor
  · have hc : ∀ z, Continuous fun g : UJ ε => (uMat g - 1) *ᵥ z := fun z =>
      (continuous_uMat.sub continuous_const).matrix_mulVec continuous_const
    have : NWset ε W = (⋂ w ∈ W, {g | (uMat g - 1) *ᵥ w = 0}) ∩
        ((⋂ z ∈ perp (Jm ε) W, (fun g : UJ ε => (uMat g - 1) *ᵥ z) ⁻¹' (W : Set _)) ∩
          ⋂ z, (fun g : UJ ε => (uMat g - 1) *ᵥ z) ⁻¹' (perp (Jm ε) W : Set _)) := by
      ext g; simp [NWset, Lowers]
    rw [this]
    exact (isClosed_biInter fun w _ => isClosed_eq (hc w) continuous_const).inter
      ((isClosed_biInter fun z _ => W.closed_of_finiteDimensional.preimage (hc z)).inter
        (isClosed_iInter fun z => (perp (Jm ε) W).closed_of_finiteDimensional.preimage (hc z)))
  · exact ⟨{ carrier := NWset ε W
             mul_mem' := fun {a b} ha hb => lowers_iff.2 (by
               simpa [uMat_mul] using (lowers_iff.1 ha).mul hW (lowers_iff.1 hb))
             one_mem' := by
               show Lowers _ _ ((1 : Matrix (Fin n) (Fin n) ℂ) - 1)
               rw [sub_self]
               exact ⟨fun _ _ => zero_mulVec _, fun _ _ => by rw [zero_mulVec]; exact W.zero_mem,
                 fun _ => by rw [zero_mulVec]; exact Submodule.zero_mem _⟩
             inv_mem' := fun {a} ha => lowers_iff.2 ((lowers_iff.1 ha).inv hW (uMat_inv_mulF a)) }, rfl⟩

def IsPr (W : Submodule ℂ (Fin n → ℂ)) (p : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  pᴴ = p ∧ (∀ z, p *ᵥ z ∈ W) ∧ ∀ w ∈ W, p *ᵥ w = w

theorem exists_isPr (W : Submodule ℂ (Fin n → ℂ)) : ∃ p, IsPr W p := by
  let e := WithLp.linearEquiv 2 ℂ (Fin n → ℂ)
  let K : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := W.comap (e : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ))
  let P : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) := K.starProjection
  have hP : ∀ z, Matrix.toEuclideanLin.symm P *ᵥ z = (P (WithLp.toLp 2 z)).ofLp := fun z => by
    conv_rhs => rw [← Matrix.toEuclideanLin.apply_symm_apply P]
    rfl
  refine ⟨Matrix.toEuclideanLin.symm P, ?_, fun z => ?_, fun w hw => ?_⟩
  · refine Matrix.isHermitian_iff_isSymmetric.2 ?_
    rw [LinearEquiv.apply_symm_apply]
    exact K.starProjection_isSymmetric
  · rw [hP]; exact K.starProjection_apply_mem _
  · rw [hP]
    exact congrArg WithLp.ofLp (Submodule.starProjection_eq_self_iff.2 (show WithLp.toLp 2 w ∈ K from hw))

theorem mat_extF {A B : Matrix (Fin n) (Fin n) ℂ} (h : ∀ z, A *ᵥ z = B *ᵥ z) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext h)

theorem IsPr.sq {p : Matrix (Fin n) (Fin n) ℂ} (hp : IsPr W p) : p * p = p :=
  mat_extF fun z => by rw [← mulVec_mulVec, hp.2.2 _ (hp.2.1 z)]

theorem IsPr.dot {p : Matrix (Fin n) (Fin n) ℂ} (hp : IsPr W p) (y z : Fin n → ℂ) :
    star y ⬝ᵥ (p *ᵥ z) = star (p *ᵥ y) ⬝ᵥ z := by
  rw [star_mulVec, hp.1, dotProduct_mulVec]

theorem IsPr.kill {p : Matrix (Fin n) (Fin n) ℂ} (hp : IsPr W p) {z : Fin n → ℂ} (hz : z ∈ perp J W) :
    p *ᵥ (J *ᵥ z) = 0 := by
  refine dotProduct_star_self_eq_zero.1 ?_
  rw [hp.dot]
  exact hz _ (hp.2.1 _)

theorem IsPr.entry {p : Matrix (Fin n) (Fin n) ℂ} (hp : IsPr W p) (i j : Fin n) : ‖p i j‖ ≤ 1 := by
  have h : ∀ j, ((∑ k, ‖p k j‖ ^ 2 : ℝ) : ℂ) = p j j := fun j => by
    conv_rhs => rw [← hp.sq, ← hp.1]
    rw [hp.1]
    conv_rhs => rw [show p * p = pᴴ * p by rw [hp.1]]
    simp only [mul_apply, conjTranspose_apply, Complex.ofReal_sum, Complex.ofReal_pow, Complex.star_def,
      Complex.conj_mul']
  have h1 : ∀ k, ‖p k j‖ ^ 2 ≤ ‖p j j‖ := fun k => by
    rw [← h j, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.single_le_sum (f := fun k => ‖p k j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  have h2 : ‖p j j‖ ≤ 1 := by nlinarith [h1 j, norm_nonneg (p j j)]
  nlinarith [h1 i, norm_nonneg (p i j)]

def am (J p : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + ((Real.exp t - 1 : ℝ) : ℂ) • p + ((Real.exp (-t) - 1 : ℝ) : ℂ) • (J * p * J)

theorem expand {p q : Matrix (Fin n) (Fin n) ℂ} (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hqp : q * p = 0)
    (a b c d : ℂ) : (1 + a • p + b • q) * (1 + c • p + d • q) =
      1 + (a + c + a * c) • p + (b + d + b * d) • q := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hp, hq,
    hpq, hqp, smul_zero, add_smul]
  module

section Am

variable {ε : Fin n → Bool} {p : Matrix (Fin n) (Fin n) ℂ}

theorem Jm_sq (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext a; split_ifs <;> simp

theorem Jm_hermF (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, diagonal_conjTranspose]
  congr 1; funext a; by_cases h : ε a <;> simp [h]

theorem pJp (hW : Isot (Jm ε) W) (hp : IsPr W p) : p * Jm ε * p = 0 :=
  mat_extF fun z => by rw [← mulVec_mulVec, ← mulVec_mulVec, hp.kill (hW (hp.2.1 z)), zero_mulVec]

theorem q_facts (hW : Isot (Jm ε) W) (hp : IsPr W p) :
    (Jm ε * p * Jm ε) * (Jm ε * p * Jm ε) = Jm ε * p * Jm ε ∧ p * (Jm ε * p * Jm ε) = 0 ∧
      (Jm ε * p * Jm ε) * p = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · calc _ = Jm ε * p * (Jm ε * Jm ε) * p * Jm ε := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Jm_sq, Matrix.mul_one, Matrix.mul_assoc (Jm ε), hp.sq]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, pJp hW hp, Matrix.zero_mul]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc p, pJp hW hp, Matrix.mul_zero]

theorem am_add (hW : Isot (Jm ε) W) (hp : IsPr W p) (s t : ℝ) : am (Jm ε) p (s + t) = am (Jm ε) p s * am (Jm ε) p t := by
  obtain ⟨h1, h2, h3⟩ := q_facts hW hp
  rw [am, am, am, expand hp.sq h1 h2 h3, neg_add, Real.exp_add, Real.exp_add]
  congr 2
  · congr 1; push_cast; ring
  · push_cast; ring

theorem am_mem (hW : Isot (Jm ε) W) (hp : IsPr W p) (t : ℝ) : inUJ ε (am (Jm ε) p t) := by
  have hH : (am (Jm ε) p t)ᴴ = am (Jm ε) p t := by
    simp only [am, conjTranspose_add, conjTranspose_one, conjTranspose_smul, conjTranspose_mul, hp.1, Jm_hermF,
      Complex.star_def, Complex.conj_ofReal, Matrix.mul_assoc]
  have hJ : am (Jm ε) p t * Jm ε = Jm ε * am (Jm ε) p (-t) := by
    simp only [am, neg_neg, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc, Jm_sq]
    rw [← Matrix.mul_assoc (Jm ε) (Jm ε), Jm_sq, Matrix.one_mul]
    abel
  rw [inUJ, hH, hJ, Matrix.mul_assoc, ← am_add hW hp, neg_add_cancel]
  simp [am]

theorem am_sc (hW : Isot (Jm ε) W) (hp : IsPr W p) (t : ℝ) :
    Sc (Jm ε) W (Real.exp t) (Real.exp (-t)) (am (Jm ε) p t) := by
  have hv : ∀ z, am (Jm ε) p t *ᵥ z = z + ((Real.exp t - 1 : ℝ) : ℂ) • p *ᵥ z +
      ((Real.exp (-t) - 1 : ℝ) : ℂ) • Jm ε *ᵥ (p *ᵥ (Jm ε *ᵥ z)) := fun z => by
    simp only [am, add_mulVec, one_mulVec, smul_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨fun w hw => ?_, fun z hz => ?_, fun z => ?_⟩
  · rw [hv, hp.kill (hW hw), hp.2.2 w hw, mulVec_zero]
    push_cast
    module
  · rw [hv, hp.kill hz, mulVec_zero, smul_zero, add_zero, add_sub_cancel_left]
    exact W.smul_mem _ (hp.2.1 z)
  · have h1 : Jm ε *ᵥ (p *ᵥ (Jm ε *ᵥ z)) - z ∈ perp (Jm ε) W := fun w hw => by
      rw [hf, mulVec_sub, mulVec_mulVec, Jm_sq, one_mulVec, dotProduct_sub, hp.dot, hp.2.2 w hw, sub_self]
    have := (perp (Jm ε) W).add_mem ((perp (Jm ε) W).smul_mem ((Real.exp t - 1 : ℝ) : ℂ) (hW (hp.2.1 z)))
      ((perp (Jm ε) W).smul_mem ((Real.exp (-t) - 1 : ℝ) : ℂ) h1)
    convert this using 1
    rw [hv]
    push_cast
    module

theorem hf_uMatF (x : UJ ε) (y z : Fin n → ℂ) : hf (Jm ε) (uMat x *ᵥ y) (uMat x *ᵥ z) = hf (Jm ε) y z := by
  have hx : (uMat x)ᴴ * Jm ε * uMat x = Jm ε := x.2
  rw [hf, hf, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hx]

end Am

theorem norm_mulVec_le (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    ‖M *ᵥ v‖ ≤ (1 + ∑ i, ∑ j, ‖M i j‖) * ‖v‖ := by
  have h0 : 0 ≤ ∑ i, ∑ j, ‖M i j‖ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(M *ᵥ v) i‖ ≤ ∑ j, ‖M i j‖ * ‖v‖ :=
        (norm_sum_le Finset.univ fun j => M i j * v j).trans (Finset.sum_le_sum fun j _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _))
    _ ≤ _ := by
        rw [← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right (le_add_of_nonneg_of_le zero_le_one ?_) (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem real_parabolic_decomposition : RealPar := by
  intro n ε W hW0 hW N hN
  have hmem : ∀ g, g ∈ N ↔ Sc (Jm ε) W 1 1 (uMat g) := fun g => by
    rw [← lowers_iff, ← SetLike.mem_coe, hN]; rfl
  obtain ⟨w₀, hw₀, hw0⟩ := (Submodule.ne_bot_iff W).1 hW0
  obtain ⟨p, hp⟩ := exists_isPr W
  let a : ℝ → UJ ε := fun t => indefiniteUnitaryMk ε _ (am_mem hW hp t)
  have hadd : ∀ s t, a (s + t) = a s * a t := fun s t => indefinite_unitary_ext (am_add hW hp s t)
  have ha0 : a 0 = 1 := indefinite_unitary_ext (by show am _ _ 0 = 1; simp [am])
  have hinv : ∀ t, (a t)⁻¹ = a (-t) := fun t => inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, ha0])
  have hee : ∀ t : ℝ, ((Real.exp t : ℝ) : ℂ) * (Real.exp (-t) : ℝ) = 1 := fun t => by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  have hne : ∀ g : UJ ε, uMat g⁻¹ *ᵥ w₀ ≠ 0 := fun g h => hw0 (by
    rw [← one_mulVec w₀, ← uMat_mul_invF g, ← mulVec_mulVec, h, mulVec_zero])
  have hamc : Continuous fun q : ℝ × Matrix (Fin n) (Fin n) ℂ => am (Jm ε) q.2 q.1 := by
    unfold am
    have c1 : Continuous fun q : ℝ × Matrix (Fin n) (Fin n) ℂ => ((Real.exp q.1 - 1 : ℝ) : ℂ) := by fun_prop
    have c2 : Continuous fun q : ℝ × Matrix (Fin n) (Fin n) ℂ => ((Real.exp (-q.1) - 1 : ℝ) : ℂ) := by fun_prop
    exact (continuous_const.add (c1.smul continuous_snd)).add
      (c2.smul ((continuous_const.matrix_mul continuous_snd).matrix_mul continuous_const))
  let S : UJ ε → ℝ := fun g => 1 + ∑ i, ∑ j, ‖uMat g i j‖
  have hS1 : ∀ g, 1 ≤ S g := fun g => le_add_of_nonneg_right
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hSc : Continuous fun g => Real.log (S g) :=
    (continuous_const.add (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_uMat.matrix_elem i j).norm)).log fun g => (one_pos.trans_le (hS1 g)).ne'
  refine ⟨a, fun g => -Real.log ‖uMat g⁻¹ *ᵥ w₀‖, ?_, hadd, fun t m hm => ?_, ?_, fun m hm g => ?_, fun t g => ?_,
    ⟨fun y => Real.log (S y) + Real.log (S y⁻¹), hSc.add (hSc.comp continuous_inv), fun x y => ?_⟩, fun U hU => ?_⟩
  · exact (isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff.2 (hamc.comp (continuous_id.prodMk continuous_const))
  · rw [hmem, hinv]
    have := ((am_sc hW hp t).mul hW ((hmem m).1 hm)).mul hW (am_sc hW hp (-t))
    rwa [mul_one, mul_one, neg_neg, hee, mul_comm, hee] at this
  · exact (((continuous_uMat.comp continuous_inv).matrix_mulVec continuous_const).norm.log
      fun g => norm_ne_zero_iff.2 (hne g)).neg
  · rw [_root_.mul_inv_rev, uMat_mul, ← mulVec_mulVec, ((hmem _).1 (N.inv_mem hm)).1 w₀ hw₀, one_smul]
  · rw [_root_.mul_inv_rev, uMat_mul, ← mulVec_mulVec, hinv]
    have : uMat (a (-t)) *ᵥ w₀ = ((Real.exp (-t) : ℝ) : ℂ) • w₀ := (am_sc hW hp (-t)).1 w₀ hw₀
    rw [this, mulVec_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.log_mul (Real.exp_pos _).ne' (norm_ne_zero_iff.2 (hne g)), Real.log_exp]
    ring
  · have p1 := norm_pos_iff.2 (hne x)
    have p2 := norm_pos_iff.2 (hne (x * y))
    have e1 : uMat (x * y)⁻¹ *ᵥ w₀ = uMat y⁻¹ *ᵥ (uMat x⁻¹ *ᵥ w₀) := by
      rw [_root_.mul_inv_rev, uMat_mul, mulVec_mulVec]
    have e2 : uMat x⁻¹ *ᵥ w₀ = uMat y *ᵥ (uMat (x * y)⁻¹ *ᵥ w₀) := by
      rw [e1, mulVec_mulVec _ (uMat y), uMat_mul_invF, one_mulVec]
    have b1 : Real.log ‖uMat (x * y)⁻¹ *ᵥ w₀‖ ≤ Real.log (S y⁻¹) + Real.log ‖uMat x⁻¹ *ᵥ w₀‖ := by
      rw [← Real.log_mul (one_pos.trans_le (hS1 _)).ne' p1.ne']
      exact Real.log_le_log p2 (by rw [e1]; exact norm_mulVec_le _ _)
    have b2 : Real.log ‖uMat x⁻¹ *ᵥ w₀‖ ≤ Real.log (S y) + Real.log ‖uMat (x * y)⁻¹ *ᵥ w₀‖ := by
      rw [← Real.log_mul (one_pos.trans_le (hS1 _)).ne' p2.ne']
      exact Real.log_le_log p1 (by nth_rewrite 1 [e2]; exact norm_mulVec_le _ _)
    have c1 := Real.log_nonneg (hS1 y)
    have c2 := Real.log_nonneg (hS1 y⁻¹)
    rw [abs_le]
    constructor <;> linarith
  · rw [(isClosedEmbeddingMatrix n ε).1.isInducing.nhds_eq_comap, mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    have hK : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : ℂ) 1) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    have hev := hK.eventually_forall_of_forall_eventually (x₀ := (0 : ℝ))
      (P := fun t q => am (Jm ε) (Matrix.of q) t ∈ V) fun q _ =>
        hamc.continuousAt (x := (0, Matrix.of q)) (by
          show V ∈ 𝓝 (am (Jm ε) (Matrix.of q) 0)
          simpa [am] using hV)
    obtain ⟨τ, hτ, hb⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨τ, hτ, fun t ht x => ?_⟩
    let W' : Submodule ℂ (Fin n → ℂ) := W.comap (Matrix.toLin' (uMat x))
    have hxx : ∀ z, uMat x *ᵥ (uMat x⁻¹ *ᵥ z) = z := fun z => by rw [mulVec_mulVec, uMat_mul_invF, one_mulVec]
    have hP' : ∀ z, z ∈ perp (Jm ε) W' ↔ uMat x *ᵥ z ∈ perp (Jm ε) W := fun z =>
      ⟨fun h w hw => by
        rw [← hxx w, hf_uMatF]
        exact h _ (show uMat x *ᵥ _ ∈ W by rwa [hxx]),
       fun h w hw => by rw [← hf_uMatF x]; exact h _ hw⟩
    have hW' : Isot (Jm ε) W' := fun z hz => (hP' z).2 (hW hz)
    obtain ⟨p', hp'⟩ := exists_isPr W'
    let a' : UJ ε := indefiniteUnitaryMk ε _ (am_mem hW' hp' t)
    have hs' : Sc (Jm ε) W' (Real.exp t) (Real.exp (-t)) (uMat a') := am_sc hW' hp' t
    have hs : Sc (Jm ε) W (Real.exp t) (Real.exp (-t)) (uMat (x * a' * x⁻¹)) := by
      have hv : ∀ z, uMat (x * a' * x⁻¹) *ᵥ z = uMat x *ᵥ (uMat a' *ᵥ (uMat x⁻¹ *ᵥ z)) := fun z => by
        rw [uMat_mul, uMat_mul, mulVec_mulVec, mulVec_mulVec]
      refine ⟨fun w hw => ?_, fun z hz => ?_, fun z => ?_⟩
      · rw [hv, hs'.1 _ (show uMat x *ᵥ _ ∈ W by rwa [hxx]), mulVec_smul, hxx]
      · have : uMat x *ᵥ _ ∈ W := hs'.2.1 (uMat x⁻¹ *ᵥ z) ((hP' _).2 (by rwa [hxx]))
        rwa [mulVec_sub, hxx, ← hv] at this
      · have := (hP' _).1 (hs'.2.2 (uMat x⁻¹ *ᵥ z))
        rwa [mulVec_sub, mulVec_smul, hxx, ← hv] at this
    refine ⟨x * a' * x⁻¹ * a (-t), (hmem _).2 ?_, ?_⟩
    · have := hs.mul hW (am_sc hW hp (-t))
      rwa [neg_neg, hee, mul_comm, hee] at this
    · rw [← hinv, inv_mul_cancel_right, show x⁻¹ * (x * a' * x⁻¹) * x = a' by group]
      exact hVU (hb (by simpa using ht) (fun i j => p' i j) fun i _ j _ => by simpa using hp'.entry i j)

end CompanionTheory.D.gk.RF
end
end

section
namespace CompanionTheory.D.gk.RF

theorem gamSub : GamSub := by
  exact arithmetic_subgroup_of_transport transport_to_standard_form

theorem geoInf : GeoInf := by
  have hT : Transp := transport_to_standard_form
  have hG : GamSub := arithmetic_subgroup_of_transport hT
  exact reduction_geometry_at_infinity successive_minima_gap (short_isotropic_vector_of hT) covolume_span (covolume_orthogonal_complement hT)
    (mahler_compactness_of hT hG) (nilpotent_cover_of hT hG nilpotent_lie_algebra nilpotent_subgroup_representation)

theorem cuspInf : CuspInf :=
  cuspidal_at_infinity_of selP (averaging_of_fundamental_domain fundamental_domain_inclusion) unipotent_radical_subgroup real_parabolic_decomposition parabolic_subgroup_decomposition transport_to_standard_form gamSub geoInf

theorem automorphic_forms_finite_dimensional : Formalism.L2.SG.RowsDef.RowsFinDim := by
  exact rowsFinDim_of discrete_series_bound_of_inputs finite_dimensional_from_linear_forms (adelic_cusp_of_infinite_cusp cuspInf congruence_subgroup_compact_open)
    (fundamental_domain_discrete_of gamSub) level_structure_of convolution_operator_representation representation_of_convolution

end CompanionTheory.D.gk.RF
end
