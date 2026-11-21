import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapInvolutionEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.LdetRatMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PGBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.WeakPf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PartEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PEvalBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PositionPairFunctionsEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.FlipHalf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PSizes
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PDomInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PHalfTerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTailInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTailOf
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.RGrowthJ
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.EllFormula2J

section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory

private theorem twist_general {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] {F : Set G}
    (fd : IsFundamentalDomain Γ F μ) (θ : G →* G) (hc : Continuous θ) (hi : ∀ x, θ (θ x) = x)
    (hΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) (f : G → ℂ) (hf : ∀ (γ : Γ) x, f ((γ : G) * x) = f x)
    (hI : Integrable f (μ.restrict F)) :
    Integrable (fun x => f (θ x)) (μ.restrict F) ∧
      ∫ x, f (θ x) ∂(μ.restrict F) = ∫ x, f x ∂(μ.restrict F) :=
  _root_.UpperTheory.Reformulated.B.Qh1.twist_general μ Γ fd θ hc hi hΓ f hf hI

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.thetaInt_pf :
    Basic → ThetaInt := by
  intro _ E _ _ _ n D f hf hI
  have hb := PositivityTheory.Rg.BcB.E1.thetaBasic_holds E
  let θ : PositivityTheory.Rg.BcB.E.H E n 0 →* PositivityTheory.Rg.BcB.E.H E n 0 :=
    (PositivityTheory.Rg.BcB.thetaA E n).prodMap (PositivityTheory.Rg.BcB.thetaA E 0)
  have hc : Continuous θ :=
    ((hb n).1.comp continuous_fst).prodMk ((hb 0).1.comp continuous_snd)
  have hi : ∀ x, θ (θ x) = x := fun x => Prod.ext ((hb n).2.1 x.1) ((hb 0).2.1 x.2)
  have hΓ : ∀ γ ∈ PositivityTheory.Rg.BcB.E.ratH E n 0, θ γ ∈ PositivityTheory.Rg.BcB.E.ratH E n 0 := by
    rintro _ ⟨g, rfl⟩
    exact ⟨(PositivityTheory.Rg.BcB.thetaE E n g.1, PositivityTheory.Rg.BcB.thetaE E 0 g.2),
      Prod.ext ((hb n).2.2 g.1).symm ((hb 0).2.2 g.2).symm⟩
  let C := PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D
  exact @twist_general C.G C.grp C.top C.tg C.lc C.sc C.ms C.bs C.μ C.haar C.Γ C.cn C.F C.fd
    θ hc hi hΓ f hf hI
end

section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory Filter GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.zero_pf :
    AeEq → Zero := by
  intro hAe E _ _ _ n D f I hf hinv hI h
  classical
  haveI : T2Space (H E n 0) := (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D).t2
  haveI : LocallyCompactSpace (H E n 0) := (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D).lc
  haveI : SecondCountableTopology (H E n 0) := (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D).sc
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  have key : ∀ K : Set (H E n 0), IsCompact K → ∀ᵐ x ∂D.ν, x ∈ K → ldet x ∈ I → f x = 0 := by
    intro K hK
    set S : Set (H E n 0) := K ∩ ldet ⁻¹' I with hS
    have hSm : MeasurableSet S :=
      hK.isClosed.measurableSet.inter (hI.preimage continuous_ldet).measurableSet
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
    have hνS : D.ν S < ⊤ :=
      lt_of_le_of_lt ((Measure.restrict_apply_le _ _).trans (measure_mono Set.inter_subset_left))
        (hK.measure_lt_top_of_nhdsWithin fun x _ => D.μ.finiteAt_nhdsWithin x K)
    set w : H E n 0 → ℂ := S.indicator fun x => starRingEnd ℂ (f x) with hwdef
    have hw : MemLp w 2 D.ν := by
      rw [hwdef, memLp_indicator_iff_restrict hSm]
      haveI : IsFiniteMeasure (D.ν.restrict S) := isFiniteMeasure_restrict.2 hνS.ne
      refine MemLp.of_bound (Complex.continuous_conj.comp hf).aestronglyMeasurable B
        ((ae_restrict_iff' hSm).2 (Eventually.of_forall fun x hx => ?_))
      simpa using hB x hx.1
    have hv : (hw.toLp w : H E n 0 → ℂ) =ᵐ[D.ν] w := hw.coeFn_toLp
    have h0 := h (hw.toLp w) (hv.mono fun y hy hl => by
      rw [hy]
      exact Set.indicator_of_notMem (fun hs => hl hs.2) _)
    have hpt : ∀ y, w y * f y = ((‖w y‖ ^ 2 : ℝ) : ℂ) := by
      intro y
      by_cases hy : y ∈ S
      · simp only [hwdef, Set.indicator_of_mem hy, RCLike.norm_conj]
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      · simp [hwdef, Set.indicator_of_notMem hy]
    have h1 : ∫ y, ‖w y‖ ^ 2 ∂D.ν = 0 := by
      have e : ∫ y, (hw.toLp w : H E n 0 → ℂ) y * f y ∂D.ν = ∫ y, ((‖w y‖ ^ 2 : ℝ) : ℂ) ∂D.ν :=
        integral_congr_ae (hv.mono fun y hy => by
          show (hw.toLp w : H E n 0 → ℂ) y * f y = ((‖w y‖ ^ 2 : ℝ) : ℂ)
          rw [hy, hpt])
      rw [e, integral_complex_ofReal] at h0
      exact_mod_cast h0
    have hint : Integrable (fun y => ‖w y‖ ^ 2) D.ν := hw.integrable_norm_pow two_ne_zero
    have h2 := (integral_eq_zero_iff_of_nonneg (fun y => by positivity) hint).1 h1
    refine h2.mono fun x hx hxK hxI => ?_
    have hx0 : w x = 0 := by simpa using hx
    have hxS : x ∈ S := ⟨hxK, hxI⟩
    rw [hwdef, Set.indicator_of_mem hxS] at hx0
    simpa using hx0
  have all : ∀ᵐ x ∂D.ν, ∀ m : ℕ, x ∈ compactCovering (H E n 0) m → ldet x ∈ I → f x = 0 :=
    ae_all_iff.2 fun m => key _ (isCompact_compactCovering _ m)
  refine hAe E n D f (fun _ => 0) I hf continuous_const hinv (fun _ _ => rfl) hI (all.mono fun x hx hl => ?_)
  obtain ⟨m, hm⟩ := exists_mem_compactCovering x
  exact hx m hm hl
end

section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open NumberField PositivityTheory.Rg.BcB.E MeasureTheory

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem ker_left (D : Dom E n 0) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {γ : H E n 0}
    (hγ : γ ∈ ratH E n 0) (x y : H E n 0) : kerH φ (γ * x) y = kerH φ x y :=
  ((PositivityTheory.Rg.BcB.E1.kerBasic (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) φ hφ).2.2.1 γ hγ x y).1

private theorem ker_right (D : Dom E n 0) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {γ : H E n 0}
    (hγ : γ ∈ ratH E n 0) (x y : H E n 0) : kerH φ x (γ * y) = kerH φ x y :=
  ((PositivityTheory.Rg.BcB.E1.kerBasic (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) φ hφ).2.2.1 γ hγ x y).2

private theorem th_mul' (x y : H E n 0) :
    PositivityTheory.Rg.BcB.E1.th (x * y) = PositivityTheory.Rg.BcB.E1.th x * PositivityTheory.Rg.BcB.E1.th y :=
  Prod.ext (map_mul (PositivityTheory.Rg.BcB.thetaA E n) x.1 y.1) (map_mul (PositivityTheory.Rg.BcB.thetaA E 0) x.2 y.2)

private theorem th_rat {δ : H E n 0} (hδ : δ ∈ ratH E n 0) : PositivityTheory.Rg.BcB.E1.th δ ∈ ratH E n 0 := by
  obtain ⟨γ, rfl⟩ := hδ
  refine ⟨(PositivityTheory.Rg.BcB.thetaE E n γ.1, PositivityTheory.Rg.BcB.thetaE E 0 γ.2), ?_⟩
  exact Prod.ext ((PositivityTheory.Rg.BcB.E1.thetaBasic_holds E n).2.2 γ.1).symm
    ((PositivityTheory.Rg.BcB.E1.thetaBasic_holds E 0).2.2 γ.2).symm

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.kInv_pf :
    KInv := by
  intro E _ _ _ n ι _ s
  refine ⟨fun γ x => ?_, fun γ x => ?_⟩
  · funext i
    refine ext_inner_right ℂ fun u => ?_
    rw [s.vecs.rep₁, s.vecs.rep₁]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ker_left s.D (s.t₁ i j) γ.2]
  · funext i
    refine ext_inner_left ℂ fun u => ?_
    rw [s.vecs.rep₂, s.vecs.rep₂]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [th_mul', ker_right s.D (s.t₂ j l) (th_rat γ.2)]
end

section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem kerH_left {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (φ : H E n 0 → ℂ) (γ : ratH E n 0) (x y : H E n 0) :
    kerH φ ((γ : H E n 0) * x) y = kerH φ x y := by
  unfold kerH
  rw [← finsum_comp_equiv (Equiv.mulLeft γ)]
  refine finsum_congr fun δ => ?_
  congr 1
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, _root_.mul_inv_rev]
  group

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pointRep_pf :
    AeEq → KInv → PointRep := by
  intro hA hK E _ _ _ n ι _ s Φ T hΦ hT h g hg x i
  obtain ⟨k, k', hk⟩ := vecsEx E n 0 s.D ι Φ Φ T T 0 hΦ hΦ hT hT
  have hF : Continuous fun x => inner ℂ (s.k₁ x i) h :=
    ((s.vecs.cont i).1).inner continuous_const
  have hG : Continuous fun x => inner ℂ (k x i) g := ((hk.cont i).1).inner continuous_const
  have hIF : Inv fun x => inner ℂ (s.k₁ x i) h := fun γ x => by
    simp only [(hK E n ι s).1 γ x]
  have hIG : Inv fun x => inner ℂ (k x i) g := fun γ x => by
    simp only [hk.rep₁, kerH_left]
  have hae : ∀ᵐ x ∂s.D.ν, ldet x ∈ (Set.univ : Set ℝ) →
      inner ℂ (s.k₁ x i) h = inner ℂ (k x i) g := by
    have h1 := s.o₁ h i
    have h2 := hT g i
    rw [hg] at h1
    filter_upwards [h1, h2] with y a1 a2 _
    rw [s.vecs.rep₁, hk.rep₁, ← a1, a2]
  have := hA E n s.D _ _ Set.univ hF hG hIF hIG isOpen_univ hae x (Set.mem_univ _)
  rw [this, hk.rep₁]
end

section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

private theorem op_unique {D : Dom E n 0} {Φ : Matrix ι ι (H E n 0 → ℂ)}
    {T T' : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D} (h : IsROp D Φ T) (h' : IsROp D Φ T') : T = T' := by
  refine ContinuousLinearMap.ext fun f => PiLp.ext fun i => ?_
  exact Lp.ext ((h f i).trans (h' f i).symm)

private theorem isTestM_adjM {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) : IsTestM (adjM Φ) := by
  intro i j
  refine ⟨Complex.continuous_conj.comp ((hΦ j i).1.comp continuous_inv), ?_⟩
  have h := (hΦ j i).2.comp_homeomorph (Homeomorph.inv (H E n 0))
  exact h.comp_left (g := starRingEnd ℂ) (map_zero _)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pComm_pf :
    PComm := by
  intro E _ _ _ n hn D π hfix ι _ Φ T hΦ hT f
  obtain ⟨T₀, h₀, hadj, -⟩ := PositivityTheory.Rg.BcB.E1.kernel_operator_exists_holds E n 0 D ι Φ hΦ
  obtain rfl : T₀ = T := op_unique h₀ hT
  have hS : ∀ g ∈ piSp D π ι, T₀ g ∈ piSp D π ι := piInv E n hn D π hfix ι Φ T₀ hΦ hT
  have hS' : ∀ g ∈ piSp D π ι, ContinuousLinearMap.adjoint T₀ g ∈ piSp D π ι :=
    piInv E n hn D π hfix ι (adjM Φ) _ (isTestM_adjM hΦ) hadj
  have hO : ∀ g ∈ (piSp D π ι)ᗮ, T₀ g ∈ (piSp D π ι)ᗮ := by
    intro g hg
    rw [Submodule.mem_orthogonal] at hg ⊢
    intro u hu
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact hg _ (hS' u hu)
  refine Submodule.eq_starProjection_of_mem_orthogonal (hS _ (Submodule.starProjection_apply_mem _ _)) ?_
  rw [← map_sub]
  exact hO _ (Submodule.sub_starProjection_mem_orthogonal _)
end

section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.supp_pf :
    Basic → Zero → KInv → PSupp → Ker → Supp := by
  intro hB hZ hK hP hKer E _ _ _ n ι _ s m R hR x y hxy
  obtain ⟨hac, hmul, -, -, hone, -, hldth, hthth, hthmul, hrat, -, hthc⟩ := hB E n s.pos
  have hl1 : ldet (1 : H E n 0) = 0 := by
    have h := hac 0
    rwa [hone] at h
  have hlinv : ∀ z : H E n 0, ldet z⁻¹ = -ldet z := by
    intro z
    have h := hmul z z⁻¹
    rw [mul_inv_cancel, hl1] at h
    linarith
  have hf : Continuous fun w : H E n 0 => m.G x (th w) := by
    show Continuous fun w : H E n 0 => ∑ i, inner ℂ (s.k₁ x i) (m.Uπ (s.k₂ (th w) i))
    refine continuous_finset_sum _ fun i _ => ?_
    exact continuous_const.inner (m.Uπ.continuous.comp (((s.vecs.cont i).2).comp hthc))
  have hinv : Inv fun w : H E n 0 => m.G x (th w) := by
    intro γ w
    have h := (hK E n ι s).2 ⟨th (γ : H E n 0), (hrat γ).2⟩ (th w)
    show Gk s.k₁ s.k₂ m.Uπ x (th ((γ : H E n 0) * w)) = Gk s.k₁ s.k₂ m.Uπ x (th w)
    rw [hthmul]
    unfold Gk
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show s.k₂ (th (γ : H E n 0) * th w) = s.k₂ (th w) from h]
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = (|ldet x + ldet y| - R) / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have key := hZ E n s.D (fun w => m.G x (th w)) (Set.Ioo (-ldet y - δ) (-ldet y + δ)) hf hinv isOpen_Ioo ?_ (th y) ?_
  · simpa only [hthth] using key
  · intro v hv
    refine ((hKer E n ι s m v x).2).trans ?_
    have hPv := hP E n s.D s.π (-ldet y - δ) (-ldet y + δ) v
      (hv.mono fun w h h' => h fun hI => h' (Set.Ioo_subset_Icc_self hI))
    apply integral_eq_zero_of_ae
    filter_upwards [hPv] with w hw
    by_cases hI : ldet w ∈ Set.Icc (-ldet y - δ) (-ldet y + δ)
    · have hk : kerH m.φ x w = 0 := by
        unfold kerH
        refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
        by_contra hne
        have h1 := hR _ hne
        rw [hmul, hmul, hlinv, (hrat γ).1] at h1
        obtain ⟨a1, a2⟩ := abs_le.mp h1
        obtain ⟨b1, b2⟩ := hI
        rcases abs_cases (ldet x + ldet y) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hδ <;> linarith
      simp [hk]
    · simp [hw hI]
  · rw [hldth]
    exact ⟨by linarith, by linarith⟩
end

section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem ker_integral_shift (X : Ctx) {φ f : X.G → ℂ} (hφ : Tst φ)
    (hinv : ∀ γ : X.Γ, ∀ y, f ((γ : X.G) * y) = f y) (hf : MemLp f 2 X.ν) (x : X.G) :
    ∫ y, ker X.Γ φ x y * f y ∂X.ν = ∫ z, φ z * f (x * z) ∂X.μ := by
  rw [(unfold X kerBasic kernel_rows_columns_square_integrable hφ hinv hf x).2,
    ← integral_mul_left_eq_self (fun y => φ (x⁻¹ * y) * f y) x]
  simp only [inv_mul_cancel_left]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.finGen_pf :
    Basic → FinGen := by
  intro hB E _ _ _ n ι _ s
  classical
  obtain ⟨-, hmul, -, -, -, -, -, -, -, hrat, -, -⟩ := hB E n s.pos
  choose W hWle hWfd hW using s.fin
  have hfd : FiniteDimensional ℂ (⨆ p : ι × ι, W p.1 p.2 : Submodule ℂ (Sm E n)) := by
    haveI : ∀ p : ι × ι, FiniteDimensional ℂ (W p.1 p.2) := fun p => hWfd _ _
    exact Submodule.finiteDimensional_iSup _
  refine ⟨⨆ p : ι × ι, W p.1 p.2, iSup_le fun p => hWle _ _, hfd, ?_⟩
  intro v hv i t
  choose ψ hψ u hu hu' hvu using hv
  let X := PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds s.D
  have hform : ∀ j, ∀ (γ : ratH E n 0) (y : H E n 0), (ψ j).1 ((γ : H E n 0) * y).1 = (ψ j).1 y.1 := by
    intro j γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    rw [Prod.fst_mul, h1]
    exact (s.π.cusp _ (hψ j)).1.left γ₁ y.1
  set Ft : ι → H E n 0 → ℂ := fun j x => (ψ j).1 x.1 * u j (ldet x) with hFt
  have hinv : ∀ j, ∀ (γ : ratH E n 0) (y : H E n 0), Ft j ((γ : H E n 0) * y) = Ft j y := by
    intro j γ y
    simp only [hFt, hform j γ y, hmul, (hrat γ).1, zero_add]
  have hmem : ∀ j, MemLp (Ft j) 2 s.D.ν := fun j => (Lp.memLp (v j)).ae_eq (hvu j)
  have hex : ∀ j, ∃ ψ' ∈ W i j, ∀ g, ψ'.1 g =
      ∫ y, s.Φ₁ i j y * (fun r => u j (t + r)) (ldet y) * (ψ j).1 (g * y.1) ∂s.D.μ := fun j =>
    hW i j (fun r => u j (t + r)) ((hu j).comp (continuous_const.add continuous_id)) (ψ j) (hψ j)
  choose ψ' hψ' hval using hex
  refine ⟨∑ j, ψ' j, Submodule.sum_mem _ fun j _ =>
    (le_iSup (fun p : ι × ι => W p.1 p.2) (i, j)) (hψ' j), fun x hx => ?_⟩
  rw [s.vecs.rep₁]
  have hsum : (∑ j, ψ' j).1 x.1 = ∑ j, (ψ' j).1 x.1 := by
    simp [Submodule.coe_sum]
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hae : ∫ y, kerH (s.Φ₁ i j) x y * (v j : H E n 0 → ℂ) y ∂s.D.ν =
      ∫ y, kerH (s.Φ₁ i j) x y * Ft j y ∂s.D.ν :=
    integral_congr_ae ((hvu j).mono fun y hy => by simp only [hy, hFt])
  rw [hae, hval j]
  have hs : ∫ y, kerH (s.Φ₁ i j) x y * Ft j y ∂s.D.ν = ∫ z, s.Φ₁ i j z * Ft j (x * z) ∂s.D.μ :=
    ker_integral_shift X (φ := s.Φ₁ i j) (f := Ft j) (s.t₁ i j) (hinv j) (hmem j) x
  refine hs.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
  show s.Φ₁ i j z * ((ψ j).1 (x * z).1 * u j (ldet (x * z))) =
    s.Φ₁ i j z * u j (t + ldet z) * (ψ j).1 (x.1 * z.1)
  rw [hmul, hx, Prod.fst_mul]
  ring
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private def evAt {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (π : CuspSub E n) (x : H E n 0) :
    π.V →ₗ[ℂ] ℂ where
  toFun ψ := ψ.1.1 x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.finFac_pf :
    Basic → EvalBasis → FinGen → FinFac := by
  intro hB hE hG E _ _ _ n ι _ s
  obtain ⟨hl, hmul, -⟩ := hB E n s.pos
  obtain ⟨W, hWV, hWf, hW⟩ := hG E n ι s
  have sep : ∀ ψ : s.π.V, (∀ x : {x : H E n 0 // ldet x = 0}, evAt s.π x.1 ψ = 0) → ψ = 0 := by
    intro ψ h
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    have hy : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)) = 0 := by
      rw [hmul, hl]; ring
    have h0 := h ⟨_, hy⟩
    have h1 := s.fix.1 ψ.1 ψ.2 (-ldet ((g, 1) : H E n 0) / (n * Module.finrank ℚ E)) g
    exact h1.symm.trans h0
  haveI : FiniteDimensional ℂ W := hWf
  obtain ⟨d, xs, ws, hw, hrep⟩ := hE {x : H E n 0 // ldet x = 0} s.π.V (fun x => evAt s.π x.1) sep
    (LinearMap.range (Submodule.inclusion hWV)) inferInstance
  refine ⟨{ B := Fin d, w := fun b => (ws b).1, x := fun b => (xs b).1, mem := fun b => (ws b).2,
            zero := fun b => (xs b).2 }, ?_⟩
  have key : ∀ v : Hs (ι := ι) s.D, IsPiVec s.D s.π v → ∀ (x : H E n 0) (i : ι),
      inner ℂ (s.k₁ x i) v =
        ∑ b, (ws b).1.1 x.1 * inner ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i) v := by
    intro v hv x i
    obtain ⟨ψ, hψ, hval⟩ := hW v hv i (ldet x)
    have hb : ∀ b, inner ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i) v = ψ.1 (xs b).1.1 := by
      intro b
      rw [hval _ (by rw [hmul, hl, (xs b).2, add_zero])]
      exact s.fix.1 ψ (hWV hψ) _ _
    have hr := congrArg (evAt s.π x) (hrep ⟨ψ, hWV hψ⟩ ⟨⟨ψ, hψ⟩, rfl⟩)
    rw [map_sum] at hr
    rw [hval x rfl]
    refine hr.trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [map_smul, hb b, smul_eq_mul, mul_comm]
    rfl
  intro v hv x i
  let L : Hs (ι := ι) s.D →L[ℂ] ℂ := innerSL ℂ (s.k₁ x i) -
    ∑ b, (ws b).1.1 x.1 • innerSL ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i)
  have hL : ∀ f, L f = inner ℂ (s.k₁ x i) f -
      ∑ b, (ws b).1.1 x.1 * inner ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i) f := by
    intro f
    simp [L, ContinuousLinearMap.sum_apply]
  have hle : Submodule.span ℂ {f | IsPiVec s.D s.π f} ≤ LinearMap.ker (L : Hs (ι := ι) s.D →ₗ[ℂ] ℂ) :=
    Submodule.span_le.2 fun f hf => by
      have := key f hf x i
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      rw [hL, this, sub_self]
  have hv' : v ∈ closure ((Submodule.span ℂ {f | IsPiVec s.D s.π f} : Submodule ℂ (Hs (ι := ι) s.D)) : Set (Hs (ι := ι) s.D)) := hv
  have h0 : L v = 0 :=
    closure_minimal (t := {f | L f = 0}) (fun f hf => LinearMap.mem_ker.1 (hle hf))
      (isClosed_eq L.continuous continuous_const) hv'
  rw [hL] at h0
  exact sub_eq_zero.1 h0

end
end

section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.dropP_pf :
    Zero → KInv → Basic → Weak → PointRep → PComm → DropP := by
  intro hZ hK hB hW hR hC E _ _ _ n ι _ s m x y
  classical
  obtain ⟨-, -, -, -, -, -, -, hthth, hthmul, hrat, -, hthc⟩ := hB E n s.pos
  set S := piSp s.D s.π ι with hS
  set P := S.starProjection with hP
  have hmem : ∀ f, P f ∈ S := fun f => Submodule.starProjection_apply_mem S f
  have hPP : ∀ f, P (P f) = P f := fun f => (Submodule.starProjection_eq_self_iff).2 (hmem f)
  have hUπ : ∀ f, m.Uπ f = m.U (P f) := fun f => by
    have h2 : f - P f ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal f
    have hdec : P f + (f - P f) = f := by abel
    calc m.Uπ f = m.Uπ (P f + (f - P f)) := by rw [hdec]
      _ = m.U (P f) := by rw [map_add, m.pp.1 _ (hmem f), m.pp.2 _ h2, add_zero]
  have C₁ : ∀ f, P (s.T₁ f) = s.T₁ (P f) := hC E n s.pos s.D s.π s.fix ι s.Φ₁ s.T₁ s.t₁ s.o₁
  have C₂ : ∀ f, P (s.T₂ f) = s.T₂ (P f) := hC E n s.pos s.D s.π s.fix ι s.Φ₂ s.T₂ s.t₂ s.o₂
  have C₃ : ∀ f, P ((s.T₁ * m.U * s.T₂) f) = (s.T₁ * m.U * s.T₂) (P f) := hC E n s.pos s.D s.π s.fix ι m.Φ (s.T₁ * m.U * s.T₂) m.t m.o
  set Q : Hs (ι := ι) s.D →L[ℂ] Hs (ι := ι) s.D := (ContinuousLinearMap.id ℂ _ - P) ∘L m.Uπ with hQ
  have hQa : ∀ f, Q f = m.Uπ f - P (m.Uπ f) := fun f => rfl
  have key : ∀ g, s.T₁ (Q (s.T₂ g)) = 0 := fun g => by
    have e : s.T₁ (m.U (s.T₂ (P g))) = (s.T₁ * m.U * s.T₂) (P g) := rfl
    rw [hQa, map_sub, ← C₁, hUπ, C₂, e, ← C₃, hPP, sub_self]
  have hz : ∀ g i, inner ℂ (s.k₁ x i) (Q (s.T₂ g)) = 0 := fun g i => by
    have h0 := hR E n ι s s.Φ₁ s.T₁ s.t₁ s.o₁ (Q (s.T₂ g)) 0 (by rw [map_zero]; exact key g) x i
    rw [h0]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj : (((0 : Hs (ι := ι) s.D) j : Lp ℂ 2 s.D.ν) : H E n 0 → ℂ) =ᵐ[s.D.ν] 0 := Lp.coeFn_zero _ _ _
    rw [integral_congr_ae (g := fun _ => (0 : ℂ)) (hj.mono fun z hz => by rw [hz]; simp)]
    simp
  set f : H E n 0 → ℂ := fun z => ∑ i, inner ℂ (s.k₁ x i) (Q (s.k₂ (th z) i)) with hf
  have hfc : Continuous f := continuous_finset_sum _ fun i _ =>
    continuous_const.inner (Q.continuous.comp ((s.vecs.cont i).2.comp hthc))
  have hfi : Inv f := fun γ z => by
    have h := (hK E n ι s).2 ⟨th (γ : H E n 0), (hrat γ).2⟩ (th z)
    simp only [hf, hthmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show s.k₂ (th (γ : H E n 0) * th z) = s.k₂ (th z) from h]
  have hf0 := hZ E n s.D f Set.univ hfc hfi isOpen_univ (fun v _ => by
    have hw := fun i => hW E n ι s v (ContinuousLinearMap.adjoint Q (s.k₁ x i)) i
    have hpt : ∀ z, (v : H E n 0 → ℂ) z * f z =
        ∑ i, (v : H E n 0 → ℂ) z * inner ℂ (ContinuousLinearMap.adjoint Q (s.k₁ x i)) (s.k₂ (th z) i) := fun z => by
      simp only [hf, Finset.mul_sum, ContinuousLinearMap.adjoint_inner_left]
    simp only [hpt]
    rw [integral_finset_sum _ fun i _ => (hw i).1]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(hw i).2, ContinuousLinearMap.adjoint_inner_left]
    exact hz _ i)
  have h1 := hf0 (th y) (Set.mem_univ _)
  simp only [hf, hthth, hQa, inner_sub_right, Finset.sum_sub_distrib] at h1
  exact sub_eq_zero.1 h1
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped Classical ENNReal

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

theorem gFac_pf : FinFac → DropP → GFac := by
  intro hF hD E _ _ _ n ι _ s
  obtain ⟨p, hp⟩ := hF E n ι s
  refine ⟨p, fun m x y => ?_⟩
  have hd := hD E n ι s m
  rw [hd x y]
  simp only [hd (ac E n (ldet x) * p.x _) y, Gk, ContinuousLinearMap.comp_apply]
  have hmem : ∀ i, (piSp s.D s.π ι).starProjection (m.Uπ (s.k₂ y i)) ∈ piSp s.D s.π ι := fun i =>
    Submodule.starProjection_apply_mem _ _
  calc _ = ∑ i, ∑ b, (p.w b).1 x.1 * inner ℂ (s.k₁ (ac E n (ldet x) * p.x b) i)
          ((piSp s.D s.π ι).starProjection (m.Uπ (s.k₂ y i))) :=
        Finset.sum_congr rfl fun i _ => hp _ (hmem i) x i
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem ac_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : ac E n 0 = 1 := by
  unfold ac
  rw [zero_div, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero]
  rfl

private theorem test_trM {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]
    {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) (M : Matrix ι ι ℂ) :
    Continuous (trM Φ M) ∧ HasCompactSupport (trM Φ M) := by
  have e : trM Φ M = ∑ i, ∑ j, fun y => Φ i j y * M j i := by
    funext y
    simp [trM, Finset.sum_apply]
  constructor
  · exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => (hΦ i j).1.mul continuous_const
  · rw [e]
    exact HasCompactSupport.finset_sum fun i _ => HasCompactSupport.finset_sum fun j _ => (hΦ i j).2.mul_right

private theorem ldet_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {φ : H E n 0 → ℂ}
    (hc : HasCompactSupport φ) : ∃ N : ℕ, ∀ z, φ z ≠ 0 → |ldet z| ≤ N := by
  obtain ⟨R, hR⟩ := (hc.isCompact.image (continuous_abs.comp (continuous_ldet (E := E) (n := n)))).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_ge R
  exact ⟨N, fun z hz => (hR ⟨z, subset_tsupport _ hz, rfl⟩).trans hN⟩

private theorem cut_cont (N : ℕ) : Continuous fun t : ℝ => ((Dcy.chi N t : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (Dcy.continuous_chi N)

private theorem cut_supp (N : ℕ) : HasCompactSupport fun t : ℝ => ((Dcy.chi N t : ℝ) : ℂ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((N : ℝ) + 1)) fun t ht => by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at ht
    rw [Dcy.chi_eq_zero ht.le, Complex.ofReal_zero]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.rangeW_pf :
    Rep → RangeW := by
  intro hR E _ _ _ n ι _ s p hF m ψ hψ x₀ h₀
  obtain ⟨N, hN⟩ := ldet_bound (test_trM m.t s.M).2
  set u : ℝ → ℂ := fun t => ((Dcy.chi N t : ℝ) : ℂ) with hu
  have rep := fun y => hR E n ι s m ψ hψ u (cut_cont N) (cut_supp N) y
  have key : ∀ y : H E n 0, ldet y = 0 →
      ∫ x, ψ.1 x.1 * m.G y x * u (ldet x) ∂s.D.ν = ∫ z, m.φ z * ψ.1 (thetaA E n (y.1 * z.1)) ∂s.D.μ := by
    intro y hy
    rw [(rep y).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : m.φ z = 0
    · simp [hz]
    · have h1 : |(-(ldet y + ldet z))| ≤ N := by
        rw [hy, zero_add, abs_neg]
        exact hN z hz
      simp only [hu, Dcy.chi_eq_one h1, Complex.ofReal_one, mul_one]
  rw [← key x₀ h₀]
  have hG : ∀ x, ψ.1 x.1 * m.G x₀ x * u (ldet x) =
      ∑ b, (p.w b).1 x₀.1 * (ψ.1 x.1 * m.G (p.x b) x * u (ldet x)) := by
    intro x
    rw [hF m x₀ x, h₀, ac_zero, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [one_mul]
    ring
  simp_rw [hG]
  rw [integral_finset_sum _ fun b _ => ((rep (p.x b)).1).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, key (p.x b) (p.zero b)]

end
end

section
namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem trFin_pf : TrFin := by
  intro V B _ _ _ L w e h
  classical
  have hr : ∀ r : LinearMap.range L, (r : V) = ∑ b, e b (r : V) • w b := by
    rintro ⟨_, v, rfl⟩
    exact h v
  let A : LinearMap.range L →ₗ[ℂ] (B → ℂ) :=
    LinearMap.pi fun b => (e b).comp (LinearMap.range L).subtype
  let c : (B → ℂ) →ₗ[ℂ] LinearMap.range L :=
    L.rangeRestrict.comp (Fintype.linearCombination ℂ w)
  have hA : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    intro r hr0
    apply Subtype.ext
    rw [hr r]
    have hz : ∀ b, e b (r : V) = 0 := fun b => congrFun hr0 b
    simp [hz]
  haveI : FiniteDimensional ℂ (LinearMap.range L) := FiniteDimensional.of_injective A hA
  have hL : (L.restrict fun x _ => LinearMap.mem_range_self L x) = c ∘ₗ A := by
    ext r
    have h1 : (c (A r) : V) = L (∑ b, e b (r : V) • w b) := by
      simp [c, A, Fintype.linearCombination_apply]
    rw [LinearMap.comp_apply, h1, ← hr r]
    rfl
  rw [hL, LinearMap.trace_comp_comm', LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ B)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [c, A, Fintype.linearCombination_apply, Pi.single_apply, ite_smul]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
end

section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
private theorem deg_finrank_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (x : GA E n)
    (W : Submodule E (Fin n → E)) (hW : Module.finrank E W = 0) : deg x W = 0 := by
  have key : ∀ (k : ℕ) (M : Matrix (Fin n) (Fin k) E), k = 0 → degM x M = 0 := by
    rintro k M rfl
    exact degM_zero x M
  exact key _ _ hW

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
private theorem logSize_inv' {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (h : GA E n) :
    logSize (h⁻¹ : GA E n) = logSize h := by
  simp only [logSize, inv_inv]
  exact add_comm _ _

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
private theorem tau_le_prof {n k : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) (h1 : 1 ≤ k) (hk : k ≤ n) : τ ≤ prof n τ k := by
  have a : (1 : ℝ) ≤ k := by exact_mod_cast h1
  have b : (k : ℝ) ≤ n := by exact_mod_cast hk
  have c : (1 : ℝ) ≤ 2 * n + 1 - k := by linarith
  have d : (1 : ℝ) ≤ (k : ℝ) * (2 * n + 1 - k) := by nlinarith
  have e : τ * 1 ≤ τ * ((k : ℝ) * (2 * n + 1 - k)) := mul_le_mul_of_nonneg_left d hτ
  simp only [prof]
  nlinarith

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.inCut_pf :
    InCut := by
  intro E _ _ _ n
  obtain ⟨C, hC0, hC⟩ := E1.degRight E n
  obtain ⟨B, hB⟩ := (D1.degBdd E n).1 (1 : GA E n)
  have hB' : ∀ W, deg (1 : GA E n) W ≤ B := fun W => hB ⟨W, rfl⟩
  set A : ℝ := deg (1 : GA E n) ⊤ with hA
  refine ⟨|B| + |A| + 2 * C + 1, by positivity, fun τ g hτ => ?_⟩
  have hr : 0 ≤ redSize g := ((E1.redBasic E n).2.1 g).1
  have hcr : C * redSize g ≤ (|B| + |A| + 2 * C + 1) * redSize g := by
    apply mul_le_mul_of_nonneg_right _ hr
    have := abs_nonneg B
    have := abs_nonneg A
    linarith
  have hexp : (|B| + |A| + 2 * C + 1) * (1 + redSize g) =
      (|B| + |A| + 2 * C + 1) + (|B| + |A| + 2 * C + 1) * redSize g := by ring
  have hBa := le_abs_self B
  have hAa := neg_abs_le A
  have hBn := abs_nonneg B
  have hAn := abs_nonneg A
  have hτ0 : 0 ≤ τ := by
    have : 0 ≤ (|B| + |A| + 2 * C + 1) * redSize g := mul_nonneg (by positivity) hr
    linarith
  obtain ⟨γ, hγ⟩ : ∃ γ : GL (Fin n) E, logSize (ratGL E n γ * g) < redSize g + 1 :=
    exists_lt_of_ciInf_lt (lt_add_one (redSize g))
  have hinv := ((E1.mahler_holds E n τ).2.1 γ g)
  refine hinv.1 ?_
  set h : GA E n := ratGL E n γ * g with hh
  have hup : ∀ W, deg h W ≤ B + C * (2 + redSize g) := by
    intro W
    have s := hC 1 h W
    rw [one_mul] at s
    have t : C * (1 + logSize h) ≤ C * (2 + redSize g) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    linarith [hB' W]
  refine ⟨fun W => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Module.finrank E W) with h0 | h1
    · rw [deg_finrank_zero h W h0, h0]
      simp [prof]
    · have hk : Module.finrank E W ≤ n := by
        have := Submodule.finrank_le W
        simpa using this
      refine le_trans (hup W) (le_trans ?_ (tau_le_prof hτ0 h1 hk))
      linarith
  · have s := hC h (h⁻¹ : GA E n) ⊤
    rw [mul_inv_cancel, logSize_inv'] at s
    have t : C * (1 + logSize h) ≤ C * (2 + redSize g) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    linarith
end

section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.diagInt_pf :
    GFac → HalfTerm → DiagInt := by
  intro hF hH
  unfold DiagInt ForSu
  intro E _ _ _ n ι _ s m
  obtain ⟨p, hp⟩ := hF E n ι s
  have hb := fun b => (hH E n ι s m (p.w b) (p.mem b) (p.x b) (p.zero b)).1
  have hsum := MeasureTheory.integrable_finset_sum (Finset.univ : Finset p.B) fun b _ => hb b
  refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Finset.sum_apply]
  exact (hp m x x).symm
end

section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1 GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.uncutOf_pf :
    Basic → GFac → HalfTerm → RangeW → TrFin → DiscreteGroups.T1.G.UncutHalf := by
  intro hB hF hH hR hT E _ _ _ n hn D π hπ ι _ Φ₁ Φ₂ T₁ T₂ M k₁ k₂ a1 a2 hfin b1 b2 hv U Uπ Φ t c1 c2 hpi ht
  let s : Su E n ι := ⟨D, π, Φ₁, Φ₂, T₁, T₂, M, k₁, k₂, hn, hπ, a1, a2, hfin, b1, b2, hv⟩
  let m : Mid s := ⟨U, Uπ, Φ, c1, c2, hpi⟩
  obtain ⟨p, hp⟩ := hF E n ι s
  obtain ⟨hac, hmul, -⟩ := hB E n hn
  have hsum : lInt0 D k₁ k₂ Uπ = fun x => ∑ b, (p.w b).1 x.1 * m.G (ac E n (ldet x) * p.x b) x :=
    funext fun x => hp m x x
  have hterm := fun b => hH E n ι s m (p.w b) (p.mem b) (p.x b) (p.zero b)
  obtain ⟨L, hL, -, rfl⟩ := ht
  let w : p.B → π.V := fun b => ⟨p.w b, p.mem b⟩
  let e : p.B → (π.V →ₗ[ℂ] ℂ) := fun b =>
    { toFun := fun ψ => ψ.1.1 (p.x b).1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hcentre : ∀ (ψ : Sm E n), ψ ∈ π.V → ∀ g : GA E n,
      ψ.1 (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)).1 = ψ.1 g := by
    intro ψ hψ g
    exact hπ.1 ψ hψ _ g
  have hspan : ∀ v, L v = ∑ b, e b (L v) • w b := by
    intro v
    apply Subtype.ext
    apply Subtype.ext
    funext g
    have h0 : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)) = 0 := by
      rw [hmul, hac]; ring
    have h1 := hR E n ι s p hp m v.1 v.2 _ h0
    have h2 : (L v).1.1 g = ∑ b, (L v).1.1 (p.x b).1 * (p.w b).1 g := by
      rw [← hcentre (L v).1 (L v).2 g, hL v]
      refine h1.trans (Finset.sum_congr rfl fun b _ => ?_)
      rw [hcentre _ (p.mem b), hL v, mul_comm]
      rfl
    let ev : π.V →ₗ[ℂ] ℂ :=
      { toFun := fun ψ => ψ.1.1 g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have h3 : (∑ b, e b (L v) • w b).1.1 g = ev (∑ b, e b (L v) • w b) := rfl
    rw [h3, map_sum]
    exact h2
  have htr := hT π.V p.B L w e hspan
  refine ⟨?_, ?_⟩
  · rw [hsum]
    exact integrable_finset_sum _ fun b _ => (hterm b).1
  · rw [hsum, integral_finset_sum _ fun b _ => (hterm b).1, htr, Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [(hterm b).2]
    congr 1
    exact (hL (w b) (p.x b).1).symm
end

section
namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem aeEq : AeEq := aeEq_pf basic_pf
theorem zero : Zero := zero_pf aeEq
theorem pointRep : PointRep := pointRep_pf aeEq kInv_pf
theorem ker : Ker := ker_pf weak_pf pointRep pComm_pf pDiag_pf
theorem supp : Supp := supp_pf basic_pf zero kInv_pf pSupp_pf ker
theorem gBound : GBound := gBound_pf basic_pf
theorem gFac : GFac := gFac_pf (finFac_pf basic_pf evalBasis_pf (finGen_pf basic_pf))
  (dropP_pf zero kInv_pf basic_pf weak_pf pointRep pComm_pf)
theorem rep : Rep := rep_pf basic_pf (thetaInt_pf basic_pf) kInv_pf pDiag_pf ker
theorem sizes : Sizes := by first | exact sizes_of_basic basic_pf | exact sizes_of_basic
theorem domInt : DomInt := domInt_pf basic_pf sizes
theorem halfTerm : HalfTerm := halfTerm_pf basic_pf gBound supp rep flip_pf domInt
theorem uncutHalf : DiscreteGroups.T1.G.UncutHalf := uncutOf_pf basic_pf gFac halfTerm (rangeW_pf rep) trFin_pf
theorem cutTail : DiscreteGroups.T1.G.CutTail2 :=
  tailOf_pf basic_pf sizes inCut_pf (tailInt_of_bounds gFac gBound supp domInt) (diagInt_pf gFac halfTerm)

theorem growthPiJ_holds : PositivityTheory.Rg.BcB.Desc.GrowthPiJ :=
  DiscreteGroups.T1.G.rGrowthPiJ_of (fun _ _ => uncutHalf) (fun _ _ => cutTail) PositivityTheory.Rg.BcB.CV.ellFormula2J
    PositivityTheory.Rg.BcB.E1.sFun_holds DiscreteGroups.T1.G.Dcy.piVecEx_holds DiscreteGroups.T1.G.piInv


end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
end
