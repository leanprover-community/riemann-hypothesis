import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreDescOf
import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.PowIndep
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CharIndep
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.UnitTrace
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.AtInj
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.ListProdStable
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.ExistsPowerSums
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.AmpFin
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.InfSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.BumpEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchSlotEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.IntPow
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.AmpSlot
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PairPosition
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitLev
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStableAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitMatch
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LineRank
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocIff
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursIff
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweLine
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.BallSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.PsiInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweBall
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxSubsetOfMemNhdsZero
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.AtDown
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.SbInv
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.OffStable
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TypedEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistY
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HasFinTraceSmul
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.GoodEx

section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped Classical

namespace UpperTheory.ConvolutionTheory.T.AbsoluteValueFixed

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {v : Pl K}

private theorem fixed_fd (U : Subgroup (Gw n v)) (hU : CO U) (σ : SmIrr (Gw n v)) :
    FiniteDimensional ℂ (fixedVectors σ.ρ U) := by
  have h := PositivityTheory.Exh.irreducibleAdmissibleGL (v.adicCompletion K) n σ.V σ.ρ σ.smooth σ.irred
  have h2 := h.2 U hU.2 hU.1
  have e : GlobalTheory.PRep.fixed σ.ρ U = fixedVectors σ.ρ U := by
    ext x
    constructor
    · intro hx g hg
      simpa using hx ⟨g, hg⟩
    · intro hx g
      simpa using hx g g.2
  rw [← e]
  exact h2

private theorem td : TotallyDisconnectedSpace (Gw n v) := by
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) (v.adicCompletion K)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → v.adicCompletion K))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

end UpperTheory.ConvolutionTheory.T.AbsoluteValueFixed

open UpperTheory.ConvolutionTheory.T.AbsoluteValueFixed in
theorem UpperTheory.ConvolutionTheory.T.absLast :
    UpperTheory.ConvolutionTheory.T.AbsLast := by
  intro K _ _ n v _ _ m _ U hU ι _ τ a Z τ₀ c Z₀ hc hZ₀ h0 hZ hfix hid
  by_contra hno
  obtain ⟨ζ, hζ⟩ := Multiset.exists_mem_of_ne_zero hZ₀
  have hk : ((Multiset.filter (· = ζ) Z₀).card : ℂ) ≠ 0 := by
    have : 0 < (Multiset.filter (· = ζ) Z₀).card :=
      Multiset.card_pos_iff_exists_mem.2 ⟨ζ, Multiset.mem_filter.2 ⟨hζ, rfl⟩⟩
    exact_mod_cast this.ne'
  let σ : Option ι → SmIrr (Gw n v) := fun o => o.elim τ₀ τ
  let C : Option ι → ℂ := fun o => o.elim (c * ((Multiset.filter (· = ζ) Z₀).card : ℂ))
    (fun i => -(a i * ((Multiset.filter (· = ζ) (Z i)).card : ℂ)))
  haveI : m.IsMulRightInvariant := GroundTheory.Automorphic.Measures.isMulRightInvariant_GL (v.adicCompletion K) n m
  haveI : LocallyCompactSpace (Gw n v) :=
    hU.1.locallyCompactSpace_of_mem_nhds_of_group (hU.2.mem_nhds U.one_mem)
  haveI : T2Space (Gw n v) := Units.isEmbedding_embedProduct.t2Space
  haveI : TotallyDisconnectedSpace (Gw n v) := td
  have key := UpperTheory.ConvolutionTheory.C.charIndep (Gw n v) m U hU (Option ι) σ C (fun o => fixed_fd U hU (σ o)) ?_ none hfix
  · have hset : {o : Option ι | Nonempty ((σ o).ρ.Equiv (σ none).ρ)} = {none} := by
      ext o
      cases o with
      | none => exact ⟨fun _ => rfl, fun _ => ⟨Representation.Equiv.refl (σ none).ρ⟩⟩
      | some i =>
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, reduceCtorEq, iff_false]
        exact fun h => hno ⟨i, h⟩
    rw [hset, finsum_mem_singleton] at key
    exact (mul_ne_zero hc hk) key
  · intro φ s hφ hinv hs
    have e := hid φ (s none) (fun i => s (some i)) hφ hinv (hs none) (fun i => hs (some i))
    have p := UpperTheory.ConvolutionTheory.C.powIndep (Option ι)
      (fun o => o.elim (c * s none) (fun i => -(a i * s (some i))))
      (fun o => o.elim Z₀ Z)
      (fun o => by cases o with
        | none => exact h0
        | some i => exact hZ i)
      (by
        filter_upwards [e] with j hj
        rw [Fintype.sum_option]
        simp only [Option.elim]
        have : ∑ i, -(a i * s (some i)) * ((Z i).map (· ^ j)).sum
            = -∑ i, a i * ((Z i).map (· ^ j)).sum * s (some i) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [this, ← hj]
        ring) ζ
    rw [Fintype.sum_option] at p ⊢
    simp only [Option.elim] at p
    have : ∑ i, C (some i) * s (some i)
        = ∑ i, -(a i * s (some i)) * ((Multiset.filter (· = ζ) (Z i)).card : ℂ) :=
      Finset.sum_congr rfl (fun i _ => by simp only [C, Option.elim]; ring)
    rw [this]
    have h1 : C none = c * ((Multiset.filter (· = ζ) Z₀).card : ℂ) := rfl
    rw [h1]
    linear_combination p
end

section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep GlobalTheory.CuspRep

namespace UpperTheory.ConvolutionTheory.T

section Rep
variable {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

private def pull (e : G ≃ₜ* H) (τ : SmIrr H) : SmIrr G where
  V := τ.V
  ρ := τ.ρ.comp (e : G →* H)
  smooth := fun x => (τ.smooth x).preimage e.continuous
  irred := by
    refine (OrderIso.isSimpleOrder_iff (β := Subrepresentation τ.ρ)
      { toFun := fun S => ⟨S.toSubmodule, fun g v hv => ?_⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (e g) hv⟩
        left_inv := fun S => rfl
        right_inv := fun S => rfl
        map_rel_iff' := Iff.rfl }).2 τ.irred
    have := S.apply_mem_toSubmodule (e.symm g) hv
    simpa using this

end Rep

section Trace
variable {G H V : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H] [AddCommGroup V] [Module ℂ V]

private theorem hasFinTrace_smul {A : V →ₗ[ℂ] V} {c s : ℂ} (hc : c ≠ 0) (h : HasFinTrace A s) :
    HasFinTrace (c • A) (c * s) := by
  obtain ⟨hf, rfl⟩ := h
  have hR : LinearMap.range (c • A) = LinearMap.range A := LinearMap.range_smul A c hc
  have key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (c • A) v ∈ R)
      (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A),
      LinearMap.trace ℂ R ((c • A).restrict h1) =
        c * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2) := by
    rintro _ rfl h1 h2
    have : (c • A).restrict h1 = c • A.restrict h2 := by
      ext x
      simp
    rw [this, map_smul, smul_eq_mul]
  exact ⟨hR ▸ hf, key _ hR _ _⟩

private theorem hasTrace_map (e : G ≃ₜ* H) (mF : Measure G) (mE : Measure H) (c : NNReal) (hc : c ≠ 0)
    (h : mE = c • mF.map e) (π : Representation ℂ H V) (ψ : H → ℂ) (s : ℂ)
    (hs : HasTrace mF (π.comp (e : G →* H)) (fun g => ψ (e g)) s) : HasTrace mE π ψ ((c : ℂ) * s) := by
  obtain ⟨A, hA, hf⟩ := hs
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  refine ⟨(c : ℂ) • A, fun x l => ?_, hasFinTrace_smul hc' hf⟩
  obtain ⟨hi, hl⟩ := hA x l
  have hi' : Integrable (fun y => ψ y * l (π y x)) (mF.map e) := hme.integrable_map_iff.2 hi
  subst h
  refine ⟨hi'.smul_measure_nnreal, ?_⟩
  rw [integral_smul_nnreal_measure, hme.integral_map, LinearMap.smul_apply, map_smul, hl]
  simp [NNReal.smul_def]

end Trace

end UpperTheory.ConvolutionTheory.T

theorem UpperTheory.ConvolutionTheory.T.pullBack :
    UpperTheory.ConvolutionTheory.T.PullBack := by
  intro F E _ _ _ _ _ n v w hs _ _ _ _ mF mE hF hE τ'
  obtain ⟨⟨e, he⟩, -⟩ := UpperTheory.ConvolutionTheory.L1.splitLoc F E v w hs n
  have hmap : (mF.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map mF e
  have hscal := Measure.isMulLeftInvariant_eq_smul mE (mF.map e)
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure mE (mF.map e)
  have hc0 : mE.haarScalarFactor (mF.map e) ≠ 0 := hpos.ne'
  refine ⟨pull e τ', ((mE.haarScalarFactor (mF.map e) : NNReal) : ℂ), by exact_mod_cast hc0, ?_, ?_, ?_⟩
  · rintro τ₁ ⟨E₁⟩
    refine ⟨E₁.toLinearEquiv, fun g x => ?_⟩
    rw [← he g]
    exact LinearMap.congr_fun (E₁.toIntertwiningMap.isIntertwining' g) x
  · intro ψ s h
    refine hasTrace_map e mF mE _ hc0 hscal τ'.ρ ψ s ?_
    have hfun : (fun g => ψ (e g)) = fun g => ψ (mapGL n (completionMap v w.1) g) :=
      funext fun g => by rw [he g]
    rw [hfun]
    exact h
  · intro J U hJ hU
    have hU' : ∀ g, g ∈ U ↔ e g ∈ J := fun g => by rw [he g]; exact hU g
    have hset : (U : Set (Gw n v)) = e ⁻¹' (J : Set (Gw n w.1)) := Set.ext hU'
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hset]
      exact e.toHomeomorph.isCompact_preimage.2 hJ.1
    · rw [hset]
      exact hJ.2.preimage e.continuous
    · intro h h0
      refine h (eq_bot_iff.2 fun x hx => ?_)
      have hx' : x ∈ fixedVectors (pull e τ').ρ U := fun u hu => hx _ ((hU' u).1 hu)
      rw [h0] at hx'
      exact hx'
    · intro φ hφ hinv
      refine ⟨fun y => φ (e.symm y), ⟨hφ.1.comp_continuous e.symm.continuous,
        hφ.2.comp_homeomorph e.symm.toHomeomorph⟩, fun u hu g => ?_, ?_⟩
      · have hu' : e.symm u ∈ U := (hU' _).2 (by simpa using hu)
        simpa [map_mul] using hinv _ hu' (e.symm g)
      · funext g
        rw [← he g]
        simp
end
end

section
theorem UpperTheory.ConvolutionTheory.T.oneTerm :
    UpperTheory.ConvolutionTheory.T.OneTerm := by
  intro K _ _ _ n l _ μ _ θ 𝔰 V Λ t hV hθ hAt x j
  have hset : {V' : Submodule ℂ (UpperTheory.ConvolutionTheory.C.LL μ) | UpperTheory.ConvolutionTheory.C.IsSummand μ V' ∧
      V'.map (θ.U : UpperTheory.ConvolutionTheory.C.LL μ →ₗ[ℂ] UpperTheory.ConvolutionTheory.C.LL μ) = V' ∧
      UpperTheory.ConvolutionTheory.At μ 𝔰.S V' Λ t} = {V} := by
    ext V'
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact UpperTheory.ConvolutionTheory.Dp.atInj K n μ V' V h1 hV 𝔰.S 𝔰.finS t h3.2 hAt.2
    · rintro rfl
      exact ⟨hV, hθ, hAt⟩
  unfold UpperTheory.ConvolutionTheory.Side.tr
  rw [hset, finsum_mem_singleton]
end

section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical

private theorem trace_range_smul {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) {c s : ℂ} (hc : c ≠ 0)
    (h : HasFinTrace A s) : HasFinTrace (c • A) (c * s) := by
  obtain ⟨hfd, rfl⟩ := h
  have hr : LinearMap.range (c • A) = LinearMap.range A := LinearMap.range_smul _ _ hc
  have key : ∀ W : Submodule ℂ V, W = LinearMap.range A → ∀ h' : ∀ v ∈ W, (c • A) v ∈ W,
      LinearMap.trace ℂ W ((c • A).restrict h') = c * LinearMap.trace ℂ (LinearMap.range A)
        (A.restrict (p := LinearMap.range A) (q := LinearMap.range A) fun v _ => LinearMap.mem_range_self A v) := by
    rintro W rfl h'
    have : (c • A).restrict h' = c • A.restrict (p := LinearMap.range A) (q := LinearMap.range A)
        (fun v _ => LinearMap.mem_range_self A v) := by
      ext v
      rfl
    rw [this, map_smul, smul_eq_mul]
  exact ⟨hr ▸ hfd, key _ hr _⟩

private theorem hasTrace_of_smul {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {s : ℂ} {d : ENNReal} (h0 : d ≠ 0) (ht : d ≠ ⊤)
    (h : HasTrace (d • m) ρ f s) : HasTrace m ρ f (((d.toReal : ℂ))⁻¹ * s) := by
  obtain ⟨A, hA, hT⟩ := h
  have hr : (d.toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'
  refine ⟨((d.toReal : ℂ))⁻¹ • A, fun v l => ?_, trace_range_smul A (inv_ne_zero hr) hT⟩
  obtain ⟨h1, h2⟩ := hA v l
  refine ⟨(integrable_smul_measure h0 ht).1 h1, ?_⟩
  rw [LinearMap.smul_apply, map_smul, h2, integral_smul_measure, smul_eq_mul, Complex.real_smul, inv_mul_cancel_left₀ hr]

private theorem fd_of_trace {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {I : Subgroup G} {s : ℂ} (hIm : MeasurableSet (I : Set G))
    (h0 : m I ≠ 0) (ht : m I ≠ ⊤) (h : HasTrace m ρ ((I : Set G).indicator 1) s) :
    FiniteDimensional ℂ (fixedVectors ρ I) := by
  obtain ⟨A, hA, hfd, -⟩ := h
  have hr : ((m (I : Set G)).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'
  have hfix : ∀ v ∈ fixedVectors ρ I, A v = ((m (I : Set G)).toReal : ℂ) • v := by
    intro v hv
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA v l).2, map_smul, smul_eq_mul]
    have e : (fun g => (I : Set G).indicator (1 : G → ℂ) g * l (ρ g v)) = (I : Set G).indicator fun _ => l v := by
      funext g
      by_cases hg : g ∈ (I : Set G)
      · have : ρ g v = v := hv g hg
        simp [hg, this]
      · simp [hg]
    rw [e, integral_indicator hIm, setIntegral_const, measureReal_def, Complex.real_smul]
  have hle : fixedVectors ρ I ≤ LinearMap.range A := by
    intro v hv
    refine ⟨((m (I : Set G)).toReal : ℂ)⁻¹ • v, ?_⟩
    rw [map_smul, hfix v hv, smul_smul, inv_mul_cancel₀ hr, one_smul]
  exact Submodule.finiteDimensional_of_le hle

private theorem test_ind {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) :
    Test (((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w)).indicator (1 : Gw n w → ℂ)) := by
  obtain ⟨hc, ho⟩ := (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test K n w).1
  have hcl : IsClosed ((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w)) :=
    Subgroup.isClosed_of_isOpen _ ho
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ ((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w))
  · filter_upwards [ho.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    rfl
  · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

private theorem iw_pow_at {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) [MeasurableSpace (Gw n w)]
    [BorelSpace (Gw n w)] (m : Measure (Gw n w)) [m.IsHaarMeasure] (σ : SmIrr (Gw n w)) (ν : Fin n → ℤ) (hν : Antitone ν)
    {s₀ : ℂ} (h₀ : HasTrace m σ.ρ (((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w)).indicator 1) s₀) :
    ∃ (c : ℂ) (Z : Multiset ℂ), 0 ∉ Z ∧ ∀ j : ℕ, HasTrace m σ.ρ ((GM.iwCoset w (j • ν)).indicator 1) (c * (Z.map (· ^ j)).sum) := by
  obtain ⟨hc, ho⟩ := (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test K n w).1
  have hpos : m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) ≠ 0 :=
    (ho.measure_pos m ⟨1, one_mem _⟩).ne'
  have htop : m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) ≠ ⊤ := hc.measure_lt_top.ne
  have hfd := fd_of_trace ho.measurableSet hpos htop h₀
  set d : ENNReal := (m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)))⁻¹ with hd
  have hd0 : d ≠ 0 := ENNReal.inv_ne_zero.2 htop
  have hdt : d ≠ ⊤ := ENNReal.inv_ne_top.2 hpos
  haveI : (d • m).IsHaarMeasure := Measure.IsHaarMeasure.smul m hd0 hdt
  have h1 : (d • m) (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) = 1 := by
    rw [Measure.smul_apply, smul_eq_mul, hd, ENNReal.inv_mul_cancel hpos htop]
  obtain ⟨Z, hZ0, -, hZ⟩ := UpperTheory.ConvolutionTheory.C.iwPow K n w (d • m) h1 σ ν hν hfd
  exact ⟨_, Z, hZ0, fun j => hasTrace_of_smul hd0 hdt (hZ j)⟩

private theorem amp_A_eq {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a : TI K n)
    (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) (h1 : 𝔞.ν = ν) (h2 : 𝔞.a₀ = a) (h3 : 𝔞.U = U) :
    𝔞.A = Oinf μ ν a ∘L prj (fixF μ U) := by
  subst h2 h3
  have : ∀ (ν' : Measure (archGroup K n)) (_ : ν'.IsHaarMeasure) (_ : ν' = ν) , Oinf μ ν' 𝔞.a₀ = Oinf μ ν 𝔞.a₀ := by
    intro ν' _ h; subst h; rfl
  exact congrArg (· ∘L prj (fixF μ 𝔞.U)) (this 𝔞.ν 𝔞.haar h1)

private theorem trOn_bot' {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (B : H →L[ℂ] H) :
    trOn (⊥ : Submodule ℂ H) B = 0 := by
  have := UpperTheory.trOn_eq_mul_of_eq_smul_on_subspace H ⊥ B B 0 inferInstance (fun v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv]; simp)
  simpa using this

theorem UpperTheory.ConvolutionTheory.T.sideSum :
    UpperTheory.ConvolutionTheory.T.SideSum := by
  intro F E _ _ _ _ _ _ σ n l hn μ _ ν _ _ _ m hm a q w₀ S UF e he p x hx
  haveI hmH : ∀ v, (m v).IsHaarMeasure := fun v => (hm v).1
  by_cases hex : ∃ (L : GM.Loc σ n q w₀) (𝔣 : Side (Twist.id μ) l), L.S = S ∧ (∀ v ∈ S, L.UF v = UF v) ∧ GM.IsSideF L ν a e 𝔣
  swap
  · refine ⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, ?_⟩
    intro L 𝔣 h1 h2 h3
    exact absurd ⟨L, 𝔣, h1, h2, h3⟩ hex
  obtain ⟨L₀, 𝔣₀, hS₀, hU₀, hF₀⟩ := hex
  obtain ⟨κ, -, hT⟩ := UpperTheory.ConvolutionTheory.C.termF F E σ n l hn μ ν m hm
  have hfin := (UpperTheory.ConvolutionTheory.T.ampFin F n hn μ 𝔣₀.toAmp).1 x hx
  set P : Set (Submodule ℂ (LL μ)) := {V | IsSummand μ V ∧ eigIn V 𝔣₀.toAmp.A x ≠ ⊥ ∧ p V} with hP
  have hPfin : P.Finite := hfin.subset fun V h => ⟨h.1, h.2.1⟩
  have hτ : ∀ V : P, ∃ τ : ∀ v : Pl F, SmIrr (Gw n v), ∀ v, Occurs μ V.1 v (τ v) := fun V => by
    have := fun v => (UpperTheory.ConvolutionTheory.C.occursBasics F n μ V.1 v (m v) V.2.1).1
    choose τ hτ using this
    exact ⟨τ, hτ⟩
  choose τ hτ using hτ
  have hZ : ∀ V : P, ∃ (c : ℂ) (Z : Multiset ℂ), 0 ∉ Z ∧ ∀ j : ℕ,
      HasTrace (m q) (τ V q).ρ ((GM.iwCoset q (j • e)).indicator 1) (c * (Z.map (· ^ j)).sum) := fun V => by
    obtain ⟨s₀, hs₀⟩ := (UpperTheory.ConvolutionTheory.C.occursBasics F n μ V.1 q (m q) V.2.1).2.2 (τ V q) (hτ V q) _ (test_ind q)
    exact iw_pow_at q (m q) (τ V q) e he hs₀
  choose c Z hZ0 hZ using hZ
  have hN := fun V : P => hT a q w₀ S V.1 (τ V) x V.2.1 hx (fun v _ => hτ V v)
  choose N hN using hN
  letI : Fintype P := hPfin.fintype
  refine ⟨P, inferInstance, fun V => V.1, τ, fun V => κ * x * N V * c V, Z, fun V => ⟨V.2.1, V.2.2.2, hZ0 V, hτ V⟩, ?_⟩
  intro L 𝔣 hS hU hF s hs j
  have hUF : L.UF = L₀.UF := by
    funext v
    by_cases hv : v ∈ S
    · rw [hU v hv, hU₀ v hv]
    by_cases hq : v = q
    · subst hq
      rw [L.at_q.2.2.2, L₀.at_q.2.2.2]
    · rw [(L.off v (hS ▸ hv) hq).2.2.2, (L₀.off v (hS₀ ▸ hv) hq).2.2.2]
  have hA : 𝔣.toAmp.A = 𝔣₀.toAmp.A := by
    obtain ⟨h1, h2, -, h3, -, -⟩ := hF
    obtain ⟨h1', h2', -, h3', -, -⟩ := hF₀
    rw [amp_A_eq 𝔣.toAmp ν a _ h1 h2 h3, amp_A_eq 𝔣₀.toAmp ν a _ h1' h2' h3', hUF]
  have hid : ∀ V : Submodule ℂ (LL μ), V.map ((Twist.id μ).U : LL μ →ₗ[ℂ] LL μ) = V := fun V => by
    have : ((Twist.id μ).U : LL μ →ₗ[ℂ] LL μ) = LinearMap.id := LinearMap.ext fun _ => rfl
    rw [this, Submodule.map_id]
  have hsum : 𝔣.tr p x j = ∑ᶠ V ∈ P, trOn (eigIn V 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) := by
    unfold Side.tr
    refine finsum_mem_inter_support_eq _ _ _ ?_
    ext V
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, hP]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩
      refine ⟨⟨h1, fun h => h4 ?_, h3⟩, h4⟩
      rw [hA, h, trOn_bot']
    · rintro ⟨⟨h1, -, h3⟩, h4⟩
      exact ⟨⟨h1, hid V, h3⟩, h4⟩
  rw [hsum, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [(hN V).2 L e 𝔣 hS he hF j _ (s V) (hZ V j) (hs V)]
  ring
end

section
open NumberField IsDedekindDomain Filter

theorem UpperTheory.ConvolutionTheory.T.pickS :
    UpperTheory.ConvolutionTheory.T.PickS := by
  classical
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V Λ t hV hAt v
  obtain ⟨hInf, hUnr, hNe, -, -, -⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨S₀, hS₀, hA⟩ := hAt
  obtain ⟨-, -, h0⟩ := UpperTheory.ConvolutionTheory.Dp.parEx E n hn μ V hV
  have hU := Filter.eventually_cofinite.1 hUnr
  have hfin := ((hS₀.image (fun w => w.under (𝓞 F))).union hU).union (Set.finite_singleton v)
  obtain ⟨q, hq, hqS⟩ := (hInf.diff hfin).nonempty
  have hsub : ∀ w, w.under (𝓞 F) ∉ hfin.toFinset → w ∉ S₀ := fun w hw hw0 =>
    hw (hfin.mem_toFinset.2 (Or.inl (Or.inl ⟨w, hw0, rfl⟩)))
  refine ⟨hfin.toFinset, q, (hNe q).some, hfin.mem_toFinset.2 (Or.inr rfl),
    fun h => hqS (hfin.mem_toFinset.1 h), hq, fun u hu => ?_, fun w hw => ?_, fun S' hS' => ?_⟩
  · by_contra h
    exact hu (hfin.mem_toFinset.2 (Or.inl (Or.inr h)))
  · exact (hA.2 w (hsub w hw)).2.1
  · have hS : ∀ w, w ∉ S' → w ∉ S₀ := fun w hw => hsub w fun h => hw ((hS' w).2 (Or.inl h))
    exact ⟨⟨hA.1, fun w hw => hA.2 w (hS w hw)⟩, fun τ => (hA.1 τ).1,
      fun w hw => ⟨(hA.2 w (hS w hw)).1, h0 w _ (hA.2 w (hS w hw))⟩⟩
end

section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1
open scoped ComplexConjugate

theorem UpperTheory.ConvolutionTheory.T.Port.adj_ne {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (u : H) (hu : star T u ≠ 0) : (T * star T) u ≠ 0 := by
  intro h0
  apply hu
  rw [ContinuousLinearMap.star_eq_adjoint] at h0 ⊢
  have h1 : T (ContinuousLinearMap.adjoint T u) = 0 := h0
  rw [← inner_self_eq_zero (𝕜 := ℂ), ContinuousLinearMap.adjoint_inner_left, h1, inner_zero_right]

theorem UpperTheory.ConvolutionTheory.T.Port.pickInf_of (hInf : UpperTheory.ConvolutionTheory.L1.InfSplit) (hAB : UpperTheory.ConvolutionTheory.L1.ArchBasic)
    (hBump : UpperTheory.ConvolutionTheory.L1.BumpEx) (hPosition : UpperTheory.ConvolutionTheory.L1.ArchSlotEx) (hSq : UpperTheory.ConvolutionTheory.L1.SqOp)
    (hAmp : UpperTheory.ConvolutionTheory.L1.AmpSlot) (hPair : UpperTheory.ConvolutionTheory.L1.PairPosition) : UpperTheory.ConvolutionTheory.T.PickInf := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ u hu
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 :=
    ⟨Module.finrank F E - 1, by have := hp.two_le; omega⟩
  obtain ⟨p⟩ := (hInf F E σ hσ m hm).1 inferInstance
  obtain ⟨D, -⟩ := (hInf F E σ hσ m hm).2 p
  obtain ⟨-, -, -, -, -, ⟨s, hsl, hs⟩, -, -⟩ := hAB F E σ m D n
  obtain ⟨νF, hνF⟩ : ∃ νF : Measure (archGroup F n), νF.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨b, hbs, hbf, hbn, hbu⟩ := hBump F n νF (LL μE)
    (((rightRegularRep (rationalGLOne E n) μE).compHom (archP E n) continuous_archP).compHom (s 0) (hs 0)) u hu
  obtain ⟨νE, hνE, a, aE, aF, hA⟩ := hPosition F E σ m D n νF b hbs hbf hbn
  obtain ⟨hsq, -, -, -⟩ := hSq F n νF b a aF m hA.sq hA.pow hA.norm (LL μE)
    (((rightRegularRep (rationalGLOne E n) μE).compHom (archP E n) continuous_archP).compHom (s 0) (hs 0))
  obtain ⟨hAE, hAF⟩ := hAmp F E σ m D n νE νF b a aE aF hA
  refine ⟨m, hm, D, s, hs, νE, hνE, νF, hνF, b, a, aE, aF, hsl, hA, hAE μE, hAF μF,
    hPair F E σ m hm D n νE νF b a aE aF hA, ?_⟩
  have key := UpperTheory.ConvolutionTheory.T.Port.adj_ne _ u hbu
  rw [← hsq] at key
  exact key

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.T.pickInf :
    UpperTheory.ConvolutionTheory.T.PickInf := UpperTheory.ConvolutionTheory.T.Port.pickInf_of infSplit archBasic bumpEx archPositionEx sqOp ampPosition pairPosition
end
end

section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

open scoped ComplexConjugate

theorem tyEx_of (hLev : SplitLev) (hSt : SplitStable) (hMa : SplitMatch) (hIn : InertData) (hOff : OffStable)
    (hTyp : TypedEx) (hEig : EigBasic) : TyEx := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV q w₀ hq S hqS hunr hsph mk
  have h1 : ∀ {G : Type} [Group G] [TopologicalSpace G] (J : Subgroup G), IsChr J 1 := fun J =>
    ⟨IsLocallyConstant.const 1, fun _ _ => norm_one, fun _ _ _ _ => (mul_one _).symm⟩
  have hu : ∀ (v : Pl F) (u : PlacesOver E v), u.1.under (𝓞 F) = v := fun v u => HeightOneSpectrum.ext u.2.over.symm
  have key : ∀ v : Pl F, ∃ (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)) (χ : ∀ u : PlacesOver E v, Gw n u.1 → ℂ)
      (c : ℂ) (f₀ : Gw n v → ℂ) (UE : Subgroup (GL (Fin n) (CompletionsOver E v))) (UF : Subgroup (Gw n v)),
      (∀ u, CO (J u) ∧ IsChr (J u) (χ u) ∧ V ⊓ eigL μ u.1 (J u) (χ u) ≠ ⊥) ∧
      (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ J u) → (∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ J u) ∧
          ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u (mapGL n (galFin σ v) x)) = ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u x)) ∧
      (GM.Split E v → ∀ u, χ u = 1) ∧
      (v ∉ S → v ≠ q → (∀ u, J u = GLnLocal.integralGL (u.1.adicCompletion E) n ∧ χ u = 1) ∧
        (UE : Set (GL (Fin n) (CompletionsOver E v))) = unitSet E n v ∧ UF = GLnLocal.integralGL (v.adicCompletion F) n) ∧
      (v = q → (∀ u, J u = GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
        (∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
        UF = GLnLocal.iwahori (v.adicCompletion F) n) ∧
      (v ∈ S → IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧
        (UE : Set (GL (Fin n) (CompletionsOver E v))) ⊆ unitSet E n v ∧ IsOpen (UF : Set (Gw n v)) ∧
        UF ≤ GLnLocal.integralGL (v.adicCompletion F) n) ∧
      (v ∈ S → ¬ GM.Split E v → (∀ u, RankOne μ V u.1 (J u) (χ u)) ∧
        GM.MatchAt σ v c (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) f₀ ∧
        Test (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) ∧ Test f₀ ∧
        (∀ y ∈ UE, ∀ g, (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) (y * g) =
          (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) g) ∧
        ∀ y ∈ UF, ∀ g, f₀ (y * g) = f₀ g) ∧
      (v ∈ S → GM.Split E v → (∀ g, g ∈ UF ↔ mapGL n (completionMap v (mk v).1) g ∈ J (mk v)) ∧
        (∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ J u) ∧
        ∀ ψ : Gw n (mk v).1 → ℂ, Test ψ → (∀ u ∈ J (mk v), ∀ g, ψ (u * g) = ψ g ∧ ψ (g * u) = ψ g) →
        GM.MatchAt σ v c
          (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ))
          (fun g => ψ (mapGL n (completionMap v (mk v).1) g)) ∧
        Test (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ)) ∧
        Test (fun g => ψ (mapGL n (completionMap v (mk v).1) g)) ∧
        (∀ y : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u y ∈ J u) → ∀ g,
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ) (y * g) =
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ) g) ∧
        ∀ y ∈ UF, ∀ g, ψ (mapGL n (completionMap v (mk v).1) (y * g)) = ψ (mapGL n (completionMap v (mk v).1) g)) := by
    intro v
    obtain ⟨o1, o2, ⟨U1, o3⟩, ⟨U2, o4⟩, o5⟩ := hOff F E σ hσ hp n hn v
    by_cases hvS : v ∈ S
    · have hvq : v ≠ q := fun h => hqS (h ▸ hvS)
      by_cases hv : GM.Split E v
      · obtain ⟨U, J, hU, hUle, hJ⟩ := hLev F E σ hσ hp n hn μ V hV v hv
        obtain ⟨s1, s2⟩ := hSt F E σ hσ hp n hn v hv U J fun u => (hJ u).2.1
        obtain ⟨UE, e1, e2, e3⟩ := s2 hU hUle
        obtain ⟨c, hc⟩ := hMa F E σ hσ hp n hn v (mk v) hv U J hU fun u => ⟨(hJ u).1, (hJ u).2.1⟩
        refine ⟨J, fun _ => 1, c, 0, UE, U, fun u => ⟨(hJ u).1, h1 _, ?_⟩, fun x hx => ⟨s1 x hx, rfl⟩, fun _ _ => rfl,
          fun h => absurd hvS h, fun h => absurd h hvq, fun _ => ⟨e2, e3, hU.2, hUle⟩, fun _ h => absurd hv h,
          fun _ _ => ⟨(hJ _).2.1, e1, hc⟩⟩
        rw [(hEig E n μ u.1 _ _ (hJ u).1 (h1 _)).2.1]; exact (hJ u).2.2
      · obtain ⟨J, χ, f, UE, UF, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := hIn F E σ hσ hp n hn μ V hV v hv
        exact ⟨J, χ, 1, f, UE, UF, fun u => ⟨(i1 u).1, (i1 u).2.1, (i1 u).2.2.2⟩, i2, fun h => absurd h hv,
          fun h => absurd hvS h, fun h => absurd h hvq, fun _ => ⟨i6, i7, i8, i9⟩,
          fun _ _ => ⟨fun u => (i1 u).2.2.1, i3, i4, i5, i10, i11⟩, fun _ h => absurd h hv⟩
    · have hs : ∀ u : PlacesOver E v, V ⊓ fixL μ u.1 (GLnLocal.integralGL (u.1.adicCompletion E) n) ≠ ⊥ := fun u =>
        hsph u.1 (by rw [show u.1.under (𝓞 F) = v from hu v u]; exact hvS)
      by_cases hvq : v = q
      · refine ⟨fun u => GLnLocal.iwahori (u.1.adicCompletion E) n, fun _ => 1, 0, 0, U2, GLnLocal.iwahori (v.adicCompletion F) n,
          fun u => ⟨(o5 u.1).2.1, h1 _, ?_⟩, fun x hx => ⟨o2 x hx, rfl⟩, fun _ _ => rfl, fun _ h => absurd hvq h,
          fun _ => ⟨fun _ => rfl, o4, rfl⟩, fun h => absurd h hvS, fun h => absurd h hvS, fun h => absurd h hvS⟩
        rw [(hEig E n μ u.1 _ _ (o5 u.1).2.1 (h1 _)).2.1]
        refine fun h => hs u (eq_bot_iff.2 (h ▸ inf_le_inf_left _ ?_))
        exact biInf_mono fun y hy => Subgroup.map_mono (o5 u.1).2.2 hy
      · refine ⟨fun u => GLnLocal.integralGL (u.1.adicCompletion E) n, fun _ => 1, 0, 0, U1,
          GLnLocal.integralGL (v.adicCompletion F) n, fun u => ⟨(o5 u.1).1, h1 _, ?_⟩, fun x hx => ⟨o1 x hx, rfl⟩,
          fun _ _ => rfl, fun _ _ => ⟨fun _ => ⟨rfl, rfl⟩, o3, rfl⟩, fun h => absurd h hvq,
          fun h => absurd h hvS, fun h => absurd h hvS, fun h => absurd h hvS⟩
        rw [(hEig E n μ u.1 _ _ (o5 u.1).1 (h1 _)).2.1]; exact hs u
  choose J χ c f₀ UE UF k1 k2 k3 k4 k5 k6 k7 k8 using key
  let J' : ∀ w : Pl E, Subgroup (Gw n w) := fun w => J (w.under (𝓞 F)) ⟨w, ⟨rfl⟩⟩
  let χ' : ∀ w : Pl E, Gw n w → ℂ := fun w => χ (w.under (𝓞 F)) ⟨w, ⟨rfl⟩⟩
  have eJ : ∀ v (u : PlacesOver E v), J' u.1 = J v u := by rintro v ⟨w, hw⟩; obtain rfl : w.under (𝓞 F) = v := hu v ⟨w, hw⟩; rfl
  have eχ : ∀ v (u : PlacesOver E v), χ' u.1 = χ v u := by rintro v ⟨w, hw⟩; obtain rfl : w.under (𝓞 F) = v := hu v ⟨w, hw⟩; rfl
  let T : Ty σ n q w₀ :=
    { S := S, q_not := hqS, J := J', χ := χ', mk' := mk
      co := fun w => (k1 _ ⟨w, ⟨rfl⟩⟩).1
      chr := fun w => (k1 _ ⟨w, ⟨rfl⟩⟩).2.1
      off := fun w a b => (k4 _ a b).1 ⟨w, ⟨rfl⟩⟩
      at_q := fun w => (eJ q w).trans ((k5 q rfl).1 w)
      triv := fun v hv w => (eχ v w).trans (k3 v hv w)
      stable := fun v x hx => by simp only [eJ, eχ] at hx ⊢; exact k2 v x hx }
  have hsp : ∀ v, v ∈ T.sp ↔ v ∈ S ∧ GM.Split E v := fun v => Finset.mem_filter
  refine ⟨T, rfl, rfl, hTyp E n μ V hV J' χ' (fun w => ⟨T.co w, T.chr w⟩) ?_ (fun w => (k1 _ ⟨w, ⟨rfl⟩⟩).2.2),
    fun v hv hn u => ?_, c, f₀, UF, fun v hv g => ?_, fun ψ hψ => ?_⟩
  · have hf : {w : Pl E | w.under (𝓞 F) ∈ insert q S}.Finite := by
      refine ((insert q S).finite_toSet.biUnion fun v _ => Set.finite_range fun u : PlacesOver E v => u.1).subset fun w hw => ?_
      exact Set.mem_biUnion hw ⟨⟨w, ⟨rfl⟩⟩, rfl⟩
    refine Filter.mem_of_superset hf.compl_mem_cofinite fun w hw => ?_
    have hw' : w.under (𝓞 F) ∉ insert q S := hw
    rw [Finset.mem_insert, not_or] at hw'
    exact T.off w hw'.2 hw'.1
  · change RankOne μ V u.1 (J' u.1) (χ' u.1)
    rw [eJ, eχ]; exact (k7 v hv hn).1 u
  · change _ ↔ _ ∈ J' (mk v).1
    rw [eJ]; exact (k8 v ((hsp v).1 hv).1 ((hsp v).1 hv).2).1 g
  · have hψ' : ∀ v ∈ S, GM.Split E v → _ := fun v a b => (k8 v a b).2.2 (ψ v) (hψ v ((hsp v).2 ⟨a, b⟩)).1 (by
      have := (hψ v ((hsp v).2 ⟨a, b⟩)).2
      change ∀ u ∈ J' (mk v).1, _ at this
      rw [eJ] at this; exact this)
    let φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ := fun v =>
      if v ∈ S then (if GM.Split E v then GM.prodFn (Function.update
          (fun u : PlacesOver E v => ((J v u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) (ψ v))
        else GM.prodFn fun u : PlacesOver E v => (J v u : Set (Gw n u.1)).indicator fun x => conj (χ v u x))
      else if h : v = q then GM.iwFn (h ▸ w₀) 0 else (unitSet E n v).indicator 1
    let f : ∀ v : Pl F, Gw n v → ℂ := fun v =>
      if v ∈ S then (if GM.Split E v then fun g => ψ v (mapGL n (completionMap v (mk v).1) g) else f₀ v)
      else if v = q then (GM.iwCoset v 0).indicator 1 else (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1
    let L : GM.Loc σ n q w₀ :=
      { S := S, q_not := hqS, unr := hunr, φ := φ, f := f, c := c, UE := UE, UF := UF
        test := fun v hv => by
          by_cases b : GM.Split E v
          · simp only [φ, f, if_pos hv, if_pos b]
            exact ⟨(hψ' v hv b).2.1.1, (hψ' v hv b).2.1.2, (hψ' v hv b).2.2.1.1, (hψ' v hv b).2.2.1.2⟩
          · simp only [φ, f, if_pos hv, if_neg b]
            exact ⟨(k7 v hv b).2.2.1.1, (k7 v hv b).2.2.1.2, (k7 v hv b).2.2.2.1.1, (k7 v hv b).2.2.2.1.2⟩
        lev := k6
        inv := fun v hv => by
          by_cases b : GM.Split E v
          · simp only [φ, f, if_pos hv, if_pos b]
            exact ⟨fun y hy => (hψ' v hv b).2.2.2.1 y (((k8 v hv b).2.1 y).1 hy), (hψ' v hv b).2.2.2.2⟩
          · simp only [φ, f, if_pos hv, if_neg b]
            exact (k7 v hv b).2.2.2.2
        mat := fun v hv => by
          by_cases b : GM.Split E v
          · simp only [φ, f, if_pos hv, if_pos b]
            exact (hψ' v hv b).1
          · simp only [φ, f, if_pos hv, if_neg b]
            exact (k7 v hv b).2.1
        at_q := ⟨by simp only [φ, if_neg hqS, dif_pos], by simp only [f, if_neg hqS, if_pos], (k5 q rfl).2⟩
        off := fun v a b => ⟨by simp only [φ, if_neg a, dif_neg b], by simp only [f, if_neg a, if_neg b], (k4 v a b).2⟩ }
    refine ⟨L, ⟨rfl, hψ, fun v hv => ?_, fun v a b => ?_⟩, fun _ _ => ⟨rfl, rfl⟩, fun v hv => ?_, fun v a b => ?_⟩
    · obtain ⟨a, b⟩ := (hsp v).1 hv
      change φ v = GM.prodFn (Function.update (fun u : PlacesOver E v => ((J' u.1 : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ))
        (mk v) (ψ v)) ∧ ∀ g, g ∈ UE v ↔ ∀ u, GM.cmp u g ∈ J' u.1
      simp only [eJ, φ, if_pos a, if_pos b, true_and]
      exact (k8 v a b).2.1
    · change φ v = GM.prodFn fun u : PlacesOver E v => (J' u.1 : Set (Gw n u.1)).indicator fun x => conj (χ' u.1 x)
      have a' : v ∈ S := a
      simp only [eJ, eχ, φ, if_pos a', if_neg b]
    · obtain ⟨a, b⟩ := (hsp v).1 hv
      change f v = _
      simp only [f, if_pos a, if_pos b]
      rfl
    · change f v = _
      simp only [f, if_pos a, if_neg b]

end UpperTheory.ConvolutionTheory.T
end
end

section
open MeasureTheory NumberField IsDedekindDomain ValuativeRel GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.Loc UpperTheory.V.Z.Tf.L4

private theorem ball_sub_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (N : Set (GL (Fin n) k)) (hN : N ∈ nhds (1 : GL (Fin n) k)) :
    ∃ ρ : ValueGroupWithZero k, 0 < ρ ∧ ball n ρ ⊆ N := by
  obtain ⟨d, -, h⟩ := GlobalTheory.GamMul.NearOne.one_add_small_near_one k n N hN
  refine ⟨valuation k (d : k), ?_, fun g hg => ?_⟩
  · exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 d.ne_zero)
  · obtain ⟨A, hA, hAN, -⟩ := h ((g : Matrix (Fin n) (Fin n) k) - 1) (fun i j => hg i j)
    have e : A = g := Units.ext (by rw [hA]; simp)
    exact e ▸ hAN

private theorem local_type (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (s : E ≃ₐ[k] E)
    (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) E) W) (hs : IsSmooth π)
    (hi : π.IsIrreducible) (hg : GlobalTheory.LocGL.IsGeneric π) (N : Set (GL (Fin n) E)) (hN : N ∈ nhds (1 : GL (Fin n) E)) :
    ∃ (J : Subgroup (GL (Fin n) E)) (χ : GL (Fin n) E → ℂ) (e : W), CO J ∧ IsChr J χ ∧ (J : Set (GL (Fin n) E)) ⊆ N ∧
      e ≠ 0 ∧ (∀ g ∈ J, π g e = χ g • e) ∧ (∀ x : W, (∀ g ∈ J, π g x = χ g • x) → ∃ c : ℂ, x = c • e) ∧
      ∀ y ∈ J, Matrix.GeneralLinearGroup.map (s : E →+* E) y ∈ J ∧
        χ (Matrix.GeneralLinearGroup.map (s : E →+* E) y) = χ y := by
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E := by
    obtain ⟨x, hx⟩ := valuation_surjective (K := E) (uniformizer E)
    exact ⟨Units.mk0 x fun h => uniformizer_ne_zero (R := E) (by rw [← hx, h, map_zero]), hx⟩
  obtain ⟨ρ, hρ, hρN⟩ := ball_sub_nhds E n N hN
  obtain ⟨c, hc⟩ := psiInv k E ϖ hϖ
  obtain ⟨a₁, h₁⟩ := howeLine E n W π hs hi hg ϖ hϖ c
  obtain ⟨a₂, h₂⟩ := howeBall E n ϖ hϖ c ρ hρ
  obtain ⟨a, ha, ψ, hψ, hinv⟩ := hc (max 1 (max a₁ a₂))
  have ha1 : 1 ≤ a := le_trans (le_max_left _ _) ha
  obtain ⟨J, hJ, ho, hk⟩ := howeGroup E n ϖ hϖ a c ha1
  obtain ⟨hlc, hmul⟩ := howeChar E n ϖ hϖ a c ha1 ψ hψ
  have hmem : ∀ x, x ∈ J ↔ x ∈ howeSet n ϖ a c := fun x => by rw [← hJ]; rfl
  have hline := h₁ a (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ha) ψ hψ
  obtain ⟨⟨e, he⟩, he0, hspan⟩ := finrank_eq_one_iff'.1 hline
  refine ⟨J, fun x => (ψ (GlobalTheory.Whittaker.superDiag x) : ℂ), e, ⟨hk, ho⟩, ⟨hlc, fun x _ => Circle.norm_coe _, fun x hx y hy => ?_⟩, ?_,
    fun h => he0 (Subtype.ext h), fun g hgJ => he g ((hmem g).1 hgJ), fun x hx => ?_, fun y hy => ?_⟩
  · beta_reduce
    rw [hmul x ((hmem x).1 hx) y ((hmem y).1 hy), Circle.coe_mul]
  · rw [hJ]
    exact (h₂ a (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ha)).trans hρN
  · obtain ⟨t, ht⟩ := hspan ⟨x, fun g hg => hx g ((hmem g).2 hg)⟩
    exact ⟨t, (congrArg Subtype.val ht).symm⟩
  · have hy' := (hmem y).1 hy
    have hent : ∀ i j, ((Matrix.GeneralLinearGroup.map (s : E →+* E) y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
        s ((y : Matrix (Fin n) (Fin n) E) i j) := fun _ _ => rfl
    refine ⟨(hmem _).2 fun i j => ?_, ?_⟩
    · have e1 : ((Matrix.GeneralLinearGroup.map (s : E →+* E) y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j -
          (1 : Matrix (Fin n) (Fin n) E) i j = s ((y : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
        rw [hent, map_sub, Matrix.one_apply, apply_ite s, map_one, map_zero]
      rw [e1, galIsom k E]
      exact hy' i j
    · have hsd : GlobalTheory.Whittaker.superDiag (Matrix.GeneralLinearGroup.map (s : E →+* E) y) = s (GlobalTheory.Whittaker.superDiag y) := by
        simp only [GlobalTheory.Whittaker.superDiag, map_sum, hent]
      change ((ψ (GlobalTheory.Whittaker.superDiag (Matrix.GeneralLinearGroup.map (s : E →+* E) y)) : Circle) : ℂ) = _
      rw [hsd, hinv]

theorem UpperTheory.ConvolutionTheory.T.howeType :
    UpperTheory.ConvolutionTheory.T.HoweType := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ μ _ V hV v w hw N hN
  obtain ⟨iA, iV, iFD, iG, s, -, -, -, hgal, -⟩ := UpperTheory.V.Z.Tf.Orb.placeData F E σ hσ v w hw
  haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
  obtain ⟨π, hπ, -⟩ := UpperTheory.ConvolutionTheory.Dp.exCusp E n μ V hV
  obtain ⟨hl, -, -, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop (w.1.adicCompletion E) n
  letI : MeasurableSpace (Gw n w.1) := borel _
  haveI : BorelSpace (Gw n w.1) := ⟨rfl⟩
  obtain ⟨⟨τ, hτ⟩, -, -⟩ := occursBasics E n μ V w.1 MeasureTheory.Measure.haar hV
  have hloc : (UpperTheory.CBC.Cusp.cx π).locComp w.1 τ :=
    (UpperTheory.ConvolutionTheory.Dp.locIff E n μ π V hπ w.1 τ).2 ((occursIff E n μ V hV w.1 τ).1 hτ)
  have hgen : GlobalTheory.LocGL.IsGeneric τ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E n π w.1 τ hloc
  obtain ⟨J, χ, e, hCO, hchr, hJN, he0, heJ, hline, hst⟩ :=
    local_type (v.adicCompletion F) (w.1.adicCompletion E) s n τ.V τ.ρ τ.smooth τ.irred hgen N hN
  have hrank := lineRank E n μ V hV w.1 τ hτ J χ hCO hchr ⟨e, hline⟩
  obtain ⟨f, hf0, hfV, hfe⟩ := hτ
  have hinj : Function.Injective f := by
    let K : Subrepresentation τ.ρ := ⟨LinearMap.ker f, fun g x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hfe, hx, map_zero]⟩
    haveI := τ.irred
    rcases eq_bot_or_eq_top K with h | h
    · refine LinearMap.ker_eq_bot.1 ?_
      exact congrArg Subrepresentation.toSubmodule h
    · exfalso
      apply hf0
      have h' : LinearMap.ker f = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.ker_eq_top.1 h'
  refine ⟨J, χ, hCO, hchr, hJN, hrank, fun h => ?_, fun x hx => ?_⟩
  · have hm : f e ∈ V ⊓ eigL μ w.1 J χ := by
      refine ⟨hfV e, ?_⟩
      simp only [eigL, SetLike.mem_coe, Submodule.mem_iInf]
      intro x hx
      change rhoL μ w.1 x (f e) = χ x • f e
      rw [← hfe, heJ x hx, map_smul]
    rw [h, Submodule.mem_bot] at hm
    exact he0 (hinj (by rw [hm, map_zero]))
  · have hcm : UpperTheory.ConvolutionTheory.GM.cmp w (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.galFin σ v) x) =
        Matrix.GeneralLinearGroup.map (s : w.1.adicCompletion E →+* w.1.adicCompletion E) (UpperTheory.ConvolutionTheory.GM.cmp w x) :=
      Units.ext (Matrix.ext fun i j => hgal _)
    rw [hcm]
    exact hst _ hx
end

section
open MeasureTheory NumberField IsDedekindDomain ValuativeRel Filter
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.Loc GlobalTheory.SplitWeil
open Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped ComplexConjugate

private theorem lc_ind {G : Type} [TopologicalSpace G] {U : Set G} (hU : IsClopen U) {h : G → ℂ}
    (hh : IsLocallyConstant h) : IsLocallyConstant (U.indicator h) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  by_cases hx : x ∈ U
  · filter_upwards [hU.isOpen.mem_nhds hx, hh.eventually_eq x] with y hy e
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, e]
  · filter_upwards [hU.compl.isOpen.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

private theorem td_gl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    TotallyDisconnectedSpace (GL (Fin n) k) := by
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

private theorem cmp_homeo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) {v : HeightOneSpectrum (𝓞 F)}
    (w : PlacesOver E v) (hw : ∀ w' : PlacesOver E v, w' = w) :
    ∃ e : GL (Fin n) (CompletionsOver E v) ≃ₜ GL (Fin n) (w.1.adicCompletion E), ∀ g, e g = UpperTheory.ConvolutionTheory.GM.cmp w g := by
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  let r : CompletionsOver E v ≃+* w.1.adicCompletion E :=
    RingEquiv.piUnique (fun u : PlacesOver E v => u.1.adicCompletion E)
  have hr : Continuous r := continuous_apply _
  have hs : Continuous r.symm :=
    (Homeomorph.piUnique (fun u : PlacesOver E v => u.1.adicCompletion E)).symm.continuous
  refine ⟨{ toEquiv := (Units.mapEquiv (RingEquiv.mapMatrix (m := Fin n) r).toMulEquiv).toEquiv
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun g => ?_⟩
  · exact Continuous.units_map _ (continuous_id.matrix_map hr)
  · exact Continuous.units_map _ (continuous_id.matrix_map hs)
  · exact Units.ext (Matrix.ext fun i j => rfl)

theorem UpperTheory.ConvolutionTheory.T.inertData :
    UpperTheory.ConvolutionTheory.T.InertData := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV v hns
  obtain ⟨-, -, hne, huniq, -, -⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨w⟩ := hne v
  have hw : ∀ w' : PlacesOver E v, w' = w := huniq v hns w
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  obtain ⟨ρ, hρ, hdown⟩ := UpperTheory.ConvolutionTheory.Loc.atDown F E σ hσ v w hw n
  have hN : ball n ρ ∈ nhds (1 : Gw n w.1) :=
    (UpperTheory.ConvolutionTheory.Loc.BallG.isOpen_ball hρ.ne').mem_nhds (fun i j => by simp)
  obtain ⟨J, χ, hCO, hchr, hJN, hrank, hne0, hst⟩ := UpperTheory.ConvolutionTheory.T.howeType F E σ hσ hp n hn μ V hV v w hw _ hN
  haveI : T2Space (Gw n w.1) := (UpperTheory.V.Z.Tf.Orb.gLTop (w.1.adicCompletion E) n).2.2.1
  haveI : T2Space (Gw n v) := (UpperTheory.V.Z.Tf.Orb.gLTop (v.adicCompletion F) n).2.2.1
  have hJc : IsClopen (J : Set (Gw n w.1)) := ⟨hCO.1.isClosed, hCO.2⟩
  let φ : Gw n w.1 → ℂ := (J : Set (Gw n w.1)).indicator fun x => conj (χ x)
  have hφl : IsLocallyConstant φ := lc_ind hJc (hchr.1.comp fun z => conj z)
  have hφc : HasCompactSupport φ := HasCompactSupport.intro hCO.1 fun x hx => Set.indicator_of_notMem hx _
  have hφS : φ ∈ SB (GL (Fin n) (w.1.adicCompletion E)) := ⟨hφl, hφc⟩
  have hsupp : Function.support φ ⊆ ball n ρ := fun x hx => hJN (Set.mem_of_indicator_ne_zero hx)
  obtain ⟨f, hfS, hmatch⟩ := hdown φ hφS hsupp
  obtain ⟨e, he⟩ := cmp_homeo (F := F) n w hw
  have hec : (fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g)) = φ ∘ e := funext fun g => by simp [he]
  have hTE : Test (fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g)) := by
    rw [hec]
    exact ⟨hφl.comp_continuous e.continuous, hφc.comp_homeomorph e⟩
  have hTF : Test f := hfS
  obtain ⟨U₁, hU₁o, hU₁K, hU₁⟩ := UpperTheory.ConvolutionTheory.Loc.sbInv (Gw n w.1) φ hφS (GLnLocal.integralGL (w.1.adicCompletion E) n)
    (GLnLocal.isOpen_integralGL _ _) (GLnLocal.isCompact_integralGL _ _) (td_gl _ n)
  obtain ⟨U₂, hU₂o, hU₂K, hU₂⟩ := UpperTheory.ConvolutionTheory.Loc.sbInv (Gw n v) f hfS (GLnLocal.integralGL (v.adicCompletion F) n)
    (GLnLocal.isOpen_integralGL _ _) (GLnLocal.isCompact_integralGL _ _) (td_gl _ n)
  let J' : ∀ u : PlacesOver E v, Subgroup (Gw n u.1) := fun u => (hw u).symm ▸ J
  let χ' : ∀ u : PlacesOver E v, Gw n u.1 → ℂ := fun u => (hw u).symm ▸ χ
  have all : ∀ P : PlacesOver E v → Prop, P w → ∀ u, P u := fun P h u => (hw u).symm ▸ h
  have hprod : (UpperTheory.ConvolutionTheory.GM.prodFn fun u : PlacesOver E v => (J' u : Set (Gw n u.1)).indicator fun x => conj (χ' u x)) =
      fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g) := funext fun g => by
    unfold UpperTheory.ConvolutionTheory.GM.prodFn
    exact finprod_unique (fun u : PlacesOver E v =>
      (J' u : Set (Gw n u.1)).indicator (fun x => conj (χ' u x)) (UpperTheory.ConvolutionTheory.GM.cmp u g))
  refine ⟨J', χ', f, U₁.comap (UpperTheory.ConvolutionTheory.GM.cmp w), U₂, ?_, ?_, by rw [hprod]; exact hmatch, by rw [hprod]; exact hTE, hTF, ?_, ?_, hU₂o, hU₂K, ?_, ?_⟩
  · exact all _ ⟨hCO, hchr, hrank, hne0⟩
  · intro x hx
    have hxw : UpperTheory.ConvolutionTheory.GM.cmp w x ∈ J := hx w
    obtain ⟨h1, h2⟩ := hst x hxw
    refine ⟨all _ h1, ?_⟩
    rw [finprod_unique, finprod_unique]
    exact h2
  · have : (UpperTheory.ConvolutionTheory.GM.cmp w : GL (Fin n) (CompletionsOver E v) → Gw n w.1) = e := funext fun g => (he g).symm
    change IsOpen ((UpperTheory.ConvolutionTheory.GM.cmp w : GL (Fin n) (CompletionsOver E v) → Gw n w.1) ⁻¹' (U₁ : Set (Gw n w.1)))
    rw [this]
    exact hU₁o.preimage e.continuous
  · intro g hg u
    have hu := hw u
    subst hu
    exact hU₁K hg
  · intro y hy g
    rw [hprod]
    change φ (UpperTheory.ConvolutionTheory.GM.cmp w (y * g)) = φ (UpperTheory.ConvolutionTheory.GM.cmp w g)
    rw [map_mul]
    exact (hU₁ _ hy _).1
  · intro y hy g
    exact (hU₂ y hy g).1
end

section
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T in
theorem UpperTheory.ConvolutionTheory.T.tyEx :
    UpperTheory.ConvolutionTheory.T.TyEx :=
  tyEx_of splitLev splitStable splitMatch inertData offStable L1.typedEx L1.eigBasic
end

section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical

private theorem fd_fixed {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    (m : Measure G) (ρ : Representation ℂ G V) (J : Subgroup G) (hJ : MeasurableSet (J : Set G))
    (h1 : m (J : Set G) = 1) (A : V →ₗ[ℂ] V) (hA : IsIntegralOp m ρ ((J : Set G).indicator 1) A)
    (hf : FiniteDimensional ℂ (LinearMap.range A)) : FiniteDimensional ℂ (fixedVectors ρ J) := by
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range A) fun x hx => ?_
  have hAx : A x = x := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, (hA x l).2, sub_eq_zero]
    have e : (fun g => ((J : Set G).indicator (1 : G → ℂ)) g * l (ρ g x)) =
        (J : Set G).indicator fun _ => l x := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · have hgx : ρ g x = x := hx g hg
        simp [Set.indicator_of_mem hg, hgx]
      · simp [Set.indicator_of_notMem hg]
    rw [e, integral_indicator hJ]
    simp [Measure.real, h1]
  exact ⟨x, hAx⟩

private theorem under_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

theorem UpperTheory.ConvolutionTheory.T.termE :
    UpperTheory.ConvolutionTheory.T.TermE := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn m hm μ _ θ hθ D s hs hsl νE _ νF _ b a aE aF hAS q w₀ hq T V hV hVθ hR hne _ _ mm hmm
    τ hocc ν hν
  obtain ⟨y, hy, hY⟩ := (UpperTheory.ConvolutionTheory.L1.twistY F E σ hσ m n hm hn μ θ hθ D s hs hsl νE νF b a aE aF hAS q w₀ hq T V hV hVθ hR).1 hne
  have hJ : T.J w₀.1 = GLnLocal.iwahori (w₀.1.adicCompletion E) n := T.at_q w₀
  have hcoI : CO (GLnLocal.iwahori (w₀.1.adicCompletion E) n) := hJ ▸ T.co w₀.1
  haveI := hmm w₀.1
  have h0 : mm w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)) ≠ 0 :=
    hcoI.2.measure_ne_zero _ ⟨1, one_mem _⟩
  have hT : mm w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)) ≠ ⊤ :=
    hcoI.1.measure_lt_top.ne
  obtain ⟨m₀, hm₀, hm₀1⟩ : ∃ m₀ : Measure (Gw n w₀.1), m₀.IsHaarMeasure ∧
      m₀ (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)) = 1 := by
    refine ⟨(mm w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)))⁻¹ • mm w₀.1,
      Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 hT) (ENNReal.inv_ne_top.2 h0), ?_⟩
    simp [ENNReal.inv_mul_cancel h0 hT]
  haveI := hm₀
  have hmm' : ∀ u, (Function.update mm w₀.1 m₀ u).IsHaarMeasure := by
    intro u
    by_cases h : u = w₀.1
    · subst h
      simpa using hm₀
    · simpa [Function.update_of_ne h] using hmm u
  obtain ⟨c, hc, hmain⟩ := UpperTheory.ConvolutionTheory.C.termE F E σ hσ m n hm hn μ θ hθ D s hs hsl νE νF b a aE aF hAS
    (Function.update mm w₀.1 m₀) hmm' q w₀ hq T V hV hVθ hR (τ w₀.1) (fun v => τ (T.mk' v).1) (hocc _) (fun v _ => hocc _) y hy
  have hYZ : T.Y μ V (fun i => OComponent μ (s i) (hs i) νF a) y ≤ T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y := by
    unfold Ty.Y Ty.Z Ty.typed
    exact inf_le_inf_left _ (le_iInf₂ fun w _ => iInf_le _ w)
  have hZne : T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y ≠ ⊥ := fun h => hY (le_bot_iff.1 (h ▸ hYZ))
  have hfix : V ⊓ fixL μ w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n) ≠ ⊥ := by
    intro h
    refine hY (le_bot_iff.1 (h ▸ le_inf ?_ ?_))
    · exact inf_le_left.trans inf_le_left
    · have heig := (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w₀.1 (T.J w₀.1) (T.χ w₀.1) (T.co _) (T.chr _)).2.1
      have hχ : T.χ w₀.1 = 1 := T.triv q hq w₀
      rw [← hJ, ← heig, ← hχ]
      exact inf_le_right.trans (iInf_le _ w₀.1)
  obtain ⟨hfx, -, -, s₀, -, A, hA, hfin, -⟩ :=
    UpperTheory.ConvolutionTheory.T.unitTrace E n μ V hV w₀.1 m₀ hm₀ (τ w₀.1) _ (hocc _) hcoI hfix
  have fd := fd_fixed m₀ (τ w₀.1).ρ _ hcoI.2.measurableSet hm₀1 A hA hfin
  obtain ⟨Z, hZ0, hcard, hZ⟩ := UpperTheory.ConvolutionTheory.C.iwPow E n w₀.1 m₀ hm₀1 (τ w₀.1) ν hν fd
  refine ⟨y ^ (m + 1), c, Z, pow_pos hy _, hc hZne, ?_, hZ0, ?_⟩
  · rintro rfl
    exact hfx (Submodule.finrank_eq_zero.1 (by simpa using hcard.symm))
  · intro L ψ hF l 𝔢 hS sv hsv j
    refine hmain L ψ hF ν l 𝔢 hν hS j _ sv ?_ ?_
    · rw [Function.update_self]
      exact hZ j
    · intro v hv
      have hne' : (T.mk' v).1 ≠ w₀.1 := by
        intro h
        have hvq : v = q := by rw [← under_eq (T.mk' v), h, under_eq w₀]
        exact T.q_not (hvq ▸ (Finset.mem_filter.1 hv).1)
      rw [Function.update_of_ne hne']
      exact hsv v hv
end

section
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T in
theorem UpperTheory.ConvolutionTheory.T.coreDesc :
    UpperTheory.ConvolutionTheory.CI → UpperTheory.ConvolutionTheory.GM.GM → UpperTheory.ConvolutionTheory.T.CoreDesc :=
  coreDesc_of absLast pullBack unitTrace oneTerm sideSum pickS pickInf tyEx termE goodEx places C.occursBasics L1.eigBasic
end
