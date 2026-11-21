import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.Ext4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.UpdateMulSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.ContinuousEntCSymm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.ExpInjInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.MinSwap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.RankInf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LineVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LineInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LineEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchSlotEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PositionOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.AmpGrp
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitLev
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitMatch
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStableAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.T2SpaceGlCompletionsOver
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.GalLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.OffStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.TensAmp
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistPerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.FiniteAdeleInclusionInjective
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExSummand
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.NormIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfIff
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.SwapAt
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FamParts
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.AtInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LineEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LintegralInvUniqueHaar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ProjEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.InfSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PairPosition
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.AmpSlot
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.GoodEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistExAlt

section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private theorem idemTr (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι)
    (μ : Measure U4) (e : ι → U4 → ℂ) (hμ : Haar4 μ)
    (h : Idem (Measure.pi fun _ : ι => μ) fun k => ∏ i, e i (k i)) : IdemA (C.κ₄ μ) (C.e e) := by
  refine ⟨(coLaws K ι C).2.1 μ hμ, h.cont.comp (C.Φ (2 + 2)).continuous, fun k => ?_, fun k => ?_⟩
  · have := h.star (C.Φ (2 + 2) k)
    rw [← map_inv] at this
    exact this
  · have := h.idem (C.Φ (2 + 2) k)
    have hm := integral_map_equiv (μ := Measure.pi fun _ : ι => μ) (C.Φ (2 + 2)).symm.toHomeomorph.toMeasurableEquiv
      (fun h => C.e e h * C.e e (h⁻¹ * k))
    refine Eq.trans hm (Eq.trans ?_ this)
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    change C.e e ((C.Φ (2 + 2)).symm a) * C.e e (((C.Φ (2 + 2)).symm a)⁻¹ * k) = _
    simp only [Co.e, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.archEx :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.ArchEx := by
  intro F E _ _ _ _ _ _ _ _ σ _ _ τ₁ τ₂ θ hP hθ h12 h21 D
  obtain ⟨CF, CE, hC⟩ := coEx F E σ D
  obtain ⟨μ, hμ, hpos⟩ := u4.2.2.2.2.2.2.2.2.2.2.2.2
  have c₁ : CuspIrr (BW.mu1 E 2) τ₁ := hP.1
  have c₂ : CuspIrr (BW.mu1 E 2) τ₂ := hP.2
  choose n q hn using fun u : InfinitePlace F => minEx E _ CE _ τ₁ c₁ (0, u)
  choose n' q' hn' using fun u : InfinitePlace F => minEx E _ CE _ τ₂ c₂ (0, u)
  choose e4 he he' using fun u : InfinitePlace F => ext4 μ hμ hpos (n u) (q u) (n' u) (q' u)
  let N : Fin 2 × InfinitePlace F → ℕ := fun i => ![n i.2, n' i.2] i.1
  let Q : Fin 2 × InfinitePlace F → ℤ := fun i => ![q i.2, q' i.2] i.1
  let N' : Fin 2 × InfinitePlace F → ℕ := fun i => ![n' i.2, n i.2] i.1
  let Q' : Fin 2 × InfinitePlace F → ℤ := fun i => ![q' i.2, q i.2] i.1
  let x : Fin 2 × InfinitePlace F → U4 := fun i => ![1, w4] i.1
  have hE : ExtP μ (fun i : Fin 2 × InfinitePlace F => e4 i.2) N Q N' Q' x := by
    refine extPi _ μ _ N Q N' Q' x hμ ?_
    rintro ⟨s, u⟩
    fin_cases s
    · exact he u
    · exact he' u
  have hF : ExtP μ e4 n q n' q' (fun _ => 1) := extPi _ μ _ n q n' q' _ hμ he
  have m₁ : ∀ i, CE.MinAt (BW.mu1 E 2) τ₁ i (N i) (Q i) := by
    rintro ⟨s, u⟩
    fin_cases s
    · exact hn u
    · exact minSwap F E σ D CF CE hC _ θ hθ τ₂ τ₁ h21 0 u _ _ (hn' u)
  have m₂ : ∀ i, CE.MinAt (BW.mu1 E 2) τ₂ i (N' i) (Q' i) := by
    rintro ⟨s, u⟩
    fin_cases s
    · exact hn' u
    · exact minSwap F E σ D CF CE hC _ θ hθ τ₁ τ₂ h12 0 u _ _ (hn u)
  have hv := lineVal E _ CE _ τ₁ τ₂ hP μ _ N Q N' Q' x hμ hE
  refine ⟨CF.κ₄ μ, CF.e e4, CE.κ₄ μ, CE.e (fun i => e4 i.2), CE.κ₂, CE.p N Q, CE.p N' Q', (CE.Φ (2 + 2)).symm x,
    idemTr F _ CF μ e4 hμ hF.idem, ?_, hv.1, rankInf E _ CE _ τ₁ c₁ N Q fun i => (m₁ i).1,
    rankInf E _ CE _ τ₂ c₂ N' Q' fun i => (m₂ i).1, hv.2,
    lineInj E _ CE _ τ₁ τ₂ hP μ _ N Q N' Q' x hμ hE m₁ m₂,
    lineEx E _ CE _ τ₁ τ₂ hP μ _ N Q N' Q' x hμ hE (fun i => (m₁ i).1) fun i => (m₂ i).1⟩
  intro k kk hk
  simp only [Co.e]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun u _ => ?_
  congr 1
  apply Subtype.ext
  rw [CE.Φ_val, CF.Φ_val, hC, hk]
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical ContDiff Manifold

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.Amp

private theorem ec_smooth {K : Type} [Field K] [NumberField K] {n : ℕ} (κ : Measure (archCompact K n)) [IsProbabilityMeasure κ]
    {e : archCompact K n → ℂ} (he : Continuous e) {f : archGroup K n → ℂ} (hf : (isExpLieAlgebra K n).IsSmoothFun f)
    (hk : ∀ (k : archCompact K n) g, f ((k : archGroup K n)⁻¹ * g) = f (g * (k : archGroup K n)⁻¹)) :
    (isExpLieAlgebra K n).IsSmoothFun (ec κ e f) := by
  set h := isExpLieAlgebra K n
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro g
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hfg : ContMDiff 𝓘(ℝ, archLie K n) 𝓘(ℝ, ℂ) ∞ (fun x : archGroup K n => f (g * x)) :=
    ContMDiff.comp (I' := 𝓘(ℝ, archLie K n)) hf (contMDiff_const.mul contMDiff_id)
  set Φ : archLie K n → archGroup K n → ℂ := fun Y y => f (g * h.expG Y * y) with hΦdef
  have hΦ : ∀ y₀ : archGroup K n, ContDiff ℝ ∞ (fun q : archLie K n × archLie K n => Φ q.1 (y₀ * h.expG q.2)) := fun y₀ => by
    simpa [hΦdef, mul_assoc] using h.contDiff_comp_expG_mul_expG hfg contDiff_fst y₀ contDiff_snd
  have hΦY : ∀ y, ContDiff ℝ ∞ (fun Y => Φ Y y) := fun y => by
    simpa [hΦdef, mul_assoc] using h.contDiff_comp_expG_mul_expG hfg contDiff_id y (contDiff_const (c := (0 : archLie K n)))
  have e1 : (fun Y : archLie K n => ec κ e f (g * h.expG Y)) = fun Y => ∫ k : archCompact K n, e k * Φ Y (k : archGroup K n)⁻¹ ∂κ := by
    funext Y
    simp only [ec, hk, hΦdef]
  rw [e1]
  have hD : ∀ (j : ℕ) (Y : archLie K n) (k : archCompact K n),
      iteratedFDeriv ℝ j (fun Y => e k * Φ Y (k : archGroup K n)⁻¹) Y =
        e k • iteratedFDeriv ℝ j (fun Y => Φ Y (k : archGroup K n)⁻¹) Y := by
    intro j Y k
    have e2 : (fun Y => e k * Φ Y (k : archGroup K n)⁻¹) = e k • fun Y => Φ Y (k : archGroup K n)⁻¹ := by
      funext Y; simp [smul_eq_mul]
    rw [e2, iteratedFDeriv_const_smul_apply ((hΦY _).contDiffAt.of_le (by exact_mod_cast le_top))]
  refine contDiff_integral_of_iteratedFDeriv (μ := κ) (fun Y (k : archCompact K n) => e k * Φ Y (k : archGroup K n)⁻¹)
    (fun k => contDiff_const.mul (hΦY _)) (fun j => ?_) (fun Y₀ => ⟨Set.univ, Filter.univ_mem, Set.univ, isCompact_univ, fun Y _ k hy => (hy (Set.mem_univ _)).elim⟩)
  have hc := h.continuous_iteratedFDeriv_param Φ hΦ j
  have hc' : Continuous fun q : archLie K n × archCompact K n => iteratedFDeriv ℝ j (fun Y => Φ Y (q.2 : archGroup K n)⁻¹) q.1 :=
    hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd).inv)
  exact ((he.comp continuous_snd).smul hc').congr fun q => (hD j q.1 q.2).symm

private theorem sc_norm {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] {K : Subgroup G} (κ : Measure K) (e : K → ℂ)
    (ν : Measure G) (ρ : G → ℝ) :
    ∃ t : ℝ, 0 < t ∧ ∫ g, ‖ec κ e (fun x => ((t * ρ x : ℝ) : ℂ)) g‖ ∂ν ≤ 1 := by
  have hI : 0 ≤ ∫ g, ‖ec κ e (fun x => (ρ x : ℂ)) g‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  refine ⟨1 / (1 + ∫ g, ‖ec κ e (fun x => (ρ x : ℂ)) g‖ ∂ν), by positivity, ?_⟩
  have e1 : ∀ (t : ℝ), 0 < t → ∀ g, ‖ec κ e (fun x => ((t * ρ x : ℝ) : ℂ)) g‖ = t * ‖ec κ e (fun x => (ρ x : ℂ)) g‖ := fun t ht g => by
    have h1 : ec κ e (fun x => ((t * ρ x : ℝ) : ℂ)) g = (t : ℂ) * ec κ e (fun x => (ρ x : ℂ)) g := by
      simp only [ec, Complex.ofReal_mul, mul_left_comm _ (t : ℂ), integral_const_mul]
    rw [h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
  simp only [e1 _ (by positivity : 0 < 1 / (1 + ∫ g, ‖ec κ e (fun x => (ρ x : ℂ)) g‖ ∂ν)), integral_const_mul]
  rw [one_div, inv_mul_le_iff₀ (by positivity)]
  linarith

private theorem sc_smooth {K : Type} [Field K] [NumberField K] {n : ℕ} {ρ : archGroup K n → ℝ}
    (hρ : (isExpLieAlgebra K n).IsTestFunction fun a => (ρ a : ℂ)) (t : ℝ) :
    (isExpLieAlgebra K n).IsSmoothFun fun x => ((t * ρ x : ℝ) : ℂ) := by
  have e1 : (fun x => ((t * ρ x : ℝ) : ℂ)) = fun y => (t : ℂ) * (ρ y : ℂ) := by
    funext x
    push_cast
    rfl
  rw [e1]
  exact (hρ.const_mul (t : ℂ)).1

private theorem leftFin_of {K : Type} [Field K] [NumberField K] {n : ℕ} {b : TI K n} {f : archGroup K n → ℂ} (h : ∀ g, b g = f g)
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : archCompact K n => fun g : archGroup K n => f ((k : archGroup K n) * g)))) :
    LeftFin b := by
  have e1 : (⇑b : archGroup K n → ℂ) = f := funext h
  unfold LeftFin
  rw [e1]
  exact hf

private theorem smoothT_of {K : Type} [Field K] [NumberField K] {n : ℕ} {b : TI K n} {f : archGroup K n → ℂ} (h : ∀ g, b g = f g)
    (hf : (isExpLieAlgebra K n).IsSmoothFun f) : SmoothT b := by
  have e1 : (⇑b : archGroup K n → ℂ) = f := funext h
  unfold SmoothT
  rw [show (fun g => b g) = f from e1]
  exact hf

private theorem exTI {K : Type} [Field K] [NumberField K] {n : ℕ} {f : archGroup K n → ℂ} (hc : Continuous f) (hs : HasCompactSupport f) :
    ∃ b : TI K n, ∀ g, b g = f g :=
  ⟨⟨⟨f, hc⟩, hs⟩, fun _ => rfl⟩

private theorem exB {K : Type} [Field K] [NumberField K] {n : ℕ} {κ : Measure (archCompact K n)} {e : archCompact K n → ℂ}
    (h : IdemA κ e) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] {N : Set (archGroup K n)} (hN : N ∈ 𝓝 (1 : archGroup K n)) :
    ∃ (β : archGroup K n → ℝ) (b : TI K n), Continuous β ∧ HasCompactSupport β ∧ (∀ x, 0 ≤ β x) ∧ (∃ x, β x ≠ 0) ∧
      (∀ x, β x ≠ 0 → x ∈ N) ∧ (∀ g, b g = ec κ e (fun x => (β x : ℂ)) g) ∧ SmoothT b ∧ LeftFin b ∧ ∫ g, ‖b g‖ ∂ν ≤ 1 := by
  haveI := h.haar.prob
  haveI : κ.IsMulLeftInvariant := ⟨fun k => (h.haar.left k).map_eq⟩
  obtain ⟨ρ, hρ0, hρt, hρ1, -, hρc, hρN, -⟩ := exists_archBump ν hN
  have hρcont : Continuous ρ := Complex.continuous_re.comp hρt.continuous
  have hρcs : HasCompactSupport ρ := hρt.2.comp_left (g := Complex.re) rfl
  obtain ⟨t, ht, hn⟩ := sc_norm κ e ν ρ
  have hβc : Continuous fun x => t * ρ x := continuous_const.mul hρcont
  have hβs : HasCompactSupport fun x => t * ρ x := hρcs.mul_left
  have hβc' : Continuous fun x => ((t * ρ x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hβc
  have hβs' : HasCompactSupport fun x => ((t * ρ x : ℝ) : ℂ) := hβs.comp_left Complex.ofReal_zero
  obtain ⟨b, hb⟩ := exTI (ec_cont κ h.cont hβc') (ec_cs κ e hβs')
  refine ⟨fun x => t * ρ x, b, hβc, hβs, fun x => mul_nonneg ht.le (hρ0 x), ?_, fun x hx => hρN x (right_ne_zero_of_mul hx), hb,
    smoothT_of hb (ec_smooth κ h.cont (sc_smooth hρt t) fun k g => ?_), leftFin_of hb (ec_fin κ h.cont h.idem hβc'), ?_⟩
  · by_contra h0
    push Not at h0
    have h2 : ∀ x, ρ x = 0 := fun x => (mul_eq_zero.1 (h0 x)).resolve_left ht.ne'
    simp [h2] at hρ1
  · have h3 := hρc (k : archGroup K n)⁻¹ (inv_mem k.2) (g * (k : archGroup K n)⁻¹)
    have h4 : (k : archGroup K n)⁻¹ * (g * (k : archGroup K n)⁻¹) * ((k : archGroup K n)⁻¹)⁻¹ = (k : archGroup K n)⁻¹ * g := by group
    rw [h4] at h3
    simp only [h3]
  · simpa only [hb] using hn

private theorem int_surj_pi {A K : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K] (m : ℕ) (α : Measure A) [IsProbabilityMeasure α] [α.IsMulRightInvariant] (κ : Measure K)
    [IsProbabilityMeasure κ] [κ.IsMulLeftInvariant] (s : (Fin m → A) → K) (hs : Continuous s) (hm : ∀ x y, s (x * y) = s x * s y)
    (ho : Function.Surjective s) {f : K → ℂ} (hf : Continuous f) :
    ∫ k, f k ∂κ = ∫ x, f (s x) ∂(Measure.pi fun _ => α) :=
  int_surj (Measure.pi fun _ => α) κ s hs hm ho hf

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F]
  {σ : E ≃ₐ[F] E} (D : InfD σ 1) {n : ℕ}

private theorem tens_ec {κF : Measure (archCompact F n)} {eF : archCompact F n → ℂ} {κ : Measure (archCompact E n)}
    {e : archCompact E n → ℂ} (hF : IdemA κF eF) (hE : IdemA κ e) (hSq : IsSq D eF e) {β : archGroup F n → ℝ} (hβ : Continuous β)
    (x : archGroup E n) :
    ec κ e (fun y => ((∏ i, β (compA D n i y) : ℝ) : ℂ)) x = ∏ i, ec κF eF (fun y => (β y : ℂ)) (compA D n i x) := by
  haveI := hE.haar.prob
  haveI := hF.haar.prob
  haveI : κ.IsMulLeftInvariant := ⟨fun k => (hE.haar.left k).map_eq⟩
  haveI : κF.IsMulRightInvariant := ⟨fun k => (hF.haar.right k).map_eq⟩
  obtain ⟨hgc, hcg, hgm, hgcont, hccont, -⟩ := archBasic F E σ 1 D n
  have hcomp := (positionOf F E σ 1 D).2 n
  let s : (Fin (1 + 1) → archCompact F n) → archCompact E n := fun kk =>
    ⟨glueA D n (fun i => kk i), (hcomp _).2 fun i => by rw [hgc]; exact (kk i).2⟩
  have hsc : Continuous s := Continuous.subtype_mk (hgcont.comp (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))) _
  have hsm : ∀ x y, s (x * y) = s x * s y := fun x y => Subtype.ext (hgm _ _)
  have hss : Function.Surjective s := fun k => ⟨fun i => ⟨compA D n i k, (hcomp k).1 k.2 i⟩, Subtype.ext (hcg k)⟩
  have hsk : ∀ kk i, compA D n i (s kk : archGroup E n) = kk i := fun kk i => hgc _ i
  have hes : ∀ kk, e (s kk) = ∏ i, eF (kk i) := fun kk => hSq (s kk) kk fun i => (hsk kk i).symm
  have hcf : Continuous fun k : archCompact E n => e k * ((∏ i, β (compA D n i ((k : archGroup E n)⁻¹ * x)) : ℝ) : ℂ) := by
    refine hE.cont.mul (Complex.continuous_ofReal.comp (continuous_finset_prod _ fun i _ => hβ.comp ((hccont i).comp ?_)))
    fun_prop
  unfold ec
  haveI : SecondCountableTopology (archCompact F n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (archCompact E n) := TopologicalSpace.Subtype.secondCountableTopology _
  rw [int_surj_pi (1 + 1) κF κ s hsc hsm hss hcf]
  have e1 : ∀ kk : Fin (1 + 1) → archCompact F n,
      e (s kk) * ((∏ i, β (compA D n i ((s kk : archGroup E n)⁻¹ * x)) : ℝ) : ℂ) =
        ∏ i, (eF (kk i) * (β ((kk i : archGroup F n)⁻¹ * compA D n i x) : ℂ)) := fun kk => by
    rw [hes, Finset.prod_mul_distrib]
    simp only [map_mul, map_inv, hsk, Complex.ofReal_prod]
  simp only [e1]
  exact integral_fintype_prod_eq_prod (μ := fun _ => κF) fun i k => eF k * (β ((k : archGroup F n)⁻¹ * compA D n i x) : ℂ)

private theorem tens_cv {νE : Measure (archGroup E n)} {νF : Measure (archGroup F n)} [νE.IsHaarMeasure] [νF.IsHaarMeasure]
    {b a : TI F n} {aE : TI E n} {aF : TI F n} (hs : ArchSlot D νE νF b a aE aF) {bE : archGroup E n → ℂ} (hbc : Continuous bE)
    (hb : ∀ x, bE x = ∏ i, b (compA D n i x)) (x : archGroup E n) :
    aE x = cv νE bE (fun y => conj (bE y⁻¹)) x := by
  obtain ⟨hgc, hcg, hgm, hgcont, hccont, -⟩ := archBasic F E σ 1 D n
  have hc : Continuous fun y => bE y * conj (bE (y⁻¹ * x)⁻¹) := by fun_prop
  have e0 : ∫ y, bE y * conj (bE (y⁻¹ * x)⁻¹) ∂νE =
      ∫ yy, bE (glueA D n yy) * conj (bE ((glueA D n yy)⁻¹ * x)⁻¹) ∂(Measure.pi fun _ => νF) := by
    rw [hs.meas]
    exact integral_map hgcont.aemeasurable hc.aestronglyMeasurable
  have e1 : ∀ yy : Fin (1 + 1) → archGroup F n, bE (glueA D n yy) * conj (bE ((glueA D n yy)⁻¹ * x)⁻¹) =
      ∏ i, (b (yy i) * conj (b ((yy i)⁻¹ * compA D n i x)⁻¹)) := fun yy => by
    rw [hb, hb, map_prod, Finset.prod_mul_distrib]
    simp only [map_mul, map_inv, hgc]
  simp only [cv]
  rw [e0]
  simp only [e1]
  rw [integral_fintype_prod_eq_prod (μ := fun _ => νF)
    fun i y => b y * conj (b (y⁻¹ * compA D n i x)⁻¹), hs.tens x]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hs.sq]
  rfl

end Tens

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.ampEx :
    AmpEx := by
  intro F E _ _ _ _ _ _ _ σ D n hn κF eF κ e hF hE hSq νE _ νF _ hν φ hφ hφ0 hfix
  haveI := hE.haar.prob
  haveI : κ.IsMulLeftInvariant := ⟨fun k => (hE.haar.left k).map_eq⟩
  haveI : νE.IsInvInvariant := isInvInvariant_archGroup νE
  obtain ⟨hgc, hcg, hgm, hgcont, hccont, -, -, htens⟩ := archBasic F E σ 1 D n
  obtain ⟨g₀, hg₀⟩ : ∃ g, φ g ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ0 (funext h)
  set ψ : archGroup E n → ℂ := fun x => φ (g₀ * archP E n x) with hψdef
  have hψ : Continuous ψ := hφ.comp (continuous_const.mul continuous_archP)
  have hψf : ∀ w, ∫ k : archCompact E n, e k * ψ (w * k) ∂κ = ψ w := fun w => by
    have := hfix (g₀ * archP E n w)
    simpa [hψdef, arc1, map_mul, mul_assoc] using this
  have hψ1 : ψ 1 ≠ 0 := by simpa [hψdef] using hg₀
  obtain ⟨O, hO, hne⟩ := sq_ne κ νE hE.cont hE.star hψ hψf hψ1
  have hglue1 : glueA D n 1 = 1 := by
    have := hcg 1
    simp only [map_one] at this
    exact this
  have hpre : glueA D n ⁻¹' O ∈ 𝓝 (1 : Fin (1 + 1) → archGroup F n) :=
    hgcont.continuousAt.preimage_mem_nhds (by rw [hglue1]; exact hO)
  rw [nhds_pi, Filter.mem_pi] at hpre
  obtain ⟨I, -, t, ht, hsub⟩ := hpre
  have hN : (⋂ i, t i) ∈ 𝓝 (1 : archGroup F n) := Filter.iInter_mem.2 ht
  obtain ⟨β, b, hβc, hβs, hβ0, ⟨x₀, hx₀⟩, hβN, hbe, hbsm, hbfin, hbn⟩ := exB hF νF hN
  obtain ⟨νE', _, a, aE, aF, hs⟩ := archPositionEx F E σ 1 D n νF b hbsm hbfin hbn
  have hs' : ArchSlot D νE νF b a aE aF := (hs.meas.trans hν.symm) ▸ hs
  set βE : archGroup E n → ℝ := fun y => ∏ i, β (compA D n i y) with hβE
  have hβEc : Continuous βE := continuous_finset_prod _ fun i _ => hβc.comp (hccont i)
  have hβEc' : Continuous fun y => (βE y : ℂ) := by fun_prop
  have hbE : ∀ x, ec κ e (fun y => (βE y : ℂ)) x = ∏ i, b (compA D n i x) := fun x => by
    simp only [hbe]
    exact tens_ec D hF hE hSq hβc x
  have hbEc := ec_cont κ hE.cont hβEc'
  have hH := tens_cv D hs' hbEc hbE
  have hβs' : HasCompactSupport fun y => (β y : ℂ) := hβs.comp_left Complex.ofReal_zero
  obtain ⟨βTI, hβTI⟩ := exTI (Complex.continuous_ofReal.comp hβc) hβs'
  obtain ⟨βT, hβT⟩ := htens fun _ => βTI
  have hβEs : HasCompactSupport βE := by
    refine βT.hasCompactSupport.mono fun y hy hz => hy ?_
    have e1 : βT y = (βE y : ℂ) := by
      rw [hβT y]
      simp [hβE, hβTI]
    rw [e1] at hz
    exact_mod_cast hz
  have hβEs' : HasCompactSupport fun y => (βE y : ℂ) := hβEs.comp_left Complex.ofReal_zero
  refine ⟨b, a, aE, aF, hs', fun g => ?_, g₀, ?_⟩
  · simp only [hH]
    exact bi_sq κ νE hE.cont hE.star hbEc (ec_cs κ e hβEs') (ec_idem κ hE.cont hE.idem hβEc') g
  · simp only [hH]
    refine hne βE hβEc hβEs (fun y => Finset.prod_nonneg fun i _ => hβ0 _) ⟨glueA D n fun _ => x₀, ?_⟩ fun y hy => ?_
    · simp only [hβE, hgc]
      exact Finset.prod_ne_zero_iff.2 fun _ _ => hx₀
    · have h1 : ∀ i, β (compA D n i y) ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hy i (Finset.mem_univ _)
      have h2 : (fun i => compA D n i y) ∈ glueA D n ⁻¹' O := hsub fun i _ => Set.mem_iInter.1 (hβN _ (h1 i)) i
      simpa [Set.mem_preimage, hcg] using h2
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem central_fixed (σ : E ≃ₐ[F] E) (s : {r : ℝ // 0 < r}) :
    mapGL n (galAd σ) (centralSection E n s) = centralSection E n s := by
  have hd : Module.finrank F E ≠ 0 := Module.finrank_pos.ne'
  have hroot : (⟨(s : ℝ) ^ ((Module.finrank F E : ℝ))⁻¹, Real.rpow_pos_of_pos s.2 _⟩ : {r : ℝ // 0 < r}) ^
      Module.finrank F E = s := by
    apply Subtype.ext
    rw [Positive.val_pow]
    exact Real.rpow_inv_natCast_pow s.2.le hd
  rw [← hroot, ← UpperTheory.centralSection_baseChange F E n]
  exact (UpperTheory.adele_galois_action_baseChange_compat F E σ n).2.2.2.2.1 _

private theorem galois_twist_finite_adelic_point (σ : E ≃ₐ[F] E) (hn : 0 < n) {μ : Measure (G1 E n)} [μ.IsHaarMeasure] {θ : Twist μ}
    (hθ : IsGalTwist σ θ) {x x' : FA E n} (h : mapGL n (galAd σ) (finEmb E n x) = finEmb E n x') :
    θ.e (fin1 x) = fin1 x' := by
  change θ.e (retractOne (finEmb E n x)) = retractOne (finEmb E n x')
  have h1 : ((θ.e (retractOne (finEmb E n x)) : G1 E n) : AdelicGLn.AdelicGL E n) *
      centralSection E n (detModule E n (finEmb E n x)) = finEmb E n x' := by
    rw [hθ, coe_retractOne, map_mul, map_inv, central_fixed, inv_mul_cancel_right, h]
  rw [← h1, retractOne_mul, retractOne_coe, retractOne_centralSection, mul_one]

private theorem indicator_prod {v : Pl F} (UE : Subgroup (GL (Fin n) (CompletionsOver E v)))
    (H : ∀ u : PlacesOver E v, Set (Gw n u.1)) (h : ∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ H u) :
    (UE : Set (GL (Fin n) (CompletionsOver E v))).indicator 1 = GM.prodFn fun u => (H u).indicator 1 := by
  funext g
  rw [GM.prodFn, finprod_eq_prod_of_fintype]
  by_cases hg : g ∈ UE
  · rw [Set.indicator_of_mem (show g ∈ (UE : Set _) from hg)]
    exact (Finset.prod_eq_one fun u _ => Set.indicator_of_mem ((h g).1 hg u) _).symm
  · rw [Set.indicator_of_notMem (show g ∉ (UE : Set _) from hg)]
    obtain ⟨u, hu⟩ := not_forall.1 fun hh => hg ((h g).2 hh)
    exact (Finset.prod_eq_zero (Finset.mem_univ u) (Set.indicator_of_notMem hu _)).symm

private theorem iwCoset_zero_eq (w : Pl E) :
    GM.iwCoset w (0 : Fin n → ℤ) = (GLnLocal.iwahori (w.adicCompletion E) n : Set (Gw n w)) := by
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [GroundTheory.Automorphic.Parabolic.diagPow_zero, mul_one]
    exact mul_mem ha hb
  · intro hg
    exact ⟨g, hg, 1, one_mem _, by rw [GroundTheory.Automorphic.Parabolic.diagPow_zero, mul_one, mul_one]⟩

private theorem indicator_test {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G) (h : CO J) :
    Test ((J : Set G).indicator (1 : G → ℂ)) ∧
      ∀ u ∈ J, ∀ g, (J : Set G).indicator (1 : G → ℂ) (u * g) = (J : Set G).indicator 1 g ∧
        (J : Set G).indicator (1 : G → ℂ) (g * u) = (J : Set G).indicator 1 g := by
  have hcl : IsClopen (J : Set G) := ⟨Subgroup.isClosed_of_isOpen J h.2, h.2⟩
  refine ⟨⟨?_, HasCompactSupport.intro h.1 fun x hx => Set.indicator_of_notMem hx _⟩, fun u hu g => ?_⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
    by_cases hx : x ∈ (J : Set G)
    · exact ⟨J, h.2, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
    · exact ⟨(J : Set G)ᶜ, hcl.compl.isOpen, hx, fun y hy => by
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  · have h1 : u * g ∈ (J : Set G) ↔ g ∈ (J : Set G) := Subgroup.mul_mem_cancel_left J hu
    have h2 : g * u ∈ (J : Set G) ↔ g ∈ (J : Set G) := Subgroup.mul_mem_cancel_right J hu
    simp only [Set.indicator_apply, h1, h2, Pi.one_apply, and_self]

private theorem split_level (v : Pl F) (hv : GM.Split E v) (u₀ : PlacesOver E v)
    (U₀ : ∀ u : PlacesOver E v, Subgroup (Gw n u.1))
    (hU : ∀ u, CO (U₀ u) ∧ U₀ u ≤ GLnLocal.integralGL (u.1.adicCompletion E) n) :
    ∃ (A : Subgroup (Gw n v)) (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)), CO A ∧
      A ≤ GLnLocal.integralGL (v.adicCompletion F) n ∧
      ∀ u, CO (J u) ∧ J u ≤ U₀ u ∧ ∀ g, g ∈ A ↔ mapGL n (completionMap v u.1) g ∈ J u := by
  have hL := fun u : PlacesOver E v => UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hv u) n
  choose e he using fun u => (hL u).1
  let A : Subgroup (Gw n v) := ⨅ u, (U₀ u).comap (mapGL n (completionMap v u.1))
  have hA : ∀ g, g ∈ A ↔ ∀ u, e u g ∈ U₀ u := fun g => by
    simp only [A, Subgroup.mem_iInf, Subgroup.mem_comap, he]
  have hAo : IsOpen (A : Set (Gw n v)) := by
    have hset : (A : Set (Gw n v)) = ⋂ u, (e u) ⁻¹' (U₀ u : Set (Gw n u.1)) := by
      ext g
      simp only [SetLike.mem_coe, hA, Set.mem_iInter, Set.mem_preimage]
    rw [hset]
    exact isOpen_iInter_of_finite fun u => (hU u).1.2.preimage (e u).continuous
  have hAc : IsCompact (A : Set (Gw n v)) := by
    have hc : IsCompact ((e u₀) ⁻¹' (U₀ u₀ : Set (Gw n u₀.1))) :=
      (e u₀).toHomeomorph.isCompact_preimage.2 (hU u₀).1.1
    exact hc.of_isClosed_subset (Subgroup.isClosed_of_isOpen A hAo) fun g hg => (hA g).1 hg u₀
  have hJ : ∀ u, ((A.map (mapGL n (completionMap v u.1)) : Subgroup (Gw n u.1)) : Set (Gw n u.1)) = e u '' A := fun u => by
    rw [Subgroup.coe_map]
    exact Set.image_congr fun g _ => (he u g).symm
  refine ⟨A, fun u => A.map (mapGL n (completionMap v u.1)), ⟨hAc, hAo⟩, fun g hg => ?_, fun u => ⟨⟨?_, ?_⟩, ?_, fun g => ⟨?_, ?_⟩⟩⟩
  · exact ((hL u₀).2.1 g).1 ((hU u₀).2 (by rw [← he]; exact (hA g).1 hg u₀))
  · rw [hJ]; exact hAc.image (e u).continuous
  · rw [hJ]; exact (e u).toHomeomorph.isOpenMap _ hAo
  · rintro _ ⟨g, hg, rfl⟩
    rw [← he]; exact (hA g).1 hg u
  · exact fun hg => ⟨g, hg, rfl⟩
  · rintro ⟨g', hg', h⟩
    rw [← he, ← he] at h
    rwa [← (e u).injective h]

end SlopeTestRemainingChoices

section Key

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private structure LevelAt (σ : E ≃ₐ[F] E) (q : Pl F) (S : Finset (Pl F)) (U₀ : ∀ w : Pl E, Subgroup (Gw n w)) (v : Pl F)
    (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)) (c : ℂ) (f : Gw n v → ℂ)
    (UE : Subgroup (GL (Fin n) (CompletionsOver E v))) (UF : Subgroup (Gw n v)) : Prop where
  co : (∀ u, CO (J u) ∧ J u ≤ GLnLocal.integralGL (u.1.adicCompletion E) n)
  mem : (∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ J u)
  stable : (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ J u) → ∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ J u)
  off : (v ∉ S → v ≠ q → (UE : Set (GL (Fin n) (CompletionsOver E v))) = unitSet E n v ∧
        f = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1 ∧
        UF = GLnLocal.integralGL (v.adicCompletion F) n ∧ ∀ u, J u = GLnLocal.integralGL (u.1.adicCompletion E) n)
  at_q : (v = q → f = (GM.iwCoset v 0).indicator 1 ∧ UF = GLnLocal.iwahori (v.adicCompletion F) n ∧
        ∀ u, J u = GLnLocal.iwahori (u.1.adicCompletion E) n)
  in_S : (v ∈ S → (∀ u, J u ≤ U₀ u.1) ∧
        IsLocallyConstant ((UE : Set (GL (Fin n) (CompletionsOver E v))).indicator (1 : GL (Fin n) (CompletionsOver E v) → ℂ)) ∧
        HasCompactSupport ((UE : Set (GL (Fin n) (CompletionsOver E v))).indicator (1 : GL (Fin n) (CompletionsOver E v) → ℂ)) ∧
        IsLocallyConstant f ∧ HasCompactSupport f ∧
        IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧ (UE : Set (GL (Fin n) (CompletionsOver E v))) ⊆ unitSet E n v ∧
        IsOpen (UF : Set (Gw n v)) ∧ UF ≤ GLnLocal.integralGL (v.adicCompletion F) n ∧
        (∀ y ∈ UE, ∀ g, (UE : Set (GL (Fin n) (CompletionsOver E v))).indicator (1 : GL (Fin n) (CompletionsOver E v) → ℂ) (y * g) =
          (UE : Set (GL (Fin n) (CompletionsOver E v))).indicator (1 : GL (Fin n) (CompletionsOver E v) → ℂ) g) ∧
        (∀ y ∈ UF, ∀ g, f (y * g) = f g) ∧
        GM.MatchAt σ v c ((UE : Set (GL (Fin n) (CompletionsOver E v))).indicator 1) f)

end Key

section Key

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
  [IsTotallyComplex E] {n : ℕ}

private theorem level_at (σ : E ≃ₐ[F] E) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) (hp : (Module.finrank F E).Prime) (hn : 0 < n)
    (q : Pl F) (S : Finset (Pl F)) (hqS : q ∉ S) (hsp : ∀ v ∈ S, GM.Split E v) (U₀ : ∀ w : Pl E, Subgroup (Gw n w)) (hU₀ : Lev U₀)
    (v : Pl F) :
    ∃ (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)) (c : ℂ) (f : Gw n v → ℂ)
      (UE : Subgroup (GL (Fin n) (CompletionsOver E v))) (UF : Subgroup (Gw n v)), LevelAt σ q S U₀ v J c f UE UF := by
  have hne : Nonempty (PlacesOver E v) := by
    obtain ⟨⟨P, hP, hl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 E)) := inferInstance
    exact ⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, hl⟩⟩
  obtain ⟨o1, o2, ⟨U1, o3⟩, ⟨U2, o4⟩, o5⟩ := UpperTheory.ConvolutionTheory.T.offStable F E σ hσ hp n hn v
  by_cases hvS : v ∈ S
  · obtain ⟨u₀⟩ := hne
    have hv := hsp v hvS
    obtain ⟨A, J, hA, hAi, hJ⟩ := split_level v hv u₀ (fun u => U₀ u.1) fun u => hU₀ u.1
    obtain ⟨s1, s2⟩ := UpperTheory.ConvolutionTheory.T.splitStable F E σ hσ hp n hn v hv A J fun u => (hJ u).2.2
    obtain ⟨UE, e1, e2, e3⟩ := s2 hA hAi
    obtain ⟨c, hc⟩ := UpperTheory.ConvolutionTheory.T.splitMatch F E σ hσ hp n hn v u₀ hv A J hA fun u => ⟨(hJ u).1, (hJ u).2.2⟩
    have hi := indicator_test (J u₀) (hJ u₀).1
    obtain ⟨m1, m2, m3, m4, m5⟩ := hc _ hi.1 hi.2
    have hφ : Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) u₀
        ((J u₀ : Set (Gw n u₀.1)).indicator 1) = fun u => (J u : Set (Gw n u.1)).indicator 1 :=
      Function.update_eq_self u₀ _
    rw [hφ, ← indicator_prod UE (fun u => (J u : Set (Gw n u.1))) e1] at m1 m2 m4
    exact ⟨J, c, _, UE, A, ⟨fun u => ⟨(hJ u).1, (hJ u).2.1.trans (hU₀ u.1).2⟩, e1, s1, fun h => absurd hvS h,
      fun h => absurd (h ▸ hvS) hqS, fun _ => ⟨fun u => (hJ u).2.1, m2.1, m2.2, m3.1, m3.2, e2, e3, hA.2, hAi,
        fun y hy => m4 y ((e1 y).1 hy), m5, m1⟩⟩⟩
  · by_cases hvq : v = q
    · exact ⟨fun u => GLnLocal.iwahori (u.1.adicCompletion E) n, 0, (GM.iwCoset v 0).indicator 1, U2,
        GLnLocal.iwahori (v.adicCompletion F) n, ⟨fun u => ⟨(o5 u.1).2.1, (o5 u.1).2.2⟩, o4, o2,
        fun _ h => absurd hvq h, fun _ => ⟨rfl, rfl, fun _ => rfl⟩, fun h => absurd h hvS⟩⟩
    · refine ⟨fun u => GLnLocal.integralGL (u.1.adicCompletion E) n, 0,
        (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1, U1, GLnLocal.integralGL (v.adicCompletion F) n,
        ⟨fun u => ⟨(o5 u.1).1, le_rfl⟩, fun g => ?_, o1, fun _ _ => ⟨o3, rfl, rfl, fun _ => rfl⟩,
        fun h => absurd h hvq, fun h => absurd h hvS⟩⟩
      rw [← SetLike.mem_coe, o3]
      exact Iff.rfl

end Key

section Build

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem exists_loc (σ : E ≃ₐ[F] E) (q : Pl F) (w₀ : PlacesOver E q) (S : Finset (Pl F)) (hqS : q ∉ S)
    (hunr : ∀ v ∉ S, GM.Unr E v) (U₀ : ∀ w : Pl E, Subgroup (Gw n w))
    (J : ∀ v : Pl F, ∀ u : PlacesOver E v, Subgroup (Gw n u.1)) (c : Pl F → ℂ) (f : ∀ v : Pl F, Gw n v → ℂ)
    (UE : ∀ v : Pl F, Subgroup (GL (Fin n) (CompletionsOver E v))) (UF : ∀ v : Pl F, Subgroup (Gw n v))
    (k : ∀ v, LevelAt σ q S U₀ v (J v) (c v) (f v) (UE v) (UF v)) :
    ∃ L : GM.Loc σ n q w₀, L.S = S ∧ L.UE = UE ∧ ∀ v, L.φ v = (UE v : Set (GL (Fin n) (CompletionsOver E v))).indicator 1 := by
  have hq : ∀ g, g ∈ UE q ↔ ∀ u, GM.cmp u g ∈ GLnLocal.iwahori (u.1.adicCompletion E) n := fun g =>
    ((k q).mem g).trans (forall_congr' fun u => by rw [((k q).at_q rfl).2.2 u])
  have hφq : (UE q : Set (GL (Fin n) (CompletionsOver E q))).indicator (1 : GL (Fin n) (CompletionsOver E q) → ℂ) = GM.iwFn w₀ 0 := by
    refine (indicator_prod (UE q) (fun u => (GLnLocal.iwahori (u.1.adicCompletion E) n : Set _)) hq).trans ?_
    unfold GM.iwFn
    congr 1
    funext u
    rw [ite_self, iwCoset_zero_eq]
  refine ⟨⟨S, hqS, hunr, fun v => (UE v : Set (GL (Fin n) (CompletionsOver E v))).indicator 1, f, c, UE, UF, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, fun _ => rfl⟩
  · exact fun v hv => by
      obtain ⟨-, a, b, d, e, -⟩ := (k v).in_S hv
      exact ⟨a, b, d, e⟩
  · exact fun v hv => by
      obtain ⟨-, -, -, -, -, a, b, d, e, -⟩ := (k v).in_S hv
      exact ⟨a, b, d, e⟩
  · exact fun v hv => by
      obtain ⟨-, -, -, -, -, -, -, -, -, a, b, -⟩ := (k v).in_S hv
      exact ⟨a, b⟩
  · exact fun v hv => by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, a⟩ := (k v).in_S hv
      exact a
  · exact ⟨hφq, ((k q).at_q rfl).1, hq, ((k q).at_q rfl).2.1⟩
  · intro v a b
    obtain ⟨e1, e2, e3, -⟩ := (k v).off a b
    refine ⟨?_, e2, e1, e3⟩
    change (UE v : Set (GL (Fin n) (CompletionsOver E v))).indicator 1 = _
    rw [e1]

end Build

section Lev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem mem_levOn_iff (SE : Finset (Pl E)) (U : ∀ w : Pl E, Subgroup (Gw n w))
    (hU : ∀ w, w ∉ SE → U w = GLnLocal.integralGL (w.adicCompletion E) n) (x : FA E n) :
    x ∈ levOn SE U ↔ ∀ w, finAt w (finEmb E n x) ∈ U w := by
  have hite : ∀ w, (if w ∈ SE then U w else GLnLocal.integralGL (w.adicCompletion E) n) = U w := fun w => by
    split_ifs with hw
    · rfl
    · exact (hU w hw).symm
  exact forall_congr' fun w => by rw [← hite w]

private theorem cmp_atFin (v : Pl F) (u : PlacesOver E v) (g : AdelicGLn.AdelicGL E n) :
    GM.cmp u (mapGL n (atFin v) g) = finAt u.1 g :=
  Units.ext (Matrix.ext fun _ _ => rfl)

private theorem levE_eq (SE : Finset (Pl E)) (U : ∀ w : Pl E, Subgroup (Gw n w))
    (hU : ∀ w, w ∉ SE → U w = GLnLocal.integralGL (w.adicCompletion E) n)
    (UE : ∀ v : Pl F, Subgroup (GL (Fin n) (CompletionsOver E v)))
    (hm : ∀ (v : Pl F) g, g ∈ UE v ↔ ∀ u : PlacesOver E v, GM.cmp u g ∈ U u.1) :
    GM.levE UE = levOn SE U := by
  ext x
  rw [mem_levOn_iff SE U hU]
  simp only [GM.levE, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.comp_apply]
  constructor
  · intro h w
    have := (hm _ _).1 (h (w.under (𝓞 F))) ⟨w, ⟨rfl⟩⟩
    rwa [cmp_atFin] at this
  · intro h v
    refine (hm v _).2 fun u => ?_
    rw [cmp_atFin]
    exact h u.1

private theorem twist_stable (σ : E ≃ₐ[F] E) (hn : 0 < n) (SE : Finset (Pl E)) (U : ∀ w : Pl E, Subgroup (Gw n w))
    (hU : ∀ w, w ∉ SE → U w = GLnLocal.integralGL (w.adicCompletion E) n)
    (hs : ∀ (v : Pl F) (x : GL (Fin n) (CompletionsOver E v)), (∀ u : PlacesOver E v, GM.cmp u x ∈ U u.1) →
      ∀ u : PlacesOver E v, GM.cmp u (mapGL n (galFin σ v) x) ∈ U u.1)
    {μ : Measure (G1 E n)} [μ.IsHaarMeasure] {θ : Twist μ} (hθ : IsGalTwist σ θ) (x : FA E n) (hx : x ∈ levOn SE U) :
    ∃ x' ∈ levOn SE U, θ.e (fin1 x) = fin1 x' := by
  obtain ⟨c1, c2, -⟩ := UpperTheory.adele_galois_action_baseChange_compat F E σ n
  have hI : finEmb E n (AdelicGLn.prodEquiv E n (mapGL n (galAd σ) (finEmb E n x))).2 =
      mapGL n (galAd σ) (finEmb E n x) := by
    apply (AdelicGLn.prodEquiv E n).injective
    rw [prodEquiv_finEmb]
    refine Prod.ext ?_ rfl
    have e1 : ∀ g : AdelicGLn.AdelicGL E n, (AdelicGLn.prodEquiv E n g).1 = T4.pI E n g := fun g =>
      Units.ext (Matrix.ext fun a b => AdelicGLn.prodEquiv_apply_fst E n g a b)
    have e2 : T4.pI E n (finEmb E n x) = 1 := by rw [← e1, prodEquiv_finEmb]
    change 1 = _
    rw [e1, c1, e2, map_one]
  refine ⟨_, ?_, galois_twist_finite_adelic_point σ hn hθ hI.symm⟩
  rw [mem_levOn_iff SE U hU, hI]
  intro w
  have h1 := (mem_levOn_iff SE U hU x).1 hx
  have h3 : mapGL n (atFin (w.under (𝓞 F))) (mapGL n (galAd σ) (finEmb E n x)) =
      mapGL n (galFin σ (w.under (𝓞 F))) (mapGL n (atFin (w.under (𝓞 F))) (finEmb E n x)) := c2 _ _
  have h4 := hs _ (mapGL n (atFin (w.under (𝓞 F))) (finEmb E n x)) (fun u => by
    rw [cmp_atFin]; exact h1 u.1) ⟨w, ⟨rfl⟩⟩
  rwa [← h3, cmp_atFin] at h4

end Lev

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.locSm :
    LocSm := by
  intro F E _ _ _ _ _ _ _ _ σ h2 hσ n hn q w₀ S hqS hunr hsp U₀ hU₀ SE hSE
  have hp : (Module.finrank F E).Prime := h2 ▸ Nat.prime_two
  choose J c f UE UF k using level_at (n := n) σ hσ hp hn q S hqS hsp U₀ hU₀
  have hu : ∀ (v : Pl F) (u : PlacesOver E v), u.1.under (𝓞 F) = v := fun v u => HeightOneSpectrum.ext u.2.over.symm
  let U : ∀ w : Pl E, Subgroup (Gw n w) := fun w => J (w.under (𝓞 F)) ⟨w, ⟨rfl⟩⟩
  have eJ : ∀ v (u : PlacesOver E v), U u.1 = J v u := by
    rintro v ⟨w, hw⟩
    obtain rfl : w.under (𝓞 F) = v := hu v ⟨w, hw⟩
    rfl
  have hoff : ∀ w, w ∉ SE → U w = GLnLocal.integralGL (w.adicCompletion E) n := fun w hw => by
    have hw' := mt (hSE w).2 hw
    rw [not_or] at hw'
    exact ((k _).off hw'.1 hw'.2).2.2.2 ⟨w, ⟨rfl⟩⟩
  have hm : ∀ (v : Pl F) g, g ∈ UE v ↔ ∀ u : PlacesOver E v, GM.cmp u g ∈ U u.1 := fun v g =>
    ((k v).mem g).trans (forall_congr' fun u => by rw [eJ])
  have hs : ∀ (v : Pl F) (x : GL (Fin n) (CompletionsOver E v)), (∀ u : PlacesOver E v, GM.cmp u x ∈ U u.1) →
      ∀ u : PlacesOver E v, GM.cmp u (mapGL n (galFin σ v) x) ∈ U u.1 := fun v x hx u => by
    rw [eJ]
    exact (k v).stable x (fun u => by rw [← eJ]; exact hx u) u
  obtain ⟨L, hS, hUE, hφ⟩ := exists_loc σ q w₀ S hqS hunr U₀ J c f UE UF k
  refine ⟨L, U, hS, fun w => (k _).co ⟨w, ⟨rfl⟩⟩, fun w hw => ((k _).in_S hw).1 ⟨w, ⟨rfl⟩⟩,
    fun w hw => ((k _).at_q hw).2.2 ⟨w, ⟨rfl⟩⟩, ?_, fun v => ?_, fun μ _ θ hθ x hx => twist_stable σ hn SE U hoff hs hθ x hx⟩
  · rw [hUE]
    exact levE_eq SE U hoff UE hm
  · rw [hφ, hUE]
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.IwahoriHeckeOperatorComm

section One

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]

private theorem iw_oc (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (w : Pl K) :
    IsOpen (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) ∧
      IsCompact (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) := by
  have hI := UpperTheory.ConvolutionTheory.Tf.uiwPow K n μ w 0 0 (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)
  exact ⟨hI.2.2.1, hI.2.2.2.1⟩

private theorem rho_comm {w w' : Pl K} (h : w ≠ w') (g : GL (Fin n) (w.adicCompletion K))
    (g' : GL (Fin n) (w'.adicCompletion K)) : Commute (rhoL μ w g) (rhoL μ w' g') := by
  obtain ⟨-, -, -, -, -, hmul, -, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
  have hc := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' h.symm g g'
  change rhoF μ _ ∘L rhoF μ _ = rhoF μ _ ∘L rhoF μ _
  rw [← hmul, ← hmul, hc]

private theorem hop_comm {w w' : Pl K} (h : w ≠ w') (J : Subgroup (GL (Fin n) (w.adicCompletion K)))
    (J' : Subgroup (GL (Fin n) (w'.adicCompletion K))) (x : GL (Fin n) (w.adicCompletion K))
    (x' : GL (Fin n) (w'.adicCompletion K)) (hJo : IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))))
    (hJc : IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))))
    (hJo' : IsOpen (J' : Set (GL (Fin n) (w'.adicCompletion K))))
    (hJc' : IsCompact (J' : Set (GL (Fin n) (w'.adicCompletion K)))) :
    Commute (Hop μ w J x) (Hop μ w' J' x') :=
  (UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w' J' x' hJo' hJc').2.2.2.2.1 _ fun g =>
    ((UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J x hJo hJc).2.2.2.2.1 (rhoL μ w' g) fun g' => (rho_comm h g' g).symm).symm

private theorem hop_amp (hn : 0 < n) (𝔞 : Amp μ) (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K)))
    (x : GL (Fin n) (w.adicCompletion K)) (hJo : IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))))
    (hJc : IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))))
    (h1 : J.map (AdelicGLn.localEmbedding w) ≤ 𝔞.U) (h2 : ∀ u ∈ 𝔞.U, finAt w (finEmb K n u) ∈ J) :
    Commute (Hop μ w J x) 𝔞.A := by
  obtain ⟨m, hm, -⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ 𝔞.ν
  have hUc : IsCompact (𝔞.U : Set (FA K n)) :=
    (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ 𝔞.isOpen) 𝔞.le
  have hP := (UpperTheory.ConvolutionTheory.Tf.hopLevel K n μ m w J x 𝔞.U hJo hJc 𝔞.isOpen hUc h1 h2).1
  have hO : Commute (Oinf μ 𝔞.ν 𝔞.a₀) (Hop μ w J x) :=
    (UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J x hJo hJc).2.2.2.2.1 _ fun g =>
      (UpperTheory.ConvolutionTheory.Tf.opAlg K n μ 𝔞.ν m).2.2.2.2.2.2.2.2 _ _
  change Commute _ (Oinf μ 𝔞.ν 𝔞.a₀ * prj (fixF μ 𝔞.U))
  exact Commute.mul_right hO.symm hP

end One

section Two

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem under_eq {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private noncomputable def pv (v : Pl F) (x : AdelicGLn.FiniteAdelicGL E n) : GL (Fin n) (CompletionsOver E v) :=
  mapGL n (atFin v) (finEmb E n x)

private theorem finEmb_entry (x : AdelicGLn.FiniteAdelicGL E n) (a b : Fin n) :
    ((finEmb E n x : AdelicGLn.AdelicGL E n) a b).2 = x a b := by
  have h := AdelicGLn.prodEquiv_apply_snd E n (finEmb E n x) a b
  rw [prodEquiv_finEmb] at h
  exact h.symm

private theorem cmp_pv {v : Pl F} (w : PlacesOver E v) (x : AdelicGLn.FiniteAdelicGL E n) :
    GM.cmp w (pv v x) = AdelicGLn.finiteRestrictedEquiv E n x w.1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  change ((finEmb E n x : AdelicGLn.AdelicGL E n) a b).2 w.1 = _
  rw [finEmb_entry]
  rfl

private theorem pv_finPart (v : Pl F) (g : AdelicGLn.AdelicGL E n) :
    pv v (CuspidalSpectrum.finPart E n g) = mapGL n (atFin v) g := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  funext w
  change ((finEmb E n (CuspidalSpectrum.finPart E n g) : AdelicGLn.AdelicGL E n) a b).2 w.1 = (g a b).2 w.1
  rw [finEmb_entry]
  rfl

private theorem mem_levE (U : ∀ v : Pl F, Subgroup (GL (Fin n) (CompletionsOver E v)))
    (x : AdelicGLn.FiniteAdelicGL E n) : x ∈ GM.levE U ↔ ∀ v, pv v x ∈ U v := by
  simp only [GM.levE, Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl

private theorem finprod_ind (S : Finset (Pl F)) (U : ∀ v : Pl F, Subgroup (GL (Fin n) (CompletionsOver E v)))
    (hU : ∀ v ∉ S, (U v : Set (GL (Fin n) (CompletionsOver E v))) = unitSet E n v) (x : AdelicGLn.FiniteAdelicGL E n) :
    ∏ᶠ v, (U v : Set (GL (Fin n) (CompletionsOver E v))).indicator (1 : GL (Fin n) (CompletionsOver E v) → ℂ) (pv v x) =
      (GM.levE U : Set (AdelicGLn.FiniteAdelicGL E n)).indicator (1 : AdelicGLn.FiniteAdelicGL E n → ℂ) x := by
  classical
  by_cases hx : x ∈ GM.levE U
  · rw [Set.indicator_of_mem (show x ∈ (GM.levE U : Set (AdelicGLn.FiniteAdelicGL E n)) from hx), Pi.one_apply]
    exact finprod_eq_one_of_forall_eq_one fun v => by
      rw [Set.indicator_of_mem (show pv v x ∈ (U v : Set _) from (mem_levE U x).1 hx v), Pi.one_apply]
  · rw [Set.indicator_of_notMem (show x ∉ (GM.levE U : Set (AdelicGLn.FiniteAdelicGL E n)) from hx)]
    rw [mem_levE, not_forall] at hx
    obtain ⟨v₀, hv₀⟩ := hx
    have hB : {w : Pl E | AdelicGLn.finiteRestrictedEquiv E n x w ∉
        GLnLocal.integralGL (w.adicCompletion E) n}.Finite :=
      Filter.eventually_cofinite.1 (AdelicGLn.finiteRestrictedEquiv E n x).2
    refine finprod_eq_zero _ v₀ (Set.indicator_of_notMem hv₀ _) ?_
    refine (S.finite_toSet.union (hB.image fun w : Pl E => w.under (𝓞 F))).subset fun v hv => ?_
    by_cases hvS : v ∈ S
    · exact Or.inl hvS
    · right
      have hnot : pv v x ∉ unitSet E n v := by
        intro h
        refine hv ?_
        rw [← hU v hvS] at h
        change (U v : Set (GL (Fin n) (CompletionsOver E v))).indicator (1 : GL (Fin n) (CompletionsOver E v) → ℂ) (pv v x) = 1
        rw [Set.indicator_of_mem h, Pi.one_apply]
      simp only [unitSet, Set.mem_setOf_eq, not_forall] at hnot
      obtain ⟨w', hw'⟩ := hnot
      refine ⟨w'.1, ?_, under_eq w'⟩
      intro h
      refine hw' ?_
      have : GM.cmp w' (pv v x) ∈ GLnLocal.integralGL (w'.1.adicCompletion E) n := by
        rw [cmp_pv]
        exact h
      exact this

end Two

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.IwahoriHeckeOperatorComm

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.IwahoriHeckeOperatorComm Pointwise in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.sideX :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
          [IsTotallyComplex E] (σ : E ≃ₐ[F] E), Module.finrank F E = 2 → (∀ τ, τ ∈ Subgroup.zpowers σ) →
          ∀ n : ℕ, 0 < n → ∀ (μ : Measure (G1 E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ → ∀ (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q →
          ∀ (L : GM.Loc σ n q w₀) (νE : Measure (archGroup E n)) (aE : TI E n) (ν : Fin n → ℤ) (𝔢 : Side θ 2), GM.IsSideE L νE aE ν 𝔢 →
          (∀ v, L.φ v = (L.UE v : Set (GL (Fin n) (CompletionsOver E v))).indicator 1) →
          ∃ (𝔢' : Side θ 2) (φ : TF E n) (w₁ : PlacesOver E q), 𝔢'.toAmp = 𝔢.toAmp ∧ 𝔢'.g = 𝔢.g ∧ 𝔢'.Uq 0 = 𝔢.Uq 0 ∧ 𝔢'.Uq 1 = Uiw μ w₁.1 ν ∧
            (∀ x, φ x = (𝔢.U : Set (FA E n)).indicator 1 x) ∧ 𝔢'.g = tens 𝔢'.a₀ φ ∧ ∃ c : ℂ, c ≠ 0 ∧ 𝔢'.a = c • 𝔢'.g := by
  intro F E _ _ _ _ _ _ _ _ σ hfr hσ n hn μ _ θ hθ q w₀ hsplit L νE aE ν 𝔢 hside hφ
  classical
  obtain ⟨hν, ha, hS, hU, hg, hq0⟩ := hside
  have hfac := (UpperTheory.baseChangeLevel_isOpen_isCompact_contains_iwahori F E σ n hn q w₀ L).2.2.2.2.2
  have hσ2 : σ * σ = 1 := by
    have h1 : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, hfr]
    have h2 := pow_card_eq_one' (x := σ)
    rw [h1, pow_two] at h2
    exact h2
  have hl : (σ • w₀.1).asIdeal.LiesOver q.asIdeal := by
    haveI := w₀.2
    change (σ • w₀.1.asIdeal).LiesOver q.asIdeal
    infer_instance
  let w₁ : PlacesOver E q := ⟨σ • w₀.1, hl⟩
  have hne : w₀.1 ≠ w₁.1 := by
    intro e
    obtain ⟨p, -⟩ := ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.galLoc F E σ hfr hσ n hn μ θ).2 ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.galLoc F E σ hfr hσ n hn μ θ).1.2 ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.galLoc F E σ hfr hσ n hn μ θ).1.1 hθ))).2.2 q hsplit
    have hfix : ∀ k : ℤ, (σ ^ k) • w₀.1 = w₀.1 := fun k => by
      have hm : σ ∈ MulAction.stabilizer (E ≃ₐ[F] E) w₀.1 := e.symm
      exact (Subgroup.zpow_mem _ hm k)
    have hall : ∀ w : PlacesOver E q, w = w₀ := by
      intro w
      haveI := w.1.isPrime
      haveI := w₀.1.isPrime
      haveI := w.2
      haveI := w₀.2
      obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup q.asIdeal w₀.1.asIdeal w.1.asIdeal (E ≃ₐ[F] E)
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hσ τ)
      exact Subtype.ext (HeightOneSpectrum.ext (hτ.symm.trans (congrArg HeightOneSpectrum.asIdeal (hfix k))))
    have h01 : p 0 = p 1 := (hall _).trans (hall _).symm
    exact absurd (p.injective h01) (by decide)
  have hw10 : σ • w₁.1 = w₀.1 := by
    change σ • σ • w₀.1 = _
    rw [smul_smul, hσ2, one_smul]
  have hA : ∀ w : PlacesOver E q, Commute (Uiw μ w.1 ν) 𝔢.toAmp.A := fun w =>
    hop_amp hn 𝔢.toAmp w.1 _ _ (iw_oc μ w.1).1 (iw_oc μ w.1).2 (by rw [hU]; exact (hfac w).1)
      (by rw [hU]; exact (hfac w).2)
  have hUo : IsOpen (𝔢.U : Set (FA E n)) := 𝔢.isOpen
  have hUc : IsCompact (𝔢.U : Set (FA E n)) :=
    (AdelicGLn.isCompact_integralFiniteGL E n).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hUo) 𝔢.le
  have hlc : IsLocallyConstant ((𝔢.U : Set (FA E n)).indicator (1 : FA E n → ℂ)) := by
    rw [← LocallyConstant.coe_charFn ℂ (⟨Subgroup.isClosed_of_isOpen _ hUo, hUo⟩ : IsClopen (𝔢.U : Set (FA E n)))]
    exact LocallyConstant.isLocallyConstant _
  have hcs : HasCompactSupport ((𝔢.U : Set (FA E n)).indicator (1 : FA E n → ℂ)) :=
    HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _
  let φ : TF E n := ⟨⟨(𝔢.U : Set (FA E n)).indicator (1 : FA E n → ℂ), hlc.continuous⟩, hcs⟩
  have hφx : ∀ x, φ x = (𝔢.U : Set (FA E n)).indicator 1 x := fun _ => rfl
  have hoff : ∀ v ∉ insert q L.S, (L.UE v : Set (GL (Fin n) (CompletionsOver E v))) = unitSet E n v := fun v hv =>
    (L.off v (fun h => hv (Finset.mem_insert_of_mem h)) (fun h => hv (Finset.mem_insert.2 (Or.inl h)))).2.2.1
  have hgt : 𝔢.g = tens 𝔢.a₀ φ := by
    ext x
    rw [hg x, ha]
    refine (UpperTheory.ConvolutionTheory.Tf.avgTens E n hn aE φ _ fun g => ?_).1 x
    have key : ∏ᶠ v, L.φ v (mapGL n (atFin v) g) = φ (CuspidalSpectrum.finPart E n g) := by
      have h := finprod_ind (insert q L.S) L.UE hoff (CuspidalSpectrum.finPart E n g)
      simp only [pv_finPart] at h
      simp only [hφ]
      rw [h, hφx, hU]
    change _ * ∏ᶠ v, L.φ v (mapGL n (atFin v) g) = aE _ * φ _
    rw [key]
    congr 1
  obtain ⟨⟨c, hc, -, hop⟩, hsm⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.tensAmp E n hn μ 𝔢.toAmp φ hφx
  have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hRop : Rop μ 𝔢.g = (c : ℂ) • 𝔢.toAmp.A := by
    rw [hgt]
    exact hop
  have hsm' : (c : ℂ)⁻¹ • 𝔢.g = tens 𝔢.a₀ ((c : ℂ)⁻¹ • φ) := by
    rw [hgt]
    exact (((UpperTheory.ConvolutionTheory.Tf.tensApply E n hn 𝔢.a₀ φ).2.2.2.2 _).2).symm
  have haop : Rop μ ((c : ℂ)⁻¹ • 𝔢.g) = 𝔢.toAmp.A := by
    obtain ⟨m, hm, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx E n hn).2.1 μ 𝔢.ν
    have hrr := UpperTheory.ConvolutionTheory.Tf.rrTens E n hn μ 𝔢.ν m hC
    have h1 : Rop μ 𝔢.g = Oinf μ 𝔢.ν 𝔢.a₀ ∘L Ofin μ m φ := by
      rw [hgt]
      exact hrr _ _
    have h2 : Rop μ ((c : ℂ)⁻¹ • 𝔢.g) = Oinf μ 𝔢.ν 𝔢.a₀ ∘L Ofin μ m ((c : ℂ)⁻¹ • φ) := by
      rw [hsm']
      exact hrr _ _
    rw [h2, ((UpperTheory.ConvolutionTheory.Tf.opAlg E n μ 𝔢.ν m).2.2.1 _ 𝔢.a₀ φ).2, ContinuousLinearMap.comp_smul, ← h1, hRop,
      smul_smul, inv_mul_cancel₀ hcc, one_smul]
  have hasm : IsLeftSmooth ((c : ℂ)⁻¹ • 𝔢.g : TG E n) := by
    rw [hgt]
    exact hsm _
  have hcases : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  let Uq : ZMod 2 → LL μ →L[ℂ] LL μ := fun i => if i = 0 then Uiw μ w₀.1 ν else Uiw μ w₁.1 ν
  have h0 : Uq 0 = Uiw μ w₀.1 ν := if_pos rfl
  have h1 : Uq 1 = Uiw μ w₁.1 ν := if_neg (by decide)
  have hin : ∀ w : PlacesOver E q, Inner μ (Uiw μ w.1 ν) := fun w =>
    (UpperTheory.ConvolutionTheory.Tf.innerOps E n μ).2.2.2.2.2 w.1 _ _ (iw_oc μ w.1).1 (iw_oc μ w.1).2
  have hcm : Commute (Uiw μ w₀.1 ν) (Uiw μ w₁.1 ν) :=
    hop_comm hne _ _ _ _ (iw_oc μ w₀.1).1 (iw_oc μ w₀.1).2 (iw_oc μ w₁.1).1 (iw_oc μ w₁.1).2
  have hP : ∀ w w' : PlacesOver E q, σ • w.1 = w'.1 →
      (Rop μ 𝔢.g ∘L θ.U) ∘L Uiw μ w.1 ν = Uiw μ w'.1 ν ∘L (Rop μ 𝔢.g ∘L θ.U) := by
    intro w w' h
    have h1 := UpperTheory.galoisTwist_comp_uOperator_eq_uOperator_smul_place F E σ n hn μ θ hθ w.1 ν
    rw [h] at h1
    have h2 : Rop μ 𝔢.g ∘L Uiw μ w'.1 ν = Uiw μ w'.1 ν ∘L Rop μ 𝔢.g := by
      have h3 : Commute (Rop μ 𝔢.g) (Uiw μ w'.1 ν) := by
        rw [hRop]
        exact (hA w').symm.smul_left _
      exact h3.eq
    rw [ContinuousLinearMap.comp_assoc, h1, ← ContinuousLinearMap.comp_assoc, h2, ContinuousLinearMap.comp_assoc]
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  refine ⟨⟨𝔢.toAmp, (c : ℂ)⁻¹ • 𝔢.g, haop, hasm, 𝔢.g, 𝔢.g_smooth, Uq, ?_, ?_, ?_, ?_⟩, φ, w₁, rfl, rfl, ?_, ?_, hφx, hgt,
    (c : ℂ)⁻¹, inv_ne_zero hcc, rfl⟩
  · intro i
    rcases hcases i with rfl | rfl
    · rw [h0]; exact hin w₀
    · rw [h1]; exact hin w₁
  · intro i k
    rcases hcases i with rfl | rfl <;> rcases hcases k with rfl | rfl
    · exact Commute.refl _
    · rw [h0, h1]; exact hcm
    · rw [h0, h1]; exact hcm.symm
    · exact Commute.refl _
  · intro i
    rcases hcases i with rfl | rfl
    · rw [h0]; exact hA w₀
    · rw [h1]; exact hA w₁
  · intro i
    rcases hcases i with rfl | rfl
    · rw [zero_add, h0, h1]; exact hP w₀ w₁ rfl
    · rw [h11, h0, h1]; exact hP w₁ w₀ hw10
  · exact h0.trans hq0.symm
  · exact h1
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem transfer {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a b : ℕ}
    {μ : Measure (normOneGL E a)} [μ.IsHaarMeasure] {μ' : Measure (normOneGL E b)} [μ'.IsHaarMeasure]
    {π : CuspSub E a} {π' : CuspSub E b} {V : Submodule ℂ (LL μ)} {V' : Submodule ℂ (LL μ')}
    (h : Dp.Carries μ π V) (h' : Dp.Carries μ' π' V')
    (e : (⟨a, CG.mk π⟩ : Σ c, CG E c) = ⟨b, CG.mk π'⟩) :
    a = b ∧ ∀ S m B, At μ' S V' m B → At μ S V m B := by
  obtain ⟨rfl, e2⟩ := Sigma.mk.inj_iff.1 e
  obtain rfl : π = π' := (Dp.isoEq E a π π').1 (Quotient.exact (eq_of_heq e2))
  refine ⟨rfl, fun S m B hA => ⟨fun τ => ?_, fun w hw => ?_⟩⟩
  · exact (Dp.sInfIff E a μ π V h τ _).2 ((Dp.sInfIff E a μ' π V' h' τ _).1 (hA.1 τ))
  · exact (Dp.sSatIff E a μ π V h w _).2 ((Dp.sSatIff E a μ' π V' h' w _).1 (hA.2 w hw))

private theorem core {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {ι κ : Type} [Fintype ι] [Fintype κ]
    (d : ι → ℕ) (d' : κ → ℕ) (hd : ∀ i, 0 < d i) (hd' : ∀ j, 0 < d' j)
    (μ : ∀ i, Measure (normOneGL E (d i))) [∀ i, (μ i).IsHaarMeasure]
    (μ' : ∀ j, Measure (normOneGL E (d' j))) [∀ j, (μ' j).IsHaarMeasure]
    (V : ∀ i, Submodule ℂ (LL (μ i))) (V' : ∀ j, Submodule ℂ (LL (μ' j)))
    (hV : ∀ i, IsSummand (μ i) (V i)) (hV' : ∀ j, IsSummand (μ' j) (V' j)) (S : Set (Pl E)) (hS : S.Finite)
    (lam : ι → ℂ) (B : ι → Pl E → Multiset ℂ) (B' : κ → Pl E → Multiset ℂ)
    (hB : ∀ i, ∀ w ∉ S, SSat (μ i) (V i) w (B i w)) (hB' : ∀ j, ∀ w ∉ S, SSat (μ' j) (V' j) w (B' j w))
    (e : ∀ w ∉ S, ∑ j, B' j w = ∑ i, (B i w).map (· * (Ideal.absNorm w.asIdeal : ℂ) ^ (-lam i))) :
    ∃ s : ι ≃ κ, ∀ i, d i = d' (s i) ∧ ∀ S m C, At (μ' (s i)) S (V' (s i)) m C → At (μ i) S (V i) m C := by
  choose π hπ using fun i => (Dp.exCusp E (d i) (μ i) (V i) (hV i)).exists
  choose π' hπ' using fun j => (Dp.exCusp E (d' j) (μ' j) (V' j) (hV' j)).exists
  have hn : ∀ i, GlobalTheory.DiscSpec.IsNormalised (π i) := fun i =>
    (Dp.normIff E _ _).2 ((Dp.exSummand E _ _ _ _).1 (hπ i)).1
  have hn' : ∀ j, GlobalTheory.DiscSpec.IsNormalised (π' j) := fun j =>
    (Dp.normIff E _ _).2 ((Dp.exSummand E _ _ _ _).1 (hπ' j)).1
  obtain ⟨s, hs⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E ι κ d d'
    (fun i => (CG.mk (π i)).twist (GlobalTheory.CuspRep.Model.absC E (lam i)))
    (fun j => (CG.mk (π' j)).twist (GlobalTheory.CuspRep.Model.absC E 0)) hd hd' (by
    filter_upwards [hS.compl_mem_cofinite] with w hw
    choose A hA hA1 using fun i => (Dp.sSatIff E _ (μ i) (π i) (V i) (hπ i) w _).1 (hB i w hw)
    choose A' hA' hA1' using fun j => (Dp.sSatIff E _ (μ' j) (π' j) (V' j) (hπ' j) w _).1 (hB' j w hw)
    refine ⟨fun i => (A i).map (· * (GlobalTheory.CuspRep.Model.absC E (lam i)).val w), A',
      fun i => PositivityTheory.Rg.Rs.StrStepB.hasSat_twist_absC (π i) (hA1 i) (lam i), fun j => ?_, ?_⟩
    · rw [PositivityTheory.Rg.Rs.StrStepB.absC_zero, CG.twist_one]
      exact hA1' j
    · apply Multiset.map_injective (f := fun b : ℂˣ => (b : ℂ)) (fun a b e => Units.ext e)
      have h1 := map_sum (Multiset.mapAddMonoidHom fun b : ℂˣ => (b : ℂ)) A' Finset.univ
      have h2 := map_sum (Multiset.mapAddMonoidHom fun b : ℂˣ => (b : ℂ))
        (fun i => (A i).map (· * (GlobalTheory.CuspRep.Model.absC E (lam i)).val w)) Finset.univ
      refine h2.trans (Eq.trans ?_ h1.symm)
      have h3 := e w hw
      simp only [hA, hA'] at h3
      refine Eq.trans ?_ h3.symm
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Multiset.coe_mapAddMonoidHom, Multiset.map_map, Function.comp_def, Units.val_mul,
        PositivityTheory.Rg.Rs.StrStepB.absC_val])
  exact ⟨s, fun i => transfer (hπ i) (hπ' (s i))
    (PositivityTheory.Rg.Rs.StrStepB.match_twist (hd i) _ _ (hn i) (hn' _) (hs i)).2⟩

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.rigidE :
    RigidE := by
  intro E _ _ _ τ₁ τ₂ hP S hS m₁ m₂ B₁ B₂ h₁ h₂
  have hs : ∀ j : Fin 2, IsSummand (BW.mu1 E 2) (![τ₁, τ₂] j) := by
    intro j
    fin_cases j
    · exact ⟨hP.irr₁.le, hP.irr₁.closed, hP.irr₁.inv, hP.irr₁.ne, hP.irr₁.irr⟩
    · exact ⟨hP.irr₂.le, hP.irr₂.closed, hP.irr₂.inv, hP.irr₂.ne, hP.irr₂.irr⟩
  have hB : ∀ j : Fin 2, ∀ w ∉ S, SSat (BW.mu1 E 2) (![τ₁, τ₂] j) w (![B₁, B₂] j w) := by
    intro j
    fin_cases j
    · exact h₁.2
    · exact h₂.2
  constructor
  · rintro b ⟨lam, m, B, hA, -, hw⟩
    obtain ⟨s, h⟩ := core b.d (fun _ : Fin 2 => 2) b.pos (fun _ => two_pos) b.μ (fun _ => BW.mu1 E 2) b.V ![τ₁, τ₂]
      b.summand hs S hS lam B ![B₁, B₂] (fun i => (hA i).2) hB fun w hS' => by
        rw [Fin.sum_univ_two]; exact hw w hS'
    refine ⟨by simpa using Fintype.card_congr s, fun i => (h i).1, s.symm 0, s.symm 1,
      s.symm.injective.ne (by decide), (h _).2 _ _ _ ?_, (h _).2 _ _ _ ?_⟩
    · rw [s.apply_symm_apply]; exact h₁
    · rw [s.apply_symm_apply]; exact h₂
  · intro μ _ V hV hA
    obtain ⟨s, -⟩ := core (fun _ : Unit => 2 + 2) (fun _ : Fin 2 => 2) (fun _ => by norm_num) (fun _ => two_pos)
      (fun _ => μ) (fun _ => BW.mu1 E 2) (fun _ => V) ![τ₁, τ₂] (fun _ => hV) hs S hS (fun _ => 0)
      (fun _ w => B₁ w + B₂ w) ![B₁, B₂] (fun _ => hA.2) hB fun w _ => by simp
    simpa using Fintype.card_congr s
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem normV_split {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (w : HeightOneSpectrum (𝓞 M)) (h : GM.Split M (w.under (𝓞 K))) :
    Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := by
  haveI hl : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hs : Function.Surjective (completionMap (w.under (𝓞 K)) w) := h ⟨w, hl⟩
  have hb : Function.Bijective (Algebra.linearMap ((w.under (𝓞 K)).adicCompletion K) (w.adicCompletion M)) :=
    ⟨(completionMap (w.under (𝓞 K)) w).injective, hs⟩
  have h1 : w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    rw [← finrank_eq_ramificationIdx_mul_inertiaDeg M (w.under (𝓞 K)) w,
      ← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, Nat.eq_one_of_mul_eq_one_left h1, pow_one]

private theorem summand_of_irr {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    {τ : Submodule ℂ (L2 μ)} (h : CuspIrr μ τ) : IsSummand μ τ :=
  ⟨h.le, h.closed, h.inv, h.ne, h.irr⟩

private theorem sat_single {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {ι : Type} {κ : ι → Type}
    [∀ i, Fintype (κ i)] {m : (Σ i, κ i) → ℕ} (Q : ∀ a, CG E (m a))
    (hinj : Function.Injective (Sigma.fst : (Σ i, κ i) → ι)) (a : Σ i, κ i) {w : HeightOneSpectrum (𝓞 E)}
    {C : Multiset ℂˣ} (h : R.sumSat (m := fun k : κ a.1 => m ⟨a.1, k⟩) (fun k => Q ⟨a.1, k⟩) w C) : (Q a).HasSat w C := by
  obtain ⟨i, k₀⟩ := a
  obtain ⟨D, hD, rfl⟩ := h
  have hu : ∀ k : κ i, k = k₀ := fun k => by
    have : (⟨i, k⟩ : Σ i, κ i) = ⟨i, k₀⟩ := hinj rfl
    simpa using this
  rw [Fintype.sum_eq_single k₀ fun k hk => absurd (hu k) hk]
  exact hD k₀

private theorem sat_of_sigma {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n n' : ℕ} {p : CG E n} {q : CG E n'}
    (h : (⟨n, p⟩ : Σ a, CG E a) = ⟨n', q⟩) {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (hq : q.HasSat w B) :
    p.HasSat w B := by
  cases h
  exact hq

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.rigidF :
    T.LiftAll → RigidF := by
  intro hL F E _ _ _ _ _ _ _ _ σ h2 hgen τ₁ τ₂ θ₂ hP hgal h12 h21 SE SF hSE hSF m₁ m₂ B₁ B₂ hA₁ hA₂ b Λ' t' hb hbc
  have hp : (Module.finrank F E).Prime := h2 ▸ Nat.prime_two
  obtain ⟨-, hsw⟩ := swapAt F E σ h2 hgen τ₁ τ₂ θ₂ hP hgal h12 h21
  have s₁ := summand_of_irr hP.irr₁
  have s₂ := summand_of_irr hP.irr₂
  obtain ⟨π₁, c₁, -⟩ := Dp.exCusp E 2 (BW.mu1 E 2) τ₁ s₁
  obtain ⟨π₂, c₂, -⟩ := Dp.exCusp E 2 (BW.mu1 E 2) τ₂ s₂
  obtain ⟨P, hPt⟩ := T.famSat F (2 + 2) b SF hSF Λ' t' hb
  choose κ fκ m Q hm hne hQ using fun i => hL F E σ hgen hp (b.d i) (b.pos i) (P i)
  have hsum := R.liftSum F E hp (Fin b.r) κ b.d (fun a => m a.1 a.2) P (fun a => Q a.1 a.2) hQ
  have hN := (T.places F E hp).2.2.2.2.1
  have hund := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ (B : Fin 2 → Multiset ℂˣ) (B' : (Σ i, κ i) → Multiset ℂˣ),
      (∀ i, ((![CG.mk π₁, CG.mk π₂] : Fin 2 → CG E 2) i).HasSat w (B i)) ∧ (∀ a, (Q a.1 a.2).HasSat w (B' a)) ∧
        ∑ i, B i = ∑ a, B' a := by
    filter_upwards [hsum, hSE.eventually_cofinite_notMem, hund.eventually hSF.eventually_cofinite_notMem] with w hw hwE hwF
    obtain ⟨B, ⟨B1, hB1, e1⟩, D, hD, eD⟩ := hw (UpperTheory.ConvolutionTheory.resDeg F w) (hN w)
    obtain ⟨C, ⟨C1, hC1, e2⟩, e⟩ := hPt _ hwF
    obtain ⟨A₁, a₁, h₁⟩ := (Dp.sSatIff E 2 _ π₁ τ₁ c₁ w _).1 (hA₁.2 w hwE)
    obtain ⟨A₂, a₂, h₂⟩ := (Dp.sSatIff E 2 _ π₂ τ₂ c₂ w _).1 (hA₂.2 w hwE)
    have e3 : B = C := by
      rw [e1, e2]
      exact Finset.sum_congr rfl fun i _ => (hB1 i).unique (hC1 i)
    refine ⟨![A₁, A₂], D, fun i => ?_, hD, ?_⟩
    · fin_cases i
      exacts [h₁, h₂]
    · have hb := hbc w hwE
      rw [bcSat, e, a₁, a₂, Multiset.map_map] at hb
      refine Multiset.map_injective (f := fun z : ℂˣ => (z : ℂ)) (fun a b e => Units.ext e) ?_
      rw [← eD, e3, Fin.sum_univ_two, Multiset.map_map]
      simpa using hb
  obtain ⟨s, hs⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E (Fin 2) (Σ i, κ i) (fun _ => 2) (fun a => m a.1 a.2)
    ![CG.mk π₁, CG.mk π₂] (fun a => Q a.1 a.2) (fun _ => by norm_num) (fun a => hm a.1 a.2) hev
  have hcard : Fintype.card (Σ i, κ i) = 2 := by simpa using (Fintype.card_congr s).symm
  have hsurj : Function.Surjective (Sigma.fst : (Σ i, κ i) → Fin b.r) := fun i => ⟨⟨i, (hne i).some⟩, rfl⟩
  have hinj : Function.Injective (Sigma.fst : (Σ i, κ i) → Fin b.r) := by
    refine ((Fintype.bijective_iff_surjective_and_card _).2 ⟨hsurj, ?_⟩).1
    have h1 := Fintype.card_le_of_surjective _ hsurj
    have h3 := b.two
    simp only [Fintype.card_fin] at h1 ⊢
    omega
  have hl0 : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ f : ℕ,
      Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 F)) ^ f →
        ∃ B, (P (s 0).1).HasSat (w.under (𝓞 F)) B ∧ (CG.mk π₁).HasSat w (B.map (· ^ f)) :=
    (hQ (s 0).1).mono fun w hw f hf => by
      obtain ⟨B, hB, hC⟩ := hw f hf
      exact ⟨B, hB, sat_of_sigma (hs 0) (sat_single (fun a => Q a.1 a.2) hinj (s 0) hC)⟩
  obtain ⟨X, hX, hlift⟩ : ∃ X : Set (HeightOneSpectrum (𝓞 E)), X.Finite ∧ ∀ w ∉ X, ∀ f : ℕ,
      Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 F)) ^ f →
        ∃ B, (P (s 0).1).HasSat (w.under (𝓞 F)) B ∧ (CG.mk π₁).HasSat w (B.map (· ^ f)) :=
    ⟨_, Filter.eventually_cofinite.1 hl0, fun w hw => not_not.1 hw⟩
  have hev2 : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, w ∉ SE ∧ SSat (BW.mu1 E 2) τ₁ w (B₂ w) := by
    filter_upwards [hund.eventually (R.decomp F E hp), hund.eventually (hX.image fun w => w.under (𝓞 F)).eventually_cofinite_notMem,
      hSE.eventually_cofinite_notMem] with w hd hy hwE
    refine ⟨hwE, ?_⟩
    have hg : ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) → w' ∉ X :=
      fun w' hu hc => hy ⟨w', hc, hu⟩
    have hq : 1 < Formalism.ConjugateSelfDual.normV (w.under (𝓞 F)) := NumberField.HeightOneSpectrum.one_lt_absNorm _
    rcases hd with ⟨hc, hn⟩ | ⟨-, hn⟩
    · obtain ⟨⟨w', hu⟩, hne', -⟩ := (Nat.card_eq_two_iff' (⟨w, rfl⟩ : {u : HeightOneSpectrum (𝓞 E) // u.under (𝓞 F) = w.under (𝓞 F)})).1
        (hc.trans h2)
      have hne : w ≠ w' := fun e => hne' (Subtype.ext e.symm)
      obtain ⟨B, hB, hw1⟩ := hlift w (hg w rfl) 1 (by rw [pow_one]; exact hn w rfl)
      obtain ⟨B', hB', hw2⟩ := hlift w' (hg w' hu) 1 (by rw [pow_one, hu]; exact hn w' hu)
      rw [hu] at hB'
      obtain rfl := hB.unique hB'
      obtain ⟨Y, eY, hY⟩ := (Dp.sSatIff E 2 _ π₁ τ₁ c₁ w' _).1 ((hsw w w' hu.symm (Or.inl hne) _).1 (hA₂.2 w hwE))
      have hY' : (CG.mk π₁).HasSat w' Y := hY
      obtain rfl : Y = B.map (· ^ 1) := hY'.unique hw2
      exact (Dp.sSatIff E 2 _ π₁ τ₁ c₁ w _).2 ⟨_, eY, hw1⟩
    · have hns : ¬ GM.Split E (w.under (𝓞 F)) := fun h => by
        have e := (hn w rfl).symm.trans (normV_split w h)
        rw [h2] at e
        have : (2 : ℕ) = 1 := Nat.pow_right_injective hq (e.trans (pow_one _).symm)
        omega
      exact (hsw w w rfl (Or.inr hns) _).1 (hA₂.2 w hwE)
  have hτ : τ₁ = τ₂ := Dp.atInj E 2 _ τ₁ τ₂ s₁ s₂ _ (Filter.eventually_cofinite.1 hev2) B₂
    (fun w hw => (not_not.1 hw).2) (fun w hw => hA₂.2 w (not_not.1 hw).1)
  have ho := hP.orth
  rw [← hτ] at ho
  exact hP.irr₁.ne (Submodule.isOrtho_self.1 ho)
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section SlopeTestRemainingChoices

private theorem fin_pre {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Set (Pl F)) (hS : S.Finite) : {w : Pl E | w.under (𝓞 F) ∈ S}.Finite := by
  have hfib : ∀ v : Pl F, {w : Pl E | w.under (𝓞 F) = v}.Finite := fun v => by
    refine (Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_
    rintro w rfl
    exact ⟨⟨w, ⟨rfl⟩⟩, rfl⟩
  exact hS.preimage' fun v _ => hfib v

private theorem under_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext (w.2.over).symm

private theorem at_mono {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    {S S' : Set (Pl K)} (h : S ⊆ S') {V : Submodule ℂ (LL μ)} {Λ : (K →+* ℂ) → Multiset ℂ} {t : Pl K → Multiset ℂ}
    (H : At μ S V Λ t) : At μ S' V Λ t :=
  ⟨H.1, fun w hw => H.2 w fun h' => hw (h h')⟩

private theorem geo_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n l : ℕ}
    {μE : Measure (G1 E n)} [μE.IsHaarMeasure] {μF : Measure (G1 F n)} [μF.IsHaarMeasure] {θ : Twist μE}
    {𝔢 𝔢' : Side θ l} {𝔣 : Side (Twist.id μF) l} {c : ℂ} (h1 : 𝔢'.toAmp = 𝔢.toAmp) (h2 : 𝔢'.g = 𝔢.g)
    (h3 : 𝔢'.Uq 0 = 𝔢.Uq 0) (h : GeoPair 𝔢 𝔣 c) : GeoPair 𝔢' 𝔣 c := by
  unfold GeoPair Side.Rep at h ⊢
  rw [h1, h2, h3]
  exact h

private theorem hecke_smul {K : Type} [Field K] [NumberField K] {n : ℕ} {D : TypeDat K n} {f : TG K n}
    (h : D.Hecke f) (c : ℂ) : D.Hecke (c • f) := by
  intro g
  have e1 : ∀ x, (c • f) x = c * f x := fun x => rfl
  simp only [e1]
  refine ⟨?_, ?_⟩
  · simp only [mul_left_comm (D.e _)]
    rw [integral_const_mul, (h g).1]
  · simp only [mul_assoc]
    rw [integral_const_mul, (h g).2]

private theorem ind_inv {G : Type} [Group G] (U : Subgroup G) (φ : G → ℂ)
    (hφ : ∀ x, φ x = (U : Set G).indicator 1 x) : ∀ u ∈ U, ∀ x, φ (u * x) = φ x ∧ φ (x * u) = φ x := by
  intro u hu x
  have h1 : u * x ∈ U ↔ x ∈ U := Subgroup.mul_mem_cancel_left U hu
  have h2 : x * u ∈ U ↔ x ∈ U := Subgroup.mul_mem_cancel_right U hu
  simp only [hφ, Set.indicator, SetLike.mem_coe, h1, h2, Pi.one_apply, and_self]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.coreInd :
    CIx → GM.GM → T.LiftAll → CoreInd := by
  intro hCI hGM hLift F E _ _ _ _ _ _ _ _ σ hσ hgen τ₁ τ₂ θ₂ hpair hgal₂ hsw₁ hsw₂ S hSsp hSunr m₁ m₂ B₁ B₂ hA₁ hA₂ μF _
  have hpr : (Module.finrank F E).Prime := hσ ▸ Nat.prime_two
  have hpl := UpperTheory.ConvolutionTheory.T.places F E hpr
  obtain ⟨q, hqsp, hqS⟩ := hpl.1.exists_notMem_finset S
  have hqsp' : GM.Split E q := hqsp
  obtain ⟨w₀⟩ := hpl.2.2.1 q
  have hf1 := fin_pre (E := E) (S : Set (Pl F)) S.finite_toSet
  have hf2 := fin_pre (E := E) (insert q (S : Set (Pl F))) (S.finite_toSet.insert q)
  obtain ⟨SE', hSE'⟩ : ∃ SE' : Finset (Pl E), ∀ w, w ∈ SE' ↔ w.under (𝓞 F) ∈ S :=
    ⟨hf1.toFinset, fun w => by simp⟩
  obtain ⟨SE, hSE⟩ : ∃ SE : Finset (Pl E), ∀ w, w ∈ SE ↔ w.under (𝓞 F) ∈ S ∨ w.under (𝓞 F) = q :=
    ⟨hf2.toFinset, fun w => by simp [or_comm]⟩
  obtain ⟨pp⟩ := (UpperTheory.ConvolutionTheory.L1.infSplit F E σ hgen 1 hσ).1 inferInstance
  obtain ⟨D, -⟩ := (UpperTheory.ConvolutionTheory.L1.infSplit F E σ hgen 1 hσ).2 pp
  obtain ⟨κF, eF, κ, e, κ₂, p₁, p₂, k₀, hIF, hSq, hAL⟩ := archEx F E σ hσ hgen τ₁ τ₂ θ₂ hpair hgal₂ hsw₁ hsw₂ D
  have hsph₁ : SphOff (BW.mu1 E 2) τ₁ SE' := fun w hw => (hA₁.2 w fun h => hw ((hSE' w).2 h)).2.1
  have hsph₂ : SphOff (BW.mu1 E 2) τ₂ SE' := fun w hw => (hA₂.2 w fun h => hw ((hSE' w).2 h)).2.1
  obtain ⟨U₀, f, hU₀, hf0, hsec, hfA, hfF⟩ := hAL.ex SE' hsph₁ hsph₂
  obtain ⟨L, U, hLS, hU, hUle, hUq, hlev, hLφ, htw⟩ :=
    locSm F E σ hσ hgen (2 + 2) (by norm_num) q w₀ S hqS hSunr hSsp U₀ hU₀ SE hSE
  have hLL := (UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.levLaws (K := E) (2 + 2) SE).1 U hU
  obtain ⟨Dt, hTy, hSt⟩ := typeOf E (2 + 2) κ e hAL.idem (levOn SE U) hLL.2 hLL.1.2
  have hflat := (UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.secTr (BW.mu1 E 2) τ₁ τ₂ κ e hAL.idem).2.1 f hsec.cont
  have hle : levOn SE U ≤ levOn SE' U₀ := by
    intro u hu
    have hu' : ∀ v, finAt v (finEmb E (2 + 2) u) ∈
        (if v ∈ SE then U v else GLnLocal.integralGL (v.adicCompletion E) (2 + 2)) := hu
    show ∀ v, finAt v (finEmb E (2 + 2) u) ∈
        (if v ∈ SE' then U₀ v else GLnLocal.integralGL (v.adicCompletion E) (2 + 2))
    intro v
    have h := hu' v
    by_cases h1 : v ∈ SE'
    · have h1' := (hSE' v).1 h1
      rw [if_pos ((hSE v).2 (Or.inl h1')), ] at h
      rw [if_pos h1]
      exact hUle v h1' h
    · rw [if_neg h1]
      split_ifs at h with h2
      · exact (hU v).2 h
      · exact h
  have hfF' : FixF (levOn SE U) f := fun u hu g => hfF u (hle hu) g
  obtain ⟨θ, hθK⟩ := UpperTheory.ConvolutionTheory.K.galTwistEx E (2 + 2) (BW.mu1 E (2 + 2)) σ.toRingEquiv
  have hgl := galLoc F E σ hσ hgen (2 + 2) (by norm_num) (BW.mu1 E (2 + 2)) θ
  have hθ : IsGalTwist σ θ := hgl.1.2 hθK
  obtain ⟨hinv, harc, -⟩ := hgl.2 hθ
  have htw' := htw (BW.mu1 E (2 + 2)) θ hθ
  have hSta : Stable Dt θ := hSt (BW.mu1 E (2 + 2)) θ (harc D eF e hSq) htw' hinv
  have hpair' : Pair (BW.mu1 E 2) τ₂ τ₁ := ⟨hpair.irr₂, hpair.irr₁, hpair.orth.symm⟩
  obtain ⟨d, ⟨A⟩⟩ := lineEx E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₁ τ₂ hpair Dt
  obtain ⟨d', ⟨A'⟩⟩ := lineEx E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₂ τ₁ hpair' Dt
  obtain ⟨⟨P, hP⟩, -⟩ := projEx E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₁ τ₂ hpair Dt d d' A A'
  obtain ⟨s, hs_sec, hs_op⟩ := convU E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₁ τ₂ hpair Dt d d' A A' σ.toRingEquiv θ θ₂
    hθK hgal₂ hSta hsw₁ hsw₂
  have hHH : Continuous (HP (K := E) 2 2) := (hpSpec (K := E)).2.2.2.1
  have hflc : Continuous (flat 0 f) :=
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hHH))).mul hsec.cont
  have hfne : flat 0 f ≠ 0 := fun h => hf0 ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.secTr (BW.mu1 E 2) τ₁ τ₂ κ e hAL.idem).2.2.1 f 0
    (h.trans (by funext x; simp [flat])))
  let νF : Measure (archGroup F (2 + 2)) := Measure.haar
  haveI hνE : (Measure.map (glueA D (2 + 2)) (Measure.pi fun _ => νF)).IsHaarMeasure :=
    (UpperTheory.ConvolutionTheory.L1.archBasic F E σ 1 D (2 + 2)).2.2.2.2.2.2.1 νF
  obtain ⟨b, a, aE, aF, hsl, hBi, g₀, hg₀⟩ := ampEx F E σ D (2 + 2) (by norm_num) κF eF κ e hIF hAL.idem hSq
    (Measure.map (glueA D (2 + 2)) (Measure.pi fun _ => νF)) νF rfl (flat 0 f) hflc hfne (hflat.1.2 hfA)
  obtain ⟨hAE, hAF⟩ := UpperTheory.ConvolutionTheory.L1.ampPosition F E σ 1 D (2 + 2) _ νF b a aE aF hsl
  have hAP : GM.ArchPair σ _ νF aE aF 1 := @UpperTheory.ConvolutionTheory.L1.pairPosition F E _ _ _ _ _ _ _ σ 1 hσ D (2 + 2) _ _ νF _ b a aE aF hsl
  obtain ⟨cκ, hcκ, hG⟩ := hGM F E σ hgen hpr (2 + 2) (by norm_num) (BW.mu1 E (2 + 2)) μF θ hθ q w₀ hqsp' _ νF aE aF 1 one_pos
    (hAE (BW.mu1 E (2 + 2))) (hAF μF) (@hAP)
  obtain ⟨ν, hν⟩ := UpperTheory.ConvolutionTheory.T.goodEx (2 + 2) (by norm_num)
  have hG' := hG L ν hν
  rw [hσ] at hG'
  obtain ⟨𝔢, 𝔣, h𝔢, h𝔣, hgeo⟩ := hG'
  obtain ⟨𝔢', φ, w₁, h1, h2, h3, h4, hφ, hten, c, hc, hca⟩ :=
    sideX F E σ hσ hgen (2 + 2) (by norm_num) (BW.mu1 E (2 + 2)) θ hθ q w₀ hqsp' L _ aE ν 𝔢 h𝔢 hLφ
  have hgeo' := geo_congr h1 h2 h3 hgeo
  have hU' : 𝔢'.toAmp.U = levOn SE U := by rw [h1]; exact h𝔢.2.2.2.1.trans hlev
  have ha₀ : 𝔢'.toAmp.a₀ = aE := by rw [h1]; exact h𝔢.2.1
  have hν' : 𝔢'.toAmp.ν = Measure.map (glueA D (2 + 2)) (Measure.pi fun _ => νF) := by rw [h1]; exact h𝔢.1
  have hSE𝔢 : ∀ w, w ∈ 𝔢'.toAmp.S ↔ w ∈ SE := fun w => by
    rw [h1, hSE w, ← hLS]; exact h𝔢.2.2.1 w
  have hUq0 : 𝔢'.Uq 0 = Uiw (BW.mu1 E (2 + 2)) w₀.1 ν := h3.trans h𝔢.2.2.2.2.2
  have hφ' : ∀ x, φ x = (levOn SE U : Set (FA E (2 + 2))).indicator 1 x := fun x => by
    rw [hφ x, ← hU', h1]
  have hinvφ := ind_inv (levOn SE U) φ hφ'
  have hBi' : BiA κ e 𝔢'.toAmp.a₀ := ha₀ ▸ hBi
  have hg_hecke : Dt.Hecke 𝔢'.g := hten ▸ hTy.hecke _ φ hBi' hinvφ
  have ha_hecke : Dt.Hecke 𝔢'.a := hca ▸ hecke_smul hg_hecke c
  have hlevel : Dt.Level (levOn SE U) := hTy.level
  have hsub : {w : Pl E | w.under (𝓞 F) ∈ S} ⊆ 𝔢'.toAmp.S := fun w hw =>
    (hSE𝔢 w).2 ((hSE w).2 (Or.inl hw))
  have hat₁ := at_mono hsub hA₁
  have hat₂ := at_mono hsub hA₂
  have hs₁ : IsSummand (BW.mu1 E 2) τ₁ := ⟨hpair.irr₁.le, hpair.irr₁.closed, hpair.irr₁.inv, hpair.irr₁.ne, hpair.irr₁.irr⟩
  have hs₂ : IsSummand (BW.mu1 E 2) τ₂ := ⟨hpair.irr₂.le, hpair.irr₂.closed, hpair.irr₂.inv, hpair.irr₂.ne, hpair.irr₂.irr⟩
  have hrE := rigidE E τ₁ τ₂ hpair 𝔢'.toAmp.S 𝔢'.toAmp.finS m₁ m₂ B₁ B₂ hat₁ hat₂
  have hw₀S : w₀.1 ∈ SE := (hSE _).2 (Or.inr (under_of w₀))
  have hw₁S : w₁.1 ∈ SE := (hSE _).2 (Or.inr (under_of w₁))
  have hI₀ := hUq w₀.1 (under_of w₀)
  have hI₁ := hUq w₁.1 (under_of w₁)
  have hUa := uiwAct E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₁ τ₂ hpair SE U hU Dt hlevel d d' A A'
  have hUb := uiwAct E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₂ τ₁ hpair' SE U hU Dt hlevel d' d A' A
  have hz : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  have hv : ∀ i : ZMod 2, ∃ s', Act A.J (𝔢'.Uq i) s' := fun i => by
    rcases hz i with rfl | rfl
    · rw [hUq0]; exact ((hUa _ hw₀S hI₀ ν).1).imp fun _ h => h.1
    · rw [h4]; exact ((hUa _ hw₁S hI₁ ν).1).imp fun _ h => h.1
  have hu : ∀ i : ZMod 2, ∃ s', Act A'.J (𝔢'.Uq i) s' := fun i => by
    rcases hz i with rfl | rfl
    · rw [hUq0]; exact ((hUb _ hw₀S hI₀ ν).1).imp fun _ h => h.1
    · rw [h4]; exact ((hUb _ hw₁S hI₁ ν).1).imp fun _ h => h.1
  choose vv hvv using hv
  choose uu huu using hu
  obtain ⟨βa, hβa⟩ := convR E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₂ τ₁ hpair' Dt d' d A' A 𝔢'.a ha_hecke
  obtain ⟨βg, hβg⟩ := convR E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₂ τ₁ hpair' Dt d' d A' A 𝔢'.g hg_hecke
  let 𝔵 : Fam 𝔢' :=
    { τ₁ := τ₁, τ₂ := τ₂, pair := hpair, m₁ := m₁, m₂ := m₂, B₁ := B₁, B₂ := B₂, at₁ := hat₁, at₂ := hat₂
      smo₁ := fun V hV hAt => UpperTheory.ConvolutionTheory.Dp.atInj E 2 (BW.mu1 E 2) V τ₁ hV hs₁ _ 𝔢'.toAmp.finS B₁ hAt.2 hat₁.2
      smo₂ := fun V hV hAt => UpperTheory.ConvolutionTheory.Dp.atInj E 2 (BW.mu1 E 2) V τ₂ hV hs₂ _ 𝔢'.toAmp.finS B₂ hAt.2 hat₂.2
      rigid := hrE.1, D := Dt, level := hU' ▸ hlevel, d := d, d' := d', A := A, A' := A', P := P, isP := hP
      σ := σ.toRingEquiv, θ₂ := θ₂, gal := hθK, gal₂ := hgal₂, stable := hSta, swap₁ := hsw₁, swap₂ := hsw₂
      s := s, s_sec := hs_sec, s_op := hs_op, a_hecke := ha_hecke, g_hecke := hg_hecke, βa := βa, βg := βg
      a_acts := hβa, g_acts := hβg, u := uu, v := vv, u_act := huu, v_act := hvv
      u_comm := by rw [hUq0]; exact (hUa _ hw₀S hI₀ ν).2 P hP }
  have hrig : ∀ (b : Datum F (2 + 2)) Λ' t', b.Pt 𝔣.toAmp.S Λ' t' →
      ¬ (𝔵.Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢'.toAmp.S, 𝔵.t w = bcSat t' w) := fun b Λ' t' hb h =>
    rigidF hLift F E σ hσ hgen τ₁ τ₂ θ₂ hpair hgal₂ hsw₁ hsw₂ 𝔢'.toAmp.S 𝔣.toAmp.S 𝔢'.toAmp.finS 𝔣.toAmp.finS
      m₁ m₂ B₁ B₂ hat₁ hat₂ b Λ' t' hb h.2
  obtain ⟨N, hN, hid⟩ := hCI F E (BW.mu1 E (2 + 2)) μF θ 𝔢' 𝔣 _ hgeo' 𝔵 hrig
  have hSpl : ∀ w ∈ SE, GM.Split E (w.under (𝓞 F)) ∧ ∀ w' : Pl E, w'.under (𝓞 F) = w.under (𝓞 F) → w' ∈ SE := by
    intro w hw
    refine ⟨?_, fun w' h => (hSE w').2 (h ▸ (hSE w).1 hw)⟩
    rcases (hSE w).1 hw with h | h
    · exact hSsp _ h
    · rw [h]; exact hqsp'
  obtain ⟨v₀, hv₀⟩ : f ∈ LinearMap.range A.sec :=
    (A.onto f).2 ⟨hsec, (hTy.fix f hsec.cont).2 ⟨hfA, hfF'⟩⟩
  have hnz : ∃ v g, ∫ y, 𝔢'.toAmp.a₀ y * flat 0 (𝔵.A.sec v) (g * archP E (2 + 2) y) ∂𝔢'.toAmp.ν ≠ 0 := by
    refine ⟨v₀, g₀, ?_⟩
    change ∫ y, 𝔢'.toAmp.a₀ y * flat 0 (A.sec v₀) (g₀ * archP E (2 + 2) y) ∂𝔢'.toAmp.ν ≠ 0
    rw [hv₀, ha₀, hν']
    exact hg₀
  obtain ⟨x, hx, hfr⟩ := famNe F E σ hσ hgen (BW.mu1 E (2 + 2)) θ hθ 𝔢' 𝔵 κ e κ₂ p₁ p₂ k₀ hAL SE U hU hSpl hU' hTy htw'
    w₀.1 hw₀S hI₀ ν hν.1.antitone hUq0 φ hφ' hten ⟨c, hc, hca⟩ hBi' hnz N hN
  obtain ⟨j, hj1, hj2⟩ := (hfr.and_eventually (hid x hx)).exists
  have hcusp : 𝔢'.tr (fun V => At (BW.mu1 E (2 + 2)) 𝔢'.toAmp.S V 𝔵.Λ 𝔵.t) x j = 0 := by
    have : {V : Submodule ℂ (LL (BW.mu1 E (2 + 2))) | IsSummand (BW.mu1 E (2 + 2)) V ∧
        V.map (θ.U : LL (BW.mu1 E (2 + 2)) →ₗ[ℂ] LL (BW.mu1 E (2 + 2))) = V ∧
        At (BW.mu1 E (2 + 2)) 𝔢'.toAmp.S V 𝔵.Λ 𝔵.t} = ∅ :=
      Set.eq_empty_of_forall_notMem fun V hV => hrE.2 (BW.mu1 E (2 + 2)) V hV.1 hV.2.2
    unfold Side.tr
    rw [this, finsum_mem_empty]
  rw [hcusp, zero_add] at hj2
  have hne : 𝔣.tr (fun V => ∃ Λ' t', At μF 𝔣.toAmp.S V Λ' t' ∧ 𝔵.Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢'.toAmp.S, 𝔵.t w = bcSat t' w) x j ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hj2
    exact hj1 ((mul_eq_zero.1 hj2).resolve_left (by norm_num))
  obtain ⟨V, hV, -, Λ', t', hAt, hΛ, ht⟩ : ∃ V : Submodule ℂ (LL μF), IsSummand μF V ∧
      V.map ((Twist.id μF).U : LL μF →ₗ[ℂ] LL μF) = V ∧
      ∃ Λ' t', At μF 𝔣.toAmp.S V Λ' t' ∧ 𝔵.Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢'.toAmp.S, 𝔵.t w = bcSat t' w := by
    by_contra hno
    apply hne
    have hemp : {V : Submodule ℂ (LL μF) | IsSummand μF V ∧ V.map ((Twist.id μF).U : LL μF →ₗ[ℂ] LL μF) = V ∧
        ∃ Λ' t', At μF 𝔣.toAmp.S V Λ' t' ∧ 𝔵.Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢'.toAmp.S, 𝔵.t w = bcSat t' w} = ∅ :=
      Set.eq_empty_of_forall_notMem fun V hV => hno ⟨V, hV⟩
    unfold Side.tr
    rw [hemp, finsum_mem_empty]
  exact ⟨V, Λ', t', hV, ⟨_, 𝔣.toAmp.finS, hAt⟩, hΛ,
    Filter.mem_of_superset 𝔢'.toAmp.finS.compl_mem_cofinite fun w hw => ht w hw⟩
end
