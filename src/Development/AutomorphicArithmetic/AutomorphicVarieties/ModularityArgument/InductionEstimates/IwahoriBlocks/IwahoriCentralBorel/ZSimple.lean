import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ParLaw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.BlockFrameConjugationIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.OpenStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.IndAmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.CoordMulInvCoordEqOne
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ExistsInjectionIntoL2Cusp
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TwoAtCharZero
import GroundTheory.AutomorphicForms.CompactFormulaCountable
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensSimple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvTransposeInvTranspose
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TSchur

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem finite_projection_one {K : Type} [Field K] [NumberField K] {n : ℕ} : fin1 (1 : FA K n) = 1 :=
  map_one (MultiplicityOne.finProj K n)

private theorem finite_adele_inclusion_mul {K : Type} [Field K] [NumberField K] {n : ℕ} (a b : FA K n) : fin1 (a * b) = fin1 a * fin1 b :=
  map_mul (MultiplicityOne.finProj K n) a b

private theorem zt0 {K : Type} [Field K] [NumberField K] : zt K 0 = 1 := by
  have h : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext (by simp)
  rw [zt, h, map_one]

private theorem lv0 {K : Type} [Field K] [NumberField K] (a b : G1 K 2) :
    ((lv a b 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (a : AdelicGLn.AdelicGL K 2) (b : AdelicGLn.AdelicGL K 2) := by
  rw [blkLaws.1, neg_zero, zt0, mul_one, mul_one]

private theorem hh0 {K : Type} [Field K] [NumberField K] (a b : G1 K 2) (x : G1 K (2 + 2)) :
    HH (lv a b 0 * x) = HH x := by
  have h := (hpSpec (K := K)).1 0 a b 0 x
  have h0 : (nn 0 : G1 K (2 + 2)) = 1 := unipOne_zero 2
  rwa [h0, one_mul, zero_add] at h

private theorem sec_ray {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)}
    {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f) (t : ℝ) (g : G1 K (2 + 2)) : f (lv 1 1 t * g) = f g := by
  refine hs.ray ⟨Real.exp t, Real.exp_pos t⟩ _ g ?_
  have h : (⟨Real.exp (-t), Real.exp_pos (-t)⟩ : {r : ℝ // 0 < r}) = (⟨Real.exp t, Real.exp_pos t⟩ : {r : ℝ // 0 < r})⁻¹ := by
    apply Subtype.ext
    change Real.exp (-t) = (Real.exp t)⁻¹
    rw [Real.exp_neg]
  rw [Subgroup.coe_mul, blkLaws.1, zt, zt, h]
  simp

private theorem reps_comb {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (τ : Submodule ℂ (L2 μ)) {ι : Type} (s : Finset ι) (φ : ι → G1 K n → ℂ) (c : ι → ℂ)
    (h : ∀ i, ∃ v ∈ τ, Reps μ v (φ i)) : ∃ v ∈ τ, Reps μ v (fun y => ∑ i ∈ s, c i * φ i y) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, τ.zero_mem, ?_⟩
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y hy
    simpa using hy
  | insert i s hi ih =>
    obtain ⟨v, hv, hr⟩ := ih
    obtain ⟨u, hu, hq⟩ := h i
    refine ⟨c i • u + v, τ.add_mem (τ.smul_mem _ hu) hv, ?_⟩
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_add (c i • u) v),
      (quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_smul (c i) u), hr, hq] with y e₁ e₂ e₃ e₄
    rw [e₁, Pi.add_apply, e₂, Pi.smul_apply, e₃, e₄, Finset.sum_insert hi, smul_eq_mul]

private theorem flat_lv {K : Type} [Field K] [NumberField K] (f : G1 K (2 + 2) → ℂ) (a b : G1 K 2) (x : G1 K (2 + 2)) :
    flat 0 f (lv a b 0 * x) = Complex.exp (2 * (HH x : ℂ)) * f (lv a b 0 * x) := by
  simp only [flat, zero_add]
  rw [show HP 2 2 (lv a b 0 * x) = HH x from hh0 a b x]

private theorem val_mem {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure]
    {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {κ : Measure (archCompact K (2 + 2))} {e : archCompact K (2 + 2) → ℂ} {κ₂ p₁ p₂ k₀}
    (hL : ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀) {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2))
    (hw : Function.Injective w) (h₄ : IsEmb w ι₄) {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f) (hfa : FixA κ e f)
    {U : ∀ v : Pl K, Subgroup (Gw (2 + 2) v)} (hU : Lev U) (hfU : FixF (levOn (im w) U) f) (g : GS (2 + 2) w) :
    (fun m : G1 K 2 × G1 K 2 => flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g))) ∈
      tensFn (Xs μ₂ τ₁ κ₂ p₁ (im w)) (Xs μ₂ τ₂ κ₂ p₂ (im w)) := by
  obtain ⟨d, φ, ψ, hφ, hψ, hx⟩ := hs.levi (arc1 k₀ * fin1 (ι₄ g))
  have hx' : ∀ a b, f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g)) = ∑ i, φ i a * ψ i b := fun a b =>
    hx a b _ (by rw [mul_assoc, Subgroup.coe_mul (x := lv a b 0), lv0])
  obtain ⟨U₂, hU₂, hlev⟩ := levBlock w ι₄ hw h₄ U hU g
  have hv := hL.val f hs hfa (ι₄ g)
  have hcl : Continuous fun p : G1 K 2 × G1 K 2 => f (lv p.1 p.2 0 * arc1 k₀ * fin1 (ι₄ g)) :=
    hs.cont.comp (((blkLaws (K := K)).2.2.2.1.comp
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))).mul continuous_const |>.mul continuous_const)
  have hsplit₁ : ∀ a b (u : G1 K 2), lv (a * u) b 0 = lv a b 0 * lv u 1 0 := fun a b u => by
    rw [blkLaws.2.1]; simp
  have hsplit₂ : ∀ a b (u : G1 K 2), lv a (b * u) 0 = lv a b 0 * lv 1 u 0 := fun a b u => by
    rw [blkLaws.2.1]; simp
  have hF : (fun m : G1 K 2 × G1 K 2 => flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g))) =
      Complex.exp (2 * (HH (arc1 k₀ * fin1 (ι₄ g)) : ℂ)) • fun m : G1 K 2 × G1 K 2 => f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g)) := by
    funext m
    rw [mul_assoc, flat_lv]
    simp [mul_assoc]
  rw [hF]
  refine Submodule.smul_mem _ _ ((tensLaws _ _).2 _ d φ ψ (fun x => hx' x.1 x.2) (fun b => ?_) (fun a => ?_))
  · refine Submodule.subset_span ⟨hcl.comp (continuous_id.prodMk continuous_const), ?_, hv.1 b, U₂, hU₂, fun u hu a => ?_⟩
    · have h := reps_comb μ₂ τ₁ Finset.univ φ (fun i => ψ i b) (fun i => let ⟨v, hv, hr⟩ := (hφ i).2; ⟨v, hv, hr⟩)
      simpa only [hx', mul_comm] using h
    · obtain ⟨u', hu', hk⟩ := hlev u hu 1 (one_mem _)
      have h1 := hk k₀
      rw [finite_projection_one] at h1
      have h2 : lv (a * fin1 u) b 0 * arc1 k₀ * fin1 (ι₄ g) = lv a b 0 * arc1 k₀ * fin1 (ι₄ g) * fin1 u' := by
        rw [hsplit₁, mul_assoc (lv a b 0), mul_assoc (lv a b 0), h1]
        simp only [mul_assoc]
      show f (lv (a * fin1 u) b 0 * arc1 k₀ * fin1 (ι₄ g)) = f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g))
      rw [h2]
      exact hfU u' hu' _
  · refine Submodule.subset_span ⟨hcl.comp (continuous_const.prodMk continuous_id), ?_, hv.2 a, U₂, hU₂, fun u hu b => ?_⟩
    · have h := reps_comb μ₂ τ₂ Finset.univ ψ (fun i => φ i a) (fun i => let ⟨v, hv, hr⟩ := (hψ i).2; ⟨v, hv, hr⟩)
      simpa only [hx'] using h
    · obtain ⟨u', hu', hk⟩ := hlev 1 (one_mem _) u hu
      have h1 := hk k₀
      rw [finite_projection_one] at h1
      have h2 : lv a (b * fin1 u) 0 * arc1 k₀ * fin1 (ι₄ g) = lv a b 0 * arc1 k₀ * fin1 (ι₄ g) * fin1 u' := by
        rw [hsplit₂, mul_assoc (lv a b 0), mul_assoc (lv a b 0), h1]
        simp only [mul_assoc]
      show f (lv a (b * fin1 u) 0 * arc1 k₀ * fin1 (ι₄ g)) = f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g))
      rw [h2]
      exact hfU u' hu' _

private theorem law_eq {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)}
    {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {r : ℕ} (w : Fin r → Pl K) (ι₂ : GS 2 w →* FA K 2) (ι₄ : GS (2 + 2) w →* FA K (2 + 2))
    (hw : Function.Injective w) (h₂ : IsEmb w ι₂) (h₄ : IsEmb w ι₄) {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f)
    (k₀ : archCompact K (2 + 2)) (p : ∀ i, PW (w i)) (g : GS (2 + 2) w) (m : G1 K 2 × G1 K 2) :
    flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p * g))) =
      (dS w p : ℂ) * flat 0 f (lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 * arc1 k₀ * fin1 (ι₄ g)) := by
  obtain ⟨hA, hB⟩ := parLaw w ι₂ ι₄ hw h₂ h₄
  obtain ⟨X, t, hX, ht⟩ := hB p
  obtain ⟨X', hX'⟩ := hA m.1 m.2 0 X
  have hc : Commute (arc1 k₀) (fin1 (ι₄ (piIncl (fun i => PW (w i)) p))) := (levLaws (K := K) (2 + 2) (im w)).2.2.1 k₀ _
  have key : lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p * g)) =
      nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g)) := by
    have hl : lv m.1 m.2 0 * lv (blocks ι₂ p).1 (blocks ι₂ p).2 t = lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t := by
      rw [blkLaws.2.1, zero_add]
    rw [map_mul, finite_adele_inclusion_mul, ← hl]
    calc lv m.1 m.2 0 * arc1 k₀ * (fin1 (ι₄ (piIncl (fun i => PW (w i)) p)) * fin1 (ι₄ g))
        = lv m.1 m.2 0 * (arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p))) * fin1 (ι₄ g) := by simp only [mul_assoc]
      _ = lv m.1 m.2 0 * (fin1 (ι₄ (piIncl (fun i => PW (w i)) p)) * arc1 k₀) * fin1 (ι₄ g) := by rw [hc.eq]
      _ = (lv m.1 m.2 0 * nn X) * lv (blocks ι₂ p).1 (blocks ι₂ p).2 t * (arc1 k₀ * fin1 (ι₄ g)) := by
          rw [hX]; simp only [mul_assoc]
      _ = _ := by rw [hX']; simp only [mul_assoc]
  have hray : lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t =
      lv 1 1 t * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 := by
    rw [blkLaws.2.1]; simp
  have hf : f (nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g))) =
      f (lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 * (arc1 k₀ * fin1 (ι₄ g))) := by
    rw [mul_assoc, hs.unip, hray, mul_assoc, sec_ray hs]
  have hh := (hpSpec (K := K)).1 X' (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t (arc1 k₀ * fin1 (ι₄ g))
  rw [key, mul_assoc (lv _ _ 0), flat_lv, ← ht]
  simp only [flat, zero_add]
  rw [show HP 2 2 (nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g))) = t + HH (arc1 k₀ * fin1 (ι₄ g)) from hh, hf]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.evMem :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) κ₂ p₁ p₂ k₀, Pair μ₂ τ₁ τ₂ → ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι₂ : GS 2 w →* FA K 2) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₂ → IsEmb w ι₄ →
      ∀ φ ∈ Zs τ₁ τ₂ κ e (im w), ev ι₄ k₀ φ ∈ IndF (piIncl fun i => PW (w i)) (xS ι₂) (tensFn (Xs μ₂ τ₁ κ₂ p₁ (im w)) (Xs μ₂ τ₂ κ₂ p₂ (im w))) := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ _ hL r w ι₂ ι₄ hw h₂ h₄ φ hφ
  obtain ⟨hiff, hsm⟩ := zMem μ₂ τ₁ τ₂ κ e hL.idem
  have hop := (hsm w ι₄ hw h₄ φ hφ).1
  obtain ⟨f, hs, hfa, ⟨U, hU, hfU⟩, rfl⟩ := (hiff _ φ).1 hφ
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · refine ⟨fun g => val_mem hL w ι₄ hw h₄ hs hfa hU hfU g, fun p g => ?_⟩
    funext m
    have h := law_eq (τ₁ := τ₁) (τ₂ := τ₂) w ι₂ ι₄ hw h₂ h₄ hs k₀ p g m
    simpa [ev, xS, twist, rightReg, LinearMap.funLeft] using h
  · have hst : ∀ g, rS ι₄ g (flat 0 f) = flat 0 f →
        rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) g (ev ι₄ k₀ (flat 0 f)) = ev ι₄ k₀ (flat 0 f) := by
      intro g hg
      conv_rhs => rw [← hg]
      funext x m
      simp [ev, rS, rightReg, LinearMap.funLeft, mul_assoc]
    show IsOpen {g | rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) g (ev ι₄ k₀ (flat 0 f)) = ev ι₄ k₀ (flat 0 f)}
    refine isOpen_iff_mem_nhds.2 fun g₀ hg₀ => ?_
    have h1 : (1 : GS (2 + 2) w) ∈ {g | rS ι₄ g (flat 0 f) = flat 0 f} := by simp
    have hn : (fun x => g₀⁻¹ * x) ⁻¹' {g | rS ι₄ g (flat 0 f) = flat 0 f} ∈ 𝓝 g₀ :=
      ((continuous_const.mul continuous_id).continuousAt (x := g₀)).preimage_mem_nhds
        (hop.mem_nhds (by simpa using h1))
    filter_upwards [hn] with x hx
    have h2 := hst _ hx
    have h3 : x = g₀ * (g₀⁻¹ * x) := by group
    show rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) x _ = _
    rw [h3, map_mul, Module.End.mul_apply, h2]
    exact hg₀
end

section
section Par

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem unip_corner {a b : ℕ} {R : Type} [CommRing R] (X : UPos (a + b) a → R) :
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 1 ((unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ 0 (1 : Matrix (Fin b) (Fin b) R) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [unipMatrix, blockEntry_apply, Matrix.one_apply, Matrix.toBlocks₁₂, Fin.ext_iff] <;> omega

private theorem unip_any {a b : ℕ} {R : Type} [CommRing R] (B : Matrix (Fin a) (Fin b) R) : ∃ X : UPos (a + b) a → R,
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks 1 B 0 (1 : Matrix (Fin b) (Fin b) R) := by
  refine ⟨fun p => Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 B 0 0) p.1.1 p.1.2, ?_⟩
  rw [unip_corner]
  congr 1
  ext i j
  have : (Fin.castAdd b i : Fin (a + b)) ≠ Fin.natAdd a j := by
    simp [Fin.ext_iff]; omega
  simp [unipMatrix, blockEntry_apply, Matrix.toBlocks₁₂, this]

private theorem split_par {a b : ℕ} {R : Type} [CommRing R] (g : GL (Fin (a + b)) R)
    (h : (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ (c : GL (Fin a) R) (d : GL (Fin b) R) (X : UPos (a + b) a → R), g = unipGL X * blk c d := by
  have e1 : g.val.submatrix finSumFinEquiv finSumFinEquiv * g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv =
      (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R) := by
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hg : ∀ M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R, g.val.submatrix finSumFinEquiv finSumFinEquiv = M →
      g.val = M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rintro _ rfl
    simp
  generalize g.val.submatrix finSumFinEquiv finSumFinEquiv = M at *
  generalize g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv = N at *
  have hM := (Matrix.fromBlocks_toBlocks M).symm
  rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks N, h, h', Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at e1
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e1
  obtain ⟨e1, -, -, e2⟩ := e1
  obtain ⟨X, hX⟩ := unip_any (M.toBlocks₁₂ * N.toBlocks₂₂)
  refine ⟨⟨_, _, e1, mul_eq_one_comm.1 e1⟩, ⟨_, _, e2, mul_eq_one_comm.1 e2⟩, X, Units.ext ?_⟩
  have hX' : unipMatrix X = (Matrix.fromBlocks 1 (M.toBlocks₁₂ * N.toBlocks₂₂) 0 1).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hX]; simp
  rw [Units.val_mul, coe_unipGL, hX', hg M rfl]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_assoc, mul_eq_one_comm.1 e2, Matrix.mul_one]
  rw [← h, ← hM]

private theorem par_of_low {K : Type} [Field K] [NumberField K] (s : G1 K (2 + 2))
    (h : ((s : AdelicGLn.AdelicGL K (2 + 2)).val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : ((s : AdelicGLn.AdelicGL K (2 + 2))⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ X m₁ m₂ t, s = nn X * lv m₁ m₂ t := by
  obtain ⟨hlv, -, -, -, hdet, -⟩ := blkLaws (K := K)
  obtain ⟨a, d, X, hX⟩ := split_par (s : AdelicGLn.AdelicGL K (2 + 2)) h h'
  refine ⟨X, retractOne a, retractOne d, Real.log (detModule K 2 a).1, ?_⟩
  have h1 : detModule K 2 a * detModule K 2 d = 1 := by
    have := mem_normOneGL_iff_detModule.1 s.2
    rwa [hX, map_mul, mem_normOneGL_iff_detModule.1 (unipGL_mem_normOneGL _), one_mul, hdet] at this
  have z1 : zt K (Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 a) := by
    unfold zt
    congr 1
    exact Subtype.ext (Real.exp_log (detModule K 2 a).2)
  have z2 : zt K (-Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 d) := by
    unfold zt
    congr 1
    refine Subtype.ext ?_
    rw [eq_inv_of_mul_eq_one_right h1]
    show Real.exp (-Real.log _) = _
    rw [Real.exp_neg, Real.exp_log (detModule K 2 a).2]
    rfl
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, hlv, z1, z2, coe_retractOne, coe_retractOne, inv_mul_cancel_right, inv_mul_cancel_right]
  exact hX

private theorem low_of_borel {K : Type} [Field K] [NumberField K] {b : AdelicGLn.AdelicGL K (2 + 2)} (hb : b ∈ adelicBorel) :
    (b.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
  ext i j
  refine mem_adelicBorel.1 hb ?_
  show finSumFinEquiv (Sum.inl j) < finSumFinEquiv (Sum.inr i)
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  omega

end Par

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical NumberField.AdeleRing

section

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem snd_entry (x : AdelicGLn.FiniteAdelicGL K n) (a b : Fin n) :
    ((finEmb K n x : AdelicGLn.AdelicGL K n) a b).2 = x a b := by
  have h := AdelicGLn.prodEquiv_apply_snd K n (finEmb K n x) a b
  rw [prodEquiv_finEmb] at h
  exact h.symm

private theorem cf_snd (v : Pl K) (x : AdelicGLn.AdelicGL K n) : GM.cf v (AdelicGLn.prodEquiv K n x).2 = finAt v x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  change ((finEmb K n (AdelicGLn.prodEquiv K n x).2 : AdelicGLn.AdelicGL K n) a b).2 v = (x a b).2 v
  rw [snd_entry, AdelicGLn.prodEquiv_apply_snd]

private theorem cf_mul (v : Pl K) (x y : AdelicGLn.FiniteAdelicGL K n) : GM.cf v (x * y) = GM.cf v x * GM.cf v y := by
  unfold GM.cf
  rw [map_mul, finAt_mul]

private theorem central_borel (s : {r : ℝ // 0 < r}) : centralSection K n s ∈ adelicBorel := by
  refine mem_adelicBorel.2 ?_
  rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits]
  exact Matrix.blockTriangular_diagonal _

private theorem fin_borel (y : AdelicGLn.FiniteAdelicGL K n)
    (hy : ∀ v : Pl K, ∀ i j : Fin n, j < i → GM.cf v y i j = 0) : finEmb K n y ∈ adelicBorel := by
  refine mem_adelicBorel.2 fun i j hij => ?_
  have hij' : j < i := hij
  refine adele_ext (fun w => ?_) fun v => ?_
  · have e1 : (finEmb K n y i j).1 = (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) i j :=
      congrArg (fun z => z.1 i j) (prodEquiv_finEmb y)
    rw [e1, Matrix.one_apply_ne hij'.ne']
    rfl
  · exact hy v i j hij'

private theorem proj_borel (y : AdelicGLn.FiniteAdelicGL K n) (h : finEmb K n y ∈ adelicBorel) :
    (MultiplicityOne.finProj K n y : AdelicGLn.AdelicGL K n) ∈ adelicBorel := by
  rw [MultiplicityOne.coe_finProj]
  exact mul_mem h (inv_mem (central_borel _))

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.finIwa :
    ∀ {K : Type} [Field K] [NumberField K] {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₄ →
      ∀ (h : FA K (2 + 2)) (k : archCompact K (2 + 2)), ∃ X m₁ m₂ t g u, (∀ U, u ∈ levOn (im w) U) ∧
        arc1 k * fin1 h = nn X * lv m₁ m₂ t * arc1 k * fin1 (ι₄ g) * fin1 u := by
  intro K _ _ r w ι hw hι h k
  obtain ⟨-, -, hoff, hdec, hcomm, -⟩ := (embEx (K := K) (2 + 2) w hw).2 ι hι
  obtain ⟨b, hb, c, hc, e⟩ := exists_adelicBorel_mul_maxCompact (finEmb K (2 + 2) h)
  have hh : h = (AdelicGLn.prodEquiv K (2 + 2) b).2 * (AdelicGLn.prodEquiv K (2 + 2) c).2 := by
    have := congrArg (fun x => (AdelicGLn.prodEquiv K (2 + 2) x).2) e
    simpa [prodEquiv_finEmb, map_mul] using this
  obtain ⟨g₁, b', eb, hb'⟩ := hdec (AdelicGLn.prodEquiv K (2 + 2) b).2
  obtain ⟨g₂, u, eu, hu⟩ := hdec (AdelicGLn.prodEquiv K (2 + 2) c).2
  have hcb : ι g₂ * b' = b' * ι g₂ := (hcomm g₂ b' hb').eq
  have hh2 : h = ι (g₁ * g₂) * b' * u := by
    rw [hh, eb, eu, map_mul, mul_assoc (ι g₁), ← mul_assoc b', ← hcb]
    simp only [mul_assoc]

  have hb1 : ∀ v ∉ im w, GM.cf v b' = finAt v b := fun v hv => by
    rw [← cf_snd, eb, cf_mul, hoff g₁ v hv, one_mul]
  have hu1 : ∀ v ∉ im w, GM.cf v u = finAt v c := fun v hv => by
    rw [← cf_snd, eu, cf_mul, hoff g₂ v hv, one_mul]
  have hup : finEmb K (2 + 2) b' ∈ adelicBorel := by
    refine fin_borel b' fun v i j hij => ?_
    by_cases hv : v ∈ im w
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hv
      rw [hb' l]
      exact Matrix.one_apply_ne hij.ne'
    · rw [hb1 v hv]
      change (b i j).2 v = 0
      rw [mem_adelicBorel.1 hb hij]
      rfl
  have hs := proj_borel b' hup
  obtain ⟨X, m₁, m₂, t, hX⟩ := par_of_low (fin1 b') (low_of_borel hs) (low_of_borel (inv_mem hs))
  refine ⟨X, m₁, m₂, t, g₁ * g₂, u, fun U v => ?_, ?_⟩
  · by_cases hv : v ∈ im w
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hv
      beta_reduce
      rw [if_pos hv]
      change GM.cf (w l) u ∈ U (w l)
      rw [hu l]
      exact one_mem _
    · beta_reduce
      rw [if_neg hv]
      change GM.cf v u ∈ _
      rw [hu1 v hv]
      exact hc.2 v
  · have c1 : Commute (arc1 k) (fin1 b') := (levLaws (K := K) (2 + 2) (im w)).2.2.1 k b'
    have c2 : fin1 (ι (g₁ * g₂)) * fin1 b' = fin1 b' * fin1 (ι (g₁ * g₂)) := by
      rw [← map_mul, ← map_mul, (hcomm (g₁ * g₂) b' hb').eq]
    have e3 : fin1 (ι (g₁ * g₂) * b' * u) = fin1 (ι (g₁ * g₂)) * fin1 b' * fin1 u :=
      (map_mul _ _ _).trans (congrArg (· * fin1 u) (map_mul _ _ _))
    rw [← hX, hh2, e3, c2, ← c1.eq]
    simp only [mul_assoc]
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem ray_lv {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)}
    {f : G1 K (2 + 2) → ℂ} (hf : IsSec τ₁ τ₂ f) (t : ℝ) (g : G1 K (2 + 2)) : f (lv 1 1 t * g) = f g := by
  refine hf.ray ⟨Real.exp t, Real.exp_pos t⟩ _ g ?_
  have h : (⟨Real.exp (-t), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) = (⟨Real.exp t, Real.exp_pos t⟩ : {r : ℝ // 0 < r})⁻¹ :=
    Subtype.ext (Real.exp_neg t)
  rw [Subgroup.coe_mul, blkLaws.1, Subgroup.coe_one, one_mul, one_mul, zt, zt, h]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.evInj :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) κ₂ p₁ p₂ k₀, ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₄ →
      ∀ φ ∈ Zs τ₁ τ₂ κ e (im w), ev ι₄ k₀ φ = 0 → φ = 0 := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hA r w ι₄ hw hι φ hφ h0
  obtain ⟨f, hf, hfa, ⟨U, -, hU⟩, rfl⟩ := ((zMem μ₂ τ₁ τ₂ κ e hA.idem).1 _ φ).1 hφ
  have h1 : ∀ g m₁ m₂, f (lv m₁ m₂ 0 * arc1 k₀ * fin1 (ι₄ g)) = 0 := fun g m₁ m₂ =>
    (mul_eq_zero.1 (congrFun (congrFun h0 g) (m₁, m₂))).resolve_left (Complex.exp_ne_zero _)
  obtain ⟨ι₂, hι₂⟩ := (embEx (K := K) 2 w hw).1
  have hz : f = 0 := by
    refine hA.inj f hf hfa fun h m₁ m₂ => ?_
    obtain ⟨X, a₁, a₂, t, g, u, hu, hd⟩ := finIwa w ι₄ hw hι h k₀
    obtain ⟨X', hX⟩ := (parLaw w ι₂ ι₄ hw hι₂ hι).1 m₁ m₂ 0 X
    have hl : lv m₁ m₂ 0 * lv a₁ a₂ t = lv 1 1 t * lv (m₁ * a₁) (m₂ * a₂) 0 := by
      rw [blkLaws.2.1, blkLaws.2.1, one_mul, one_mul, zero_add, add_zero]
    have he : lv m₁ m₂ 0 * arc1 k₀ * fin1 h =
        nn X' * (lv 1 1 t * (lv (m₁ * a₁) (m₂ * a₂) 0 * arc1 k₀ * fin1 (ι₄ g))) * fin1 u := by
      rw [mul_assoc, hd]
      simp only [← mul_assoc]
      rw [hX, mul_assoc (nn X'), hl, ← mul_assoc (nn X')]
    rw [he, hU u (hu U), hf.unip, ray_lv hf, h1]
  funext x
  rw [hz]
  exact mul_zero _
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical InnerProductSpace

section Hil
variable {G H : Type*} [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma prjMem (Z : Submodule ℂ H) (hZ : IsClosed (Z : Set H)) (u : H) : prj Z u ∈ Z :=
  (SetLike.ext_iff.1 hZ.submodule_topologicalClosure_eq _).1
    (Submodule.starProjection_apply_mem Z.topologicalClosure u)

private lemma prjOrth (Z : Submodule ℂ H) (u e : H) (he : e ∈ Z) : ⟪u - prj Z u, e⟫_ℂ = 0 :=
  Submodule.starProjection_inner_eq_zero (K := Z.topologicalClosure) u e (Submodule.le_topologicalClosure _ he)

private lemma prjComm (π : UnitaryRep G H) (Z : Submodule ℂ H) (hZ : IsClosed (Z : Set H)) (x : G)
    (h1 : ∀ v ∈ Z, π x v ∈ Z) (h2 : ∀ v ∈ Z, π x⁻¹ v ∈ Z) (v : H) : prj Z (π x v) = π x (prj Z v) := by
  show Z.topologicalClosure.starProjection (π x v) = _
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.le_topologicalClosure _ (h1 _ (prjMem Z hZ v))) ?_
  intro e he
  have he' : e ∈ Z := (SetLike.ext_iff.1 hZ.submodule_topologicalClosure_eq _).1 he
  have hee : π x (π x⁻¹ e) = e := by
    rw [← UnitaryRep.map_mul_apply, mul_inv_cancel, UnitaryRep.map_one_apply]
  rw [← hee, ← map_sub, UnitaryRep.inner_map_map]
  exact prjOrth Z v _ (h2 e he')

private lemma existsNe (π : UnitaryRep G H) (τ : Submodule ℂ H) (hcl : IsClosed (τ : Set H))
    (hirr : ∀ ρ : Submodule ℂ H, ρ ≤ τ → IsClosed (ρ : Set H) → (∀ g, ∀ v ∈ ρ, π g v ∈ ρ) → ρ = ⊥ ∨ ρ = τ)
    (hinv : ∀ g, ∀ v ∈ τ, π g v ∈ τ)
    {v₀ u : H} (hv₀ : v₀ ∈ τ) (h0 : v₀ ≠ 0) (hu : u ∈ τ) (hu0 : u ≠ 0) : ∃ y, ⟪v₀, π y u⟫_ℂ ≠ 0 := by
  by_contra hc
  push_neg at hc
  let ρ : Submodule ℂ H :=
    { carrier := {v | v ∈ τ ∧ ∀ y, ⟪v₀, π y v⟫_ℂ = 0}
      add_mem' := fun ha hb => ⟨τ.add_mem ha.1 hb.1, fun y => by rw [map_add, inner_add_right, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨τ.zero_mem, fun y => by simp⟩
      smul_mem' := fun c _ ha => ⟨τ.smul_mem c ha.1, fun y => by rw [map_smul, inner_smul_right, ha.2, mul_zero]⟩ }
  have hρc : IsClosed (ρ : Set H) := by
    have e : (ρ : Set H) = (τ : Set H) ∩ ⋂ y, {v | ⟪v₀, π y v⟫_ℂ = 0} := by
      ext v
      simp [ρ]
    rw [e]
    exact hcl.inter (isClosed_iInter fun y => isClosed_eq (continuous_const.inner (π y).continuous) continuous_const)
  have hρi : ∀ g, ∀ v ∈ ρ, π g v ∈ ρ := fun g v hv =>
    ⟨hinv g v hv.1, fun y => by rw [← UnitaryRep.map_mul_apply]; exact hv.2 _⟩
  rcases hirr ρ (fun v hv => hv.1) hρc hρi with h | h
  · have : u ∈ ρ := ⟨hu, hc⟩
    rw [h] at this
    exact hu0 ((Submodule.mem_bot ℂ).1 this)
  · have : v₀ ∈ ρ := h ▸ hv₀
    have h1 := this.2 1
    rw [UnitaryRep.map_one_apply, inner_self_eq_zero] at h1
    exact h0 h1

private lemma occAbs {Gl V : Type*} [Group Gl] [AddCommGroup V] [Module ℂ V] (π : UnitaryRep G H) (τ : Submodule ℂ H)
    (hcl : IsClosed (τ : Set H))
    (hirr : ∀ ρ : Submodule ℂ H, ρ ≤ τ → IsClosed (ρ : Set H) → (∀ g, ∀ v ∈ ρ, π g v ∈ ρ) → ρ = ⊥ ∨ ρ = τ)
    (hinv : ∀ g, ∀ v ∈ τ, π g v ∈ τ) (L : Gl →* G) (σ : Representation ℂ Gl V) (f₀ : V →ₗ[ℂ] H) (hf₀ : f₀ ≠ 0)
    (hf₀τ : ∀ x, f₀ x ∈ τ) (hf₀e : ∀ g x, f₀ (σ g x) = π (L g) (f₀ x))
    (hsp : ∀ y : G, ∃ x g, y = x * L g ∧ ∀ g', x * L g' = L g' * x)
    (T : Set (H →L[ℂ] H)) (hT : ∀ t ∈ T, ∀ g v, t (π (L g) v) = π (L g) (t v))
    {v₀ : H} (hv₀ : v₀ ∈ τ) (h0 : v₀ ≠ 0) (hv₀T : ∀ t ∈ T, t v₀ = v₀) :
    ∃ F : V →ₗ[ℂ] H, F ≠ 0 ∧ (∀ s, F s ∈ τ ∧ ∀ t ∈ T, t (F s) = F s) ∧ ∀ g s, F (σ g s) = π (L g) (F s) := by
  let Z : Submodule ℂ H :=
    { carrier := {v | v ∈ τ ∧ ∀ t ∈ T, t v = v}
      add_mem' := fun ha hb => ⟨τ.add_mem ha.1 hb.1, fun t ht => by rw [map_add, ha.2 t ht, hb.2 t ht]⟩
      zero_mem' := ⟨τ.zero_mem, fun t _ => by simp⟩
      smul_mem' := fun c _ ha => ⟨τ.smul_mem c ha.1, fun t ht => by rw [map_smul, ha.2 t ht]⟩ }
  have hZc : IsClosed (Z : Set H) := by
    have e : (Z : Set H) = (τ : Set H) ∩ ⋂ t ∈ T, {v | t v = v} := by
      ext v
      simp [Z]
    rw [e]
    exact hcl.inter (isClosed_biInter fun t _ => isClosed_eq t.continuous continuous_id)
  have hZi : ∀ g, ∀ v ∈ Z, π (L g) v ∈ Z := fun g v hv =>
    ⟨hinv _ v hv.1, fun t ht => by rw [hT t ht, hv.2 t ht]⟩
  have hcomm : ∀ g u, prj Z (π (L g) u) = π (L g) (prj Z u) := fun g u =>
    prjComm π Z hZc (L g) (hZi g) (fun v hv => by rw [← map_inv]; exact hZi _ v hv) u
  have hPZ : ∀ u, prj Z u ∈ Z := prjMem Z hZc
  have hPin : ∀ u, prj Z u = 0 → ⟪v₀, u⟫_ℂ = 0 := fun u hu => by
    have h2 := prjOrth Z u v₀ ⟨hv₀, hv₀T⟩
    rw [hu, sub_zero] at h2
    exact inner_eq_zero_symm.1 h2
  obtain ⟨s, hs⟩ : ∃ s, f₀ s ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf₀ (LinearMap.ext hc)
  obtain ⟨y, hy⟩ := existsNe π τ hcl hirr hinv hv₀ h0 (hf₀τ s) hs
  obtain ⟨x, g, rfl, hx⟩ := hsp y
  refine ⟨(prj Z : H →ₗ[ℂ] H) ∘ₗ (π x : H →ₗ[ℂ] H) ∘ₗ f₀, ?_, fun s => hPZ _, fun g' s => ?_⟩
  · intro hF
    apply hy
    have h1 := LinearMap.congr_fun hF (σ g s)
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.zero_apply, hf₀e] at h1
    have h2 := hPin _ h1
    rwa [← UnitaryRep.map_mul_apply] at h2
  · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hf₀e]
    rw [← hcomm, ← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, hx]

private lemma avgComm {A : Type*} [MeasurableSpace A] (π : UnitaryRep G H) (κ : Measure A) (a : A → G) (p : A → ℂ) (b : G) (v : H)
    (hcm : ∀ k, a k * b = b * a k) (hint : Integrable (fun k => p k • π (a k) v) κ) :
    ∫ k, p k • π (a k) (π b v) ∂κ = π b (∫ k, p k • π (a k) v ∂κ) := by
  rw [← (π b).integral_comp_comm hint]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  show p k • π (a k) (π b v) = π b (p k • π (a k) v)
  rw [map_smul, ← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, hcm]

end Hil

section Conc
variable {K : Type} [Field K] [NumberField K]

private lemma pInt (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] {κ : Measure (archCompact K 2)} {p : archCompact K 2 → ℂ}
    (hp : IdemA κ p) (v : L2 μ) : Integrable (fun k => p k • rightRegularRep (Gam K 2) μ (arc1 k) v) κ := by
  haveI := hp.haar.prob
  obtain ⟨-, -, -, harc, hcpt, -⟩ := levLaws (K := K) 2 ∅
  have hc : Continuous fun k => p k • rightRegularRep (Gam K 2) μ (arc1 k) v :=
    hp.cont.smul (((rightRegularRep (Gam K 2) μ).continuous_orbit v).comp harc)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private lemma pClm (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] {κ : Measure (archCompact K 2)} {p : archCompact K 2 → ℂ}
    (hp : IdemA κ p) : ∃ P : L2 μ →L[ℂ] L2 μ, ∀ v, P v = pOp μ κ p v := by
  haveI := hp.haar.prob
  obtain ⟨-, -, -, harc, hcpt, -⟩ := levLaws (K := K) 2 ∅
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hp.cont.continuousOn
  let P : L2 μ →ₗ[ℂ] L2 μ :=
    { toFun := pOp μ κ p
      map_add' := fun a b => by
        simp only [pOp, map_add, smul_add]
        exact integral_add (pInt μ hp a) (pInt μ hp b)
      map_smul' := fun c a => by
        simp only [pOp, map_smul, RingHom.id_apply]
        rw [← integral_smul]
        exact integral_congr_ae (Eventually.of_forall fun k => smul_comm _ _ _) }
  refine ⟨P.mkContinuous C fun v => ?_, fun v => rfl⟩
  show ‖pOp μ κ p v‖ ≤ C * ‖v‖
  have := norm_integral_le_of_norm_le_const (μ := κ) (C := C * ‖v‖)
    (f := fun k => p k • rightRegularRep (Gam K 2) μ (arc1 k) v) (Eventually.of_forall fun k => by
      rw [norm_smul, UnitaryRep.norm_map]
      exact mul_le_mul_of_nonneg_right (hC k (Set.mem_univ _)) (norm_nonneg _))
  simpa [pOp] using this

private lemma pComm (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] {κ : Measure (archCompact K 2)} {p : archCompact K 2 → ℂ}
    (hp : IdemA κ p) (h : FA K 2) (v : L2 μ) :
    pOp μ κ p (rightRegularRep (Gam K 2) μ (fin1 h) v) = rightRegularRep (Gam K 2) μ (fin1 h) (pOp μ κ p v) := by
  obtain ⟨-, -, hcm, -, -, -⟩ := levLaws (K := K) 2 ∅
  exact avgComm (rightRegularRep (Gam K 2) μ) κ arc1 p (fin1 h) v (fun k => (hcm k h).eq) (pInt μ hp v)

private lemma cfMul (w : Pl K) (a b : FA K 2) : GM.cf w (a * b) = GM.cf w a * GM.cf w b := by
  show AdelicGLn.finiteRestrictedEquiv K 2 (a * b) w = AdelicGLn.finiteRestrictedEquiv K 2 a w * AdelicGLn.finiteRestrictedEquiv K 2 b w
  rw [map_mul]
  rfl

private lemma splitAt (v : Pl K) (y : G1 K 2) :
    ∃ (x : G1 K 2) (g : Gw 2 v), y = x * fin1 (AdelicGLn.localEmbedding v g) ∧
      ∀ g' : Gw 2 v, x * fin1 (AdelicGLn.localEmbedding v g') = fin1 (AdelicGLn.localEmbedding v g') * x := by
  obtain ⟨A, u, rfl⟩ := MultiplicityOne.exists_archProj_mul_finProj y
  obtain ⟨⟨ι', hι⟩, hall⟩ := embEx (K := K) 2 (fun _ : Fin 1 => v) (Function.injective_of_subsingleton _)
  obtain ⟨-, -, -, hdec, -, -⟩ := hall ι' hι
  obtain ⟨g, h', e, hc⟩ := hdec u
  have hg : ι' g = AdelicGLn.localEmbedding v (g 0) := by
    rw [← hι 0 (g 0)]
    congr 1
    funext j
    rw [Subsingleton.elim j 0, Pi.mulSingle_eq_same]
  have comm := (UpperTheory.ConvolutionTheory.Tf.locEmb K 2 v).2.2.2.2 h' (hc 0)
  have comm' : ∀ g', fin1 h' * fin1 (AdelicGLn.localEmbedding v g') = fin1 (AdelicGLn.localEmbedding v g') * fin1 h' := fun g' => by
    rw [← map_mul, ← map_mul, comm]
  refine ⟨archProj K 2 A * fin1 h', g 0, ?_, fun g' => ?_⟩
  · rw [e, hg, map_mul, mul_assoc, comm']
  · rw [mul_assoc, comm', ← mul_assoc, ← mul_assoc, ← MultiplicityOne.finProj_mul_archProj_comm]

end Conc

set_option maxHeartbeats 1000000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.xOcc :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K 2)) (p : archCompact K 2 → ℂ), CuspIrr μ τ → IdemA κ p → ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS 2 w →* FA K 2), Function.Injective w → IsEmb w ι → Xs μ τ κ p (im w) ≠ ⊥ → ∀ i,
      ∃ (σ : SmIrr (Gw 2 (w i))) (f : σ.V →ₗ[ℂ] (G1 K 2 → ℂ)), Occurs μ τ (w i) σ ∧ f ≠ 0 ∧ (∀ v, f v ∈ Xs μ τ κ p (im w)) ∧
        ∀ g v, f (σ.ρ g v) = rS ι (Pi.mulSingle i g) (f v) := by
  intro K _ _ _ μ _ τ κ p hτ hp r w ι hw hι hX i
  obtain ⟨hmem, hmem2⟩ := xMem μ τ κ p hp
  have hstab := hmem2 hτ w ι hw hι
  obtain ⟨J, hJi, hJ1, hJ2, hJ3⟩ := exists_injection_into_l2_cusp μ τ κ p hτ hp (im w)
  obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).1 hX
  obtain ⟨-, -, -, U, hU, hfix⟩ := (hmem _ _).1 hφ
  obtain ⟨-, hco, -, -, -, hlev⟩ := (embEx (K := K) 2 w hw).2 ι hι
  have hv₀0 : J ⟨φ, hφ⟩ ≠ 0 := fun h => hφ0 (congrArg Subtype.val (hJi (h.trans (map_zero J).symm)))
  have hv₀H := (hJ1 ⟨φ, hφ⟩).2
  have hv₀f : ∀ u ∈ levOn (im w) U, rhoF μ u (J ⟨φ, hφ⟩) = J ⟨φ, hφ⟩ := fun u hu =>
    (hJ2 u ⟨φ, hφ⟩ ⟨φ, hφ⟩ (fun x => (hfix u hu x).symm)).symm
  have hSum : IsSummand μ τ :=
    ⟨hτ.le, hτ.closed, fun g v hv => hτ.inv g v hv, hτ.ne, fun V' h1 h2 h3 => hτ.irr V' h1 h2 fun g v hv => h3 g v hv⟩
  letI : MeasurableSpace (Gw 2 (w i)) := borel _
  haveI : BorelSpace (Gw 2 (w i)) := ⟨rfl⟩
  let K₀ : TopologicalSpace.PositiveCompacts (Gw 2 (w i)) :=
    ⟨⟨U (w i), (hU (w i)).1.1⟩, ⟨1, mem_interior_iff_mem_nhds.2 ((hU (w i)).1.2.mem_nhds (U (w i)).one_mem)⟩⟩
  obtain ⟨⟨σ, hσ⟩, -, -⟩ := UpperTheory.ConvolutionTheory.C.occursBasics K 2 μ τ (w i) (Measure.haarMeasure K₀) hSum
  obtain ⟨f₀, hf₀, hf₀τ, hf₀e⟩ := id hσ
  obtain ⟨P, hP⟩ := pClm μ hp
  let L : Gw 2 (w i) →* G1 K 2 := (MultiplicityOne.finProj K 2).comp (AdelicGLn.localEmbedding (w i))
  let T : Set (L2 μ →L[ℂ] L2 μ) := {t | t = P ∨ ∃ h ∈ levOn (im w) U, GM.cf (w i) h = 1 ∧ t = rightRegularRep (Gam K 2) μ (fin1 h)}
  have hT : ∀ t ∈ T, ∀ g v, t (rightRegularRep (Gam K 2) μ (L g) v) = rightRegularRep (Gam K 2) μ (L g) (t v) := by
    rintro t (rfl | ⟨h, -, hc, rfl⟩) g v
    · rw [hP, hP]
      exact pComm μ hp _ v
    · rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply]
      have h1 := (UpperTheory.ConvolutionTheory.Tf.locEmb K 2 (w i)).2.2.2.2 h hc g
      have h2 : fin1 h * L g = L g * fin1 h := by
        show fin1 h * fin1 (AdelicGLn.localEmbedding (w i) g) = fin1 (AdelicGLn.localEmbedding (w i) g) * fin1 h
        rw [← map_mul, ← map_mul, h1]
      rw [h2]
  have hvT : ∀ t ∈ T, t (J ⟨φ, hφ⟩) = J ⟨φ, hφ⟩ := by
    rintro t (rfl | ⟨h, hh, -, rfl⟩)
    · rw [hP]
      exact hv₀H.2.1
    · exact hv₀f h hh
  obtain ⟨F, hF0, hFZ, hFe⟩ := occAbs (rightRegularRep (Gam K 2) μ) τ hτ.closed hτ.irr hτ.inv L σ.ρ f₀ hf₀ hf₀τ hf₀e
    (splitAt (w i)) T hT hv₀H.1 hv₀0 hvT
  have hran : ∀ s, F s ∈ LinearMap.range J := by
    intro s
    let O : Subgroup (Gw 2 (w i)) :=
      { carrier := {g | σ.ρ g s = s}
        mul_mem' := fun {a b} ha hb => by
          show σ.ρ (a * b) s = s
          rw [map_mul, Module.End.mul_apply, show σ.ρ b s = s from hb, show σ.ρ a s = s from ha]
        one_mem' := by
          show σ.ρ 1 s = s
          simp
        inv_mem' := fun {a} ha => by
          show σ.ρ a⁻¹ s = s
          have h1 : σ.ρ a⁻¹ (σ.ρ a s) = s := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
          rwa [show σ.ρ a s = s from ha] at h1 }
    have hOo : IsOpen (O : Set (Gw 2 (w i))) := σ.smooth s
    let U' : ∀ v : Pl K, Subgroup (Gw 2 v) := Function.update U (w i) (U (w i) ⊓ O)
    have hU'eq : U' (w i) = U (w i) ⊓ O := Function.update_self _ _ _
    have hU'ne : ∀ v, v ≠ w i → U' v = U v := fun v hv => Function.update_of_ne hv _ _
    have hU' : Lev U' := by
      intro v
      by_cases hv : v = w i
      · subst hv
        rw [hU'eq]
        refine ⟨⟨?_, (hU _).1.2.inter hOo⟩, inf_le_left.trans (hU _).2⟩
        exact (hU _).1.1.inter_right (Subgroup.isClosed_of_isOpen O hOo)
      · rw [hU'ne v hv]
        exact hU v
    have hfixF : F s ∈ fixF μ (levOn (im w) U') := by
      simp only [fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus]
      intro u hu
      show rhoF μ u (F s) = F s
      obtain ⟨g, h', rfl, hg, hc, hint⟩ := (hlev U' u).1 hu
      let g2 : GS 2 w := Function.update g i 1
      have hsplit : ι g = AdelicGLn.localEmbedding (w i) (g i) * ι g2 := by
        rw [← hι i (g i), ← map_mul]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj
          simp [g2]
        · simp [g2, hj, Pi.mulSingle_eq_of_ne hj]
      have hn : ι g2 * h' ∈ levOn (im w) U := by
        refine (hlev U _).2 ⟨g2, h', rfl, fun j => ?_, hc, hint⟩
        by_cases hj : j = i
        · subst hj
          simp [g2, one_mem]
        · have h3 := hg j
          rw [hU'ne (w j) (fun h => hj (hw h))] at h3
          simpa [g2, hj] using h3
      have hcn : GM.cf (w i) (ι g2 * h') = 1 := by
        rw [cfMul, hco, hc i]
        simp [g2]
      have e1 : rhoF μ (ι g * h') (F s) =
          rightRegularRep (Gam K 2) μ (L (g i)) (rightRegularRep (Gam K 2) μ (fin1 (ι g2 * h')) (F s)) := by
        rw [← UnitaryRep.map_mul_apply, hsplit, mul_assoc]
        exact congrArg (fun y => rightRegularRep (Gam K 2) μ y (F s)) (map_mul (MultiplicityOne.finProj K 2) _ _)
      rw [e1, (hFZ s).2 _ (Or.inr ⟨_, hn, hcn, rfl⟩), ← hFe]
      have h3 := hg i
      rw [hU'eq] at h3
      rw [show σ.ρ (g i) s = s from h3.2]
    have hInH : InH μ τ κ p (im w) (F s) := by
      refine ⟨(hFZ s).1, (hP _).symm.trans ((hFZ s).2 P (Or.inl rfl)), ?_⟩
      simp only [sphOff, Submodule.mem_iInf]
      intro v hv
      simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus]
      rintro _ ⟨k, hk, rfl⟩
      show rhoF μ (AdelicGLn.localEmbedding v k) (F s) = F s
      have hvn : ∀ j, w j ≠ v := fun j h => hv (h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _))
      have hl := UpperTheory.ConvolutionTheory.Tf.locEmb K 2 v
      refine (hFZ s).2 _ (Or.inr ⟨_, (hlev U _).2 ⟨1, AdelicGLn.localEmbedding v k, by simp,
        fun _ => one_mem _, fun j => hl.2.2.1 _ (hvn j) k, fun v' => ?_⟩, hl.2.2.1 _ (hvn i) k, rfl⟩)
      by_cases hv' : v' = v
      · subst hv'
        show finAt v' (finEmb K 2 (AdelicGLn.localEmbedding v' k)) ∈ _
        rw [hl.2.1]
        exact hk
      · show finAt v' (finEmb K 2 (AdelicGLn.localEmbedding v k)) ∈ _
        rw [hl.2.2.1 _ hv' k]
        exact one_mem _
    obtain ⟨φ', hφ', -⟩ := (hJ3 U' hU').1 (F s) hInH hfixF
    exact ⟨φ', hφ'⟩
  let Je := LinearEquiv.ofInjective J hJi
  let f' : σ.V →ₗ[ℂ] Xs μ τ κ p (im w) := Je.symm.toLinearMap ∘ₗ F.codRestrict (LinearMap.range J) hran
  have hJf : ∀ s, J (f' s) = F s := fun s =>
    congrArg Subtype.val (Je.apply_symm_apply ⟨F s, hran s⟩)
  refine ⟨σ, (Xs μ τ κ p (im w)).subtype ∘ₗ f', hσ, ?_, fun v => (f' v).2, fun g s => ?_⟩
  · intro h0
    apply hF0
    refine LinearMap.ext fun s => ?_
    have h1 : f' s = 0 := Subtype.ext (LinearMap.congr_fun h0 s)
    rw [← hJf, h1, map_zero]
    rfl
  · let φ2 : Xs μ τ κ p (im w) := ⟨rS ι (Pi.mulSingle i g) (f' s).1, (hstab _ (f' s).2).2 _⟩
    have e : J φ2 = rhoF μ (ι (Pi.mulSingle i g)) (J (f' s)) := hJ2 _ _ _ (fun x => rfl)
    have e2 : f' (σ.ρ g s) = φ2 := hJi (by
      rw [hJf, e, hJf, hFe, hι i g]
      rfl)
    exact congrArg Subtype.val e2
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.occUnit :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (w : Pl K) (σ : SmIrr (Gw n w)), Occurs μ τ w σ → IsUnitarisable σ.ρ := by
  intro K _ _ n μ _ τ w σ ⟨f, hf0, _, hf⟩
  have hin : ∀ g (x y : LL μ), inner ℂ (rhoL μ w g x) (rhoL μ w g y) = inner ℂ x y := by
    intro g x y
    unfold rhoL
    exact UnitaryRep.inner_map_map _ _ _ _
  have hinj : ∀ v, f v = 0 → v = 0 := by
    have hirr : σ.ρ.IsIrreducible := by cases σ; assumption
    let Q : Subrepresentation σ.ρ := ⟨LinearMap.ker f, fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hf, hv, map_zero]⟩
    rcases eq_bot_or_eq_top Q with h | h
    · intro v hv
      have : v ∈ Q := hv
      rw [h] at this
      exact this
    · exfalso
      apply hf0
      ext1 v
      have : v ∈ Q := by rw [h]; trivial
      exact this
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => inner ℂ (f y) (f x)) ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩
  · intro a b c; simp only [map_add, inner_add_right]
  · intro a b c; simp only [map_smul, inner_smul_right, RingHom.id_apply, smul_eq_mul]
  · intro a b c; simp only [map_add, inner_add_left]
  · intro a b c; simp only [map_smul, inner_smul_left, smul_eq_mul]
  · intro v u; simp only [LinearMap.mk₂'ₛₗ_apply, inner_conj_symm]
  · intro v hv
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact (re_inner_self_pos (𝕜 := ℂ)).2 (fun h => hv (hinj v h))
  · intro g v u; simp only [LinearMap.mk₂'ₛₗ_apply, hf, hin]
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.schurSm :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (w : Pl K) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Gw n w) V), GlobalTheory.PRep.IsSmooth ρ → ρ.IsIrreducible → Schur ρ := by
  intro K _ _ n w V _ _ ρ hs hi T hT
  haveI := hi
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (w.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → w.adicCompletion K))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (w.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (Gw n w) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have hsm : GroundTheory.Automorphic.IsSmooth ρ := fun v => hs v
  let φ : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := T, isIntertwining' := fun g => LinearMap.ext fun v => hT g v }
  obtain ⟨c, hc⟩ := (algebraMap_intertwiningMap_bijective_of_isSmooth hsm).2 φ
  exact ⟨c, fun v => (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hc).symm⟩
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem irr_twist {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (f : G →* H) (hf : Function.Surjective f) (χ : G →* ℂˣ) (hi : ρ.IsIrreducible) (hs : Schur ρ) :
    (twist (ρ.comp f) χ).IsIrreducible ∧ Schur (twist (ρ.comp f) χ) := by
  constructor
  · let E : Subrepresentation (twist (ρ.comp f) χ) ≃o Subrepresentation ρ :=
      { toFun := fun S => ⟨S.toSubmodule, fun h v hv => by
          obtain ⟨g, rfl⟩ := hf h
          have h1 := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
          rw [twist_apply, smul_smul, Units.inv_mul, one_smul] at h1
          exact h1⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv => by
          rw [twist_apply]
          exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule (f g) hv)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    exact E.isSimpleOrder_iff.2 hi
  · intro T hT
    refine hs T fun h v => ?_
    obtain ⟨g, rfl⟩ := hf h
    have h1 := hT g v
    rw [twist_apply, twist_apply, map_smul] at h1
    exact smul_right_injective V (χ g).ne_zero h1

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.locDat :
    ∀ {K : Type} [Field K] [NumberField K] (w : Pl K) (σ₁ σ₂ : SmIrr (Gw 2 w)), IsUnitarisable σ₁.ρ → IsUnitarisable σ₂.ρ → LocOk (PW w) (rhoW w σ₁ σ₂) := by
  intro K _ _ w σ₁ σ₂ u₁ u₂
  have hT := tensSimple σ₁.ρ σ₂.ρ σ₁.irred (schurSm 2 w σ₁.ρ σ₁.smooth σ₁.irred) σ₂.irred
  have hsurj : Function.Surjective (lev₂ w) := by
    intro g
    refine ⟨⟨leviEmb _ _ (leviTwo (w.adicCompletion K) (Fin 2) (Fin 2) g), leviEmb_mem_parab _ _ _⟩, ?_⟩
    change (leviTwo (w.adicCompletion K) (Fin 2) (Fin 2)).symm (leviProj _ _ _) = g
    rw [leviProj_leviEmb, MulEquiv.symm_apply_apply]
  have hR := irr_twist _ (lev₂ w) hsurj (dl w) hT.1 (hT.2 (schurSm 2 w σ₂.ρ σ₂.smooth σ₂.irred))
  haveI : CharZero (w.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
  have hI : (smInd (PW w) (rhoW w σ₁ σ₂)).IsIrreducible :=
    UpperTheory.Lit.Mix.twoAt_charZero (w.adicCompletion K) 2 2 _ _ σ₁.ρ σ₂.ρ σ₁.smooth σ₁.irred u₁ σ₂.smooth σ₂.irred u₂
  refine ⟨⟨_, ⟨GlobalTheory.SplitFlip.isCompact_KO, GlobalTheory.SplitFlip.isOpen_KO⟩, fun g => ?_⟩, fun N hN => ?_, hR.1, hR.2, hI,
    schurSm (2 + 2) w _ (isSmooth_smoothRep _) hI⟩
  · obtain ⟨p, k, hk, e⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul (two (stdSum (rfl : 2 + 2 = 2 + 2))) g
    exact ⟨p, p.2, k, hk, e⟩
  · obtain ⟨U, h1, -, h2⟩ := GlobalTheory.LocalThetaGL.compact_open_basis (k := w.adicCompletion K) (Fin (2 + 2)) N hN
    exact ⟨U, h1, h2⟩
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem dS_single {K : Type} [Field K] [NumberField K] {r : ℕ} (w : Fin r → Pl K) (i : Fin r) (p : PW (w i)) :
    dS w (Pi.mulSingle i p) = dl (w i) p := by
  unfold dS
  rw [MonoidHom.finset_prod_apply, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.mulSingle_eq_of_ne hj]
  · simp

private theorem blocks_single {K : Type} [Field K] [NumberField K] {r : ℕ} {w : Fin r → Pl K} (ι : GS 2 w →* FA K 2)
    (i : Fin r) (p : PW (w i)) :
    blocks ι (Pi.mulSingle i p) =
      (MultiplicityOne.finProj K 2 (ι (Pi.mulSingle i (lev₂ (w i) p).1)),
        MultiplicityOne.finProj K 2 (ι (Pi.mulSingle i (lev₂ (w i) p).2))) := by
  have h1 : (fun j => (lev₂ (w j) ((Pi.mulSingle i p : ∀ j, PW (w j)) j)).1) = Pi.mulSingle i (lev₂ (w i) p).1 := by
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Pi.mulSingle_eq_of_ne h]
  have h2 : (fun j => (lev₂ (w j) ((Pi.mulSingle i p : ∀ j, PW (w j)) j)).2) = Pi.mulSingle i (lev₂ (w i) p).2 := by
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Pi.mulSingle_eq_of_ne h]
  refine Prod.ext ?_ ?_
  · change MultiplicityOne.finProj K 2 (ι (fun j => (lev₂ (w j) ((Pi.mulSingle i p : ∀ j, PW (w j)) j)).1)) = _
    rw [h1]
  · change MultiplicityOne.finProj K 2 (ι (fun j => (lev₂ (w j) ((Pi.mulSingle i p : ∀ j, PW (w j)) j)).2)) = _
    rw [h2]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.exists_local_subrep_of_isotypic_tensor_ne_bot :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K 2)) (p₁ p₂ : archCompact K 2 → ℂ),
      CuspIrr μ τ₁ → CuspIrr μ τ₂ → IdemA κ p₁ → IdemA κ p₂ → ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS 2 w →* FA K 2), Function.Injective w → IsEmb w ι →
      tensFn (Xs μ τ₁ κ p₁ (im w)) (Xs μ τ₂ κ p₂ (im w)) ≠ ⊥ → ∀ i,
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (PW (w i)) V) (f : V →ₗ[ℂ] (G1 K 2 × G1 K 2 → ℂ)), LocOk (PW (w i)) ρ ∧ f ≠ 0 ∧
        (∀ v, f v ∈ tensFn (Xs μ τ₁ κ p₁ (im w)) (Xs μ τ₂ κ p₂ (im w))) ∧ ∀ p v, f (ρ p v) = xS ι (Pi.mulSingle i p) (f v) := by
  intro K _ _ _ μ _ τ₁ τ₂ κ p₁ p₂ h₁ h₂ e₁ e₂ r w ι hw hι hne i
  have hX₁ : Xs μ τ₁ κ p₁ (im w) ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff, tensFn, Submodule.span_le]
    rintro _ ⟨φ, hφ, ψ, _, rfl⟩
    rw [h, Submodule.mem_bot] at hφ
    subst hφ
    simp only [Submodule.bot_coe, Set.mem_singleton_iff]
    funext x
    simp
  have hX₂ : Xs μ τ₂ κ p₂ (im w) ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff, tensFn, Submodule.span_le]
    rintro _ ⟨φ, _, ψ, hψ, rfl⟩
    rw [h, Submodule.mem_bot] at hψ
    subst hψ
    simp only [Submodule.bot_coe, Set.mem_singleton_iff]
    funext x
    simp
  obtain ⟨σ₁, f₁, o₁, n₁, m₁, q₁⟩ := xOcc μ τ₁ κ p₁ h₁ e₁ w ι hw hι hX₁ i
  obtain ⟨σ₂, f₂, o₂, n₂, m₂, q₂⟩ := xOcc μ τ₂ κ p₂ h₂ e₂ w ι hw hι hX₂ i
  let f : σ₁.V ⊗[ℂ] σ₂.V →ₗ[ℂ] (G1 K 2 × G1 K 2 → ℂ) :=
    TensorProduct.lift (LinearMap.mk₂ ℂ (fun a b x => f₁ a x.1 * f₂ b x.2)
      (fun _ _ _ => by funext x; simp [add_mul]) (fun _ _ _ => by funext x; simp [mul_assoc])
      (fun _ _ _ => by funext x; simp [mul_add]) (fun _ _ _ => by funext x; simp [mul_left_comm]))
  have hf : ∀ a b, f (a ⊗ₜ b) = fun x => f₁ a x.1 * f₂ b x.2 := by
    intro a b
    simp only [f, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
  refine ⟨σ₁.V ⊗[ℂ] σ₂.V, inferInstance, inferInstance, rhoW (w i) σ₁ σ₂, f,
    locDat (w i) σ₁ σ₂ (occUnit 2 μ τ₁ (w i) σ₁ o₁) (occUnit 2 μ τ₂ (w i) σ₂ o₂), ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ : ∃ a, f₁ a ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact n₁ (LinearMap.ext hc)
    obtain ⟨b, hb⟩ : ∃ b, f₂ b ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact n₂ (LinearMap.ext hc)
    obtain ⟨x, hx⟩ := Function.ne_iff.1 ha
    obtain ⟨y, hy⟩ := Function.ne_iff.1 hb
    intro h0
    have := congrFun (hf a b) (x, y)
    rw [h0] at this
    exact mul_ne_zero hx hy this.symm
  · intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hf]
      exact Submodule.subset_span ⟨_, m₁ a, _, m₂ b, rfl⟩
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  · intro p v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      have hL : rhoW (w i) σ₁ σ₂ p (a ⊗ₜ b) =
          ((dl (w i) p : ℂˣ) : ℂ) • (σ₁.ρ (lev₂ (w i) p).1 a ⊗ₜ σ₂.ρ (lev₂ (w i) p).2 b) := by
        simp only [rhoW, twist_apply, MonoidHom.comp_apply, extTensor_tmul]
      rw [hL, map_smul, hf, hf, q₁, q₂]
      simp only [xS, twist_apply, MonoidHom.comp_apply, dS_single, blocks_single]
      congr 1
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.zSimple :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) κ₂ p₁ p₂ k₀, Pair μ₂ τ₁ τ₂ → ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι → SimpleIn (rS ι) (Zs τ₁ τ₂ κ e (im w)) := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hP hA r w ι hw hι
  have hz := (zMem μ₂ τ₁ τ₂ κ e hA.idem).2 w ι hw hι
  refine ⟨fun g v hv => (hz v hv).2 g, fun Q hQ hst => ?_⟩
  obtain ⟨ι₂, hι₂⟩ := (embEx 2 w hw).1
  have hm := evMem μ₂ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hP hA w ι₂ ι hw hι₂ hι
  have hi := evInj μ₂ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hA w ι hw hι
  have hc1 : CuspIrr μ₂ τ₁ := hP.1
  have hc2 : CuspIrr μ₂ τ₂ := hP.2
  by_cases hQ0 : Q = ⊥
  · exact Or.inl hQ0
  right
  obtain ⟨q, hq, hq0⟩ := (Submodule.ne_bot_iff _).1 hQ0
  have hX : tensFn (Xs μ₂ τ₁ κ₂ p₁ (im w)) (Xs μ₂ τ₂ κ₂ p₂ (im w)) ≠ ⊥ := by
    intro h
    refine hq0 (hi q (hQ hq) ?_)
    funext g
    have := (hm q (hQ hq)).1.1 g
    rw [h] at this
    exact this
  have h12 := x12 μ₂ τ₁ τ₂ κ₂ p₁ p₂ hc1 hc2 hA.rank₁ hA.rank₂ w ι₂ hw hι₂
  have hS := indAmb (fun i => PW (w i)) (xS ι₂) _ h12.1 h12.2
    (exists_local_subrep_of_isotypic_tensor_ne_bot μ₂ τ₁ τ₂ κ₂ p₁ p₂ hc1 hc2 hA.rank₁.1 hA.rank₂.1 w ι₂ hw hι₂ hX)
  have hint : ∀ g φ, ev ι k₀ (rS ι g φ) = rightReg ℂ _ _ g (ev ι k₀ φ) := by
    intro g φ
    funext x m
    change φ (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι x) * fin1 (ι g)) = φ (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι (x * g)))
    simp only [fin1, map_mul, mul_assoc]
  rcases hS.2 (Q.map (ev ι k₀)) (by rintro _ ⟨φ, hφ, rfl⟩; exact hm φ (hQ hφ))
    (by rintro g _ ⟨φ, hφ, rfl⟩; exact ⟨_, hst g φ hφ, hint g φ⟩) with h | h
  · exact absurd (hi q (hQ hq) (by have := Submodule.mem_map_of_mem (f := ev ι k₀) hq; rw [h] at this; exact this)) hq0
  · refine le_antisymm hQ fun φ hφ => ?_
    have := hm φ hφ
    rw [← h] at this
    obtain ⟨ψ, hψ, e⟩ := this
    have : φ - ψ = 0 := hi _ (Submodule.sub_mem _ hφ (hQ hψ)) (by rw [map_sub, e, sub_self])
    rw [sub_eq_zero.1 this]; exact hψ
end
