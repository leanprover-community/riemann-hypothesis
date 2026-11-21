import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.GalLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.RepsSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ZSimple
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.HeckeSimple
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.HopProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.HopEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.TensAmp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.PosSymb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.EvExSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.CosAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CtZero
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.FixLev
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ConjMemIwahori
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.BlockFrameConjugationIdentity
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.AlgTrace
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.GalLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActUniq

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.HeckeOperatorExistence

section Abs

variable {G X : Type} [Group G] [Group X]

private def dbl (U : Subgroup G) (h : G) : Set (G ⧸ U) :=
  {c | ∃ u ∈ U, c = QuotientGroup.mk (u * h)}

private theorem dbl_finite [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G} (hU : CO U) (h : G) :
    (dbl U h).Finite := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU.2
  have hc : Continuous fun u : G => (QuotientGroup.mk (u * h) : G ⧸ U) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hU.1.image hc).finite_of_discrete).subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

private noncomputable def ops (j : G →* X) (U : Subgroup G) (h : G) (Φ : X → ℂ) (x : X) : ℂ :=
  ∑ᶠ c ∈ dbl U h, Φ (x * j c.out)

private def Inv (j : G →* X) (U : Subgroup G) (Φ : X → ℂ) : Prop := ∀ u ∈ U, ∀ x, Φ (x * j u) = Φ x

variable {j : G →* X} {U : Subgroup G} {h h' : G} {Φ Ψ : X → ℂ}

private theorem val_congr (hΦ : Inv j U Φ) {a b : G} (hab : (QuotientGroup.mk a : G ⧸ U) = QuotientGroup.mk b) (x : X) :
    Φ (x * j a) = Φ (x * j b) := by
  have h1 := hΦ _ (QuotientGroup.eq.1 hab) (x * j a)
  have h2 : x * j a * j (a⁻¹ * b) = x * j b := by rw [mul_assoc, ← map_mul, mul_inv_cancel_left]
  rw [h2] at h1
  exact h1.symm

private theorem ops_sum (hf : (dbl U h).Finite) (x : X) :
    ops j U h Φ x = ∑ c ∈ hf.toFinset, Φ (x * j c.out) :=
  finsum_mem_eq_finite_toFinset_sum _ hf

private theorem ops_rep (hf : (dbl U h).Finite) (hΦ : Inv j U Φ) (r : G ⧸ U → G)
    (hr : ∀ c, (QuotientGroup.mk (r c) : G ⧸ U) = c) (x : X) :
    ops j U h Φ x = ∑ c ∈ hf.toFinset, Φ (x * j (r c)) := by
  rw [ops_sum hf]
  refine Finset.sum_congr rfl fun c _ => val_congr hΦ ?_ x
  rw [hr, QuotientGroup.out_eq']

private theorem ops_add (hf : (dbl U h).Finite) : ops j U h (Φ + Ψ) = ops j U h Φ + ops j U h Ψ := by
  funext x
  simp only [Pi.add_apply, ops_sum hf, Finset.sum_add_distrib]

private theorem ops_smul (hf : (dbl U h).Finite) (a : ℂ) : ops j U h (a • Φ) = a • ops j U h Φ := by
  funext x
  simp only [Pi.smul_apply, ops_sum hf, Finset.smul_sum]

private theorem mk_left {u a b : G} (hab : (QuotientGroup.mk a : G ⧸ U) = QuotientGroup.mk b) :
    (QuotientGroup.mk (u * a) : G ⧸ U) = QuotientGroup.mk (u * b) := by
  rw [QuotientGroup.eq] at hab ⊢
  simpa [mul_assoc] using hab

private theorem ops_inv (hΦ : Inv j U Φ) : Inv j U (ops j U h Φ) := by
  intro u hu x
  have hm : ∀ v ∈ U, Set.MapsTo (fun c : G ⧸ U => (QuotientGroup.mk (v * c.out) : G ⧸ U)) (dbl U h) (dbl U h) := by
    rintro v hv c ⟨t, ht, rfl⟩
    refine ⟨v * t, U.mul_mem hv ht, ?_⟩
    change (QuotientGroup.mk (v * (QuotientGroup.mk (t * h) : G ⧸ U).out) : G ⧸ U) = _
    rw [mk_left (QuotientGroup.out_eq' _), mul_assoc]
  have hi : ∀ v : G, Set.LeftInvOn (fun c : G ⧸ U => (QuotientGroup.mk (v⁻¹ * c.out) : G ⧸ U))
      (fun c : G ⧸ U => (QuotientGroup.mk (v * c.out) : G ⧸ U)) (dbl U h) := by
    intro v c _
    change (QuotientGroup.mk (v⁻¹ * (QuotientGroup.mk (v * c.out) : G ⧸ U).out) : G ⧸ U) = c
    rw [mk_left (QuotientGroup.out_eq' _), inv_mul_cancel_left, QuotientGroup.out_eq']
  have hi' : Set.RightInvOn (fun c : G ⧸ U => (QuotientGroup.mk (u⁻¹ * c.out) : G ⧸ U))
      (fun c : G ⧸ U => (QuotientGroup.mk (u * c.out) : G ⧸ U)) (dbl U h) := by
    intro c _
    change (QuotientGroup.mk (u * (QuotientGroup.mk (u⁻¹ * c.out) : G ⧸ U).out) : G ⧸ U) = c
    rw [mk_left (QuotientGroup.out_eq' _), mul_inv_cancel_left, QuotientGroup.out_eq']
  have hb : Set.BijOn (fun c : G ⧸ U => (QuotientGroup.mk (u * c.out) : G ⧸ U)) (dbl U h) (dbl U h) :=
    Set.InvOn.bijOn ⟨hi u, hi'⟩ (hm u hu) (hm u⁻¹ (U.inv_mem hu))
  refine finsum_mem_eq_of_bijOn _ hb fun c _ => ?_
  have h1 := val_congr (x := x) hΦ (QuotientGroup.out_eq' (QuotientGroup.mk (u * c.out) : G ⧸ U)).symm
  rw [map_mul, ← mul_assoc] at h1
  exact h1

private theorem ops_comm (hf : (dbl U h).Finite) (hf' : (dbl U h').Finite) (hΦ : Inv j U Φ) (r r' : G ⧸ U → G)
    (hr : ∀ c, (QuotientGroup.mk (r c) : G ⧸ U) = c) (hr' : ∀ c, (QuotientGroup.mk (r' c) : G ⧸ U) = c)
    (hc : ∀ c ∈ dbl U h, ∀ c' ∈ dbl U h', Commute (r c) (r' c')) (x : X) :
    ops j U h (ops j U h' Φ) x = ops j U h' (ops j U h Φ) x := by
  rw [ops_rep hf (ops_inv hΦ) r hr, ops_rep hf' (ops_inv hΦ) r' hr']
  simp only [ops_rep hf' hΦ r' hr', ops_rep hf hΦ r hr]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' hc' => Finset.sum_congr rfl fun c hc₁ => ?_
  have := (hc c (hf.mem_toFinset.1 hc₁) c' (hf'.mem_toFinset.1 hc')).eq
  rw [mul_assoc, mul_assoc, ← map_mul, ← map_mul, this]

private theorem rep_in (P : Subgroup G) (hh : h ∈ P)
    (hs : ∀ u ∈ U, ∃ a ∈ P, ∃ t ∈ U, u = a * t ∧ Commute t h) :
    ∃ r : G ⧸ U → G, (∀ c, (QuotientGroup.mk (r c) : G ⧸ U) = c) ∧ ∀ c ∈ dbl U h, r c ∈ P := by
  have h1 : ∀ c : G ⧸ U, ∃ p : G, (QuotientGroup.mk p : G ⧸ U) = c ∧ (c ∈ dbl U h → p ∈ P) := by
    intro c
    by_cases hc : c ∈ dbl U h
    · obtain ⟨u, hu, rfl⟩ := hc
      obtain ⟨a, ha, t, ht, rfl, hcm⟩ := hs u hu
      refine ⟨a * h, ?_, fun _ => P.mul_mem ha hh⟩
      rw [QuotientGroup.eq]
      have : (a * h)⁻¹ * (a * t * h) = t := by
        rw [mul_assoc a t h, hcm.eq]
        group
      rw [this]
      exact ht
    · exact ⟨c.out, QuotientGroup.out_eq' c, fun h' => absurd h' hc⟩
  choose r h2 h3 using h1
  exact ⟨r, h2, h3⟩

end Abs

section Con

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem lev_split (W : ∀ v : Pl K, Subgroup (Gw n v)) (w : Pl K) (g : Gw n w) :
    ∀ u ∈ UpperTheory.ConvolutionTheory.GM.levF W, ∃ a ∈ (AdelicGLn.localEmbedding (K := K) (n := n) w).range, ∃ t ∈ UpperTheory.ConvolutionTheory.GM.levF W, u = a * t ∧
      Commute t (AdelicGLn.localEmbedding w g) := by
  intro u hu
  obtain ⟨-, h1, h2, -, h4⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n w
  have ha : AdelicGLn.localEmbedding w (finAt w (finEmb K n u)) ∈ UpperTheory.ConvolutionTheory.GM.levF W := by
    intro v
    by_cases hv : v = w
    · subst hv
      rw [h1]
      exact hu v
    · rw [h2 v hv]
      exact one_mem _
  refine ⟨_, ⟨finAt w (finEmb K n u), rfl⟩, _, mul_mem (inv_mem ha) hu, (mul_inv_cancel_left _ _).symm, ?_⟩
  have h5 : finAt w (finEmb K n ((AdelicGLn.localEmbedding w (finAt w (finEmb K n u)))⁻¹ * u)) = 1 := by
    rw [map_mul, finAt_mul, map_inv, finAt_inv, h1, inv_mul_cancel]
  exact (h4 _ h5 g).symm

private theorem norm_one_adelic_split_arch_finite (g : G1 K n) (hu : finPart K n (g : AdelicGLn.AdelicGL K n) ∈ AdelicGLn.integralFiniteGL K n) :
    g = archP K n (infPart K n (g : AdelicGLn.AdelicGL K n)) * fin1 (finPart K n (g : AdelicGLn.AdelicGL K n)) := by
  have h1 := detModule_finEmb hu
  have hg := (mem_normOneGL_iff_detModule).1 g.2
  have h2 := infEmb_infPart_mul_finEmb_finPart (g : AdelicGLn.AdelicGL K n)
  have h3 : detModule K n (infEmb K n (infPart K n (g : AdelicGLn.AdelicGL K n))) = 1 := by
    rw [← h2, map_mul, h1, mul_one] at hg
    exact hg
  ext1
  rw [Subgroup.coe_mul, ← retract_infEmb, coe_retractOne, MultiplicityOne.coe_finProj, h1, h3, map_one, inv_one, mul_one, mul_one]
  exact h2.symm

end Con

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.HeckeOperatorExistence

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.HeckeOperatorExistence in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.heckeEx :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.HeckeEx := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ _ κ e he S U hU D hD d A
  obtain ⟨hL, hLle⟩ := (levLaws (K := K) (2 + 2) S).1 U hU
  obtain ⟨⟨h0, hadd⟩, hfix, hinj, htr⟩ := secTr μ₂ τ₁ τ₂ κ e he
  obtain ⟨-, -, -, hac, -⟩ := levLaws (K := K) (2 + 2) S
  haveI := he.haar.prob
  have hHH : Continuous (HP (K := K) 2 2) := (hpSpec (K := K)).2.2.2.1
  have hflc : ∀ f : G1 K (2 + 2) → ℂ, Continuous f → Continuous (flat 0 f) := fun f hf =>
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hHH))).mul hf
  have hfadd : ∀ (f f' : G1 K (2 + 2) → ℂ) (c : ℂ), flat 0 (f + c • f') = flat 0 f + c • flat 0 f' := by
    intro f f' c
    funext x
    simp only [flat, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hA0 : FixA κ e 0 := fun g => by simp
  have hAadd : ∀ f f' : G1 K (2 + 2) → ℂ, Continuous f → Continuous f' → FixA κ e f → FixA κ e f' → ∀ c : ℂ,
      FixA κ e (f + c • f') := by
    intro f f' hc hc' hf hf' c g
    have hi : ∀ f₁ : G1 K (2 + 2) → ℂ, Continuous f₁ → Integrable (fun k => e k * f₁ (g * arc1 k)) κ := fun f₁ h₁ =>
      (he.cont.mul (h₁.comp (continuous_const.mul hac))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h1 : ∀ k, e k * (f + c • f') (g * arc1 k) = e k * f (g * arc1 k) + c * (e k * f' (g * arc1 k)) := by
      intro k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [h1]
    rw [integral_add (hi f hc) ((hi f' hc').const_mul c), integral_const_mul, hf g, hf' g]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsum : ∀ f, IsSec τ₁ τ₂ f → FixA κ e f → ∀ C : Finset (FA K (2 + 2) ⧸ levOn S U),
      ∃ f', IsSec τ₁ τ₂ f' ∧ FixA κ e f' ∧ ∀ x, flat 0 f' x = ∑ c ∈ C, flat 0 f (x * fin1 c.out) := by
    intro f hs hA C
    induction C using Finset.induction_on with
    | empty => exact ⟨0, h0, hA0, fun x => by simp [flat]⟩
    | insert c C hc ih =>
      obtain ⟨f₁, hs₁, hA₁, hx₁⟩ := ih
      obtain ⟨f₂, hs₂, hA₂, hx₂⟩ := htr f c.out hs hA
      refine ⟨f₂ + (1 : ℂ) • f₁, hadd _ _ hs₂ hs₁ 1, hAadd _ _ hs₂.cont hs₁.cont hA₂ hA₁ 1, fun x => ?_⟩
      rw [hfadd, Finset.sum_insert hc, Pi.add_apply, Pi.smul_apply, hx₁, hx₂, one_smul]
  have hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v) := fun v => (A.onto _).1 ⟨v, rfl⟩
  have hFx : ∀ v, FixA κ e (A.sec v) ∧ FixF (levOn S U) (A.sec v) := fun v =>
    (hD.fix _ (hsec v).1.cont).1 (hsec v).2
  have hTc : ∀ v, Continuous (flat 0 (A.sec v)) := fun v => hflc _ (hsec v).1.cont
  have hTi : ∀ v, Inv (MultiplicityOne.finProj K (2 + 2)) (levOn S U) (flat 0 (A.sec v)) := fun v =>
    ((hfix _ (hsec v).1.cont).2 _ hLle).2 (hFx v).2
  have hTj : ∀ a b, flat 0 (A.sec a) = flat 0 (A.sec b) → a = b := fun a b h => A.inj (hinj _ _ h)
  have hTa : ∀ a b : Eu d, flat 0 (A.sec (a + b)) = flat 0 (A.sec a) + flat 0 (A.sec b) := by
    intro a b
    have h1 := hfadd (A.sec a) (A.sec b) 1
    rw [one_smul, one_smul] at h1
    rw [map_add, h1]
  have hTs : ∀ (c : ℂ) (a : Eu d), flat 0 (A.sec (c • a)) = c • flat 0 (A.sec a) := by
    intro c a
    funext x
    simp only [flat, map_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hop_eq : ∀ h (Φ : G1 K (2 + 2) → ℂ), hop (levOn S U) h Φ = ops (MultiplicityOne.finProj K (2 + 2)) (levOn S U) h Φ :=
    fun _ _ => rfl
  have hex : ∀ h v, ∃ v', flat 0 (A.sec v') = hop (levOn S U) h (flat 0 (A.sec v)) := by
    intro h v
    obtain ⟨f', hs', hA', hx'⟩ := hsum _ (hsec v).1 (hFx v).1 (dbl_finite hL h).toFinset
    have h1 : flat 0 f' = hop (levOn S U) h (flat 0 (A.sec v)) := by
      funext x
      rw [hx', hop_eq, ops_sum (dbl_finite hL h)]
    have h2 : FixF (levOn S U) f' :=
      ((hfix _ hs'.cont).2 _ hLle).1 (by rw [h1, hop_eq]; exact ops_inv (hTi v))
    obtain ⟨v', rfl⟩ := (A.onto f').2 ⟨hs', (hD.fix _ hs'.cont).2 ⟨hA', h2⟩⟩
    exact ⟨v', h1⟩
  refine ⟨fun h => ?_, fun w w' hne g g' M M' hM hM' => ?_, fun b φ β hφ hAct h M hM => ?_⟩
  · have hf := dbl_finite hL h
    choose m hm using hex h
    refine ⟨{ toFun := m, map_add' := fun a b => ?_, map_smul' := fun c a => ?_ }, fun v => hm v, fun M' hM' => ?_⟩
    · apply hTj
      rw [hm (a + b), hTa a b, hTa (m a) (m b), hm a, hm b, hop_eq, hop_eq, hop_eq]
      exact ops_add hf
    · apply hTj
      simp only [RingHom.id_apply]
      rw [hm (c • a), hTs c a, hTs c (m a), hm a, hop_eq, hop_eq]
      exact ops_smul hf c
    · exact LinearMap.ext fun v => hTj _ _ ((hM' v).trans (hm v).symm)
  · have hf := dbl_finite hL (AdelicGLn.localEmbedding w g)
    have hf' := dbl_finite hL (AdelicGLn.localEmbedding w' g')
    obtain ⟨r, hr, hrP⟩ := rep_in (AdelicGLn.localEmbedding w).range ⟨g, rfl⟩ (lev_split _ w g)
    obtain ⟨r', hr', hrP'⟩ := rep_in (AdelicGLn.localEmbedding w').range ⟨g', rfl⟩ (lev_split _ w' g')
    refine LinearMap.ext fun v => hTj _ _ ?_
    change flat 0 (A.sec (M (M' v))) = flat 0 (A.sec (M' (M v)))
    rw [hM (M' v), hM' v, hM' (M v), hM v]
    funext x
    refine ops_comm hf hf' (hTi v) r r' hr hr' (fun c hc c' hc' => ?_) x
    obtain ⟨y, hy⟩ := hrP c hc
    obtain ⟨y', hy'⟩ := hrP' c' hc'
    rw [← hy, ← hy']
    exact (UpperTheory.ConvolutionTheory.Tf.locEmb K (2 + 2) w).2.2.2.1 w' hne.symm y y'
  · have hf := dbl_finite hL h
    have hsupp : ∀ g, tens b φ g ≠ 0 → finPart K (2 + 2) (g : AdelicGLn.AdelicGL K (2 + 2)) ∈ levOn S U := by
      intro g hg
      by_cases hc : Continuous (tensFun b φ) ∧ HasCompactSupport (tensFun b φ)
      · have h1 : tens b φ g = tensFun b φ g := by
          rw [tens, dif_pos hc]
          rfl
        rw [h1, tensFun, hφ] at hg
        by_contra hn
        exact hg (by rw [Set.indicator_of_notMem (show _ ∉ (levOn S U : Set (FA K (2 + 2))) from hn), mul_zero])
      · have h1 : tens b φ g = 0 := by
          rw [tens, dif_neg hc]
          rfl
        exact absurd h1 hg
    have hAB := hAct.2.2 0
    refine LinearMap.ext fun v => hTj _ _ ?_
    change flat 0 (A.sec (M (PositivityTheory.Rg.Tf.IntegralApplyAeEq.symb β 0 v))) = flat 0 (A.sec (PositivityTheory.Rg.Tf.IntegralApplyAeEq.symb β 0 (M v)))
    funext x
    rw [hM (PositivityTheory.Rg.Tf.IntegralApplyAeEq.symb β 0 v), ← hAB (M v) x, hop_eq, ops_sum hf]
    have h2 : ∀ c : FA K (2 + 2) ⧸ levOn S U, flat 0 (A.sec (PositivityTheory.Rg.Tf.IntegralApplyAeEq.symb β 0 v)) (x * fin1 c.out) =
        ∫ g, tens b φ g * flat 0 (A.sec v) (x * fin1 c.out * g) ∂μ := fun c => (hAB v _).symm
    simp only [h2]
    have hint : ∀ c : FA K (2 + 2) ⧸ levOn S U, Integrable (fun g => tens b φ g * flat 0 (A.sec v) (x * fin1 c.out * g)) μ :=
      fun c => ((tens b φ).continuous.mul ((hTc v).comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
        (tens b φ).hasCompactSupport.mul_right
    rw [← integral_finset_sum _ fun c _ => hint c]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    by_cases hg : tens b φ g = 0
    · simp [hg]
    have hu := hsupp g hg
    have hd := norm_one_adelic_split_arch_finite g (hLle hu)
    obtain ⟨p, hp⟩ : ∃ p, p = archP K (2 + 2) (infPart K (2 + 2) (g : AdelicGLn.AdelicGL K (2 + 2))) := ⟨_, rfl⟩
    have hpc : ∀ y : FA K (2 + 2), p * fin1 y = fin1 y * p := fun y => by
      rw [hp]
      exact (MultiplicityOne.finProj_mul_archProj_comm y _).symm
    rw [← hp] at hd
    simp only []
    rw [← Finset.mul_sum]
    congr 1
    rw [hM v, hop_eq]
    have h3 : x * g = x * p * MultiplicityOne.finProj K (2 + 2) (finPart K (2 + 2) (g : AdelicGLn.AdelicGL K (2 + 2))) := by
      rw [mul_assoc, ← hd]
    rw [h3, ops_inv (hTi v) _ hu, ops_sum hf]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h4 : x * fin1 c.out * g = x * p * fin1 c.out * fin1 (finPart K (2 + 2) (g : AdelicGLn.AdelicGL K (2 + 2))) := by
      have h5 : x * fin1 c.out * g = x * fin1 c.out * (p * fin1 (finPart K (2 + 2) (g : AdelicGLn.AdelicGL K (2 + 2)))) :=
        congrArg _ hd
      rw [h5, ← mul_assoc (x * fin1 c.out), mul_assoc x (fin1 c.out) p, ← hpc, ← mul_assoc x p]
    rw [h4]
    exact hTi v _ hu _
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.irreducible_cuspidal_weight_component {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2)))
    [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (hP : Pair μ₂ τ₁ τ₂)
    {κ e κ₂ p₁ p₂ k₀} (hA : ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀) {r : ℕ} (w : Fin r → Pl K) (hw : Function.Injective w)
    (U : ∀ v : Pl K, Subgroup (Gw (2 + 2) v)) (hU : Lev U) (D : TypeDat K (2 + 2)) (hD : IsTy D κ e (levOn (im w) U))
    (d : ℕ) (A : Line μ τ₁ τ₂ D d) (P : Submodule ℂ (Eu d))
    (hst : ∀ v ∈ im w, ∀ (g : Gw (2 + 2) v) M, HeckeAt A (levOn (im w) U) (AdelicGLn.localEmbedding v g) M → ∀ x ∈ P, M x ∈ P) :
    P = ⊥ ∨ P = ⊤ := by
  obtain ⟨⟨ι, hι⟩, hemb⟩ := embEx (2 + 2) w hw
  obtain ⟨-, hc1, hc2, -, -, hlev⟩ := hemb ι hι
  have hcf1 : ∀ v : Pl K, GM.cf v (1 : FA K (2 + 2)) = 1 := by
    intro v
    by_cases hv : v ∈ im w
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      have h := hc1 1 i
      rwa [map_one] at h
    · have h := hc2 1 v hv
      rwa [map_one] at h
  have hinU : ∀ u ∈ Subgroup.pi Set.univ (fun i => U (w i)), ι u ∈ levOn (im w) U := fun u hu =>
    (hlev U _).2 ⟨u, 1, (mul_one _).symm, fun i => hu i trivial, fun i => hcf1 _, fun v => by rw [hcf1]; exact one_mem _⟩
  obtain ⟨-, hfl, hinj, -⟩ := secTr μ₂ τ₁ τ₂ κ e hA.idem
  obtain ⟨hZ, hZ'⟩ := zMem μ₂ τ₁ τ₂ κ e hA.idem
  have hle := (levLaws (2 + 2) (im w)).1
  have hsimple := zSimple μ₂ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hP hA w ι hw hι
  have hex := (heckeEx K μ μ₂ τ₁ τ₂ hP κ e hA.idem (im w) U hU D hD d A).1
  let Φ : Eu d →ₗ[ℂ] (G1 K (2 + 2) → ℂ) :=
    { toFun := fun v => flat 0 (A.sec v)
      map_add' := fun a b => by funext x; simp [flat, mul_add]
      map_smul' := fun c a => by funext x; simp [flat, mul_left_comm] }
  have hΦ : ∀ v, Φ v = flat 0 (A.sec v) := fun _ => rfl
  have hΦinj : Function.Injective Φ := fun a b h => A.inj (hinj _ _ h)
  have hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ FixA κ e (A.sec v) ∧ FixF (levOn (im w) U) (A.sec v) := fun v => by
    obtain ⟨h1, h2⟩ := (A.onto _).1 (LinearMap.mem_range_self A.sec v)
    exact ⟨h1, (hD.fix _ h1.cont).1 h2⟩
  have hfixΦ : ∀ v, FixF (levOn (im w) U) (Φ v) := fun v =>
    ((hfl _ (hsec v).1.cont).2 _ (hle U hU).2).2 (hsec v).2.2
  have hmem : ∀ v, Φ v ∈ Zs τ₁ τ₂ κ e (im w) := fun v =>
    (hZ _ _).2 ⟨_, (hsec v).1, (hsec v).2.1, ⟨U, hU, (hsec v).2.2⟩, rfl⟩
  have hCO : ∀ i, CO (U (w i)) := fun i => (hU (w i)).1
  have hCOpi : CO (Subgroup.pi Set.univ fun i => U (w i)) := by
    refine ⟨?_, ?_⟩
    · rw [Subgroup.coe_pi]; exact isCompact_univ_pi fun i => (hCO i).1
    · rw [Subgroup.coe_pi]; exact isOpen_set_pi Set.finite_univ fun i _ => (hCO i).2
  have hrS : ∀ g (φ : G1 K (2 + 2) → ℂ) x, rS ι g φ x = φ (x * fin1 (ι g)) := fun _ _ _ => rfl
  have hQfix : ∀ φ ∈ P.map Φ, ∀ u ∈ Subgroup.pi Set.univ fun i => U (w i), rS ι u φ = φ := by
    rintro _ ⟨v, -, rfl⟩ u hu
    funext x
    rw [hrS]
    exact hfixΦ v _ (hinU u hu) x
  have hQhop : ∀ g, ∀ φ ∈ P.map Φ, hopR (rS ι) (Subgroup.pi Set.univ fun i => U (w i)) g φ ∈ P.map Φ := by
    refine hopProd (rS ι) (fun i => U (w i)) (P.map Φ) hCO hQfix ?_
    rintro i g _ ⟨v, hv, rfl⟩
    obtain ⟨M, hM, -⟩ := hex (AdelicGLn.localEmbedding (w i) g)
    refine ⟨M v, hst (w i) (Finset.mem_image_of_mem _ (Finset.mem_univ i)) g M hM v hv, ?_⟩
    rw [← hopEmb (2 + 2) w ι hw hι U hU _ (hfixΦ v), hι i g]
    exact hM v
  rcases heckeSimple (rS ι) (Zs τ₁ τ₂ κ e (im w)) _ hCOpi hsimple (fun φ hφ => (hZ' w ι hw hι φ hφ).1) (P.map Φ)
    (by rintro _ ⟨v, -, rfl⟩; exact hmem v) hQfix hQhop with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun v hv => hΦinj ?_
    rw [map_zero]
    exact (Submodule.eq_bot_iff _).1 h _ ⟨v, hv, rfl⟩
  · right
    refine Submodule.eq_top_iff'.2 fun v => ?_
    have hv : ∀ u ∈ Subgroup.pi Set.univ fun i => U (w i), rS ι u (Φ v) = Φ v := by
      intro u hu
      funext x
      rw [hrS]
      exact hfixΦ v _ (hinU u hu) x
    obtain ⟨v', hv', he⟩ := h _ (hmem v) hv
    rwa [← hΦinj he]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.irrW :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.IrrW := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP κ e κ₂ p₁ p₂ k₀ hA S U hU D hD d A P hst
  obtain ⟨r, w, hw, rfl⟩ : ∃ (r : ℕ) (w : Fin r → Pl K), Function.Injective w ∧ S = im w := by
    refine ⟨S.card, fun i => (S.equivFin.symm i : Pl K), fun a b h => S.equivFin.symm.injective (Subtype.ext h), ?_⟩
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun hv => ⟨S.equivFin ⟨v, hv⟩, by simp⟩, fun ⟨i, hi⟩ => hi ▸ (S.equivFin.symm i).2⟩
  exact irreducible_cuspidal_weight_component μ μ₂ τ₁ τ₂ hP hA w hw U hU D hD d A P hst
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical InnerProductSpace ComplexOrder

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.famScalar :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
          [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ κ e κ₂ p₁ p₂ k₀, ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
          ∀ (S : Finset (Pl K)) (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)), Lev U → ∀ (D : TypeDat K (2 + 2)), IsTy D κ e (levOn S U) →
          ∀ (d : ℕ) (A : Line μ τ₁ τ₂ D d) (𝔞 : Amp μ) (φ : TF K (2 + 2)) (c : ℂ) (β : ℝ → Eu d →L[ℂ] Eu d), 𝔞.U = levOn S U →
          (∀ x, φ x = (levOn S U : Set (FA K (2 + 2))).indicator 1 x) → c ≠ 0 → Rop μ (c • tens 𝔞.a₀ φ) = 𝔞.A → ActsBy μ A (c • tens 𝔞.a₀ φ) β →
          (∃ v g, ∫ y, 𝔞.a₀ y * flat 0 (A.sec v) (g * archP K (2 + 2) y) ∂𝔞.ν ≠ 0) → 0 < d ∧ ∃ x : ℝ, 0 < x ∧ symb β 0 = (x : ℂ) • (1 : Eu d →L[ℂ] Eu d) := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP κ e κ₂ p₁ p₂ k₀ hL S U hLev D hD d A 𝔞 φ c β hU hφ hc hR hA hne
  obtain ⟨v₀, g₀, hI⟩ := hne
  have hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v) := fun v => (A.onto _).1 ⟨v, rfl⟩
  have hflat0 : ∀ x, flat 0 (0 : G1 K (2 + 2) → ℂ) x = 0 := fun x => by simp [flat]
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exfalso
      apply hI
      rw [show v₀ = 0 from Subsingleton.elim _ _, map_zero]
      simp only [hflat0, mul_zero, integral_zero]
    · exact h
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨h0, h1, -⟩ := UpperTheory.ConvolutionTheory.evEx K (2 + 2) (by norm_num) μ 𝔞
  have hpos := (posSymb A.J 𝔞.A β hA.1 (hR ▸ hA.2.1) h0 h1).1
  have hcomm : ∀ h M, HeckeAt A (levOn S U) h M → Commute M (symb β 0 : Eu d →ₗ[ℂ] Eu d) := by
    have hA' : ActsBy μ A (tens (c • 𝔞.a₀) φ) β := by
      rw [((UpperTheory.ConvolutionTheory.Tf.tensApply K (2 + 2) (by norm_num) 𝔞.a₀ φ).2.2.2.2 c).1]
      exact hA
    exact (heckeEx K μ μ₂ τ₁ τ₂ hP κ e hL.idem S U hLev D hD d A).2.2 _ φ β hφ hA'
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue (symb β 0 : Eu d →ₗ[ℂ] Eu d)
  have hE : Module.End.eigenspace (symb β 0 : Eu d →ₗ[ℂ] Eu d) l = ⊤ := by
    refine (irrW K μ μ₂ τ₁ τ₂ hP κ e κ₂ p₁ p₂ k₀ hL S U hLev D hD d A _ fun w _ g M hM v hv => ?_).resolve_left hl
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have h := LinearMap.congr_fun (hcomm _ M hM).eq v
    simp only [Module.End.mul_apply] at h
    rw [← h, hv, map_smul]
  have hT : ∀ v, symb β 0 v = l • v := fun v =>
    Module.End.mem_eigenspace_iff.1 (hE ▸ Submodule.mem_top : v ∈ Module.End.eigenspace (symb β 0 : Eu d →ₗ[ℂ] Eu d) l)
  have hl0 : 0 ≤ l := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Eu d)
    have hp := (ContinuousLinearMap.nonneg_iff_isPositive _).1 hpos
    have h2 := hp.inner_nonneg_right v
    rw [hT, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
    have hn : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
    have h3 : 0 ≤ l * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      simpa using h2
    obtain ⟨a, b⟩ := Complex.nonneg_iff.1 h3
    rw [Complex.re_mul_ofReal] at a
    rw [Complex.im_mul_ofReal] at b
    refine Complex.nonneg_iff.2 ⟨le_of_mul_le_mul_right (by simpa using a) hn, ?_⟩
    exact ((mul_eq_zero.1 (by simpa using b.symm)).resolve_right hn.ne').symm
  have hlne : l ≠ 0 := by
    rintro rfl
    obtain ⟨⟨c', hc', hint, -⟩, -⟩ := tensAmp K (2 + 2) (by norm_num) μ 𝔞 φ (fun x => by rw [hφ, hU])
    have hH : Continuous fun x : G1 K (2 + 2) => Complex.exp ((0 + 2) * (HP 2 2 x : ℂ)) :=
      Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hpSpec.2.2.2.1))
    have hΘ : Continuous (flat 0 (A.sec v₀)) := hH.mul (hsec v₀).1.cont
    have hfix : FixF 𝔞.U (flat 0 (A.sec v₀)) := by
      refine (((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.secTr μ₂ τ₁ τ₂ κ e hL.idem).2.1 _ (hsec v₀).1.cont).2 𝔞.U 𝔞.le).2 ?_
      rw [hU]
      exact ((hD.fix _ (hsec v₀).1.cont).1 (hsec v₀).2).2
    have e1 := hA.2.2 0 v₀ g₀
    rw [hT, zero_smul, map_zero, hflat0] at e1
    simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, mul_assoc] at e1
    rw [integral_const_mul, hint _ hΘ hfix g₀] at e1
    exact mul_ne_zero hc (mul_ne_zero (Complex.ofReal_ne_zero.2 hc'.ne') hI) e1
  obtain ⟨a, b⟩ := Complex.nonneg_iff.1 hl0
  have hre : l = ((l.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← b])
  refine ⟨hd, l.re, lt_of_le_of_ne a fun h => hlne (by rw [hre, ← h]; simp), ?_⟩
  ext1 v
  rw [hT, ← hre]
  simp
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem fix_of_avg {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (ν : Measure G)
    (e : G → ℂ) (u : G) (hu : MeasurePreserving (u * ·) ν ν) (he : ∀ᵐ k ∂ν, e (u * k) = e k) (w : H)
    (hw : ∫ k, e k • π k w ∂ν = w) : π u w = w := by
  by_cases hi : Integrable (fun k => e k • π k w) ν
  · have h1 := (π u).integral_comp_comm hi
    have h2 := hu.integral_comp (Homeomorph.mulLeft u).measurableEmbedding (fun k => e k • π k w)
    rw [hw] at h1 h2
    rw [← h1]
    refine Eq.trans (integral_congr_ae ?_) h2
    filter_upwards [he] with k hk
    rw [map_smul, hk, π.map_mul_apply]
  · rw [integral_undef hi] at hw
    rw [← hw, map_zero]

private theorem coset_bij {G L : Type*} [Group G] [Group L] (loc : L →* G) (p : G →* L) (h1 : ∀ x, p (loc x) = x)
    (hc : ∀ h, p h = 1 → ∀ x, loc x * h = h * loc x) (J : Subgroup L) (x : L) (U : Subgroup G)
    (hJU : ∀ j ∈ J, loc j ∈ U) (hUJ : ∀ u ∈ U, p u ∈ J) :
    Set.BijOn (fun c : L ⧸ J => (QuotientGroup.mk (loc c.out) : G ⧸ U)) {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}
      {c | ∃ k ∈ U, c = QuotientGroup.mk (k * loc x)} := by
  have key : ∀ y : L, (QuotientGroup.mk (loc (QuotientGroup.mk y : L ⧸ J).out) : G ⧸ U) = QuotientGroup.mk (loc y) := by
    intro y
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul J y
    rw [hj, map_mul, QuotientGroup.mk_mul_of_mem _ (hJU _ j.2)]
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact ⟨loc k, hJU k hk, by simp only [key, map_mul]⟩
  · intro a _ b _ hab
    have h := hUJ _ (QuotientGroup.eq.1 hab)
    rw [map_mul, map_inv, h1, h1] at h
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
    exact QuotientGroup.eq.2 h
  · rintro _ ⟨k, hk, rfl⟩
    refine ⟨QuotientGroup.mk (p k * x), ⟨p k, hUJ k hk, rfl⟩, ?_⟩
    have hp : p (k * (loc (p k))⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    have e1 : k * loc x = loc (p k * x) * (k * (loc (p k))⁻¹) := by
      rw [hc _ hp, map_mul]
      group
    simp only [key]
    rw [e1, QuotientGroup.mk_mul_of_mem _ (U.mul_mem hk (U.inv_mem (hJU _ (hUJ k hk))))]

private theorem hop_prj {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (Gw n w)) (x : Gw n w) (U : Subgroup (FA K n)) (hJ : CO J)
    (hJU : ∀ j ∈ J, AdelicGLn.localEmbedding w j ∈ U) (hUJ : ∀ u ∈ U, finAt w (finEmb K n u) ∈ J) :
    (∑ᶠ c ∈ {c : FA K n ⧸ U | ∃ k ∈ U, c = QuotientGroup.mk (k * AdelicGLn.localEmbedding w x)}, rhoF μ c.out) ∘L
      prj (fixF μ U) = Hop μ w J x ∘L prj (fixF μ U) := by
  obtain ⟨hfin, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J x hJ.2 hJ.1
  obtain ⟨-, hmemU, hPU, -, habs, hmul, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U
  obtain ⟨-, hmemJ, -, hPJ, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))
  obtain ⟨-, hl1, -, -, hl5⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n w
  have hb := coset_bij (AdelicGLn.localEmbedding w)
    (MonoidHom.mk' (fun g : FA K n => finAt w (finEmb K n g)) fun a b => by rw [map_mul, finAt_mul]) hl1 hl5 J x U hJU hUJ
  have hfin' := hb.image_eq ▸ hfin.image _
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : prj (fixL μ w J) (prj (fixF μ U) v) = prj (fixF μ U) v := by
    refine hPJ _ ((hmemJ _).2 ?_)
    rintro _ ⟨j, hj, rfl⟩
    exact (hmemU _).1 (hPU v) _ (hJU j hj)
  rw [Hop, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hv]
  let ev : (LL μ →L[ℂ] LL μ) →+ LL μ := AddMonoidHom.mk' (fun T => T (prj (fixF μ U) v)) fun _ _ => rfl
  refine (ev.map_finsum_mem _ hfin').trans (Eq.trans ?_ (ev.map_finsum_mem _ hfin).symm)
  refine (finsum_mem_eq_of_bijOn _ hb fun c _ => ?_).symm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (AdelicGLn.localEmbedding w c.out)
  change rhoF μ _ (prj (fixF μ U) v) = rhoF μ _ (prj (fixF μ U) v)
  rw [hu, hmul, ContinuousLinearMap.comp_apply, (hmemU _).1 (hPU v) u u.2]

private theorem level_facts {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (D : TypeDat K n) (U : Subgroup (FA K n)) (hD : D.Level U) (hle : U ≤ AdelicGLn.integralFiniteGL K n) :
    IsOpen (U : Set (FA K n)) ∧ IsCompact (U : Set (FA K n)) ∧ ∀ v, D.FixedByTypeProjector μ v → v ∈ fixF μ U := by
  have hpe : ∀ u ∈ AdelicGLn.integralFiniteGL K n, ((fin1 u : G1 K n) : AdelicGLn.AdelicGL K n) = finEmb K n u := by
    intro u hu
    exact congrArg Subtype.val (MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact hu)))
  have hiff : ∀ u ∈ AdelicGLn.integralFiniteGL K n, fin1 u ∈ D.U ↔ u ∈ U := by
    intro u hu
    have h := hD.1 (fin1 u) (by rw [hpe u hu, prodEquiv_finEmb])
    rwa [hpe u hu, prodEquiv_finEmb] at h
  have ho : IsOpen (U : Set (FA K n)) := by
    obtain ⟨O, hO, hUO⟩ := D.isOpen
    have : (U : Set (FA K n)) = (AdelicGLn.integralFiniteGL K n : Set (FA K n)) ∩ finEmb K n ⁻¹' O := by
      ext u
      constructor
      · intro hu
        have h := ((hUO _).1 ((hiff u (hle hu)).2 hu)).1
        rw [hpe u (hle hu)] at h
        exact ⟨hle hu, h⟩
      · rintro ⟨hu, h⟩
        refine (hiff u hu).1 ((hUO _).2 ?_)
        rw [hpe u hu]
        exact ⟨h, finEmb_mem_maxCompact hu⟩
    rw [this]
    exact (AdelicGLn.isOpen_integralFiniteGL K n).inter (hO.preimage continuous_finEmb)
  refine ⟨ho, (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (U.isClosed_of_isOpen ho) hle, fun v hv => ?_⟩
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U).2.1 v).2 fun u hu => ?_
  have hu' := (hiff u (hle hu)).2 hu
  refine fix_of_avg _ D.ν D.e (fin1 u) (D.inv _ hu') ?_ v hv
  filter_upwards [D.supp] with k hk
  exact hD.2.2 _ hu' (by rw [hpe u (hle hu), prodEquiv_finEmb]) k hk

private theorem comm_proj {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (P T : H →L[ℂ] H) (F : Submodule ℂ H) (hP : IsOrthogonalProjectionTwoLines J J' P)
    (hJ : ∀ u, J u ∈ F) (hJ' : ∀ u, J' u ∈ F) (hT : Commute T (prj F))
    (hY : (T ∘L prj F) ∘L P = P ∘L (T ∘L prj F)) : T ∘L P = P ∘L T := by
  have h0 : ∀ a ∈ F, ∀ h, inner ℂ a (h - prj F h) = 0 := fun a ha h =>
    inner_eq_zero_symm.1 (Submodule.starProjection_inner_eq_zero h a (F.le_topologicalClosure ha))
  have h1 : P * prj F = P := by
    refine ContinuousLinearMap.ext fun h => ?_
    have := (hP.2.2 (h - prj F h)).2 ⟨fun u => h0 _ (hJ u) h, fun u => h0 _ (hJ' u) h⟩
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  have hQ : IsSelfAdjoint (prj F) := isSelfAdjoint_starProjection _
  have h2 : prj F * P = P := by
    have := congrArg star h1
    rwa [star_mul, hQ.star_eq, hP.1.star_eq] at this
  change (T * prj F) * P = P * (T * prj F) at hY
  change T * P = P * T
  rw [mul_assoc, h2, hT.eq, ← mul_assoc, h1] at hY
  exact hY

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.uiwAct :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
          [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ (S : Finset (Pl K)) (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)), Lev U → ∀ (D : TypeDat K (2 + 2)), D.Level (levOn S U) →
          ∀ (d d' : ℕ) (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d'), ∀ w ∈ S, U w = GLnLocal.iwahori (w.adicCompletion K) (2 + 2) → ∀ ν : Fin (2 + 2) → ℤ,
          (∃ s, Act A.J (Uiw μ w ν) s ∧
            HeckeAt A (levOn S U) (AdelicGLn.localEmbedding w (Cartan.diagPow (w.adicCompletion K) (2 + 2) ν)) (s 0 : Eu d →ₗ[ℂ] Eu d)) ∧
          ∀ P, IsOrthogonalProjectionTwoLines A.J A'.J P → Uiw μ w ν ∘L P = P ∘L Uiw μ w ν := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp S U hU D hD d d' A A' w hw hI ν
  have hmem : ∀ u, u ∈ levOn S U ↔ ∀ v, finAt v (finEmb K (2 + 2) u) ∈
      (if v ∈ S then U v else GLnLocal.integralGL (v.adicCompletion K) (2 + 2)) := fun u => Iff.rfl
  have hle : levOn S U ≤ AdelicGLn.integralFiniteGL K (2 + 2) := by
    intro u hu
    refine (AdelicGLn.mem_integralFiniteGL_iff_forall K (2 + 2)).2 fun v => ?_
    have h := (hmem u).1 hu v
    split_ifs at h
    · exact (hU v).2 h
    · exact h
  obtain ⟨-, hl1, hl2, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K (2 + 2) w
  have hJU : ∀ j ∈ U w, AdelicGLn.localEmbedding w j ∈ levOn S U := by
    intro j hj
    refine (hmem _).2 fun v => ?_
    by_cases hv : v = w
    · subst hv
      rw [hl1, if_pos hw]
      exact hj
    · rw [hl2 v hv]
      exact one_mem _
  have hUJ : ∀ u ∈ levOn S U, finAt w (finEmb K (2 + 2) u) ∈ U w := by
    intro u hu
    have h := (hmem u).1 hu w
    rwa [if_pos hw] at h
  obtain ⟨ho, hc, hfix⟩ := level_facts μ D _ hD hle
  have hT : Uiw μ w ν = Hop μ w (U w) (Cartan.diagPow (w.adicCompletion K) (2 + 2) ν) := by rw [hI]; rfl
  obtain ⟨⟨s, ⟨u, κ, hκ, hact, hs⟩, hsec⟩, hcomm⟩ := cosAct K μ μ₂ τ₁ τ₂ hp D d d' A A' _ hD hle _ _
    (hop_prj μ w (U w) (Cartan.diagPow (w.adicCompletion K) (2 + 2) ν) _ (hU w).1 hJU hUJ).symm
  have hA : ∀ x, A.J x ∈ fixF μ (levOn S U) := fun x => hfix _ (ctZero K μ μ₂ τ₁ τ₂ hp D d d' A A' x).2.1
  have hA' : ∀ x, A'.J x ∈ fixF μ (levOn S U) := fun x =>
    hfix _ (ctZero K μ μ₂ τ₂ τ₁ ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩ D d' d A' A x).2.1
  rw [hT]
  refine ⟨⟨s, ⟨u, κ, hκ, fun x => ?_, hs⟩, fun v => funext fun x => hsec 0 v x⟩, fun P hP => ?_⟩
  · rw [← hact x, ContinuousLinearMap.comp_apply, (UpperTheory.ConvolutionTheory.Tf.commPrj K (2 + 2) μ _).2.2.2.1 _ (hA x)]
  · refine comm_proj A.J A'.J P _ _ hP hA hA' ?_ (hcomm P hP)
    refine (UpperTheory.ConvolutionTheory.Tf.hopLevel K (2 + 2) μ Measure.haar w (U w) _ _ (hU w).1.2 (hU w).1.1 ho hc ?_ hUJ).1
    rintro _ ⟨j, hj, rfl⟩
    exact hJU j hj
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem hopR_single {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (∀ i, G i) V) (U : ∀ i, Subgroup (G i)) (i : Fin r) (t : G i) (v : V)
    (hv : ∀ u ∈ Subgroup.pi Set.univ U, ρ u v = v) :
    hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i t) v =
      hopR (ρ.comp (MonoidHom.mulSingle G i)) (U i) t v := by
  have hsing : ∀ {a b : G i}, a⁻¹ * b ∈ U i →
      (Pi.mulSingle i a : ∀ j, G j)⁻¹ * Pi.mulSingle i b ∈ Subgroup.pi Set.univ U := by
    intro a b hab j _
    by_cases hj : j = i
    · subst hj
      simpa using hab
    · simpa [Pi.mulSingle_eq_of_ne hj] using (U j).one_mem
  let f : G i ⧸ U i → (∀ j, G j) ⧸ Subgroup.pi Set.univ U :=
    Quotient.lift (fun a => (QuotientGroup.mk (Pi.mulSingle i a) : (∀ j, G j) ⧸ Subgroup.pi Set.univ U)) (by
      intro a b hab
      exact QuotientGroup.eq.2 (hsing (QuotientGroup.leftRel_apply.1 hab)))
  have hf : ∀ a : G i, f (QuotientGroup.mk a) = QuotientGroup.mk (Pi.mulSingle i a) := fun _ => rfl
  have hinj : Function.Injective f := by
    intro c c' h
    induction c using QuotientGroup.induction_on with | _ a => ?_
    induction c' using QuotientGroup.induction_on with | _ b => ?_
    rw [hf, hf, QuotientGroup.eq] at h
    have := h i (Set.mem_univ i)
    simpa [QuotientGroup.eq] using this
  unfold hopR
  symm
  refine finsum_mem_eq_of_bijOn f ⟨?_, hinj.injOn, ?_⟩ ?_
  · rintro c ⟨u, hu, rfl⟩
    refine ⟨Pi.mulSingle i u, ?_, ?_⟩
    · intro j _
      by_cases hj : j = i
      · subst hj
        simpa using hu
      · simpa [Pi.mulSingle_eq_of_ne hj] using (U j).one_mem
    · rw [hf, Pi.mulSingle_mul]
  · rintro c ⟨u, hu, rfl⟩
    refine ⟨QuotientGroup.mk (u i * t), ⟨u i, hu i (Set.mem_univ i), rfl⟩, ?_⟩
    rw [hf, QuotientGroup.eq]
    intro j _
    by_cases hj : j = i
    · subst hj
      simp
    · simpa [Pi.mulSingle_eq_of_ne hj] using hu j (Set.mem_univ j)
  · intro c _
    have hc : (QuotientGroup.mk (f c).out : (∀ j, G j) ⧸ Subgroup.pi Set.univ U) = QuotientGroup.mk (Pi.mulSingle i c.out) := by
      rw [QuotientGroup.out_eq', ← hf, QuotientGroup.out_eq']
    have hu := QuotientGroup.eq.1 hc
    calc (ρ.comp (MonoidHom.mulSingle G i)) c.out v
        = ρ ((f c).out * ((f c).out⁻¹ * Pi.mulSingle i c.out)) v := by
          rw [mul_inv_cancel_left]; rfl
      _ = ρ (f c).out (ρ ((f c).out⁻¹ * Pi.mulSingle i c.out) v) := by rw [map_mul]; rfl
      _ = ρ (f c).out v := by rw [hv _ hu]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.heckeInj :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.HeckeInj := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP κ e he S U hU D hD d A w hw hUw ν hν M hM
  obtain ⟨r, w', hinj, rfl⟩ : ∃ (r : ℕ) (w' : Fin r → Pl K), Function.Injective w' ∧ im w' = S := by
    refine ⟨S.card, fun j => (S.equivFin.symm j : Pl K), ?_, ?_⟩
    · intro a b h
      exact S.equivFin.symm.injective (Subtype.ext h)
    · ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, rfl⟩
        exact (S.equivFin.symm j).2
      · intro hx
        exact ⟨S.equivFin ⟨x, hx⟩, by simp⟩
  obtain ⟨i, rfl⟩ : ∃ i, w' i = w := by simpa [im] using hw
  obtain ⟨⟨ι, hι⟩, hemb⟩ := embEx (K := K) (2 + 2) w' hinj
  obtain ⟨-, -, -, -, -, hmem⟩ := hemb ι hι
  have hlev := (levLaws (K := K) (2 + 2) (im w')).1 U hU
  have hsec := secTr μ₂ τ₁ τ₂ κ e he
  have hz := zMem μ₂ τ₁ τ₂ κ e he
  have hZ2 := hz.2 w' ι hinj hι
  have hflat0 : flat 0 (0 : G1 K (2 + 2) → ℂ) = 0 := by
    funext x
    simp [flat]
  refine (injective_iff_map_eq_zero M).2 fun v hv => ?_
  have hfS : IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v) := (A.onto _).1 ⟨v, rfl⟩
  have hfix := (hD.fix _ hfS.1.cont).1 hfS.2
  have hFφ : FixF (levOn (im w') U) (flat 0 (A.sec v)) := ((hsec.2.1 _ hfS.1.cont).2 _ hlev.2).2 hfix.2
  have hZ : flat 0 (A.sec v) ∈ Zs τ₁ τ₂ κ e (im w') :=
    (hz.1 _ _).2 ⟨_, hfS.1, hfix.1, ⟨U, hU, hfix.2⟩, rfl⟩
  have hWfix : ∀ u ∈ Subgroup.pi Set.univ (fun j => U (w' j)), rS ι u (flat 0 (A.sec v)) = flat 0 (A.sec v) := by
    intro u hu
    have hin : ι u ∈ levOn (im w') U :=
      (hmem U _).2 ⟨u, 1, by simp, fun j => hu j (Set.mem_univ j), fun j => by simp [GM.cf], fun x => by simp [GM.cf, one_mem]⟩
    funext x
    exact hFφ _ hin x
  have hzero : hopR ((rS ι).comp (MonoidHom.mulSingle (fun j => Gw (2 + 2) (w' j)) i))
      (GLnLocal.iwahori ((w' i).adicCompletion K) (2 + 2)) (Cartan.diagPow ((w' i).adicCompletion K) (2 + 2) ν)
      (flat 0 (A.sec v)) = 0 := by
    have h1 := hM v
    rw [hv, map_zero, hflat0, ← hι i, hopEmb (2 + 2) w' ι hinj hι U hU _ hFφ,
      hopR_single (rS ι) (fun j => U (w' j)) i _ _ hWfix, hUw] at h1
    exact h1.symm
  have hφ : flat 0 (A.sec v) = 0 :=
    iwInj (2 + 2) (w' i) ((rS ι).comp (MonoidHom.mulSingle (fun j => Gw (2 + 2) (w' j)) i)) (Zs τ₁ τ₂ κ e (im w'))
      (fun g φ hφ => (hZ2 φ hφ).2 _)
      (fun φ hφ => (hZ2 φ hφ).1.preimage (continuous_mulSingle i))
      ν hν _ hZ
      (fun u hu => hWfix _ fun j _ => by
        by_cases hj : j = i
        · subst hj
          simpa [hUw] using hu
        · simpa [Pi.mulSingle_eq_of_ne hj] using (U (w' j)).one_mem)
      hzero
  have hs0 : A.sec v = 0 := hsec.2.2.1 _ _ (hφ.trans hflat0.symm)
  exact A.inj (hs0.trans (map_zero A.sec).symm)
end

section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem exists_trace_pow_ne {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (R : Module.End ℂ W) (hR : Function.Injective R) : ∃ j : ℕ, LinearMap.trace ℂ W (R ^ (j + 1)) ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : R.charpoly.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨m, hm, hm0⟩ := (LinearMap.charpoly_constantCoeff_eq_zero_iff R).1 h0
    exact hm (hR (by rw [hm0, map_zero]))
  have h1 := congrArg (LinearMap.trace ℂ W) (LinearMap.aeval_self_charpoly R)
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ', map_add, map_sum, map_zero] at h1
  simp only [map_smul, h, mul_zero, Finset.sum_const_zero, zero_add, pow_zero, LinearMap.trace_one, smul_eq_mul] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact h0 h2
  · exact (Module.finrank_pos (R := ℂ) (M := W)).ne' (by exact_mod_cast h2)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.finTw :
    FinTw := by
  intro W X _ _ _ _ T hc hirr U hU i x hinj
  obtain ⟨c, hc0, H⟩ := UpperTheory.ConvolutionTheory.L1.algTrace W X 1 T
    (by
      intro a b hab y z
      fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · exact hc y z
      · exact (hc z y).symm
      · exact absurd rfl hab) hirr U hU
  have hcom : ∀ (k : ℕ) (j : Fin 2), j ≠ i → ∀ y, Commute (T i x ^ k) (T j y) := by
    intro k j hj y
    apply Commute.pow_left
    fin_cases i <;> fin_cases j
    · exact absurd rfl hj
    · exact hc x y
    · exact (hc y x).symm
    · exact absurd rfl hj
  rw [Filter.frequently_atTop]
  intro N
  have hN : Function.Injective (T i x ^ N : Module.End ℂ W) := by
    rw [Module.End.coe_pow]
    exact hinj.iterate N
  obtain ⟨j, hj⟩ := exists_trace_pow_ne _ hN
  refine ⟨N * (j + 1), Nat.le_mul_of_pos_right N j.succ_pos, ?_⟩
  rw [H i _ (hcom _), pow_mul]
  exact mul_ne_zero hc0 hj
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

private theorem coset_tr {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f) (t : H ≃* H)
    (ht : ∀ g, t (t g) = g) (L : Subgroup G) (hL : ∀ u ∈ L, ∃ u' ∈ L, t (f u) = f u') (h h' : G) (hh : t (f h) = f h')
    (ψ : H → ℂ) (hψ : ∀ u ∈ L, ∀ y, ψ (y * f u) = ψ y) (x : H) :
    ∑ᶠ c ∈ {c : G ⧸ L | ∃ u ∈ L, c = QuotientGroup.mk (u * h)}, ψ (x * f c.out) =
      ∑ᶠ c ∈ {c : G ⧸ L | ∃ u ∈ L, c = QuotientGroup.mk (u * h')}, ψ (t (t x * f c.out)) := by
  have hh' : t (f h') = f h := by rw [← hh, ht]
  have dec : ∀ (a : G) (c : G ⧸ L), c = QuotientGroup.mk a → ∃ l ∈ L, c.out = a * l := by
    intro a c hc
    have : (QuotientGroup.mk c.out : G ⧸ L) = QuotientGroup.mk a := by rw [QuotientGroup.out_eq', hc]
    have h2 := QuotientGroup.eq.1 this.symm
    exact ⟨_, h2, by group⟩
  have imgOf : ∀ (p p' : G), t (f p) = f p' → ∀ u ∈ L, ∀ l ∈ L, ∃ g' u' l', u' ∈ L ∧ l' ∈ L ∧ g' = u' * p' * l' ∧ t (f (u * p * l)) = f g' := by
    intro p p' hp u hu l hl
    obtain ⟨u', hu', e1⟩ := hL u hu
    obtain ⟨l', hl', e2⟩ := hL l hl
    exact ⟨_, u', l', hu', hl', rfl, by simp only [map_mul, e1, e2, hp]⟩
  have key : ∀ c ∈ {c : G ⧸ L | ∃ u ∈ L, c = QuotientGroup.mk (u * h)}, ∃ g', t (f c.out) = f g' ∧
      ∃ u' ∈ L, ∃ l' ∈ L, g' = u' * h' * l' := by
    rintro c ⟨u, hu, rfl⟩
    obtain ⟨l, hl, e⟩ := dec _ _ rfl
    obtain ⟨g', u', l', hu', hl', e1, e2⟩ := imgOf h h' hh u hu l hl
    exact ⟨g', by rw [e, e2], u', hu', l', hl', e1⟩
  classical
  let m : G ⧸ L → G ⧸ L := fun c => if hc : ∃ g', t (f c.out) = f g' then QuotientGroup.mk hc.choose else c
  have hm : ∀ c g', t (f c.out) = f g' → m c = QuotientGroup.mk g' := by
    intro c g' hg
    have hc : ∃ g', t (f c.out) = f g' := ⟨g', hg⟩
    have : hc.choose = g' := hf (hc.choose_spec.symm.trans hg)
    simp only [m, dif_pos hc, this]
  refine finsum_mem_eq_of_bijOn m ⟨?_, ?_, ?_⟩ ?_
  · intro c hc
    obtain ⟨g', e, u', hu', l', hl', rfl⟩ := key c hc
    refine ⟨u', hu', ?_⟩
    rw [hm c _ e]
    exact QuotientGroup.eq.2 (by simpa [mul_assoc] using hl')
  · intro c hc c' hc' e
    obtain ⟨g, eg, -⟩ := key c hc
    obtain ⟨g', eg', -⟩ := key c' hc'
    rw [hm c _ eg, hm c' _ eg'] at e
    obtain ⟨l', hl', e2⟩ := hL _ (QuotientGroup.eq.1 e)
    have e3 : f (c.out⁻¹ * c'.out) = f l' := by
      rw [← e2]
      simp only [map_mul, map_inv, ← eg, ← eg', ht]
    have e4 : c.out⁻¹ * c'.out ∈ L := by rw [hf e3]; exact hl'
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
    exact QuotientGroup.eq.2 e4
  · rintro c' ⟨u', hu', rfl⟩
    obtain ⟨u, hu, e1⟩ := hL u' hu'
    have e0 : t (f (u * h)) = f (u' * h') := by
      have : f (u * h) = t (f (u' * h')) := by simp only [map_mul, e1, hh']
      rw [this, ht]
    refine ⟨QuotientGroup.mk (u * h), ⟨u, hu, rfl⟩, ?_⟩
    obtain ⟨l, hl, e⟩ := dec (u * h) _ rfl
    obtain ⟨l', hl', e2⟩ := hL l hl
    have e3 : t (f (QuotientGroup.mk (u * h) : G ⧸ L).out) = f (u' * h' * l') := by
      rw [e, map_mul, map_mul, e0, e2]
      simp only [map_mul]
    rw [hm _ _ e3]
    exact (QuotientGroup.eq.2 (by simpa [mul_assoc] using L.inv_mem hl')).symm
  · intro c hc
    obtain ⟨g', e, -⟩ := key c hc
    obtain ⟨l, hl, e2⟩ := dec g' (m c) (hm c _ e)
    obtain ⟨l', hl', e3⟩ := hL l hl
    rw [e2, map_mul, map_mul, map_mul, ht, ← e, ht, e3, ← mul_assoc, hψ _ hl']

end SlopeTestRemainingChoices

section Hop

variable {K : Type} [Field K] [NumberField K]

private theorem finite_adele_inclusion_injective {n : ℕ} : Function.Injective (fin1 : FA K n → G1 K n) := by
  intro a b h
  have h2 : ((MultiplicityOne.finProj K n a : G1 K n) : AdelicGLn.AdelicGL K n) = (MultiplicityOne.finProj K n b : G1 K n) :=
    congrArg Subtype.val h
  rw [MultiplicityOne.coe_finProj, MultiplicityOne.coe_finProj] at h2
  have h3 := congrArg (CuspidalSpectrum.finPart K n) h2
  simpa only [map_mul, map_inv, finPart_centralSection, inv_one, mul_one, finPart_finEmb] using h3

private theorem hop_tr {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure] (θ : Twist μ) (hinv : ∀ g, θ.e (θ.e g) = g)
    (L : Subgroup (FA K n)) (hL : ∀ u ∈ L, ∃ u' ∈ L, θ.e (fin1 u) = fin1 u') (h h' : FA K n) (hh : θ.e (fin1 h) = fin1 h')
    (ψ : G1 K n → ℂ) (hψ : FixF L ψ) (x : G1 K n) :
    hop L h ψ x = hop L h' (fun y => ψ (θ.e y)) (θ.e x) :=
  coset_tr (MultiplicityOne.finProj K n) finite_adele_inclusion_injective θ.e.toMulEquiv hinv L hL h h' hh ψ hψ x

private theorem flat_fix {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {μ : Measure (G1 K (2 + 2))} [μ.IsHaarMeasure]
    {D : TypeDat K (2 + 2)} {d : ℕ} (A : Line μ τ₁ τ₂ D d) {κ : Measure (archCompact K (2 + 2))} {e : archCompact K (2 + 2) → ℂ}
    {L : Subgroup (FA K (2 + 2))} (hty : IsTy D κ e L) (hle : L ≤ AdelicGLn.integralFiniteGL K (2 + 2)) (v : Eu d) :
    FixF L (flat 0 (A.sec v)) := by
  obtain ⟨hs, hD⟩ := (A.onto _).1 ⟨v, rfl⟩
  have hF := ((hty.fix _ hs.cont).1 hD).2
  intro u hu g
  have hk : fin1 u ∈ KG K (2 + 2) := by
    change ((MultiplicityOne.finProj K (2 + 2) u : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈ (maxCompact : Subgroup _)
    rw [MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact (hle hu)))]
    exact finEmb_mem_maxCompact (hle hu)
  have hh : HP 2 2 (g * fin1 u) = HP 2 2 g := ((hpSpec (K := K)).2.1 _ hk).2 g
  simp only [flat, hh, hF u hu g]

end Hop

section Lines

variable {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure] {τ₁ τ₂ : Submodule ℂ (L2 μ₂)}
  {μ : Measure (G1 K (2 + 2))} [μ.IsHaarMeasure] {D : TypeDat K (2 + 2)} {d d' : ℕ}

private theorem flat_tw (θ : Twist μ) (hH : ∀ g, HH (θ.e g) = HH g) (f f' : G1 K (2 + 2) → ℂ)
    (h : ∀ x, f' x = f (θ.e.symm x)) (x : G1 K (2 + 2)) : flat 0 f' x = flat 0 f (θ.e.symm x) := by
  have h1 : HP 2 2 (θ.e.symm x) = HP 2 2 x := by
    have := hH (θ.e.symm x)
    rw [ContinuousMulEquiv.apply_symm_apply] at this
    exact this.symm
  simp only [flat, h1, h]

private theorem exists_heckeAt_transport_of_linearIsometryEquiv (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d') {κ : Measure (archCompact K (2 + 2))}
    {e : archCompact K (2 + 2) → ℂ} {L : Subgroup (FA K (2 + 2))} (hty : IsTy D κ e L)
    (hle : L ≤ AdelicGLn.integralFiniteGL K (2 + 2)) (θ : Twist μ) (hinv : ∀ g, θ.e (θ.e g) = g)
    (hH : ∀ g, HH (θ.e g) = HH g) (hL : ∀ u ∈ L, ∃ u' ∈ L, θ.e (fin1 u) = fin1 u') (s : Eu d ≃ₗᵢ[ℂ] Eu d')
    (hs : ∀ v x, A'.sec (s v) x = A.sec v (θ.e.symm x)) (h h' : FA K (2 + 2)) (hh : θ.e (fin1 h) = fin1 h')
    (M : Eu d →ₗ[ℂ] Eu d) (hM : HeckeAt A L h M) :
    ∃ M' : Eu d' →ₗ[ℂ] Eu d', HeckeAt A' L h' M' ∧ ∀ v, M' (s v) = s (M v) := by
  have hsy : ∀ y, θ.e.symm y = θ.e y := fun y => θ.e.injective (by rw [ContinuousMulEquiv.apply_symm_apply, hinv])
  refine ⟨(s.toLinearEquiv : Eu d →ₗ[ℂ] Eu d') ∘ₗ M ∘ₗ (s.symm.toLinearEquiv : Eu d' →ₗ[ℂ] Eu d), fun v' => ?_, fun v => ?_⟩
  · obtain ⟨v, rfl⟩ := s.surjective v'
    funext x
    have e1 : ((s.toLinearEquiv : Eu d →ₗ[ℂ] Eu d') ∘ₗ M ∘ₗ (s.symm.toLinearEquiv : Eu d' →ₗ[ℂ] Eu d)) (s v) = s (M v) := by simp
    rw [e1, flat_tw θ hH _ _ (hs (M v)) x, hM v, hop_tr θ hinv L hL h h' hh _ (flat_fix A hty hle v),
      ContinuousMulEquiv.apply_symm_apply]
    congr 1
    funext y
    rw [flat_tw θ hH _ _ (hs v) y, hsy]
  · simp

private theorem hecke_N (hp : Pair μ₂ τ₁ τ₂) [IsTotallyComplex K] (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d')
    {L : Subgroup (FA K (2 + 2))} (hlev : D.Level L) (hle : L ≤ AdelicGLn.integralFiniteGL K (2 + 2))
    (hu : ∀ h, ∃! M, HeckeAt A L h M) (hu' : ∀ h, ∃! M, HeckeAt A' L h M) (N : Eu d' ≃ₗᵢ[ℂ] Eu d)
    (hN : ∀ (Y : L2 μ →L[ℂ] L2 μ) s s', Act A.J Y s → Act A'.J Y s' → ∀ w, N (s' 0 w) = s 0 (N w))
    (h : FA K (2 + 2)) (M : Eu d →ₗ[ℂ] Eu d) (M' : Eu d' →ₗ[ℂ] Eu d') (hM : HeckeAt A L h M) (hM' : HeckeAt A' L h M')
    (w : Eu d') : N (M' w) = M (N w) := by
  have hp' : Pair μ₂ τ₂ τ₁ := ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩
  obtain ⟨Y, hY⟩ : ∃ Y : L2 μ →L[ℂ] L2 μ, Y = (∑ᶠ c ∈ {c : AdelicGLn.FiniteAdelicGL K (2 + 2) ⧸ L | ∃ k ∈ L, c = QuotientGroup.mk (k * h)},
      rhoF μ c.out) ∘L prj (fixF μ L) := ⟨_, rfl⟩
  obtain ⟨⟨s, hs, hsv⟩, -⟩ := cosAct K μ μ₂ τ₁ τ₂ hp D d d' A A' L hlev hle h Y hY
  obtain ⟨⟨s', hs', hsv'⟩, -⟩ := cosAct K μ μ₂ τ₂ τ₁ hp' D d' d A' A L hlev hle h Y hY
  have e1 : M = (s 0 : Eu d →ₗ[ℂ] Eu d) := (hu h).unique hM fun v => funext fun x => hsv 0 v x
  have e2 : M' = (s' 0 : Eu d' →ₗ[ℂ] Eu d') := (hu' h).unique hM' fun v => funext fun x => hsv' 0 v x
  rw [e1, e2]
  exact hN Y s s' hs hs' w

end Lines

section Tr

private theorem gl_surj {R T : Type*} [Field R] [Field T] (f : R →+* T) (hf : Function.Surjective f) {n : ℕ}
    (g : GL (Fin n) T) : ∃ g', mapGL n f g' = g := by
  let e : R ≃+* T := RingEquiv.ofBijective f ⟨f.injective, hf⟩
  refine ⟨Matrix.GeneralLinearGroup.map (e.symm : T →+* R) g, ?_⟩
  ext i j
  exact e.apply_symm_apply _

private theorem trace_step {d d' : ℕ} (N : Eu d' ≃ₗᵢ[ℂ] Eu d) (s : Eu d ≃ₗᵢ[ℂ] Eu d') (u a g : Eu d' →L[ℂ] Eu d')
    (V : Module.End ℂ (Eu d)) (hV : ∀ w, N (u w) = V (N w)) (x : ℝ) (r : ℂ) (ha : a = (x : ℂ) • 1) (hg : g = r • 1) (j : ℕ) :
    LinearMap.trace ℂ (Eu d) ((N.toLinearEquiv : Eu d' →ₗ[ℂ] Eu d) ∘ₗ
      ((eigP a x ∘L (u ^ j) ∘L g : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ (s.toLinearEquiv : Eu d →ₗ[ℂ] Eu d')) =
    r * LinearMap.trace ℂ (Eu d) ((V ^ j) ∘ₗ ((s.toLinearEquiv.trans N.toLinearEquiv : Eu d ≃ₗ[ℂ] Eu d) : Eu d →ₗ[ℂ] Eu d)) := by
  have hpow : ∀ (j : ℕ) (y : Eu d'), N ((u ^ j) y) = (V ^ j) (N y) := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ih =>
      intro y
      rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, ih, hV, Module.End.mul_apply]
  have hP : ∀ y, eigP a x y = y := by
    intro y
    refine Submodule.starProjection_eq_self_iff.2 ?_
    rw [Module.End.mem_eigenspace_iff, ha]
    simp
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  refine LinearMap.ext fun w => ?_
  change N (eigP a x ((u ^ j) (g (s w)))) = r • (V ^ j) (N (s w))
  rw [hP, hg]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_smul, hpow]

end Tr

private abbrev Zs (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (Pl E)) : Type :=
  {v : Pl F // ∃ w ∈ S, w.under (𝓞 F) = v}

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.famNe :
    FamNe := by
  intro F E _ _ _ _ _ _ _ _ σ hdeg hgen μ _ θ hθ 𝔢 𝔵 κ e κ₂ p₁ p₂ k₀ hAL S U hU hS heU hty hUθ w₀ hw₀ hI ν hν hUq φ hφ hg hac hBi hne N hN
  obtain ⟨c, hc, ha⟩ := hac
  have hp := 𝔵.pair
  have hp' : Pair (BW.mu1 E 2) 𝔵.τ₂ 𝔵.τ₁ := ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩
  have hle : levOn S U ≤ AdelicGLn.integralFiniteGL E (2 + 2) := by
    intro u hu
    refine (AdelicGLn.mem_integralFiniteGL_iff_forall E (2 + 2)).2 fun v => ?_
    have h : finAt v (finEmb E (2 + 2) u) ∈ (if v ∈ S then U v else GLnLocal.integralGL (v.adicCompletion E) (2 + 2)) := hu v
    split_ifs at h
    · exact (hU v).2 h
    · exact h
  have hac := ha
  rw [hg] at hac

  obtain ⟨β, hβ⟩ := convR E μ _ 𝔵.τ₁ 𝔵.τ₂ hp 𝔵.D 𝔵.d 𝔵.d' 𝔵.A 𝔵.A' 𝔢.a 𝔵.a_hecke
  rw [hac] at hβ
  obtain ⟨hd, x, hx, hsym⟩ := famScalar E μ _ 𝔵.τ₁ 𝔵.τ₂ hp κ e κ₂ p₁ p₂ k₀ hAL S U hU 𝔵.D hty 𝔵.d 𝔵.A 𝔢.toAmp φ c β heU hφ hc
    (by rw [← hac]; exact 𝔢.a_op) hβ hne
  have hAct : Act 𝔵.A.J (Rop μ 𝔢.a) (symb β) := by
    rw [hac]
    exact (actLaws 𝔵.A.J).2.1 _ β hβ.1 hβ.2.1
  have hAct' : Act 𝔵.A'.J (Rop μ 𝔢.a) (symb 𝔵.βa) := (actLaws 𝔵.A'.J).2.1 _ 𝔵.βa 𝔵.a_acts.1 𝔵.a_acts.2.1
  have ha0 : 𝔵.a₀ = (x : ℂ) • 1 := by
    refine ContinuousLinearMap.ext fun w => N.injective ?_
    have := hN _ _ _ hAct hAct' w
    rw [hsym] at this
    change N (symb 𝔵.βa 0 w) = N (((x : ℂ) • (1 : Eu 𝔵.d' →L[ℂ] Eu 𝔵.d')) w)
    rw [this]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_smul]
  have hg0 : symb 𝔵.βg 0 = ((x : ℂ) / c) • 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    have hsec : 𝔵.A'.sec (𝔵.a₀ v) = 𝔵.A'.sec (c • symb 𝔵.βg 0 v) := by
      funext y
      have e1 := 𝔵.a_acts.2.2 0 v y
      have e2 := 𝔵.g_acts.2.2 0 v y
      have e3 : ∫ g, 𝔢.a g * flat 0 (𝔵.A'.sec v) (y * g) ∂μ = c * ∫ g, 𝔢.g g * flat 0 (𝔵.A'.sec v) (y * g) ∂μ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp [ha, mul_assoc]
      rw [e1, e2] at e3
      rw [map_smul]
      simp only [flat, Pi.smul_apply, smul_eq_mul] at e3 ⊢
      have hne' := Complex.exp_ne_zero ((0 + 2) * (HP 2 2 y : ℂ))
      apply mul_left_cancel₀ hne'
      rw [show symb 𝔵.βa 0 = 𝔵.a₀ from rfl] at e3
      rw [e3]
      ring
    have h1 := 𝔵.A'.inj hsec
    rw [ha0] at h1
    have h2 : (x : ℂ) • v = c • symb 𝔵.βg 0 v := by simpa using h1
    have h3 : symb 𝔵.βg 0 v = c⁻¹ • (x : ℂ) • v := by rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [h3]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_smul, div_eq_inv_mul]

  have HE := heckeEx E μ _ 𝔵.τ₁ 𝔵.τ₂ hp κ e hAL.idem S U hU 𝔵.D hty 𝔵.d 𝔵.A
  have HE' := heckeEx E μ _ 𝔵.τ₂ 𝔵.τ₁ hp' κ e hAL.idem S U hU 𝔵.D hty 𝔵.d' 𝔵.A'
  choose Mh hMh using fun h => (HE.1 h).exists
  have huniq : ∀ h M, HeckeAt 𝔵.A (levOn S U) h M → M = Mh h := fun h M hM => (HE.1 h).unique hM (hMh h)
  obtain ⟨hinv, -, hsplit⟩ := (galLoc F E σ hdeg hgen (2 + 2) (by norm_num) μ θ).2 hθ
  have hH : ∀ g, HH (θ.e g) = HH g := (galLaws μ _ 𝔵.σ θ 𝔵.θ₂ 𝔵.gal 𝔵.gal₂).2.2.2.2
  have hsp : ∀ z : Zs F E S, GM.Split E z.1 := by
    rintro ⟨_, w, hw, rfl⟩
    exact (hS w hw).1
  choose wv hwv using fun z : Zs F E S => hsplit z.1 (hsp z)
  obtain ⟨hh, hhd⟩ : ∃ hh : Fin 2 → (Σ z : Zs F E S, Gw (2 + 2) z.1) → FA E (2 + 2), ∀ i z g, hh i ⟨z, g⟩ =
      AdelicGLn.localEmbedding (wv z i).1 (mapGL (2 + 2) (completionMap z.1 (wv z i).1) g) :=
    ⟨fun i x => AdelicGLn.localEmbedding (wv x.1 i).1 (mapGL (2 + 2) (completionMap x.1.1 (wv x.1 i).1) x.2), fun _ _ _ => rfl⟩
  have hθh : ∀ i x, θ.e (fin1 (hh i x)) = fin1 (hh (i + 1) x) := by
    rintro i ⟨z, g⟩
    rw [hhd, hhd]
    exact hwv z i g
  have hreach : ∀ w ∈ S, ∀ g : Gw (2 + 2) w, ∃ i x, hh i x = AdelicGLn.localEmbedding w g := by
    intro w hw g
    have hlies : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    obtain ⟨z, hz⟩ : ∃ z : Zs F E S, z = ⟨w.under (𝓞 F), w, hw, rfl⟩ := ⟨_, rfl⟩
    have hlies' : w.asIdeal.LiesOver z.1.asIdeal := by rw [hz]; exact hlies
    obtain ⟨i, hi⟩ := (wv z).surjective ⟨w, hlies'⟩
    have H : ∀ g' : Gw (2 + 2) (wv z i).1, ∃ i' x, hh i' x = AdelicGLn.localEmbedding (wv z i).1 g' := by
      intro g'
      obtain ⟨g₀, rfl⟩ := gl_surj _ (hsp z (wv z i)) g'
      exact ⟨i, ⟨z, g₀⟩, hhd i z g₀⟩
    rw [hi] at H
    exact H g
  have hcomm : ∀ x y, Commute (Mh (hh 0 x)) (Mh (hh 1 y)) := by
    rintro ⟨z, g⟩ ⟨z', g'⟩
    rw [hhd, hhd]
    refine HE.2.1 _ _ ?_ _ _ _ _ (hMh _) (hMh _)
    intro heq
    have o1 : (wv z 0).1.under (𝓞 F) = z.1 := HeightOneSpectrum.ext (wv z 0).2.over.symm
    have o2 : (wv z' 1).1.under (𝓞 F) = z'.1 := HeightOneSpectrum.ext (wv z' 1).2.over.symm
    have hz : z = z' := Subtype.ext (o1.symm.trans ((congrArg (HeightOneSpectrum.under (𝓞 F)) heq).trans o2))
    subst hz
    exact absurd ((wv z).injective (Subtype.ext heq)) (by decide)
  have hirr : ∀ P : Submodule ℂ (Eu 𝔵.d), (∀ i x, ∀ w ∈ P, Mh (hh i x) w ∈ P) → P = ⊥ ∨ P = ⊤ := fun P hP =>
    irrW E μ _ 𝔵.τ₁ 𝔵.τ₂ hp κ e κ₂ p₁ p₂ k₀ hAL S U hU 𝔵.D hty 𝔵.d 𝔵.A P fun w hw g M hM v hv => by
      obtain ⟨i, x', hx'⟩ := hreach w hw g
      rw [← hx'] at hM
      rw [huniq _ _ hM]
      exact hP i x' v hv
  have htw : ∀ i x (w : Eu 𝔵.d), ((𝔵.s.toLinearEquiv.trans N.toLinearEquiv : Eu 𝔵.d ≃ₗ[ℂ] Eu 𝔵.d)) (Mh (hh (i + 1) x) w) =
      Mh (hh i x) ((𝔵.s.toLinearEquiv.trans N.toLinearEquiv : Eu 𝔵.d ≃ₗ[ℂ] Eu 𝔵.d) w) := by
    intro i x' w
    have hi2 : i + 1 + 1 = i := by revert i; decide
    have e1 : θ.e (fin1 (hh (i + 1) x')) = fin1 (hh i x') := by
      have := hθh (i + 1) x'
      rwa [hi2] at this
    obtain ⟨M', hM', hcmp⟩ := exists_heckeAt_transport_of_linearIsometryEquiv 𝔵.A 𝔵.A' hty hle θ hinv hH hUθ 𝔵.s 𝔵.s_sec _ _ e1 _ (hMh _)
    have h2 := hecke_N hp 𝔵.A 𝔵.A' hty.level hle HE.1 HE'.1 N hN _ _ _ (hMh (hh i x')) hM' (𝔵.s w)
    rw [hcmp] at h2
    exact h2

  obtain ⟨⟨s₀, hact, hs₀⟩, -⟩ := (uiwAct E μ _ 𝔵.τ₁ 𝔵.τ₂ hp S U hU 𝔵.D hty.level 𝔵.d 𝔵.d' 𝔵.A 𝔵.A' w₀ hw₀ hI ν)
  have hv0 : 𝔵.v 0 = s₀ := actUniq _ _ _ _ (hUq ▸ 𝔵.v_act 0) hact
  obtain ⟨i₀, x₀, hx₀⟩ := hreach w₀ hw₀ (Cartan.diagPow (w₀.adicCompletion E) (2 + 2) ν)
  have hV : Mh (hh i₀ x₀) = (𝔵.v 0 0 : Eu 𝔵.d →ₗ[ℂ] Eu 𝔵.d) := by
    rw [hv0]
    refine (huniq _ _ ?_).symm
    rw [hx₀]
    exact hs₀
  have hinj : Function.Injective (Mh (hh i₀ x₀)) :=
    heckeInj E μ _ 𝔵.τ₁ 𝔵.τ₂ hp κ e hAL.idem S U hU 𝔵.D hty 𝔵.d 𝔵.A w₀ hw₀ hI ν hν _ (hx₀ ▸ hMh _)
  have hN0 : ∀ w, N (𝔵.u 0 0 w) = Mh (hh i₀ x₀) (N w) := by
    intro w
    rw [hV]
    exact hN _ _ _ (𝔵.v_act 0) (𝔵.u_act 0) w
  haveI : Nontrivial (Eu 𝔵.d) := Module.nontrivial_of_finrank_pos (R := ℂ) (by simpa using hd)
  have hF := finTw (Eu 𝔵.d) _ (fun i x => Mh (hh i x)) hcomm hirr (𝔵.s.toLinearEquiv.trans N.toLinearEquiv) htw i₀ x₀ hinj
  refine ⟨x, hx, hF.mono fun j hj => ?_⟩
  have hxc : (x : ℂ) / c ≠ 0 := div_ne_zero (by exact_mod_cast hx.ne') hc
  have hT := trace_step N 𝔵.s (𝔵.u 0 0) 𝔵.a₀ (symb 𝔵.βg 0) (Mh (hh i₀ x₀)) hN0 x ((x : ℂ) / c) ha0 hg0 j
  change LinearMap.trace ℂ (Eu 𝔵.d) _ ≠ 0
  rw [hT]
  exact mul_ne_zero hxc hj
end
