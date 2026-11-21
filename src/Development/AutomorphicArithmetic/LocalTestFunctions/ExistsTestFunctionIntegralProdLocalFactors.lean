import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HomConv
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor

section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.exists_testFunction_integral_local_factor :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (w : Pl K)
          [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (mw : Measure (Gw n w)) [mw.IsHaarMeasure] (J : Subgroup (Gw n w)), CO J →
          ∀ (ψ : CompactlySupportedContinuousMap (Gw n w) ℂ), (∀ k ∈ J, ∀ x, ψ (x * k) = ψ x) →
          ∀ (R : AdelicGLn.FiniteAdelicGL K n → ℂ), (∀ y x, R (AdelicGLn.localEmbedding w y * x) = R x) →
          ∀ e₀ : TF K n, (∀ x, e₀ x = R x * (J : Set (Gw n w)).indicator 1 (finAt w (finEmb K n x))) →
          ∃ g : TF K n, (∀ x, g x = (mw.real J : ℂ) * (R x * ψ (finAt w (finEmb K n x)))) ∧
            (∫ x, g x ∂m = (∫ y, ψ y ∂mw) * ∫ x, e₀ x ∂m) ∧
            ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (AdelicGLn.FiniteAdelicGL K n) H),
              π.integrated m (UnitaryRep.ccToL1 m g) =
                (π.compHom (AdelicGLn.localEmbedding w) (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1).integrated mw (UnitaryRep.ccToL1 mw ψ) ∘L
                  π.integrated m (UnitaryRep.ccToL1 m e₀) := by
  intro K _ _ n m _ w _ _ mw _ J hJ ψ hψ R hR e₀ he₀
  have hp := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1
  obtain ⟨g, hg, -, hop⟩ := UpperTheory.ConvolutionTheory.Tf.homConv _ _ (AdelicGLn.localEmbedding w) hp m mw ψ e₀
  have hJm : MeasurableSet (J : Set (Gw n w)) := hJ.2.measurableSet
  have hval : ∀ x, g x = (mw.real J : ℂ) * (R x * ψ (finAt w (finEmb K n x))) := by
    intro x
    set a := finAt w (finEmb K n x) with ha
    have hfa : ∀ y, finAt w (finEmb K n ((AdelicGLn.localEmbedding w y)⁻¹ * x)) = y⁻¹ * a := by
      intro y
      rw [map_mul, finAt_mul, map_inv, finAt_inv, (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1]
    have hRy : ∀ y, R ((AdelicGLn.localEmbedding w y)⁻¹ * x) = R x := by
      intro y
      rw [← map_inv, hR]
    have hpt : ∀ y, ψ (a * y) * e₀ ((AdelicGLn.localEmbedding w (a * y))⁻¹ * x) =
        (J : Set (Gw n w)).indicator (fun _ => R x * ψ a) y := by
      intro y
      rw [he₀, hRy, hfa]
      have e1 : (a * y)⁻¹ * a = y⁻¹ := by group
      rw [e1]
      by_cases hy : y ∈ J
      · have hy' : y⁻¹ ∈ J := J.inv_mem hy
        rw [Set.indicator_of_mem (show y⁻¹ ∈ (J : Set (Gw n w)) from hy'),
          Set.indicator_of_mem (show y ∈ (J : Set (Gw n w)) from hy), hψ y hy, Pi.one_apply]
        ring
      · have hy' : y⁻¹ ∉ J := fun h => hy (by simpa using J.inv_mem h)
        rw [Set.indicator_of_notMem (show y⁻¹ ∉ (J : Set (Gw n w)) from hy'),
          Set.indicator_of_notMem (show y ∉ (J : Set (Gw n w)) from hy)]
        ring
    rw [hg, ← integral_mul_left_eq_self _ a]
    simp only [hpt]
    rw [integral_indicator hJm, setIntegral_const]
    simp [Measure.real, mul_comm]
  have hint : ∫ x, g x ∂m = (∫ y, ψ y ∂mw) * ∫ x, e₀ x ∂m := by
    have hf : IsCompact (tsupport ψ) := ψ.hasCompactSupport.isCompact
    have hS : IsCompact ((AdelicGLn.localEmbedding w) '' tsupport ψ * tsupport e₀) :=
      (hf.image hp).mul e₀.hasCompactSupport.isCompact
    have hker : Continuous fun q : AdelicGLn.FiniteAdelicGL K n × Gw n w =>
        ψ q.2 * e₀ ((AdelicGLn.localEmbedding w q.2)⁻¹ * q.1) :=
      (ψ.continuous.comp continuous_snd).mul
        (e₀.continuous.comp ((hp.comp continuous_snd).inv.mul continuous_fst))
    have hI : Integrable (Function.uncurry fun (x : AdelicGLn.FiniteAdelicGL K n) (y : Gw n w) =>
        ψ y * e₀ ((AdelicGLn.localEmbedding w y)⁻¹ * x)) (m.prod mw) := by
      refine Continuous.integrable_of_hasCompactSupport hker ?_
      refine HasCompactSupport.intro (hS.prod hf) fun q hq => ?_
      change ψ q.2 * e₀ ((AdelicGLn.localEmbedding w q.2)⁻¹ * q.1) = 0
      by_contra hne
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
      exact hq ⟨⟨_, ⟨q.2, subset_tsupport _ h1, rfl⟩, _, subset_tsupport _ h2,
        mul_inv_cancel_left _ _⟩, subset_tsupport _ h1⟩
    simp only [hg]
    rw [integral_integral_swap hI]
    simp only [integral_const_mul]
    have hinv : ∀ y : Gw n w, ∫ x, e₀ ((AdelicGLn.localEmbedding w y)⁻¹ * x) ∂m = ∫ x, e₀ x ∂m :=
      fun y => integral_mul_left_eq_self (fun x => e₀ x) _
    simp only [hinv]
    rw [integral_mul_const]
  exact ⟨g, hval, hint, hop⟩
end

section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.exists_testFunction_integral_prod_local_factors :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (r : ℕ) (w : Fin r → Pl K),
          Function.Injective w → ∀ [∀ i, MeasurableSpace (Gw n (w i))] [∀ i, BorelSpace (Gw n (w i))] (mw : ∀ i, Measure (Gw n (w i))) [∀ i, (mw i).IsHaarMeasure]
          (J : ∀ i, Subgroup (Gw n (w i))), (∀ i, CO (J i)) →
          ∀ (ψ : ∀ i, CompactlySupportedContinuousMap (Gw n (w i)) ℂ), (∀ i, ∀ k ∈ J i, ∀ x, ψ i (x * k) = ψ i x) →
          ∀ (R : AdelicGLn.FiniteAdelicGL K n → ℂ), (∀ i y x, R (AdelicGLn.localEmbedding (w i) y * x) = R x) →
          ∀ e₀ : TF K n, (∀ x, e₀ x = R x * ∏ i, (J i : Set (Gw n (w i))).indicator 1 (finAt (w i) (finEmb K n x))) →
          ∃ g : TF K n, (∀ x, g x = (∏ i, ((mw i).real (J i) : ℂ)) * (R x * ∏ i, ψ i (finAt (w i) (finEmb K n x)))) ∧
            (∫ x, g x ∂m = (∏ i, ∫ y, ψ i y ∂(mw i)) * ∫ x, e₀ x ∂m) ∧
            ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (AdelicGLn.FiniteAdelicGL K n) H),
              π.integrated m (UnitaryRep.ccToL1 m g) =
                (List.ofFn fun i => (π.compHom (AdelicGLn.localEmbedding (w i)) (UpperTheory.ConvolutionTheory.Tf.locEmb K n (w i)).1).integrated (mw i) (UnitaryRep.ccToL1 (mw i) (ψ i))).prod ∘L
                  π.integrated m (UnitaryRep.ccToL1 m e₀) := by
  intro K _ _ n m _ r
  have hfree : ∀ (u v : Pl K), u ≠ v → ∀ (y : Gw n v) (x : AdelicGLn.FiniteAdelicGL K n),
      finAt u (finEmb K n (AdelicGLn.localEmbedding v y * x)) = finAt u (finEmb K n x) := by
    intro u v huv y x
    rw [map_mul, finAt_mul, (UpperTheory.ConvolutionTheory.Tf.locEmb K n v).2.2.1 u huv, one_mul]
  induction r with
  | zero =>
    intro w hw _ _ mw _ J hJ ψ hψ R hR e₀ he₀
    refine ⟨e₀, fun x => ?_, ?_, fun H _ _ _ π => ?_⟩
    · simp [he₀]
    · simp
    · simp only [List.ofFn_zero, List.prod_nil]
      rfl
  | succ r ih =>
    intro w hw inst1 inst2 mw inst3 J hJ ψ hψ R hR e₀ he₀
    have hne : ∀ i : Fin r, w i.succ ≠ w 0 := fun i h => Fin.succ_ne_zero i (hw h)
    let R' : AdelicGLn.FiniteAdelicGL K n → ℂ := fun x =>
      R x * (J 0 : Set (Gw n (w 0))).indicator 1 (finAt (w 0) (finEmb K n x))
    have hR' : ∀ (i : Fin r) (y : Gw n (w i.succ)) (x : AdelicGLn.FiniteAdelicGL K n),
        R' (AdelicGLn.localEmbedding (w i.succ) y * x) = R' x := by
      intro i y x
      simp only [R']
      rw [hR i.succ y x, hfree _ _ (hne i).symm]
    have he₀' : ∀ x, e₀ x = R' x * ∏ i : Fin r,
        (J i.succ : Set (Gw n (w i.succ))).indicator 1 (finAt (w i.succ) (finEmb K n x)) := by
      intro x
      rw [he₀, Fin.prod_univ_succ]
      simp only [R']
      ring
    obtain ⟨g', hg', hgi', hgo'⟩ := @ih (fun i => w i.succ) (hw.comp (Fin.succ_injective r))
      (fun i => inst1 i.succ) (fun i => inst2 i.succ) (fun i => mw i.succ) (fun i => inst3 i.succ)
      (fun i => J i.succ) (fun i => hJ i.succ) (fun i => ψ i.succ) (fun i => hψ i.succ)
      R' hR' e₀ he₀'
    let R'' : AdelicGLn.FiniteAdelicGL K n → ℂ := fun x =>
      (∏ i : Fin r, ((mw i.succ).real (J i.succ) : ℂ)) *
        (R x * ∏ i : Fin r, ψ i.succ (finAt (w i.succ) (finEmb K n x)))
    have hR'' : ∀ (y : Gw n (w 0)) (x : AdelicGLn.FiniteAdelicGL K n),
        R'' (AdelicGLn.localEmbedding (w 0) y * x) = R'' x := by
      intro y x
      simp only [R'']
      rw [hR 0 y x]
      congr 2
      exact Finset.prod_congr rfl fun i _ => by rw [hfree _ _ (hne i)]
    have hg's : ∀ x, g' x = R'' x *
        (J 0 : Set (Gw n (w 0))).indicator 1 (finAt (w 0) (finEmb K n x)) := by
      intro x
      rw [hg' x]
      simp only [R', R'']
      ring
    obtain ⟨g, hg, hgi, hgo⟩ := UpperTheory.exists_testFunction_integral_local_factor K n m (w 0) (mw 0) (J 0) (hJ 0) (ψ 0) (hψ 0)
      R'' hR'' g' hg's
    refine ⟨g, fun x => ?_, ?_, fun H _ _ _ π => ?_⟩
    · rw [hg x, Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [R'']
      ring
    · rw [hgi, hgi', Fin.prod_univ_succ]
      ring
    · rw [hgo H π, hgo' H π, List.ofFn_succ, List.prod_cons, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_assoc]
end
