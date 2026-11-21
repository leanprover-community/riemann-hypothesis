import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.NormCount
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ExistsNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AutomorphicArithmetic.UnitaryInvolutions.EventuallyMapMemMaximalCompactGL
import Development.AutomorphicArithmetic.UnitaryInvolutions.EventuallySeparableOfIntegralModel
import Development.AutomorphicArithmetic.UnitaryInvolutions.UnitaryInvolutionStabilizesIntegralAtNonsplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompact
import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.OrbZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup

section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

private theorem phi_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : ℕ) :
    (GlobalTheory.Tw.Phi a R).map f = GlobalTheory.Tw.Phi a S := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

private theorem phi_mul_transpose {R : Type} [CommRing R] (a : ℕ) :
    GlobalTheory.Tw.Phi a R * (GlobalTheory.Tw.Phi a R)ᵀ = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, GlobalTheory.Tw.Phi, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single i.rev]
  · have h1 : (i : ℕ) + (i.rev : ℕ) + 1 = a := by rw [Fin.val_rev]; omega
    rw [if_pos h1]
    by_cases h : i = k
    · subst h
      rw [if_pos h1, if_pos rfl, ← mul_pow]
      simp
    · rw [if_neg (fun h2 => h (Fin.ext (by rw [Fin.val_rev] at h2; omega))), if_neg h, mul_zero]
  · intro j _ hj
    rw [if_neg (fun h => hj (Fin.ext (by rw [Fin.val_rev]; omega))), zero_mul]
  · simp

private theorem exists_scalar (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    ∃ z : E, z ≠ 0 ∧ z = (-1) ^ (n - 1) * IsCMField.complexConj E z := by
  rcases Nat.even_or_odd (n - 1) with h | h
  · exact ⟨1, one_ne_zero, by simp [h.neg_one_pow]⟩
  · have hx : ∃ x : E, IsCMField.complexConj E x ≠ x := by
      by_contra hc
      push_neg at hc
      exact IsCMField.complexConj_ne_one E (AlgEquiv.ext hc)
    obtain ⟨x, hx⟩ := hx
    refine ⟨x - IsCMField.complexConj E x, sub_ne_zero.mpr hx.symm, ?_⟩
    rw [h.neg_one_pow, map_sub, IsCMField.complexConj_apply_apply]
    ring

private def uMat {E : Type} [Field E] (n : ℕ) (z : E) (hz : z ≠ 0) : GL (Fin n) E where
  val := z • GlobalTheory.Tw.Phi n E
  inv := z⁻¹ • (GlobalTheory.Tw.Phi n E)ᵀ
  val_inv := by
    rw [Matrix.smul_mul, Matrix.mul_smul, phi_mul_transpose, smul_smul, mul_inv_cancel₀ hz, one_smul]
  inv_val := by
    rw [Matrix.smul_mul, Matrix.mul_smul, mul_eq_one_comm.mp (phi_mul_transpose n), smul_smul,
      inv_mul_cancel₀ hz, one_smul]

theorem UpperTheory.ConvolutionTheory.G3.transl :
    UpperTheory.ConvolutionTheory.G3.Transl := by
  intro E _ _ _ _ n
  obtain ⟨z, hz0, hz⟩ := exists_scalar E n
  have hΦΦ : GlobalTheory.Tw.Phi n E * GlobalTheory.Tw.Phi n E = ((-1 : E) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) E) :=
    GlobalTheory.LocTwist.Phi_mul_self n
  refine ⟨uMat n z hz0, ?_, ?_, ?_⟩
  · intro g
    apply Units.ext
    have hL : (thE E n g).val = GlobalTheory.Tw.Phi n E *
        ((g⁻¹ : GL (Fin n) E).val.map (IsCMField.complexConj E))ᵀ * (GlobalTheory.Tw.Phi n E)ᵀ :=
      GlobalTheory.LocTwist.thetaGL_val n _ g
    have hR : ((uMat n z hz0) * UpperTheory.ConvolutionTheory.D.th (IsCMField.complexConj E) g * (uMat n z hz0)⁻¹).val =
        (z • GlobalTheory.Tw.Phi n E) * ((g⁻¹ : GL (Fin n) E).val.map (IsCMField.complexConj E))ᵀ *
          (z⁻¹ • (GlobalTheory.Tw.Phi n E)ᵀ) := rfl
    rw [hL, hR, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hz0, one_smul]
  · apply Units.ext
    have hc : (IsCMField.complexConj E z)⁻¹ * z * (-1) ^ (n - 1) = 1 := by
      have hcz : IsCMField.complexConj E z ≠ 0 := (_root_.map_ne_zero _).mpr hz0
      have hs : ((-1 : E) ^ (n - 1)) * (-1) ^ (n - 1) = 1 := by rw [← mul_pow]; simp
      have e : (IsCMField.complexConj E z)⁻¹ * z * (-1) ^ (n - 1) =
          ((IsCMField.complexConj E z)⁻¹ * IsCMField.complexConj E z) * (((-1 : E) ^ (n - 1)) * (-1) ^ (n - 1)) := by
        rw [show (IsCMField.complexConj E z)⁻¹ * z * (-1) ^ (n - 1) =
          (IsCMField.complexConj E z)⁻¹ * ((-1) ^ (n - 1) * IsCMField.complexConj E z) * (-1) ^ (n - 1) by rw [← hz]]
        ring
      rw [e, inv_mul_cancel₀ hcz, hs, one_mul]
    have hm : ((GlobalTheory.Tw.Phi n E)ᵀ.map (IsCMField.complexConj E))ᵀ = GlobalTheory.Tw.Phi n E := by
      rw [Matrix.transpose_map, Matrix.transpose_transpose]
      exact phi_map ((IsCMField.complexConj E : E →+* E)) n
    have hL : ((uMat n z hz0) * UpperTheory.ConvolutionTheory.D.th (IsCMField.complexConj E) (uMat n z hz0)).val =
        (z • GlobalTheory.Tw.Phi n E) * (((z⁻¹ • (GlobalTheory.Tw.Phi n E)ᵀ)).map (IsCMField.complexConj E))ᵀ := rfl
    have hs : ((z⁻¹ • (GlobalTheory.Tw.Phi n E)ᵀ)).map (IsCMField.complexConj E) =
        (IsCMField.complexConj E z)⁻¹ • ((GlobalTheory.Tw.Phi n E)ᵀ.map (IsCMField.complexConj E)) := by
      ext i j
      simp
    rw [hL, hs, Matrix.transpose_smul, hm, Matrix.smul_mul, Matrix.mul_smul, hΦΦ, smul_smul, smul_smul,
      Units.val_one, mul_comm z, hc, one_smul]
  · intro w hw g
    have ht : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hw]
    have hf : algebraMap E (w.adicCompletion E) z ≠ 0 := (_root_.map_ne_zero _).mpr hz0
    have h1 : (uMat n z hz0).val.map (algebraMap E (w.adicCompletion E)) =
        algebraMap E (w.adicCompletion E) z • GlobalTheory.Tw.Phi n (w.adicCompletion E) := by
      rw [← phi_map (algebraMap E (w.adicCompletion E)) n]
      ext i j
      simp [uMat]
    have h2 : ((uMat n z hz0)⁻¹ : GL (Fin n) E).val.map (algebraMap E (w.adicCompletion E)) =
        (algebraMap E (w.adicCompletion E) z)⁻¹ • (GlobalTheory.Tw.Phi n (w.adicCompletion E))ᵀ := by
      rw [← phi_map (algebraMap E (w.adicCompletion E)) n]
      ext i j
      simp [uMat]
    rw [ht, GlobalTheory.LocTwist.thetaGL_val, h1, h2, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      inv_mul_cancel₀ hf, one_smul]
    rfl
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

private theorem splitCase {E : Type} [Field E] [NumberField E] (w : Pl E) (n : ℕ) (g y : GLw n w)
    (hg : g ∈ GlobalTheory.LFun.KGL w n) (hy : y ∈ GlobalTheory.LFun.KGL w n) (hp : y.val.charpoly = g.val.charpoly)
    (hsep : ∀ Q : (Ov E w)[X], Q.map (Ov E w).subtype = g.val.charpoly → Q.Separable) :
    ∃ k ∈ GlobalTheory.LFun.KGL w n, y = k⁻¹ * g * k := by
  obtain ⟨g₀, rfl⟩ := hg
  obtain ⟨y₀, rfl⟩ := hy
  have e : ∀ a : GL (Fin n) (Ov E w), (Formalism.UG.bc (n := Fin n) (Ov E w).subtype a).val = a.val.map (Ov E w).subtype := fun a => rfl
  have hinj : Function.Injective (Ov E w).subtype := Subtype.val_injective
  have hcp : ∀ a : GL (Fin n) (Ov E w), (Formalism.UG.bc (n := Fin n) (Ov E w).subtype a).val.charpoly = a.val.charpoly.map (Ov E w).subtype := by
    intro a
    rw [e, Matrix.charpoly_map]
  have hs : g₀.val.charpoly.Separable := hsep _ (hcp g₀).symm
  have hyg : y₀.val.charpoly = g₀.val.charpoly := by
    apply Polynomial.map_injective _ hinj
    rw [← hcp, ← hcp, hp]
  obtain ⟨x, hx⟩ := (UpperTheory.ConvolutionTheory.D.conjSep (Ov E w) (Ov E w) n g₀.val hs).1 y₀.val hyg
  refine ⟨Formalism.UG.bc (n := Fin n) (Ov E w).subtype x, ⟨x, rfl⟩, ?_⟩
  rw [mul_assoc, eq_inv_mul_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, e, e, e, ← Matrix.map_mul, ← Matrix.map_mul, hx]

theorem UpperTheory.ConvolutionTheory.G3.intUniq :
    UpperTheory.ConvolutionTheory.G3.IntUniq := by
  intro E _ _ _ hU n δ hsep
  obtain ⟨u, hth, hu, hloc⟩ := UpperTheory.ConvolutionTheory.G3.transl E hU n
  have h1 := UpperTheory.eventually_map_mem_maximalCompactGL E n (δ * thE E n δ)
  have h2 := UpperTheory.eventually_map_mem_maximalCompactGL E n δ
  have h3 := UpperTheory.eventually_map_mem_maximalCompactGL E n u
  have h4 := UpperTheory.eventually_separable_of_integral_model E (UpperTheory.ConvolutionTheory.G3.gpol δ) hsep
  filter_upwards [h1, h2, h3, h4] with w h1 h2 h3 h4
  by_cases hs : IsSplitAt w
  · have hl : locEl n w δ = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
      simp [locEl, hs]
    have hcp : (locEl n w δ).val.charpoly = atPl w (UpperTheory.ConvolutionTheory.G3.gpol δ) := by
      rw [hl]
      exact Matrix.charpoly_map _ _
    refine ⟨hl ▸ h1, fun y hy hp => ?_⟩
    have hy' : y.val.charpoly = (locEl n w δ).val.charpoly := by
      rw [hcp, ← hp]
      simp [UpperTheory.ConvolutionTheory.G3.lpol, nrmL, hs]
    obtain ⟨k, hk, e⟩ := splitCase w n (locEl n w δ) y (hl ▸ h1) hy hy' (fun Q hQ => h4 Q (hQ.trans hcp))
    refine ⟨k, hk, ?_⟩
    simpa [thL, hs] using e
  · have hl : locEl n w δ = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ := by
      simp [locEl, hs]
    exact ⟨hl ▸ h2, UpperTheory.unitary_involution_stabilizes_integral_at_nonsplit E hU n u δ hth hu w hs (hloc w hs) h3 h2 h4⟩
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

private theorem nrmL_locEl {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (δ : GL (Fin n) E) :
    nrmL n w (locEl n w δ) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
  unfold nrmL locEl
  split_ifs with hs
  · rfl
  · have hm : thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) =
        GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (thE E n δ) :=
      (GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hs).1 x |>.symm) δ).symm
    rw [hm, ← map_mul]

theorem UpperTheory.ConvolutionTheory.G3.cptInt :
    UpperTheory.ConvolutionTheory.G3.CptInt := by
  intro E _ _ _ hU n δ hs
  have hs' : (δ * thE E n δ).val.charpoly.Separable := hs
  filter_upwards [GlobalTheory.BCT.SepBezout.bezout_eventually E _ hs', GlobalTheory.BCT.GoodInt.eventually_mem_KGL (δ * thE E n δ)] with w hb hK
  obtain ⟨-, hinv, -, -, -, hKc, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  have hNe := nrmL_locEl hU n w δ
  have hNK : nrmL n w (locEl n w δ) ∈ GlobalTheory.LFun.KGL w n := hNe ▸ hK
  have hgood : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w (locEl n w δ)).val.charpoly + v * derivative (nrmL n w (locEl n w δ)).val.charpoly = 1 := by
    have e : (nrmL n w (locEl n w δ)).val.charpoly =
        (δ * thE E n δ).val.charpoly.map (algebraMap E (w.adicCompletion E)) := by
      rw [hNe]; exact Matrix.charpoly_map _ _
    rw [e]; exact hb
  have hcomm : ∀ t ∈ twCent (thL n w) (locEl n w δ),
      t * nrmL n w (locEl n w δ) = nrmL n w (locEl n w δ) * t := by
    intro t ht
    have ht' : t * locEl n w δ = locEl n w δ * thL n w t := ht
    generalize locEl n w δ = y at ht' ⊢
    by_cases hsp : IsSplitAt w
    · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hsp]
      have hn1 : nrmL n w y = y := by unfold nrmL; rw [if_pos hsp]
      rw [hn1]; rw [hθ1] at ht'; simpa using ht'
    · have hn1 : nrmL n w y = y * thL n w y := by
        unfold nrmL; rw [if_neg hsp]; unfold thL; rw [if_neg hsp]
      rw [hn1]
      calc t * (y * thL n w y) = y * thL n w t * thL n w y := by rw [← mul_assoc, ht']
        _ = y * thL n w (t * y) := by simp only [map_mul, mul_assoc]
        _ = y * thL n w (y * thL n w t) := by rw [ht']
        _ = y * thL n w y * t := by simp only [map_mul, hinv, mul_assoc]
  refine le_antisymm (le_inf ((Subgroup.closure_le _).2 fun t ht => ht.1) ((Subgroup.closure_le _).2 fun t ht => ?_)) ?_
  · exact GlobalTheory.StabInt.mem_KGL_of_commute E n w _ t hNK hgood (hcomm t ht.1) ht.2
  · intro t ht
    refine Subgroup.subset_closure ⟨ht.1, ?_⟩
    refine hKc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hKc.isClosed)
    exact (Subgroup.zpowers_le.2 ht.2 : _)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

private theorem avg_const' {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have htop : rStab (fun _ : H => c) = ⊤ := by
    rw [eq_top_iff]
    intro k _ x
    rfl
  unfold avg
  rw [htop, Subgroup.index_top, Nat.cast_one, inv_one, one_mul]
  rw [finsum_eq_single (fun _ => c) ((1 : H) : H ⧸ (⊤ : Subgroup H))]
  intro x hx
  exact absurd (QuotientGroup.subsingleton_quotient_top.elim x _) hx

private theorem cptPart_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (T : Subgroup G) {t c : G} (ht : t ∈ T) (hc : c ∈ cptPart T) : t⁻¹ * c * t ∈ cptPart T := by
  unfold cptPart at hc ⊢
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hx.1) ht, ?_⟩
    let e : G ≃ₜ G := (Homeomorph.mulLeft t⁻¹).trans (Homeomorph.mulRight t)
    have he : ∀ y, e y = t⁻¹ * y * t := fun y => rfl
    have hz : ∀ n : ℤ, (t⁻¹ * x * t) ^ n = t⁻¹ * x ^ n * t := by
      intro n
      simpa using (conj_zpow (a := t⁻¹) (b := x) (i := n))
    have himg : (Subgroup.zpowers (t⁻¹ * x * t) : Set G) = e '' (Subgroup.zpowers x : Set G) := by
      ext y
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨x ^ n, ⟨n, rfl⟩, (hz n).symm⟩
      · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, hz n⟩
    rw [himg, ← e.image_closure]
    exact hx.2.image e.continuous
  | one => simp
  | mul x y _ _ hx hy =>
    have : t⁻¹ * (x * y) * t = (t⁻¹ * x * t) * (t⁻¹ * y * t) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : t⁻¹ * x⁻¹ * t = (t⁻¹ * x * t)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem UpperTheory.ConvolutionTheory.G3.orbUnit :
    UpperTheory.ConvolutionTheory.G3.OrbUnit := by
  intro G _ _ _ θ K δ hθ hδ horb hcpt
  unfold twOrb
  rw [finsum_eq_single _ (DoubleCoset.mk (twCent θ δ) K 1)]
  · obtain ⟨t, k, ht, hk, hx⟩ := DoubleCoset.mk_out_eq_mul (twCent θ δ) K (1 : G)
    generalize hxx : Quotient.out (DoubleCoset.mk (twCent θ δ) K 1) = x at hx ⊢
    rw [mul_one] at hx
    have ht' : t * δ = δ * θ t := ht
    have h1 : (twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) = 1 := by
      rw [Subgroup.relIndex_eq_one]
      intro c hc
      have hc' := cptPart_conj _ ht hc
      rw [hcpt] at hc hc'
      refine ⟨hc.1, k⁻¹ * (t⁻¹ * c * t) * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hc'.2) hk, ?_⟩
      rw [hx]
      simp [mul_assoc]
    have h2 : (fun k' : K => (K : Set G).indicator (1 : G → ℂ) ((x * k')⁻¹ * δ * θ (x * k'))) = fun _ => 1 := by
      funext k'
      have e : (x * k')⁻¹ * δ * θ (x * k') = (k * k')⁻¹ * δ * θ (k * k') := by
        have : δ * θ (x * k') = t * δ * θ (k * k') := by
          rw [ht', hx, mul_assoc t k, map_mul θ t, mul_assoc]
        rw [mul_assoc, this, hx]
        group
      have hkk : k * k' ∈ K := K.mul_mem hk k'.2
      rw [e, Set.indicator_of_mem]
      · rfl
      · exact K.mul_mem (K.mul_mem (K.inv_mem hkk) hδ) (hθ _ hkk)
    rw [h1, h2, avg_const']
    simp
  · intro q hq
    have h2 : (fun k' : K => (K : Set G).indicator (1 : G → ℂ)
        ((Quotient.out q * k')⁻¹ * δ * θ (Quotient.out q * k'))) = fun _ => 0 := by
      funext k'
      apply Set.indicator_of_notMem
      intro hy
      apply hq
      obtain ⟨k, hk, e⟩ := horb _ hy ⟨_, rfl⟩
      rw [← DoubleCoset.out_eq' (twCent θ δ) K q]
      symm
      rw [DoubleCoset.eq]
      refine ⟨Quotient.out q * k' * k⁻¹, ?_, k * (k' : G)⁻¹, K.mul_mem hk (K.inv_mem k'.2), ?_⟩
      · generalize Quotient.out q * (k' : G) = g at e
        show g * k⁻¹ * δ = δ * θ (g * k⁻¹)
        rw [map_mul, map_inv]
        calc g * k⁻¹ * δ = g * (k⁻¹ * δ * θ k) * (θ k)⁻¹ := by group
          _ = δ * (θ g * (θ k)⁻¹) := by rw [← e]; group
      · show Quotient.out q = _
        group
    rw [h2, avg_const', mul_zero]
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace UpperTheory.ConvolutionTheory.G3

private theorem unit_conj_mem {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hK : ∀ k ∈ K, θ k ∈ K)
    (z k : G) (hk : k ∈ K) : k⁻¹ * z * θ k ∈ K ↔ z ∈ K := by
  constructor
  · intro h
    have h' := K.mul_mem (K.mul_mem hk h) (K.inv_mem (hK k hk))
    have e : k * (k⁻¹ * z * θ k) * (θ k)⁻¹ = z := by group
    rwa [e] at h'
  · intro h
    exact K.mul_mem (K.mul_mem (K.inv_mem hk) h) (hK k hk)

private theorem unit_index {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hK : ∀ k ∈ K, θ k ∈ K) (δ x : G) :
    (rStab fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0 := by
  have key : ∀ k : K, (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * δ * θ (x * k)) =
      (K : Set G).indicator (1 : G → ℂ) (x⁻¹ * δ * θ x) := by
    intro k
    have e : (x * (k : G))⁻¹ * δ * θ (x * k) = (k : G)⁻¹ * (x⁻¹ * δ * θ x) * θ k := by
      rw [map_mul]; group
    simp only [Set.indicator_apply, SetLike.mem_coe, e, unit_conj_mem θ K hK _ _ k.2, Pi.one_apply]
  have top : (rStab fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * δ * θ (x * k))) = ⊤ := by
    refine (Subgroup.eq_top_iff' _).2 fun k y => ?_
    exact (key _).trans (key _).symm
  rw [top, Subgroup.index_top]
  exact one_ne_zero

private theorem tw_symm {G : Type} [Group G] {θ : G →* G} {x y : G} (h : Tw θ x y) : Tw θ y x := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨g⁻¹, by rw [map_inv]; group⟩

private theorem tw_trans {G : Type} [Group G] {θ : G →* G} {x y z : G} (h : Tw θ x y) (h' : Tw θ y z) :
    Tw θ x z := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨g', rfl⟩ := h'
  exact ⟨g * g', by rw [map_mul]; group⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem lpol_tw (hU : Unr E) (n : ℕ) (w : Pl E) {x y : GLw n w} (h : Tw (thL n w) x y) :
    lpol w y = lpol w x := by
  obtain ⟨g, rfl⟩ := h
  unfold lpol
  rw [ThBasic.nrmL_twist hU, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

private theorem lpol_locEl (hU : Unr E) (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) :
    lpol w (locEl n w δ) = atPl w (gpol δ) :=
  ThBasic.charpoly_nrmL hU n w δ

private theorem unit_uniq (hU : Unr E) (n : ℕ) (w : Pl E) (δ : GL (Fin n) E)
    (i : ∀ y ∈ GlobalTheory.LFun.KGL w n, lpol w y = atPl w (gpol δ) →
      ∃ k ∈ GlobalTheory.LFun.KGL w n, y = k⁻¹ * locEl n w δ * thL n w k)
    (y : GLw n w) (hy : y ∈ GlobalTheory.LFun.KGL w n) (h : Tw (thL n w) (locEl n w δ) y) :
    ∃ k ∈ GlobalTheory.LFun.KGL w n, y = k⁻¹ * locEl n w δ * thL n w k :=
  i y hy ((lpol_tw hU n w h).trans (lpol_locEl hU n w δ))

theorem _root_.UpperTheory.ConvolutionTheory.G3.unitAe : UnitAe := by
  intro E _ _ _ hU a b δ₁ δ₂ h₁ h₂
  filter_upwards [intUniq E hU a δ₁ h₁, intUniq E hU b δ₂ h₂, cptInt E hU a δ₁ h₁, cptInt E hU b δ₂ h₂]
    with w i₁ i₂ c₁ c₂ y₁ y₂ l₁ l₂
  have hK₁ := ThBasic.thL_mem_KGL hU a w
  have hK₂ := ThBasic.thL_mem_KGL hU b w
  have hK : ∀ k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b),
      (thL a w).prodMap (thL b w) k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) :=
    fun k hk => Subgroup.mem_prod.2 ⟨hK₁ _ (Subgroup.mem_prod.1 hk).1, hK₂ _ (Subgroup.mem_prod.1 hk).2⟩
  by_cases ht : Tw (thL a w) (locEl a w δ₁) y₁ ∧ Tw (thL b w) (locEl b w δ₂) y₂
  · rw [if_pos ht]
    obtain ⟨⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩ := ht
    have e : ((g₁⁻¹ * locEl a w δ₁ * thL a w g₁, g₂⁻¹ * locEl b w δ₂ * thL b w g₂) : GLw a w × GLw b w) =
        (g₁, g₂)⁻¹ * (locEl a w δ₁, locEl b w δ₂) * (thL a w).prodMap (thL b w) (g₁, g₂) := rfl
    rw [e, GlobalTheory.TwOrbConj.twOrb_twConj _ _ _ _ _ _ fun x => unit_index _ _ hK _ x]
    refine orbUnit _ _ _ _ hK (Subgroup.mem_prod.2 ⟨i₁.1, i₂.1⟩) ?_ ?_
    · rintro ⟨z₁, z₂⟩ hz ⟨⟨x₁, x₂⟩, hx⟩
      have hz' := Subgroup.mem_prod.1 hz
      have e₁ : z₁ = x₁⁻¹ * locEl a w δ₁ * thL a w x₁ := congrArg Prod.fst hx
      have e₂ : z₂ = x₂⁻¹ * locEl b w δ₂ * thL b w x₂ := congrArg Prod.snd hx
      obtain ⟨k₁, hk₁, f₁⟩ := unit_uniq hU a w δ₁ i₁.2 z₁ hz'.1 ⟨x₁, e₁⟩
      obtain ⟨k₂, hk₂, f₂⟩ := unit_uniq hU b w δ₂ i₂.2 z₂ hz'.2 ⟨x₂, e₂⟩
      exact ⟨(k₁, k₂), Subgroup.mem_prod.2 ⟨hk₁, hk₂⟩, Prod.ext f₁ f₂⟩
    · rw [OrbProd.twCent_prod, KapMul.cptPart_prod, c₁, c₂, OrbProd.prod_inf_prod]
  · rw [if_neg ht]
    refine orbZero _ _ _ _ _ fun z hz => ?_
    refine Set.indicator_of_notMem (fun hzK => ht ?_) _
    have hz' := Subgroup.mem_prod.1 hzK
    obtain ⟨⟨x₁, x₂⟩, hx⟩ := hz
    have e₁ : z.1 = x₁⁻¹ * y₁ * thL a w x₁ := congrArg Prod.fst hx
    have e₂ : z.2 = x₂⁻¹ * y₂ * thL b w x₂ := congrArg Prod.snd hx
    have t₁ : Tw (thL a w) y₁ z.1 := ⟨x₁, e₁⟩
    have t₂ : Tw (thL b w) y₂ z.2 := ⟨x₂, e₂⟩
    obtain ⟨k₁, hk₁, f₁⟩ := i₁.2 z.1 hz'.1 ((lpol_tw hU a w t₁).trans l₁)
    obtain ⟨k₂, hk₂, f₂⟩ := i₂.2 z.2 hz'.2 ((lpol_tw hU b w t₂).trans l₂)
    exact ⟨tw_trans ⟨k₁, f₁⟩ (tw_symm t₁), tw_trans ⟨k₂, f₂⟩ (tw_symm t₂)⟩

end UpperTheory.ConvolutionTheory.G3
end
