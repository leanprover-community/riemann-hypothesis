import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerUnipotentMulEqAdditiveCharMul
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem gln_val {E : Type} [Field E] [NumberField E] (b : A E) :
    (gl (nU b) : GL (Fin 2) (A E)).val = !![1, b; 0, 1] := rfl

private theorem nU_inv {E : Type} [Field E] [NumberField E] (b : A E) :
    (gl (nU b) : GL (Fin 2) (A E))⁻¹ = gl (nU (-b)) := by
  rw [inv_eq_iff_mul_eq_one]
  refine Units.ext ?_
  rw [Units.val_mul, gln_val, gln_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem cont_n {E : Type} [Field E] [NumberField E] :
    Continuous fun b : A E => (gl (nU b) : GL (Fin 2) (A E)) := by
  have hv : ∀ g : A E → A E, Continuous g →
      Continuous fun b : A E => ((gl (nU (g b)) : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) := by
    intro g hg
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [nU] <;> first | exact hg | exact continuous_const
  refine Units.continuous_iff.2 ⟨hv id continuous_id, ?_⟩
  simp only [nU_inv]
  exact hv _ continuous_neg

private theorem map_unipotent_eq_one {E S : Type} [Field E] [NumberField E] [CommRing S] (p : A E →+* S) (z : A E) (hz : p z = 0) :
    Matrix.GeneralLinearGroup.map p (gl (nU z)) = 1 := by
  refine Units.ext ?_
  ext i j
  change p ((gl (nU z) : GL (Fin 2) (A E)).val i j) = (1 : Matrix (Fin 2) (Fin 2) S) i j
  rw [gln_val]
  fin_cases i <;> fin_cases j <;> simp [hz]

private theorem pInf_mk {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (x : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    pInf E (D.mkE 0 ((0, x) : A ℚ)) = 0 := by
  have h : pInf E (AdeleBaseChange.adeleMap ℚ E ((0, x) : A ℚ)) = 0 := by
    change (infEq E).symm (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (0 : InfiniteAdeleRing ℚ)) = 0
    rw [map_zero, map_zero]
  simp [Dat.mkE, h]

private theorem cont_mk {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => D.mkE 0 ((0, x) : A ℚ) := by
  have h : Continuous fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => ((0, x) : A ℚ) :=
    continuous_const.prodMk continuous_id
  unfold Dat.mkE
  exact continuous_const.add ((AdeleBaseChange.continuous_adeleMap.comp h).mul continuous_const)

theorem UpperTheory.exists_level_unipotent_invariance_automorphicForm :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2), IsAutForm f →
        ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ N : ℕ, 0 < N ∧ ∀ k ∈ C, ∀ b : FiniteAdeleRing (𝓞 ℚ) ℚ,
          (∀ v, b v ∈ v.adicCompletionIntegers ℚ) → ∀ G, f.1 (G * (gl (nU (D.mkE 0 ((0, (N : FiniteAdeleRing (𝓞 ℚ) ℚ) * b) : A ℚ))) * k)) = f.1 (G * k) := by
  intro E _ _ _ D f hf C hC
  let m : FiniteAdeleRing (𝓞 ℚ) ℚ → GL (Fin 2) (A E) := fun x => gl (nU (D.mkE 0 ((0, x) : A ℚ)))
  have hm : Continuous m := cont_n.comp (cont_mk D)
  have hm0 : m 0 = 1 := by
    have h0 : D.mkE 0 ((0, 0) : A ℚ) = 0 := by
      have h : D.mkE 0 ((0, 0) : A ℚ) = D.mkE 0 (0 : A ℚ) := rfl
      rw [h]
      unfold Dat.mkE
      rw [map_zero, zero_mul, add_zero]
    change gl (nU (D.mkE 0 ((0, 0) : A ℚ))) = 1
    rw [h0]
    refine Units.ext ?_
    rw [gln_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  let Φ : FiniteAdeleRing (𝓞 ℚ) ℚ × GL (Fin 2) (A E) → GL (Fin 2) (Af E) :=
    fun p => Matrix.GeneralLinearGroup.map (pFin E) (p.2⁻¹ * m p.1 * p.2)
  have hΦ : Continuous Φ :=
    (Continuous.units_map _ (continuous_id.matrix_map continuous_snd)).comp ((continuous_snd.inv.mul (hm.comp continuous_fst)).mul continuous_snd)
  have hO : IsOpen (Φ ⁻¹' {k | finRep E 2 k f = f}) := hf.level.preimage hΦ
  have hsub : ({0} : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) ×ˢ C ⊆ Φ ⁻¹' {k | finRep E 2 k f = f} := by
    rintro ⟨x, k⟩ ⟨hx, -⟩
    have hx0 : x = 0 := hx
    subst hx0
    have e : Φ (0, k) = 1 := by
      change Matrix.GeneralLinearGroup.map (pFin E) (k⁻¹ * m 0 * k) = 1
      rw [hm0, mul_one, inv_mul_cancel, map_one]
    change finRep E 2 (Φ (0, k)) f = f
    rw [e, map_one]
    rfl
  obtain ⟨U, V, hU, hV, h0U, hCV, hUV⟩ := generalized_tube_lemma isCompact_singleton hC hO hsub
  have h0 : (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ U := h0U rfl
  have key : ∀ᶠ d in 𝓝 (0 : FiniteAdeleRing (𝓞 ℚ) ℚ),
      ∀ z ∈ (integralFiniteAdeles (𝓞 ℚ) ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)), d * z ∈ U :=
    (isCompact_integralFiniteAdeles ℚ).eventually_forall_of_forall_eventually fun z _ =>
      (hU.preimage (continuous_fst.mul continuous_snd)).mem_nhds (by simpa using h0)
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele ℚ).eventually key).exists
  refine ⟨n.factorial, n.factorial_pos, fun k hk b hb G => ?_⟩
  have hx := hn b hb
  have hS : finRep E 2 (Φ (_, k)) f = f := hUV (Set.mk_mem_prod hx (hCV hk))
  have hy : finGL E 2 (Φ ((n.factorial : FiniteAdeleRing (𝓞 ℚ) ℚ) * b, k)) =
      k⁻¹ * m ((n.factorial : FiniteAdeleRing (𝓞 ℚ) ℚ) * b) * k := by
    refine ga_ext ?_ ?_
    · rw [pInf_finGL, map_mul, map_mul, map_unipotent_eq_one _ _ (pInf_mk D _), mul_one, ← map_mul, inv_mul_cancel, map_one]
    · rw [pFin_finGL]
  have e := congrArg (fun ψ : Sm E 2 => ψ.1 (G * k)) hS
  change f.1 (G * k * finGL E 2 _) = f.1 (G * k) at e
  rw [hy] at e
  rw [← e]
  change f.1 (G * (m _ * k)) = _
  congr 1
  group
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem diff_top : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
  rw [← Ideal.absNorm_eq_one_iff, absNorm_differentIdeal ℚ (𝓞 ℚ), Rat.numberField_discr]
  rfl

private theorem int_of_inv (v : HeightOneSpectrum (𝓞 ℚ)) {z : v.adicCompletion ℚ}
    (hz : z ∈ GroundTheory.Global.localInvDifferent v) : z ∈ v.adicCompletionIntegers ℚ := by
  rw [GroundTheory.Global.mem_localInvDifferent_iff_valued, diff_top, FractionalIdeal.coeIdeal_top,
    FractionalIdeal.count_one, WithZero.exp_zero] at hz
  exact hz

theorem UpperTheory.exists_isCompact_annihilator_scaled_integralAdeles :
    ∀ N : ℕ, 0 < N → ∃ K : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact K ∧ ∀ x : FiniteAdeleRing (𝓞 ℚ) ℚ,
        (∀ b : FiniteAdeleRing (𝓞 ℚ) ℚ, (∀ v, b v ∈ v.adicCompletionIntegers ℚ) → ψ (((0, x * ((N : FiniteAdeleRing (𝓞 ℚ) ℚ) * b)) : A ℚ)) = 1) → x ∈ K := by
  intro N hN
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  set c : FiniteAdeleRing (𝓞 ℚ) ℚ := algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (N : ℚ)⁻¹ with hc
  have hcN : c * (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := by
    have : (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (N : ℚ) := by
      simp
    rw [this, hc, ← map_mul, inv_mul_cancel₀ hNq, map_one]
  refine ⟨(fun z => c * z) '' (integralFiniteAdeles (𝓞 ℚ) ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)),
    (GroundTheory.Global.isCompact_integralFiniteAdeles ℚ).image (continuous_const.mul continuous_id),
    fun x hx => ?_⟩
  refine ⟨x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ), ?_, ?_⟩
  · intro v
    refine int_of_inv v ((GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff v _).mp fun a ha => ?_)
    have hb : ∀ u, GroundTheory.Global.finiteAdeleSingleAdd v a u ∈ u.adicCompletionIntegers ℚ := by
      intro u
      rcases eq_or_ne u v with rfl | hu
      · rwa [GroundTheory.Global.finiteAdeleSingleAdd_apply_self]
      · rw [GroundTheory.Global.finiteAdeleSingleAdd_apply_of_ne hu]
        exact zero_mem _
    have h := hx _ hb
    have e : x * ((N : FiniteAdeleRing (𝓞 ℚ) ℚ) * GroundTheory.Global.finiteAdeleSingleAdd v a) =
        GroundTheory.Global.finiteAdeleSingleAdd v (a * (x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ)) v) := by
      rw [← GroundTheory.Global.finiteAdeleSingleAdd_mul]
      ring
    rw [e] at h
    have h' : ((GroundTheory.Global.localAdelicChar ℚ v (a * (x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ)) v) : Circle) : ℂ) = 1 := h
    exact Circle.ext (by simpa using h')
  · show c * (x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ)) = x
    rw [mul_comm x, ← mul_assoc, hcN, one_mul]
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.embedGL2_diag_mul_unipotent_theta_eq :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (y : (A ℚ)ˣ) (x : A ℚ),
        em E (aE y) * gl (nU (D.mkE 0 x)) = nE D ![0, (y : A ℚ) * x] * em E (aE y) := by
  intro E _ _ D y x
  have hm : ∀ (h : GL (Fin 2) (A ℚ)) (i j : Fin 2), (em E h).val i j = AdeleBaseChange.adeleMap ℚ E (h.val i j) := fun _ _ _ => rfl
  have hn : ∀ (q : A E), (nU q).val = !![1, q; 0, 1] := fun _ => rfl
  have hk : ∀ u t : A ℚ, D.mkE u t = AdeleBaseChange.adeleMap ℚ E u + AdeleBaseChange.adeleMap ℚ E t * rt D.θ := fun _ _ => rfl
  refine Units.ext ?_
  ext i j
  simp only [nE, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hm]
  fin_cases i <;> fin_cases j <;> simp [aE, hn, hk, map_mul, mul_assoc]
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.whittakerCoeff_ne_zero_finiteAdele_mem_compact :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2), IsAutForm f → Pp.Lf f.1 →
        ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ K : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact K ∧
          ∀ (y : (A ℚ)ˣ), ∀ k ∈ C, Wo D f.1 (em E (aE y) * k) ≠ 0 → (y : A ℚ).2 ∈ K := by
  intro E _ _ _ D f hf hL C hC
  obtain ⟨N, hN, hfN⟩ := UpperTheory.exists_level_unipotent_invariance_automorphicForm E D f hf C hC
  obtain ⟨K, hK, hKN⟩ := UpperTheory.exists_isCompact_annihilator_scaled_integralAdeles N hN
  refine ⟨K, hK, fun y k hk hW => hKN _ fun b hb => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : A ℚ, x = ((0, (N : FiniteAdeleRing (𝓞 ℚ) ℚ) * b) : A ℚ) := ⟨_, rfl⟩
  have h1 : Wo D f.1 (em E (aE y) * k) = Wo D f.1 (em E (aE y) * gl (nU (D.mkE 0 x)) * k) := by
    have pt : ∀ G, f.1 (G * (em E (aE y) * k)) = f.1 (G * (em E (aE y) * gl (nU (D.mkE 0 x)) * k)) := by
      intro G
      have h := hfN k hk b hb (G * em E (aE y))
      rw [← hx] at h
      simp only [mul_assoc] at h ⊢
      exact h.symm
    simp only [Wo]
    congr 1
    funext u
    rw [pt]
  rw [UpperTheory.embedGL2_diag_mul_unipotent_theta_eq, mul_assoc, UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul E D f.1 hL] at h1
  have h2 : ψ (-((y : A ℚ) * x)) = 1 := by
    have h3 : ψ (-((y : A ℚ) * x)) * Wo D f.1 (em E (aE y) * k) = 1 * Wo D f.1 (em E (aE y) * k) := by
      rw [one_mul]
      exact h1.symm
    exact mul_right_cancel₀ hW h3
  have h4 : ψ ((y : A ℚ) * x) = 1 := by
    have h5 := Pp.ψ_add ((y : A ℚ) * x) (-((y : A ℚ) * x))
    have h6 : ψ (0 : A ℚ) = 1 := by
      have := Pp.ψ_rt (0 : ℚ)
      simpa using this
    rw [add_neg_cancel, h6, h2, mul_one] at h5
    exact h5.symm
  have h7 : (y : A ℚ) * x = ((0, (y : A ℚ).2 * ((N : FiniteAdeleRing (𝓞 ℚ) ℚ) * b)) : A ℚ) := by
    rw [hx]
    exact Prod.ext (mul_zero _) rfl
  rw [← h7]
  exact h4
end
