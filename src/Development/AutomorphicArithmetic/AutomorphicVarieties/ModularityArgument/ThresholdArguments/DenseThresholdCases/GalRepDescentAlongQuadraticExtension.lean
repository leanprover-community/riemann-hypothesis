import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.RankTwoDescentSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuspUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IsoOfFrobOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCentChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.RtWMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistInvarianceAutomorphic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.GaloisRepRankTwoOfHyps
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RatioWOfHasSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExRS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.GapTwo

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Matrix Neutral.B1 GlobalTheory.CuspRep Formalism.L2.Host
namespace UpperTheory.V.Sd.Wc
private def wGL (R : Type) [CommRing R] : GL (Fin 2) R :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
private theorem map_wGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    GeneralLinearGroup.map f (wGL R) = wGL S := by
  ext i j
  change f ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R) i j) = (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) S) i j
  fin_cases i <;> fin_cases j <;> simp
private theorem invT_eq {R : Type} [CommRing R] (g : GL (Fin 2) R) :
    invT 2 R g = GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det g)⁻¹ * (wGL R * (g * (wGL R)⁻¹)) := by
  rw [map_inv, eq_inv_mul_iff_mul_eq, ← eq_mul_inv_iff_mul_eq]
  apply Units.ext
  change Matrix.scalar (Fin 2) g.val.det = !![0, 1; -1, 0] * (g.val * !![0, -1; 1, 0]) * g.valᵀ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.det_fin_two, Fin.sum_univ_two] <;> ring
private theorem rt_w_mem {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2)
    {φ : TR.Sm F 2} (hφ : φ ∈ π.V) : TR.rt F 2 (wGL (Ad F))⁻¹ φ ∈ π.V := by
  let k : TR.Kinf F 2 := ⟨!![0, -1; 1, 0], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  have hk : Unitary.toUnits k = (wGL (TR.Rinf F))⁻¹ := Units.ext rfl
  rw [← TR.infGL_mul_finGL (wGL (Ad F))⁻¹, map_inv, map_wGL, ← hk, map_mul]
  exact π.stable (.cpt k) _ (π.stable (.fin _) _ hφ)
end UpperTheory.V.Sd.Wc
open UpperTheory.V UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.polGL2_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.Wc.PolGL2 := by
  intro P F _ _ _ π ω h
  obtain ⟨B, hl, hr, hf, hc, hX⟩ := P.gkR F 2 π
  refine TR.CuspSub.isSelfDualBy_of_iso B hl hr hf hc hX ?_
  have hle : (π.dual.twist ω).V ≤ π.V := by
    rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    convert rt_w_mem π hφ using 1
    refine Subtype.ext (funext fun g => ?_)
    change φ.1 (invT 2 (Ad F) g) * ((ω.1 (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = φ.1 (g * (wGL (Ad F))⁻¹)
    have e : wGL (Ad F) = ratGL F 2 (wGL F) := (map_wGL _).symm
    rw [invT_eq, h _ φ hφ, map_inv, mul_right_comm, Units.inv_mul, one_mul]
    conv_lhs => rw [e]
    rw [(π.cusp φ hφ).1.left, ← e]
  have e : π.dual.twist ω = π :=
    TR.CuspSub.ext ((π.irred _ hle (π.dual.twist ω).stable).resolve_left (π.dual.twist ω).ne_bot)
  rw [e]
  exact TR.CuspSub.Iso.refl π
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol UpperTheory.V.Z.Bc
private theorem cusp_unique {F : Type} [Field F] [NumberField F] {n : ℕ} {sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop}
    {inf : (F →+* ℂ) → Multiset ℂ → Prop} (h : IsCusp n sat inf) : ∀ v B B', sat v B → sat v B' → B = B' := by
  rcases h with ⟨_, π, rfl, -⟩ | ⟨_, π, rfl, -⟩
  · exact fun _ _ _ h h' => h.unique h'
  · exact fun _ _ _ h h' => h.unique h'
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)
private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem isoOfFrobOne (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r r' : G F Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r)
    (hr' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r')
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 →
      ∃ B, FrobEig ι r w B ∧ FrobEig ι r' w B) : RepIso r r' := by
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  have hc : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G F Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    rintro σ ⟨v, hv, hd, A, hA, hσ⟩
    obtain ⟨B, hB, hB'⟩ := not_not.1 hv hd
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩
private theorem normV_one {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) (h : w.asIdeal.inertiaDeg ℤ = 1) : normV w = normV (w.under (𝓞 K)) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  rw [Ideal.inertiaDeg_tower (R := ℤ) (w.under (𝓞 K)).asIdeal w.asIdeal] at h
  rw [normV_under (K := K) w, Nat.eq_one_of_mul_eq_one_left h, pow_one]
theorem UpperTheory.V.Z.Bc.automorphic_rank_two_of_automorphic_restrict_of_finite_det :
    ∀ (H : _root_.UpperTheory.V.Af.HypothesesH') (cyc : DescS) (hG : GapTwo) (hR : ExRTwo) (M Ω : Type) [Field M] [NumberField M] [Field Ω] [Algebra ℚ Ω]
      [Algebra M Ω] [IsScalarTower ℚ M Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure M Ω] (hp : Module.finrank ℚ M = 2) (hM : IsCMField M)
      (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hr : Continuous r)
      (hirr : IsIrr (r.comp (resG ℚ M Ω))) (hfin : ∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (r s) ^ N = 1), IsAut ι (r.comp (resG ℚ M Ω)) → IsAut ι r := by
  intro H cyc hG hR M Ω _ _ _ _ _ _ _ _ hp hM l _ ι r hr hirr hfin
  haveI : Algebra.IsQuadraticExtension ℚ M := ⟨hp⟩
  have hK : IsTotallyReal ℚ := inferInstance
  have hdown := cyc M hp inferInstance
  have hss : IsSSRep (r.comp (resG ℚ M Ω)) := (Bc.irrBasic.1 _ Unit _ 2 _).2.1 hirr
  have hirr' : IsIrr r := (Bc.irrBasic.1 _ _ _ 2 r).1 _ hirr
  have hcont := continuous_restrictScalarsHom ℚ M Ω
  rintro ⟨sat', inf', hc', hreg', hatt'⟩
  have hgap : Gap2 inf' := by
    rcases hc' with ⟨_, P, rfl, rfl⟩ | ⟨hR', -⟩
    · refine hG M Ω l ι _ P ((GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_) hatt' (hfin.imp fun N h => ⟨h.1, fun s => h.2 _⟩)
      obtain ⟨m, hm, h⟩ := hreg' τ
      rw [CG.HasInfChar.infChar_eq (π := CG.mk P) hm]
      exact h
    · exact (not_both M hR' inferInstance).elim
  obtain ⟨sat, inf, hc, hbc, hinf⟩ := hdown sat' inf' hc' hreg' hgap (UpperTheory.satake_invariant_of_frobConj_of_eigenvalue_basic UpperTheory.frobenius_conj_of_galois_conjugate_places UpperTheory.hecke_eigenvalue_basic_properties ℚ M Ω l ι 2 r sat' hatt')
  have hreg : RegInf 2 inf := fun τ => by
    obtain ⟨m, hm, h⟩ := hreg' (ComplexEmbedding.lift M τ)
    have := hinf _ m hm
    rw [ComplexEmbedding.lift_comp_algebraMap] at this
    exact ⟨m, this, h⟩
  obtain ⟨r₁, hr₁, hatt₁⟩ := (show ∃ r₁ : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous r₁ ∧ AttachedSys ι r₁ sat by
    rcases hc with ⟨hC, -⟩ | ⟨hR', π, rfl, rfl⟩
    · exact (not_both ℚ hK hC).elim
    · obtain ⟨ω, hω, -⟩ := _root_.UpperTheory.V.Sd.Wc.centChar_alt H.toClassicalTheorems ℚ π
      refine hR ℚ Ω l ι π ω (fun v => ?_) ⟨fun v v' => by rw [Subsingleton.elim v v'], _root_.UpperTheory.V.Sd.Wc.polGL2_alt H.toClassicalTheorems ℚ π ω hω⟩
      have := hreg v.embedding
      simpa only [InfinitePlace.mk_embedding] using this)
  have hN := (UpperTheory.galois_representation_image_spec ℚ M Ω).1
  have hss₁ := UpperTheory.semisimpleModule_restriction_to_normal_subgroup _ _ _ 2 r₁ (resG ℚ M Ω) hN hatt₁.1
  have hiso : RepIso (r₁.comp (resG ℚ M Ω)) (r.comp (resG ℚ M Ω)) := by
    refine isoOfFrobOne M Ω l ι 2 _ _ (hr₁.comp hcont) (hr.comp hcont) hss₁ hss ?_
    filter_upwards [hbc, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under ℚ M).eventually hatt₁.2, hatt'.2]
      with w h1 ⟨B₁, hB₁, h₁⟩ ⟨B', hB', h'⟩ hd
    have hn := normV_one (K := ℚ) w hd
    obtain ⟨B, hB, hP⟩ := h1 hn
    obtain rfl := cusp_unique hc _ _ _ hB hB₁
    obtain rfl := cusp_unique hc' _ _ _ hP hB'
    have h3 := (UpperTheory.frobenius_power_compatibility ℚ M Ω l ι w 1 (by rw [pow_one]; exact hn)).1 2 r₁ _ h₁
    simp only [pow_one, Multiset.map_id'] at h3
    rw [← hn] at h3
    exact ⟨_, h3, h'⟩
  obtain ⟨δ, hδ, hiso'⟩ := UpperTheory.schur_extension _ _ _ 2 r r₁ (resG ℚ M Ω) hN hirr hiso
  have hF := UpperTheory.finiteCharacter_of_algebraic_cyclotomic (_root_.UpperTheory.V.Af.algOfCyc_s H)
  obtain ⟨sat₂, inf₂, hc₂, hreg₂, hatt₂⟩ := _root_.UpperTheory.V.Af.twist_invariance_automorphic H ℚ Ω l ι 2 r₁ δ ⟨sat, inf, hc, hreg, hatt₁⟩
    (hF.1 ℚ Ω l ι δ (hF.2 ℚ M Ω l δ hδ))
  exact ⟨sat₂, inf₂, hc₂, hreg₂, (Bc.irrBasic.1 _ Unit _ 2 _).2.1 hirr',
    hatt₂.2.mono fun w ⟨B, hB, h⟩ => ⟨B, hB, h.of_iso hiso'⟩⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol
namespace UpperTheory.V.Z.Bc
theorem exists_residual_rep_quadratic_alt (P : _root_.UpperTheory.V.Af.HypothesesH') : ExRTwo := fun F Ω _ _ _ _ _ _ l _ ι π χ h1 h2 =>
  let ⟨r, _, _, H, h, _⟩ := _root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems F Ω l ι 2 one_le_two π χ h1 h2
  ⟨r, H.cont, h⟩
end UpperTheory.V.Z.Bc
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Base UpperTheory.V.Af
open scoped Matrix
private theorem cc_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ c : G ℚ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
private theorem cc_mu {Ω : Type} [Field Ω] [CharZero Ω] {c : G ℚ Ω} (hc : IsConjEl c) {M : ℕ} (hM : 1 ≤ M) {ζ : Ω}
    (h : ζ ^ M = 1) : c ζ = ζ⁻¹ := by
  obtain ⟨j, hj⟩ := hc
  apply j.injective
  have h1 : (j ζ) ^ M = 1 := by rw [← map_pow, h, map_one]
  rw [hj, map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 (by omega))]
private theorem kills_cc {Ω : Type} [Field Ω] [CharZero Ω] {C : Type} [CommGroup C] {M : ℕ} (hM : 1 ≤ M) {χ : G ℚ Ω →* C}
    (hχ : KillsMu M χ) {c c' : G ℚ Ω} (hc : IsConjEl c) (hc' : IsConjEl c') : χ c = χ c' := by
  have := hχ (c⁻¹ * c') fun ζ h => by
    rw [AlgEquiv.mul_apply, cc_mu hc' hM h, ← cc_mu hc hM h]
    exact c.symm_apply_apply ζ
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this
private theorem kills_pow {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {C : Type} [CommGroup C] {M : ℕ} (hM : 1 ≤ M)
    {χ : G ℚ Ω →* C} (hχ : KillsMu M χ) : ∃ k : ℕ, 0 < k ∧ ∀ s, χ s ^ k = 1 := by
  haveI : NeZero M := ⟨by omega⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  refine ⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, fun s => ?_⟩
  rw [← map_pow]
  refine hχ _ fun ζ h => ?_
  have h1 := hμ.autToPow_spec ℚ (s ^ Fintype.card (ZMod M)ˣ)
  rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hμ.pow_eq_one, pow_one] at h1
  obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one h
  rw [map_pow, ← h1]
private theorem pair2 {k : Type} [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
private theorem pairing2 {F Ω k : Type} [Field F] [Field Ω] [Algebra F Ω] [Field k] (r : G F Ω →* GL (Fin 2) k) (c : G F Ω) :
    ∃ P, IsPairing c r ((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω)) P := by
  let J : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
  have h' : s' = c * s * c⁻¹ := h
  have e : r c⁻¹ * r s' = r s * r c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (r c⁻¹).val * (r s').val = (r s).val * (r c⁻¹).val := congrArg Units.val e
  have hp : (r s).valᵀ * J.val * (r s).val = (r s).val.det • J.val := pair2 _
  have hd : (((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω) s : kˣ) : k) = (r s).val.det := rfl
  rw [hd, Units.val_mul, ← Matrix.smul_mul, ← hp]
  simp only [Matrix.mul_assoc, e']
private theorem tf (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree
attribute [local instance] tf
private theorem algClosure_up (L Ω : Type) [Field L] [CharZero L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] :
    IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
open UpperTheory.V UpperTheory.V.Af in
private theorem via (P : _root_.UpperTheory.V.Af.HypothesesH') (cyc : Z.Bc.CycC) (cyc2 : Z.Bc.DescS) (hG : Z.Bc.GapTwo) (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsAbelianGalois ℚ L]
    (hK : Module.finrank ℚ K = 2) (hC : IsCMField K) (hL : IsCMField L) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hW : Continuous W) (hirr : IsIrr (W.comp (resG ℚ L Ω))) (hpol : Sol.Pol ι W)
    (hfin : ∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (W s) ^ N = 1)
    (haut : IsAut ι (W.comp (resG ℚ L Ω))) : IsAut ι W := by
  haveI : IsAlgClosure K Ω := algClosure_up K Ω
  haveI : IsAlgClosure L Ω := algClosure_up L Ω
  haveI a : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  have e : (W.comp (resG ℚ K Ω)).comp (resG K L Ω) = W.comp (resG ℚ L Ω) := MonoidHom.ext fun _ => rfl
  rw [← e] at hirr haut
  have h1 := (_root_.UpperTheory.V.Z.Bc.solC_alt P cyc K L Ω (isSolvable_of_comm a.is_comm.comm) hC hL l ι 2 one_le_two (W.comp (resG ℚ K Ω))
    (hW.comp (continuous_restrictScalarsHom ℚ K Ω)) hirr (UpperTheory.solvable_polarized_restriction ℚ K Ω l ι 2 W hpol)).2 haut
  exact _root_.UpperTheory.V.Z.Bc.automorphic_rank_two_of_automorphic_restrict_of_finite_det P cyc2 hG (_root_.UpperTheory.V.Z.Bc.exists_residual_rep_quadratic_alt P) K Ω hK hC l ι W hW ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hirr) hfin h1
open UpperTheory.V UpperTheory.V.Af in
theorem UpperTheory.V.Z.Bc.isAutR_of_isAutC_comp_galEmb_of_odd_quadratic_char (P : _root_.UpperTheory.V.Af.HypothesesH') (cyc : Z.Bc.CycC) (cyc2 : Z.Bc.DescS) (hG : Z.Bc.GapTwo) :
  ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [IsAbelianGalois ℚ L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous W →
    IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) → IsIrr (W.comp (galEmb ℚ L Ω)) →
    (∃ (η : G ℚ Ω →* ℤˣ) (σ : G ℚ Ω), Sd.IsCC σ ∧ η σ = -1 ∧ ∀ s : G L Ω, η (galEmb ℚ L Ω s) = 1) →
    Sd.IsAutC ι (W.comp (galEmb ℚ L Ω)) → IsAutR ι W := by
  intro L Ω _ _ _ _ _ _ _ _ l _ ι W hW hdet hirr ⟨η, σ, hσ, hησ, hηL⟩ haut
  haveI : IsAlgClosure L Ω := algClosure_up L Ω
  obtain ⟨M, χ, hM, hχ, hθ⟩ := hdet
  rw [zpow_zero, one_mul] at hθ
  have hcont : Continuous (Matrix.GeneralLinearGroup.det.comp W) :=
    Matrix.GeneralLinearGroup.continuous_det.comp hW
  obtain ⟨k, hk, hpow⟩ := kills_pow hM hχ
  have halg : IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s P ℚ Ω l ι).1 _ hcont fun w _ => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    exact ⟨A, hA, 0, k, hk, fun s _ => by rw [neg_zero, zpow_zero, mul_one, hθ, hpow]⟩
  obtain ⟨c, hc⟩ := cc_ex Ω
  obtain ⟨Q, hQ⟩ := pairing2 W c
  have hfin : ∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (W s) ^ N = 1 :=
    ⟨k, hk, fun s => by
      have e : Matrix.GeneralLinearGroup.det (W s) = χ s := DFunLike.congr_fun hθ s
      rw [e, hpow]⟩
  obtain ⟨K, hK, hC⟩ := Z.Bc.exists_quad L Ω η σ hσ hησ hηL
  have hpol : Sol.Pol ι W := ⟨ℚ, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, Q, halg,
    fun c c' h h' => by rw [hθ]; exact kills_cc hM hχ h h', hc, hQ⟩
  exact (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida P ℚ Ω l ι 2 W).1.1 (via P cyc cyc2 hG K L Ω hK hC inferInstance l ι W hW hirr hpol hfin ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida P L Ω l ι 2 _).2.1.2 haut))
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Z.Bc
section SlopeTestRemainingChoices
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
private theorem lie_central {π : CuspSub E a} {ω : HChar E} (hω : π.HasCentral ω) (z : Cinf E) {ψ : Sm E a} (hψ : ψ ∈ π.V) :
    ∑ i, lieS E a i i z ψ = dchi ω z • ψ := by
  have e2 : lie E a (Central.scL a z) = ∑ i, lieS E a i i z := by
    simp only [lieS_apply, ← map_sum]
    exact congrArg (lie E a) (Matrix.sum_single_eq_diagonal (fun _ : Fin a => z)).symm
  rw [← LinearMap.sum_apply, ← e2]
  refine Subtype.ext (funext fun g => ?_)
  have h1 := Central.hasDerivAt_scalar z ψ g
  have h2 : (fun t : ℝ => ψ.1 (g * Matrix.GeneralLinearGroup.scalar (Fin a) (infId E (expU (t • z))))) =
      fun t : ℝ => Complex.exp (t * dchi ω z) * ψ.1 g := by
    funext t
    have h3 := congrFun (congrArg Subtype.val (hω (infId E (expU (t • z))) ψ hψ)) g
    have h4 := chiInf_expU ω (t • z)
    rw [map_smul, Complex.real_smul] at h4
    rw [← h4]
    exact h3
  rw [h2] at h1
  have h5 := (((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi ω z)).cexp).mul_const (ψ.1 g)
  have h6 := h1.unique h5
  change lieD _ ψ.1 g = dchi ω z * ψ.1 g
  rw [h6]
  simp
private theorem expo_central {π : CuspSub E a} {ω : HChar E} (hω : π.HasCentral ω) {τ : E →+* ℂ} {m : Multiset ℂ}
    (hm : π.HasInfChar τ m) : expo ω τ = m.sum := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  refine smul_left_injective ℂ h0 ?_
  beta_reduce
  rw [← GlobalTheory.trace_Eop_of_hasInfChar E a π τ m hm φ hφ]
  have h1 := lie_central hω (atEmb τ 1) hφ
  have h2 := lie_central hω (atEmb τ Complex.I) hφ
  simp only [Eop, expo, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply, ← Finset.smul_sum, Finset.sum_sub_distrib, h1, h2]
  module
private theorem det_algSat (M : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) (x y : ℂˣ)
    (h : M.charpoly = ((algSat 2 q {x, y}).map fun b => X - C b).prod) : M.det = (q : ℂ) * ((x * y : ℂˣ) : ℂ) := by
  have hq : ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) * ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) = q := by
    rw [← Real.rpow_add' (Nat.cast_nonneg q) (by norm_num)]
    norm_num
  have hq' := congrArg (fun x : ℝ => (x : ℂ)) hq
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hq'
  have e : algSat 2 q {x, y} = {(((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * x,
      (((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * y} := by
    simp [algSat]
  rw [Matrix.det_eq_prod_roots_charpoly, h, roots_multiset_prod_X_sub_C, e, Multiset.prod_pair, mul_mul_mul_comm, hq',
    Units.val_mul]
private theorem gap_of_sum {x y : ℂ} (hne : x ≠ y) {i j : ℤ} (hi : x = i + 1 / 2) (hj : y = j + 1 / 2) (hs : x + y = 1) :
    ∃ (c : ℂ) (k : ℕ), 2 ≤ k ∧ ({x, y} : Multiset ℂ) = {c, c + k} := by
  have h0 : i + j = 0 := by
    have : ((i + j : ℤ) : ℂ) = 0 := by push_cast; linear_combination hs - hi - hj
    exact_mod_cast this
  have h1 : i ≠ j := fun e => hne (by rw [hi, hj, e])
  rcases lt_or_gt_of_ne h1 with h | h
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h.le)
    refine ⟨x, k, by omega, ?_⟩
    have : ((j - i : ℤ) : ℂ) = k := by rw [hk]; simp
    push_cast at this
    rw [show x + k = y by linear_combination hi - hj - this]
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h.le)
    refine ⟨y, k, by omega, ?_⟩
    have : ((i - j : ℤ) : ℂ) = k := by rw [hk]; simp
    push_cast at this
    rw [show y + k = x by linear_combination hj - hi - this, Multiset.pair_comm]
end SlopeTestRemainingChoices
theorem UpperTheory.V.Z.Bc.gapTwo_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Bc.GapTwo := by
  intro _ F Ω _ _ _ _ _ _ l _ ι r P hreg hatt ⟨N, hN, hdet⟩ τ
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral F 2 P
  have hone : (ω * GlobalTheory.HeckeGal.Model.absPow F (-1)) ^ N = 1 := by
    refine PositivityTheory.jumpWindows.FiniteInfinitePlaceProduct.eq_one _ ?_
    filter_upwards [hatt.2] with w ⟨B, hB, hF⟩
    obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have h1 := PositivityTheory.jumpWindows.PSmo.val_eq_prod (CuspSub.hasCentral_iff.1 hω) hB
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
    have e2 := (hF A hA).2 σ hσ
    rw [← Matrix.charpoly_map] at e2
    have e3 := det_algSat _ _ _ _ e2
    have e4 : ι (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det =
        ((r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).map ι.toRingHom).det := ι.toRingHom.map_det _
    have e5 := congrArg (fun u : (Qbar l)ˣ => ι (u : Qbar l)) (hdet σ⁻¹)
    simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one, Matrix.GeneralLinearGroup.val_det_apply] at e5
    rw [e4, e3] at e5
    have e6 := (GlobalTheory.HeckeGal.Model.absPow_isAbsPow F (-1)).2.1 w
    refine Units.ext ?_
    have hp : ∀ ν : HChar F, (ν ^ N).val w = ν.val w ^ N := fun ν => MonoidHom.pow_apply ν.1 N _
    rw [hp, HChar.val_mul, Units.val_pow_eq_pow_val, Units.val_mul, e6, h1, Multiset.prod_pair, Units.val_one, ← e5, mul_comm]
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsum : ((CG.mk P).infChar τ).sum = 1 := by
    have h1 := GlobalTheory.BCT.TwistDisc.expo_pow (ω * GlobalTheory.HeckeGal.Model.absPow F (-1)) N τ
    have h2 := GlobalTheory.BCT.TwistDisc.expo_pow (1 : HChar F) 0 τ
    rw [pow_zero, Nat.cast_zero, zero_mul] at h2
    have h3 := (CG.hasInfChar_ofChar ω τ).twist (GlobalTheory.HeckeGal.Model.absPow F (-1))
    rw [CG.twist_ofChar, Multiset.map_singleton] at h3
    have h4 := h3.infChar_eq
    rw [CG.infChar_ofChar, Multiset.singleton_inj] at h4
    have h5 : expo (GlobalTheory.HeckeGal.Model.absPow F (-1)) τ = ((-1 : ℝ) : ℂ) := GlobalTheory.CuspRep.Model.expo_absC _ τ
    rw [hone, h2, h4, h5, expo_central hω (ParLaws.hasInfChar_infChar (CG.mk P) τ)] at h1
    have h6 := (mul_eq_zero.1 h1.symm).resolve_left (Nat.cast_ne_zero.2 hN.ne')
    push_cast at h6
    linear_combination h6
  have hm : P.HasInfChar τ ((CG.mk P).infChar τ) := ParLaws.hasInfChar_infChar (CG.mk P) τ
  obtain ⟨hnd, hint⟩ := hreg τ
  obtain ⟨x, y, e⟩ := Multiset.card_eq_two.1 (CG.card_infChar (CG.mk P) τ)
  rw [e] at hm hnd hint hsum
  obtain ⟨i, hi⟩ := hint x (by simp)
  obtain ⟨j, hj⟩ := hint y (by simp)
  obtain ⟨c, k, hk, e'⟩ := gap_of_sum (x := x) (y := y) (by simpa using hnd) (i := i) (j := j) (by rw [hi]; norm_num)
    (by rw [hj]; norm_num) (by simpa using hsum)
  exact ⟨c, k, hk, e' ▸ hm⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Af.rankTwoAutomorphyDescends_of_printsH :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Pr.RankTwoAutomorphyDescendsFromAbelianCMToRat := fun P =>
  Or.elim P.cyc2 (fun h => _root_.UpperTheory.V.Z.Bc.isAutR_of_isAutC_comp_galEmb_of_odd_quadratic_char P P.cyc h (_root_.UpperTheory.V.Z.Bc.gapTwo_alt P))
    fun h L Ω _ _ _ _ _ _ _ _ l _ ι W h1 h2 h3 h4 h5 => h L Ω l ι W h1 h2 h3 h4 h5
end
end
