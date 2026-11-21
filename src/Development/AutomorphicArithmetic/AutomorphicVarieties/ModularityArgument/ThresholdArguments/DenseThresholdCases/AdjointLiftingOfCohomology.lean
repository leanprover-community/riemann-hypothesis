import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.VwinOfEnd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThFinal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PmExTh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVCore
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.ConductorAtMapInjectiveCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAut4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RigEnd3
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CountNormInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelPS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.MonoOddOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CompatP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WinNumN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FrobeniusTraceCountBoundOfCmEigensystemCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KeepLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelAdmissibleRestrictionHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.ExistsPlaceAbovePrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.LinkEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWAutKQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQ0
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RRFreeW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuspUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AuTh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPhiEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.HalfPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistInvarianceAutomorphic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWCsdOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNiceFour

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private count_norm_int count_chi count_pow count_trace from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CountNormInt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
theorem UpperTheory.V.Z.Win.A4.exists_frob_nonvanishing_with_sha_bound :
    _root_.UpperTheory.V.Af.NumberSp4Alt → ∃ C A : ℕ, ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.ψ → Af.KillsMu N D.ξ → Af.KillsMu N D.om → ∀ k : ℕ, 0 < k → D.ψ ^ k = 1 → D.ξ ^ k = 1 → D.om ^ k = 1 → ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ N → p ∉ D.S → ∀ ι, D.AllIrr (_root_.UpperTheory.V.Aut.IsAut4Alt ι) → ∃ σ : G ℚ Ω, D.AllIrr (fun r => D.aVal σ r ≠ 0) ∧ (D.Ineq σ → Chr.nrm l c.O D.sha * Real.log l ≤ 2 * C * k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p) := by
  classical
  rintro ⟨C, A, hnum⟩
  refine ⟨C, A, ?_⟩
  intro Ω _ _ _ l hl c D hD N hN hψN hξN hoN k hk hψ hξ ho p hp hp5 hpN hpS ι haut
  have hlp : l ≠ p := fun h => hpS (h ▸ hD.l_mem)
  obtain ⟨-, hfr, -, hco, -, -, -, -, hpl, -⟩ := ML.placeBasic Ω
  have hB : ML.Over (D.pl p) p := hD.pl_over p hp
  obtain ⟨σ, hσ⟩ := hfr _ p hp hB
  obtain ⟨w, hw, -, hpw⟩ := hpl _ p hp hB
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => by
    refine hco _ p l ((Nat.coprime_primes hp hl.out).2 hlp.symm) hB ?_
    have h1 := (hw ((l : ℕ) : 𝓞 ℚ)).2 h
    have e : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω) := by simp
    rw [e] at h1
    exact h1
  have hχ := count_chi c hlw hw hσ
  have h3 : (D.om⁻¹ * D.ξ) ^ k = 1 := by rw [mul_pow, inv_pow, ho, hξ, inv_one, one_mul]
  have h1 : (D.om⁻¹ * D.ξ * D.ψ) ^ k = 1 := by rw [mul_pow, h3, hψ, one_mul]
  obtain ⟨NN, hNN, hlog, hX⟩ := hnum D.e hD.two_le N hN p w hp hpw hp5 hpN k hk _ _ _
    (count_pow c ι _ h1 σ) (count_pow c ι _ hψ σ) (count_pow c ι _ h3 σ)
  replace hX := hX l hD.l_odd hlp Ω ι (D.pl p) hw σ hσ
  rw [← count_trace D ι hχ] at hX
  have hadm : ∀ r, D.EPt r → Irr r → _root_.UpperTheory.V.Af.AdmRAlt ι N ![(D.e : ℤ) + 1, D.e, 1, 0] (D.e + 1) r.toHomUnits := by
    intro r hr hi
    obtain ⟨hlev, θ, hθ, hdual, -⟩ := level D hD N hN hψN hξN hoN r hr
    exact ⟨((irrIff _).1 r).1 hi, haut r hr hi, hlev, ⟨θ, hθ, hdual⟩, _root_.UpperTheory.V.Z.Win.A4.safe4' D hD N hN hψN hξN hoN r hr⟩
  have hne : D.AllIrr (fun r => D.aVal σ r ≠ 0) := by
    intro r hr hi
    have h := (hX {r.toHomUnits} (fun s hs => by rw [Finset.mem_singleton.1 hs]; exact hadm r hr hi)
      (fun s hs s' hs' _ => by rw [Finset.mem_singleton.1 hs, Finset.mem_singleton.1 hs'])).1 _
      (Finset.mem_singleton_self _)
    exact sub_ne_zero.2 h
  refine ⟨σ, hne, ?_⟩
  rintro ⟨-, Xi, hXi, hconj, hle⟩
  have hinj : Function.Injective fun r : G ℚ Ω →* M4 (PadicAlgCl l) => r.toHomUnits := fun r r' h =>
    MonoidHom.ext fun g => congrArg Units.val (DFunLike.congr_fun h g)
  have h := (hX (Xi.image fun r => r.toHomUnits) (fun s hs => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hs
      exact hadm r (hXi r hr).1 (hXi r hr).2) (fun s hs s' hs' hss => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨r', hr', rfl⟩ := Finset.mem_image.1 hs'
      rw [hconj r hr r' hr' (((irrIff _).2 r r').2 hss)])).2
  rw [Finset.prod_image hinj.injOn] at h
  change _ ≤ ∏ r ∈ Xi, ‖D.aVal σ r‖ at h
  have hN0 : 0 < ‖(NN : PadicAlgCl l)‖ := norm_pos_iff.2 (by exact_mod_cast hNN)
  have h4 := Real.log_le_log hN0 h
  rw [Real.log_prod fun r hr => norm_ne_zero_iff.2 (hne r (hXi r hr).1 (hXi r hr).2)] at h4
  have h5 := count_norm_int l NN hNN
  have h6 : (C : ℝ) * Nat.totient k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p ≤
      C * k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p := by
    have : (Nat.totient k : ℝ) ≤ k := by exact_mod_cast Nat.totient_le k
    have := Real.log_natCast_nonneg p
    gcongr
  rw [Finset.sum_neg_distrib] at hle
  linarith
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
section Transfer
variable {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O')
private def chHom : DirichletCharacter O N →* DirichletCharacter O' N where
  toFun χ := χ.ringHomComp f
  map_one' := MulChar.ringHomComp_one f
  map_mul' a b := MulChar.ringHomComp_mul a b f
private theorem chHom_inj (hf : Function.Injective f) : Function.Injective (chHom (N := N) f) :=
  MulChar.injective_ringHomComp hf
private theorem chHom_ord (hf : Function.Injective f) (χ : DirichletCharacter O N) : orderOf (chHom f χ) = orderOf χ :=
  orderOf_injective _ (chHom_inj f hf) _
private theorem chHom_comp (r : ℕ) (χ : DirichletCharacter O N) : chHom f (comp r χ) = comp r (chHom f χ) := by
  refine MulChar.ext fun a => ?_
  show f (comp r χ a) = _
  simp only [HV.comp, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rfl
private theorem map_injective_coeff_twist_comm (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    chHom f (th0 l χ) = th0 l (chHom f χ) := by
  simp only [th0, lPrime, lPart, map_mul, map_inv, map_pow, chHom_ord f hf]
private theorem chHom_chiP (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    chHom f (chiP l χ) = chiP l (chHom f χ) := by
  simp only [chiP, map_mul, map_inv, chHom_comp, map_injective_coeff_twist_comm f hf]
private theorem conductor_at_map_injective_coeff (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    n0 l (chHom f χ) = n0 l χ := by
  have h : chHom f (th1 l χ) = th1 l (chHom f χ) := by
    simp only [th1, map_mul, map_inv, chHom_comp, map_injective_coeff_twist_comm f hf]
  unfold n0 f0
  rw [← h, chHom_ord f hf]
private theorem chHom_ker (hf : Function.Injective f) (χ : DirichletCharacter O N) :
    (chHom f χ).toUnitHom.ker = χ.toUnitHom.ker := by
  ext u
  simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
  exact map_eq_one_iff f hf
private theorem parity_at_map_injective_coeff [NeZero N] (hf : Function.Injective f) (χ : DirichletCharacter O N) :
    c2 (chHom f χ) = c2 χ := by
  have h : ∀ φ : DirichletCharacter O N, (chHom f φ).conductor = φ.conductor := fun φ => by
    unfold DirichletCharacter.conductor
    congr 1
    ext d
    simp only [DirichletCharacter.mem_conductorSet_iff]
    by_cases hd : d ∣ N
    · rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd, DirichletCharacter.factorsThrough_iff_ker_unitsMap hd,
        chHom_ker f hf]
    · exact ⟨fun h => absurd h.dvd hd, fun h => absurd h.dvd hd⟩
  unfold c2 psi2
  rw [← chHom_comp, h]
private theorem chHom_even (hf : Function.Injective f) (e : ℕ) (χ : DirichletCharacter O N) :
    PsiEven e (chHom f χ) ↔ PsiEven e χ := by
  show f (χ (-1)) = _ ↔ χ (-1) = _
  rw [← hf.eq_iff (a := χ (-1)), map_pow, map_neg f, map_one f]
end Transfer
private theorem enough_of_le {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) (n : ℕ) [NeZero n]
    [HasEnoughRootsOfUnity c.O n] : HasEnoughRootsOfUnity c'.O n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot c.O n
  exact ⟨⟨_, hζ.map_of_injective (f := Subalgebra.inclusion h) (Subalgebra.inclusion_injective h)⟩, inferInstance⟩
private theorem main_big (hA : _root_.UpperTheory.V.Aut.SymplecticFourImageDense) (hP : CohomologyHyp) (hM : LemmaM) (hM' : LemmaM') (hLP : LemmaP) (hN : _root_.UpperTheory.V.Af.NumberSp4Alt)
    (hAd : _root_.UpperTheory.V.Th.RigiditySymplecticFour) (hX : X.CorX)
    (hSo : ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], SoV Ω l ∧ SoFin Ω l)
    (χ : Formalism.HC.PChar) : ∃ C : ℕ, ∀ h : Host, h.chi = χ → ∀ t : ℕ, h.Big t →
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ),
      l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, h.CaseII l e ψ ∨ h.CaseIII l e ψ →
      HasEnoughRootsOfUnity c.O (2 ^ h.nII l ψ) → HasEnoughRootsOfUnity c.O (2 ^ h.nIII l ψ) →
      VLe Ω c e ψ (((l : ℝ) * h.N * e) ^ C) := by
  obtain ⟨C, A, hc⟩ := _root_.UpperTheory.V.Z.Win.A4.exists_frob_nonvanishing_with_sha_bound hN
  obtain ⟨C', hC'⟩ := arith χ C A
  refine ⟨C', fun h hχ t ht Ω _ _ _ l hl c e hl2 he0 het ψ hψ hcase r1 r2 => ?_⟩
  obtain ⟨D, hD, hOf⟩ := dataEx hX Ω h t ht l c e hl2 he0 het ψ hψ hcase r1 r2
  obtain ⟨hF, hNE, ι, hAU⟩ := hA Ω h t ht l c e hl2 he0 het ψ hψ D hD hOf
  have hctx : Ctx2 D ∨ Ctx3 D :=
    hOf.imp (fun hc => ⟨hD, h, t, e, ψ, ht, he0, het, hψ, hc.1, hc.2⟩)
      (fun hc => ⟨hD, h, t, e, ψ, ht, he0, het, hψ, hc.1, hc.2⟩)
  have hsha := shaEq Ω h t ht l c e hl2 he0 het ψ hψ D hD hOf
  obtain ⟨M⟩ := exModel D hD hLP (phiGam D hD hP) (nums D hD hP) (locBase D hD hP.loc)
  have ho : 0 < h.o := (hostIndex h).2.2.2.1
  have hlp := hl.out
  obtain ⟨n', p₁, m₀, hO, hn', hm₀, har⟩ : ∃ n' p₁ m₀ : ℕ, Aut.OfChar D e ψ n' p₁ m₀ ∧ c2 ψ ≤ n' ∧ m₀ ∣ h.o ∧
      ((n' = h.nII l ψ ∧ p₁ = 1) ∨ (n' = h.nIII l ψ ∧ p₁ = UpperTheory.V.pOne χ)) := by
    rcases hOf with ⟨-, hO⟩ | ⟨h3, hO⟩
    · refine ⟨_, _, _, hO, ?_, one_dvd _, Or.inl ⟨rfl, rfl⟩⟩
      have h1 : 2 ^ c2 ψ ≤ max (l * h.N * 4 ^ n0 l ψ) (2 ^ (c2 ψ + 6) * h.o * l ^ 3 * h.q ^ 2) := by
        refine le_trans ?_ (le_max_right _ _)
        have hq : 0 < h.q := NeZero.pos _
        have := hlp.pos
        rw [pow_add, mul_assoc, mul_assoc, mul_assoc]
        exact Nat.le_mul_of_pos_right _ (by positivity)
      have h2 := Nat.clog_mono_right 2 h1
      rwa [Nat.clog_pow 2 _ (by norm_num)] at h2
    · obtain ⟨a, -, b, -⟩ := (hostOdd h c.O ψ (h.mem_X.1 hψ).1).1 h3.2.2.1
      exact ⟨_, _, _, hO, b ▸ Nat.zero_le _, a.trans (Nat.ordCompl_dvd _ _), Or.inr ⟨rfl, by rw [hχ]⟩⟩
  obtain ⟨⟨k1, k2, k3⟩, o1, o2, o3⟩ := levOf Ω h t ht l c e hl2 he0 het ψ hψ D hD n' p₁ m₀ hO hn' hm₀
  have hp₁ : 0 < p₁ := by
    obtain ⟨a, -⟩ := hO.xi
    exact NeZero.pos _
  have hNp := h.N_pos
  have hlpos := hlp.pos
  obtain ⟨q1, q2, q3, -⟩ := pZeroLe (l * h.N * p₁) (by positivity)
  have q4 : ¬ pZero (l * h.N * p₁) ∣ 2 := fun hd => by have := Nat.le_of_dvd two_pos hd; omega
  have q5 : ¬ pZero (l * h.N * p₁) ∣ l * 2 ^ n' * h.N * p₁ := fun hd => by
    rw [show l * 2 ^ n' * h.N * p₁ = 2 ^ n' * (l * h.N * p₁) by ring] at hd
    exact ((Nat.Prime.dvd_mul q1).1 hd).elim (fun a => q4 (q1.dvd_of_dvd_pow a)) q3
  have q6 : pZero (l * h.N * p₁) ∉ D.S := fun hd => by
    rw [hO.S_eq] at hd
    have hd := Nat.dvd_of_mem_primeFactors hd
    rw [show 2 * l * h.N * p₁ = 2 * (l * h.N * p₁) by ring] at hd
    exact ((Nat.Prime.dvd_mul q1).1 hd).elim q4 q3
  have hlev : 1 ≤ l * 2 ^ n' * h.N * p₁ := Nat.pos_of_ne_zero (by positivity)
  have hk : 0 < (l - 1) * 2 ^ n' * (2 * h.o) := by
    have : 0 < l - 1 := Nat.sub_pos_of_lt hlp.one_lt
    positivity
  obtain ⟨σ, hσ, hle⟩ := hc D hD _ hlev k1 k2 k3 _ hk o1 o2 o3 _ q1 q2 q5 q6 ι hAU
  have hI : D.Ineq σ := galoisRep_ineq_of_allIrreducible_nonvanishing D hD M hM hM' hP.loc (hSo Ω l).1 (hSo Ω l).2 hF hNE
    (fun r hr hi => hAd Ω l c D hctx _ hlev k1 k2 k3 ι r hr hi (hAU r hr hi)) σ hσ
  have he2 : 2 ≤ e := hO.e_eq ▸ hD.two_le
  have hb := hC' h hχ l c e hl2 he2 ψ hψ n' p₁ har
  have hle' := hle hI
  rw [hO.e_eq] at hle'
  refine ⟨ne_top_of_le_ne_top hI.1 hsha, le_trans ?_ (hle'.trans hb)⟩
  exact mul_le_mul_of_nonneg_right (Chr.nrm_mono l hsha hI.1) (Real.log_natCast_nonneg l)
theorem UpperTheory.V.Th.sp4Main_alt :
    _root_.UpperTheory.V.Aut.SymplecticFourImageDense → CohomologyHyp → LemmaM → LemmaM' → LemmaP → _root_.UpperTheory.V.Af.NumberSp4Alt → _root_.UpperTheory.V.Th.RigiditySymplecticFour → X.CorX → (∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], SoV Ω l ∧ SoFin Ω l) → CountII ∧ CountIII := by
  intro hA hP hM hM' hLP hN hAd hX hSo
  have key : CountShape fun h l _ _ e ψ => h.CaseII l e ψ ∨ h.CaseIII l e ψ := by
    intro χ
    obtain ⟨C, hC⟩ := main_big hA hP hM hM' hLP hN hAd hX hSo χ
    refine ⟨C, fun h hχ t ht Ω _ _ _ l _ c e hl2 he0 het ψ hψ hcase => ?_⟩
    obtain ⟨c₁, h₁⟩ := exists_coef l (2 ^ (h.nII l ψ + h.nIII l ψ))
    obtain ⟨c', hc, hc₁⟩ := (coefSup l).1 c c₁
    have h₂ := enough_of_le hc₁ (2 ^ (h.nII l ψ + h.nIII l ψ))
    let f : c.O →+* c'.O := (Subalgebra.inclusion hc).toRingHom
    have hf : Function.Injective f := Subalgebra.inclusion_injective hc
    have e2 : h.nII l (chHom f ψ) = h.nII l ψ := by
      unfold Host.nII
      rw [conductor_at_map_injective_coeff f hf, parity_at_map_injective_coeff f hf]
    have e3 : h.nIII l (chHom f ψ) = h.nIII l ψ := by
      unfold Host.nIII
      rw [conductor_at_map_injective_coeff f hf]
    have hψ' : chHom f ψ ∈ h.X c' e := by
      rw [h.mem_X] at hψ ⊢
      refine ⟨?_, (chHom_even f hf e ψ).2 hψ.2⟩
      unfold Host.IsChar
      rw [chHom_ker f hf]
      exact hψ.1
    have hcase' : h.CaseII l e (chHom f ψ) ∨ h.CaseIII l e (chHom f ψ) := by
      rcases hcase with ⟨a, b, d⟩ | ⟨a, b, d, g⟩
      · refine Or.inl ⟨a, ?_, d⟩
        unfold EV
        rw [← chHom_chiP f hf, chHom_ord f hf]
        exact b
      · exact Or.inr ⟨a, b, (chHom_ord f hf ψ).symm ▸ d, fun h0 => g ((map_eq_one_iff _ (chHom_inj f hf)).1 h0)⟩
    have hV := hC h hχ t ht Ω l c' e hl2 he0 het _ hψ' hcase'
      (e2.symm ▸ HasEnoughRootsOfUnity.of_dvd c'.O (pow_dvd_pow 2 (Nat.le_add_right _ (h.nIII l ψ))))
      (e3.symm ▸ HasEnoughRootsOfUnity.of_dvd c'.O (pow_dvd_pow 2 (Nat.le_add_left _ (h.nII l ψ))))
    obtain ⟨a, b⟩ := coefIndep Ω l c c' h.N e ψ (chHom f ψ) fun _ => rfl
    exact ⟨fun h0 => hV.1 (a.1 h0), b ▸ hV.2⟩
  refine ⟨fun χ => ?_, fun χ => ?_⟩
  · obtain ⟨C, hC⟩ := key χ
    exact ⟨C, fun h hχ t ht Ω _ _ _ l _ c e a b d ψ hψ hc => hC h hχ t ht Ω l c e a b d ψ hψ (Or.inl hc)⟩
  · obtain ⟨C, hC⟩ := key χ
    exact ⟨C, fun h hχ t ht Ω _ _ _ l _ c e a b d ψ hψ hc => hC h hχ t ht Ω l c e a b d ψ hψ (Or.inr hc)⟩
end
end

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br
namespace UpperTheory.GalN.V.Win.N
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V.CongNum
section
private theorem normV_rat {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  have h : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hN : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
    simp
  have hd : Ideal.absNorm w.asIdeal ∣ p :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [h]
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact w.isPrime.ne_top
private theorem est {p e : ℕ} (hp : 5 ≤ p) (he : 2 ≤ e) {t z₁ z₂ z₃ : ℂ} (h1 : ‖z₁‖ = 1) (h2 : ‖z₂‖ = 1) (h3 : ‖z₃‖ = 1)
    (ht : ‖t‖ ≤ 3 * (Real.sqrt p * (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2)) + (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2)) :
    t - eis4 p e z₁ z₂ z₃ ≠ 0 ∧ ‖t - eis4 p e z₁ z₂ z₃‖ ≤ (p : ℝ) ^ (2 * (e + 1)) := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  set x : ℝ := (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2) with hx
  set y : ℝ := (p : ℝ) ^ e with hy
  have hx0 : 0 ≤ x := by positivity
  have hxx : x * x = p * y := by
    rw [hx, ← Real.rpow_add (by linarith), hy, ← pow_succ', ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have hy2 : (p : ℝ) ^ 2 ≤ y := pow_le_pow_right₀ (by linarith) he
  have hy0 : 0 ≤ y := by positivity
  have hxy : 2 * x ≤ y := by
    refine abs_le_of_sq_le_sq' ?_ hy0 |>.2
    nlinarith [mul_le_mul_of_nonneg_right hy2 hy0, mul_nonneg (show (0:ℝ) ≤ p - 4 by linarith) (mul_nonneg (show (0:ℝ) ≤ p by linarith) hy0)]
  have hsx : Real.sqrt p * x ≤ y := by
    refine abs_le_of_sq_le_sq' ?_ hy0 |>.2
    rw [mul_pow, Real.sq_sqrt (by linarith), pow_two x, hxx]
    nlinarith [mul_le_mul_of_nonneg_right hy2 hy0]
  replace ht : ‖t‖ ≤ 7 / 2 * y := by linarith
  have n1 : ‖(p : ℂ) ^ (e + 1) * z₁‖ = p * y := by simp [h1, hy, pow_succ']
  have n2 : ‖(p : ℂ) ^ e * z₂‖ = y := by simp [h2, hy]
  have n3 : ‖(p : ℂ) * z₃‖ = p := by simp [h3]
  have hr : ‖t - ((p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1)‖ ≤ 7 / 2 * y + (y + p + 1) := by
    refine (norm_sub_le _ _).trans (add_le_add ht ?_)
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, ← n2, ← n3]
    have := norm_add_le ((p : ℂ) ^ e * z₂) ((p : ℂ) * z₃)
    simpa using this
  have hE : t - eis4 p e z₁ z₂ z₃ = (t - ((p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1)) - (p : ℂ) ^ (e + 1) * z₁ := by
    rw [eis4]; ring
  have hlt : 7 / 2 * y + (y + p + 1) < p * y := by nlinarith
  constructor
  · intro h0
    rw [hE, sub_eq_zero] at h0
    rw [h0, n1] at hr
    linarith
  · rw [hE]
    refine (norm_sub_le _ _).trans ?_
    rw [n1, mul_comm 2, pow_mul, pow_succ' (p : ℝ) e, ← hy]
    have : (2 : ℝ) ≤ p * y := by nlinarith
    nlinarith
private theorem size {c A M e N d p : ℕ} (hN : N ≤ c * (M * (e + 1 + 1)) ^ A) (hM : 1 ≤ M) (hp : 5 ≤ p) :
    ((N * d : ℕ) : ℝ) * Real.log ((p : ℝ) ^ (2 * (e + 1))) ≤
      ((c * 2 ^ A * 2 : ℕ) : ℝ) * d * ((M : ℝ) * (e + 1)) ^ (A + 1) * Real.log p := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h1 : N * d * (2 * (e + 1)) ≤ c * 2 ^ A * 2 * d * (M * (e + 1)) ^ (A + 1) := by
    have a1 : (M * (e + 1 + 1)) ^ A ≤ 2 ^ A * (M * (e + 1)) ^ A := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by nlinarith) _
    have a2 : e + 1 ≤ M * (e + 1) := Nat.le_mul_of_pos_left _ hM
    calc N * d * (2 * (e + 1)) ≤ c * (2 ^ A * (M * (e + 1)) ^ A) * d * (2 * (M * (e + 1))) := by
          gcongr
          exact hN.trans (by gcongr)
      _ = _ := by ring
  rw [Real.log_pow, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hl
  exact_mod_cast h1
end
open UpperTheory.V.Af in
theorem number_sp4_of_admissible_to_admissible_n :
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.GalN.V.LevelPNAlt → _root_.UpperTheory.GalN.V.AdmResNAlt →
    (∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin 4 → ℤ) (wt : ℤ)
      (r : G ℚ Ω →* GL (Fin 4) (Qbar l)), _root_.UpperTheory.V.Af.AdmRAlt ι M m wt r → _root_.UpperTheory.GalN.V.AdmRNAlt ι M m wt r) →
    _root_.UpperTheory.V.Af.NumberSp4Alt := by
  intro hP hLP hA hR
  obtain ⟨c, A, hc⟩ := _root_.UpperTheory.GalN.V.Win.N.countQ_alt hP hLP hA 4 (by norm_num)
  refine ⟨c * 2 ^ A * 2, A + 1, fun e he M hM p w hp hw h5 hpM k hk z₁ z₂ z₃ h1 h2 h3 => ?_⟩
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨D, hD, hcl⟩ := hc ![(e : ℤ) + 1, e, 1, 0] (e + 1)
    (by
      rw [Fin.strictAnti_iff_succ_lt]
      intro i; fin_cases i <;> simp <;> omega)
    (by intro i; fin_cases i <;> simp [Fin.rev] <;> omega) (e + 1)
    (by intro i; fin_cases i <;> simp [abs_le] <;> omega) M hM p w hp hw hpM
  haveI := D.fin
  letI := Fintype.ofFinite D.S
  let f : D.S × (ZMod k)ˣ → ℂ := fun x =>
    (D.β x.1).sum - eis4 p e (z₁ ^ (x.2 : ZMod k).val) (z₂ ^ (x.2 : ZMod k).val) (z₃ ^ (x.2 : ZMod k).val)
  have hzi : ∀ z : ℂ, z ^ k = 1 → IsIntegral ℤ z := fun z hz => IsIntegral.of_pow hk (hz ▸ isIntegral_one)
  have hzn : ∀ z : ℂ, z ^ k = 1 → ∀ a : ℕ, ‖z ^ a‖ = 1 := fun z hz a => by
    rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one hz hk.ne', one_pow]
  have hi : ∀ x, IsIntegral ℤ (f x) := fun x => by
    have hpi : IsIntegral ℤ (p : ℂ) := isIntegral_natCast p
    refine IsIntegral.sub (IsIntegral.multiset_sum fun b hb => ?_) ?_
    · simpa using D.int 0 (by intro i; fin_cases i <;> simp <;> omega) x.1 b hb
    · exact ((((hpi.pow _).mul ((hzi _ h1).pow _)).add ((hpi.pow _).mul ((hzi _ h2).pow _))).add
        (hpi.mul ((hzi _ h3).pow _))).add isIntegral_one
  have hconj : ∀ σ : ℂ ≃+* ℂ, ∃ u : D.S × (ZMod k)ˣ ≃ D.S × (ZMod k)ˣ, ∀ x, f (u x) = σ (f x) := fun σ => by
    obtain ⟨u, hu⟩ := D.conj σ
    obtain ⟨b, hb⟩ := exists_unit_pow k σ
    refine ⟨u.prodCongr (Equiv.mulLeft b), fun x => ?_⟩
    simp only [f, eis4, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, hu, Equiv.coe_mulLeft, Units.val_mul, map_sub,
      map_add, map_mul, map_pow, map_one, map_natCast, map_multiset_sum, hb _ h1, hb _ h2, hb _ h3,
      pow_val_mul h1, pow_val_mul h2, pow_val_mul h3]
  have hest : ∀ x, f x ≠ 0 ∧ ‖f x‖ ≤ (p : ℝ) ^ (2 * (e + 1)) := fun x => by
    refine est h5 he (hzn _ h1 _) (hzn _ h2 _) (hzn _ h3 _) ?_
    simpa only [Nat.cast_ofNat] using WinC.sum_le (D.pure x.1) (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _) (n := 3) (D.card _)
  obtain ⟨NN, hNN⟩ := exists_int_prod f hi hconj
  obtain ⟨h0, hlog⟩ := log_abs_le f NN hNN (fun x => (hest x).1) _ fun x => (hest x).2
  refine ⟨NN, h0, hlog.trans ?_, fun l _ hl2 hlp Ω _ _ _ ι B hB σ hσ X hX hX' => ?_⟩
  · rw [Fintype.card_prod, ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
    exact size hD hM h5
  replace hX := fun r hr => hR Ω l ι _ _ _ r (hX r hr)
  obtain ⟨cl, hinj, hfr⟩ := hcl l hl2 hlp Ω ι
  have hone : ∀ z : ℂ, z ^ k = 1 → z ^ (((1 : (ZMod k)ˣ) : ZMod k)).val = z := fun z hz => by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hz, pow_one]
  have key : ∀ (r) (hr : r ∈ X), (r σ : Matrix (Fin 4) (Fin 4) (Qbar l)).trace - ι.symm (eis4 p e z₁ z₂ z₃) =
      ι.symm (f (cl ⟨r, hX r hr⟩, 1)) := fun r hr => by
    have h := (hfr ⟨r, hX r hr⟩ B hB).2 σ (by rwa [normV_rat hp w hw])
    rw [map_inv] at h
    rw [trace_eq_sum_of_inv ι _ _ h]
    simp only [f, hone _ h1, hone _ h2, hone _ h3, map_sub]
  refine ⟨fun r hr h => ?_, ?_⟩
  · have := key r hr
    rw [h, sub_self, eq_comm, map_eq_zero_iff _ ι.symm.injective] at this
    exact (hest _).1 this
  · have := norm_le_prod ι f hi NN hNN (fun r : X => (cl ⟨r.1, hX r.1 r.2⟩, (1 : (ZMod k)ˣ))) fun r r' h =>
      Subtype.ext (hX' _ r.2 _ r'.2 (hinj _ _ (congrArg Prod.fst h)))
    refine this.trans_eq ?_
    rw [← Finset.prod_coe_sort X]
    exact Finset.prod_congr rfl fun r _ => by rw [key r.1 r.2]
end
end UpperTheory.GalN.V.Win.N
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Af
namespace UpperTheory.GalN.V
theorem numberSp4_n_alt : _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.V.Af.NumberSp4Alt := fun P =>
  _root_.UpperTheory.GalN.V.Win.N.number_sp4_of_admissible_to_admissible_n P (_root_.UpperTheory.V.Keep.levelPA_alt P) (_root_.UpperTheory.V.Z.Win.A4.admissible_restriction_level_n_of_printed_results P) fun _ _ _ _ _ _ _ _ _ _ _ h =>
    ⟨h.irr, _root_.UpperTheory.GalN.V.autQN'_alt P (by norm_num) h.dual h.aut, h.level, h.dual, h.safe⟩
end UpperTheory.GalN.V
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk
private theorem pre_ex {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
    (T : Tower D) (hO : T.Ok) (hG : D.Good) (hC : Ctx2 D ∨ Ctx3 D) : Nonempty (Pre T) := by
  obtain ⟨η, N, m, hN, hK, hm, hη, hcc, hun, hv⟩ := etaEx hC
  obtain ⟨κ₀, m', h1, h2, h3, h4, h5⟩ := Tw.kap0 Ω l hG.l_odd T.K T.degK (hO.split 2 hG.two_mem) η N m hN hK hm hη hcc
    (fun A => by
      by_cases hA : Raw.Away D.S A
      · exact Or.inl (hun A hA)
      · simp only [Raw.Away, not_forall, not_not] at hA
        obtain ⟨p, hp, hA⟩ := hA
        exact Or.inr (hO.split p hp A hA))
  obtain ⟨γ, g1, g2, g3, g4⟩ := halfEx hG
  have hl := hG.pl_over l Fact.out
  obtain ⟨t, β, c₁, b1, b2, b3, b4, b5, b6, b7, U, hU, b8⟩ :=
    Tw.bt0 Ω l hG.l_odd T.K T.degK (D.pl l) hl (hO.split l hG.l_mem _ hl)
  exact ⟨{ κ₀ := κ₀, γ := γ, β := β, t := t, κ₀_open := h1, κ₀_ord := ⟨m', h2, h3⟩,
           κ₀_conj := fun σ hσ s s' e hs => by rw [h4 σ hσ s s' e]; exact hv _ hs
           κ₀_unr := fun A hA => h5 A (hun A hA), γ_cont := g1, γ_red := g2, γ_sq := g3, γ_ker := g4,
           β_cont := b3, t_cont := b1, β_t := b2, β_red := fun s => (b4 s).2,
           conj := fun σ hσ s s' e => ⟨b6 σ hσ s s' e, b5 σ hσ s s' e⟩, t_unr := b7,
           cyc := betaCyc Ω l T.K T.degK (D.pl l) hl β b6 U hU b8 }⟩
theorem UpperTheory.V.Ws.nonempty_link_of_fit_deep_unramified :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∃ c₁ : Coef l, ∀ (c' : Coef l) (h : c.O ≤ c'.O), c₁.O ≤ c'.O → Nonempty (Link T c' h) := by
  intro hU Ω _ _ _ l _ c D T hF hD
  have hC : Ctx2 D ∨ Ctx3 D := hF.2.imp And.left And.left
  have hG : D.Good := hC.elim And.left And.left
  have hO := hF.1
  obtain ⟨P⟩ := pre_ex T hO hG hC
  obtain ⟨k1, k2, k3⟩ := kapCont P
  obtain ⟨u1, u2, u3⟩ := kapUnr P hG
  let Q : QCh T :=
    { κ := P.κ, β := P.βL, t := P.tL, κ_cont := k1, β_cont := k2, t_cont := k3, β_t := fun _ hg => P.β_t hg,
      β_red := fun _ => P.β_red _, conj := kapConj P hD, t_unr := u1, unr := u2, tame := u3, mu := kapMu P hG,
      cyc := kapCyc P hG }
  obtain ⟨c₁, -, hL, hκ, hβ, -⟩ := Pr.coefEx l c T.L Ω Q.κ Q.β Q.κ_cont Q.β_cont
  refine ⟨c₁, fun c' h h₁ => ?_⟩
  obtain ⟨κ, a1, a2, -⟩ := liftO c' Q.κ Q.κ_cont fun g => h₁ (hκ g)
  obtain ⟨β, b1, b2, b3⟩ := liftO c' Q.β Q.β_cont fun g => h₁ (hβ g)
  obtain ⟨X⟩ := ochOf Q c' h κ β a1 b1 a2 b2 fun g => b3 g (Q.β_red g)
  obtain ⟨Y⟩ := setEx T hG hO
  obtain ⟨V, hV⟩ := hU.lev l T.L Ω Y.s Y.s.S Y.fin subset_rfl Y.s.split
  obtain ⟨r, r1, r2, r3⟩ := residEx X Y V hG hO hV
  obtain ⟨σ, hσ, hc⟩ := Y.cc
  obtain ⟨g₀, -, hg₀⟩ := Y.om0
  exact ⟨{ s := Y.s, V := V, hV := hV, noMu := noMu hG T.L g₀ hg₀, large := fun τ x => h₁ (hL τ x), e := Y.e, hA := Y.hA,
           κ := X.κ, β := X.β, t := X.t, κ_cont := X.κ_cont, β_cont := X.β_cont, t_cont := X.t_cont, β_t := X.β_t,
           β_red := X.β_red, conj := fun g g' e => X.conj σ hσ g g' (hc g g' e), t_unr := X.t_unr,
           unr := fun A v hA hv g hg =>
             ⟨X.unr A (Y.away A v hA hv) hg, (((barFacts hG).2.2 A (Y.away A v hA hv) _ ⟨hg.1, hg.2⟩)).2⟩
           tame := X.tame
           mu := fun v g hg => by
             obtain ⟨a, ha⟩ := (prFacts l T.L Ω Y.s V).2.2.2 v g hg
             exact X.mu g a ha
           cyc := X.cyc, r := r, chib := fun i g => by rw [r1]; rfl
           psib := r2, th := r3, v0 := v0ok X Y V hG r r1 }⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
section Alg
open Matrix
end Alg
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
theorem automorphic_of_gsp4_rigid_solvable_galois (H : _root_.UpperTheory.V.Af.HypothesesH') (K L : IntermediateField ℚ Ω) [NumberField K] [NumberField L] [IsCMField K] [IsCMField L]
    (hle : K ≤ L) (hK : Module.finrank ℚ K = 2) (hgal : IsGalois ℚ L) (hsol : IsSolvable (L ≃ₐ[ℚ] L)) (ι : Qbar l ≃+* ℂ)
    (r : G ℚ Ω →* M4 (Qbar l)) (θ : G ℚ Ω →* (Qbar l)ˣ) (hr : Continuous r.toHomUnits) (hθ : Af.IsAlgChar ι θ)
    (hm : ∀ g, IsGSp (θ g : Qbar l) (r g)) (cc : G ℚ Ω) (hc : Af.IsConjEl cc) (hirr : Af.IsIrr (r.toHomUnits.comp (resQ L)))
    (haut : Af.IsAut ι (r.toHomUnits.comp (resQ K))) : Af.IsAut ι (r.toHomUnits.comp (resQ L)) := by
  letI : Algebra K L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[ℚ] L) := hsol
  have s2 : IsSolvable (L ≃ₐ[K] L) :=
    Group.isSolvable_of_isSolvable_injective (f := (AlgEquiv.restrictScalarsHom ℚ : (L ≃ₐ[K] L) →* (L ≃ₐ[ℚ] L)))
      (AlgEquiv.restrictScalars_injective ℚ)
  obtain ⟨P, hP⟩ := auPair r θ hm cc
  have hp : Af.IsPairing cc (r.toHomUnits.comp (Af.resG ℚ K Ω)) (θ.comp (Af.resG ℚ K Ω)) P := fun s s' h => by
    have h' : Af.resG ℚ K Ω s' = cc * Af.resG ℚ K Ω s * cc⁻¹ := h
    have h1 := hP (Af.resG ℚ K Ω s)
    rw [← h'] at h1
    exact h1
  exact (Z.Bc.solQ (_root_.UpperTheory.V.Z.Bc.solC_alt H H.cyc) ℚ K L Ω s2 ⟨inferInstance, Or.inr ⟨hK, inferInstance⟩⟩
    inferInstance inferInstance l ι 4 (by norm_num) (r.toHomUnits.comp (Af.resG ℚ K Ω)) θ
    (hr.comp (Af.continuous_restrictScalarsHom ℚ K Ω)) hirr hθ (auSign _) ⟨cc, _, hc, hp⟩).1 haut
end Gal
section Core
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
end Core
section Rg
open scoped Matrix TensorProduct
section BK
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
end BK
end Rg
end
end

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private half_pow from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.HalfPow
open UpperTheory.GalN.V UpperTheory.V.Ws.Pt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp
theorem UpperTheory.GalN.V.point_automorphy_w_of_gsp_cusp_sub_rank_four :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (ι : PadicAlgCl l ≃+* ℂ) (r : G T.F Ω →* M4 (PadicAlgCl l)), (∀ g, IsGSp (algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.F g)))) (r g)) → ∀ (κ : G T.L Ω →* (PadicAlgCl l)ˣ) (π : CuspSub T.L 4) (a : ℤ) (k : ℕ), Continuous κ → 0 < k → Even (a + n) → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := T.L) A, (κ s ^ 2 * cycBar T.L Ω l s ^ (-a)) ^ k = 1) → (CG.mk π).IsRegAlg → Af.AttC ι (Af.tw (r.comp (resLe T.F_le)).toHomUnits κ) π → _root_.UpperTheory.V.Z.Win.WitA ι (Af.tw (r.comp (resLe T.F_le)).toHomUnits κ) → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (K.rhoQ n r) := by
  intro hP Ω _ _ _ l _ c D T c' h K n ι r hr κ π a k hκ hk ha hw hreg hatt hW
  have h1 := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP T.L Ω l ι 4 _).2.1.2 ⟨π, hreg, hatt⟩
  have h2 : Af.IsAlgChar ι (K.twc n * κ⁻¹) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hP T.L Ω l ι).1 _ ((twc_cont K n).mul hκ.inv) fun w hlw => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    have hl : A.valuation (l : Ω) < 1 := by
      have h1 := (hA ((l : ℕ) : 𝓞 T.L)).2 hlw
      have e : algebraMap T.L Ω (((l : ℕ) : 𝓞 T.L) : T.L) = (l : Ω) := by simp
      rwa [e] at h1
    obtain ⟨e, k', hk', he, H⟩ := twWts K n A hl
    obtain ⟨m, hm⟩ : Even (e - a) := by
      have := he.sub ha
      rwa [add_sub_add_right_eq_sub] at this
    exact ⟨A, hA, m, 2 * (k * k'), by positivity, fun s hs => half_pow hm (H s hs) (hw A hl s hs)⟩
  have h3 := _root_.UpperTheory.V.Af.twist_invariance_automorphic hP T.L Ω l ι 4 _ _ h1 h2
  have h4 : Af.tw (Af.tw (r.comp (resLe T.F_le)).toHomUnits κ) (K.twc n * κ⁻¹) = K.rhoQ n r := by
    ext g : 2
    rw [Af.tw_val, Af.tw_val, smul_smul, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
      Units.inv_mul_cancel_right, K.rho_val]
    rfl
  rw [h4] at h3
  obtain ⟨P, hPair⟩ := ptPair K n r hr
  exact _root_.UpperTheory.GalN.V.mkCsd'_alt (_root_.UpperTheory.GalN.V.csdOf0_alt hP (W.Lp T.L) T.L Ω inferInstance l ι 4 (by norm_num) _ K.s.c P K.s.hc h3 hPair) fun _ =>
    h4 ▸ _root_.UpperTheory.V.Z.Win.WitA.witness_twist_algebraic_character hP.toClassicalTheorems h2 ((twc_cont K n).mul hκ.inv) ⟨π, hreg, hatt⟩ hW
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private factor_abs irr_conj free_up par' from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.ExistsPlaceAbovePrime
open UpperTheory.GalN.V
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
section Alg
open Matrix
end Alg
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
end Gal
section Core
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
theorem adjoint_vanishing_gsp4_rigid_point (hU : _root_.UpperTheory.V.Ws.UnramifiedInputs) (hAd : _root_.UpperTheory.V.Th.AdjointLiftingTheorem) {D : Raw Ω c} (hG : D.Good) {T : Tower D} (hF : T.Fit) (hD : T.Deep) {c' : Coef l}
    {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l) (ι : PadicAlgCl l ≃+* ℂ)
    (r r₁ : G ℚ Ω →* M4 (PadicAlgCl l)) (hconj : IsConj4 r r₁)
    (hres : r₁.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r)
    (hw : T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l))) (hc : Continuous r) (hm : D.Mult r)
    (hi : Irr (r.comp T.L.fixingSubgroup.subtype)) (haut : Af.IsAut ι (r.toHomUnits.comp (resQ T.L)))
    (hWit : _root_.UpperTheory.V.Z.Win.WitA ι (r.toHomUnits.comp (resQ T.L))) (hf : FreeAt l (r.toHomUnits.comp (resQ T.K))) :
    ∃ ρ : K.V.frame.G₀ →* GL (Fin 4) (Qbar l), ρ.comp K.V.pr = K.rhoQ 0 (r.comp (resQ T.F)) ∧ AdZero K.V ρ := by
  obtain ⟨⟨B, -⟩, hB⟩ := _root_.UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link hU D T hF hD c' h K X 0
  obtain ⟨φ, hφ⟩ := hB B
  obtain ⟨u, hu⟩ := hconj
  have hcj : ∀ g, K.rhoQ 0 (X.P.map (y : X.A →+* PadicAlgCl l)).r g = u * K.rhoQ 0 (r.comp (resQ T.F)) g * u⁻¹ := fun g => by
    apply Units.ext
    rw [← hres, Units.val_mul, Units.val_mul, K.rho_val, K.rho_val, MonoidHom.comp_apply, MonoidHom.comp_apply, hu,
      Matrix.mul_smul, Matrix.smul_mul]
  have hrep₁ : (Link.pt φ y).IsRep (K.rhoQ 0 _) := auRep D T c' h K X B 0 φ hφ y _ fun _ => rfl
  have hrep : (Link.pt φ y).IsRep (K.rhoQ 0 (r.comp (resQ T.F))) := by
    refine Eq.trans hrep₁ ((AlgebraTools.Det.repApi _).2.2.2.2.2.2.2 _ u fun g => ?_).symm
    exact congrArg Units.val (eq_mul_inv_iff_mul_eq.1 (hcj g)).symm
  have hcρ := Pt.rho_cont K 0 (r := r.comp (resQ T.F)) (hc.comp (Af.continuous_restrictScalarsHom ℚ T.F Ω))
  have hirr : Af.IsIrr (K.rhoQ 0 (r.comp (resQ T.F))) :=
    (auIrr _ (r.comp (resQ T.L)) hi fun g => ⟨IntermediateField.fixingSubgroupEquiv T.L g, rfl⟩).2 (K.twc 0)
  have hfull : Eb.Full (K.rhoQ 0 (r.comp (resQ T.F))) :=
    (AlgebraTools.Det.irrIffSpan (W.mat _)).1 fun N hN => hirr.2.2 N le_top fun g v hv => hN g v hv
  obtain ⟨hs, hq, -⟩ := phiKer K.V
  obtain ⟨ρ, hρ, hfull', -⟩ := factor_abs (Link.pt φ y).D K.V.pr hs _ (by norm_num) hfull hrep
  refine ⟨ρ, hρ, ?_⟩
  have hanti : StrictAnti fun i => (D.wts4 i : ℤ) := by
    have := hG.two_le
    refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
    fin_cases i <;> simp [Raw.wts4] <;> omega
  obtain ⟨m, hmm, k, hk, hmk⟩ := Pt.ptWts K X B 0 φ hφ y _ (fun i => by simp) hw
  obtain ⟨π, hreg, hatt⟩ := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hU.pr T.L Ω l ι 4 _).2.1.1 haut
  have haut' : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (K.rhoQ 0 (r.comp (resQ T.F))) := by
    have e : Af.tw ((r.comp (resQ T.F)).comp (resLe T.F_le)).toHomUnits 1 = r.toHomUnits.comp (resQ T.L) := by
      ext g : 2
      rw [Af.tw_val, MonoidHom.one_apply, Units.val_one, one_smul]
      rfl
    refine _root_.UpperTheory.GalN.V.point_automorphy_w_of_gsp_cusp_sub_rank_four hU.pr K 0 ι _ (fun g => hm _) 1 π 0 1 continuous_const one_pos (by simp) (fun A _ s _ => by simp) hreg ?_ ?_ <;>
      rwa [e]
  have hunr := Pt.ptUnr K 0 (X.P.map (y : X.A →+* PadicAlgCl l)).r fun g hg => by
    change (y : X.A →+* PadicAlgCl l).mapMatrix (X.P.r g) = 1
    rw [X.pair.kill g hg, map_one]
  have hfl : ∀ v : W.Vl l T.L, W.HasFlag ((K.rhoQ 0 (r.comp (resQ T.F))).comp (Dec (F := T.L) (K.s.A v)).subtype)
      ((Link.pt φ y).psi v) := fun v => by
    obtain ⟨a, ha⟩ := Pt.ptFlag K X B 0 φ hφ y v
    refine ⟨a * u, fun s => ?_⟩
    have h1 := ha s
    rw [MonoidHom.comp_apply, hcj] at h1
    simpa only [mul_inv_rev, mul_assoc, MonoidHom.comp_apply] using h1
  have hapt : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι (Link.pt φ y) ρ := by
    refine ⟨hq.continuous_iff.2 ?_, hρ ▸ hrep, ?_, hρ ▸ haut', ?_, fun v => ?_⟩
    · have e : (ρ : _ → _) ∘ K.V.pr = K.rhoQ 0 (r.comp (resQ T.F)) := congrArg DFunLike.coe hρ
      exact e ▸ hcρ
    · exact auArith hU.pr.toClassicalTheorems.litN.aut.art D T c' h K X B φ hφ y _ (fun _ => rfl) (Pt.psi_cont _) _ hanti hw
    · rintro _ ⟨g, hg, rfl⟩
      have h1 := hunr g hg
      rw [hcj, mul_inv_eq_one, mul_eq_left] at h1
      exact (DFunLike.congr_fun hρ g).trans h1
    · have h1 := hfl v
      rw [← hρ] at h1
      exact h1
  have hirr₀ : U3.MatIrr ⊤ (W.mat ρ) := fun N hN => (AlgebraTools.Det.irrIffSpan (W.mat ρ)).2 hfull' N fun g v hv => hN g trivial v hv
  have hfree : Free K.V.frame fun v => (Link.pt φ y).psi v := fun v : W.Vl l T.L => by
    obtain ⟨g, hg, hfr⟩ := free_up T.K T.L r.toHomUnits hf (K.twc 0) (K.s.A v) (by simpa using (K.s.hA v _).2 v.2) _ (hfl v)
    refine ⟨g, ?_, hfr⟩
    have e : K.V.ε (toGS Ω K.V.S' (W.resP T.L Ω g)) = cycZ (W.Lp T.L) Ω l (W.resP T.L Ω g) := DFunLike.congr_fun K.V.hε _
    exact e.trans hg
  exact hAd l T.L Ω K.s K.V K.hV K.noMu c' K.large 4 (by omega) le_rfl K.r K.v0 B ι _ ρ
    (_root_.UpperTheory.V.Th.nice0four_alt ι _ ρ hapt hirr₀ hfree (P1.condC D T hF hD c' h K) (P1.condD D T hF hD c' h K))
    (par' _ m (fun v i j hij => by have h1 := hmm v i j; have h2 := hanti hij; simp only at h1 h2; omega) k hk hmk)
end Core
section Rg
open scoped Matrix TensorProduct
section BK
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
end BK
end Rg
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private factor_abs irr_conj free_up par' from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.ExistsPlaceAbovePrime
open UpperTheory.GalN.V
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
open UpperTheory.V.Z.Win in
theorem UpperTheory.V.Z.Win.Dn.exists_cm_field_twist_h1 (hU : _root_.UpperTheory.V.Ws.UnramifiedInputs) (hAd : _root_.UpperTheory.V.Th.AdjointLiftingTheorem) (D : Raw Ω c) (hD : Ctx2 D ∨ Ctx3 D) (N : ℕ) (hN : 1 ≤ N) (h1 : Af.KillsMu N D.ψ)
    (h2 : Af.KillsMu N D.ξ) (h3 : Af.KillsMu N D.om) (ι : PadicAlgCl l ≃+* ℂ) (r : G ℚ Ω →* M4 (PadicAlgCl l)) (hr : D.EPt r)
    (hirr : Irr r) (haut : _root_.UpperTheory.V.Aut.IsAut4Alt ι r) :
    ∃ (K : IntermediateField ℚ Ω) (_ : NumberField K) (_ : IsCMField K) (θ : G ℚ Ω →* (Qbar l)ˣ), Module.finrank ℚ K = 2 ∧
      (∀ g, IsGSp (θ g : PadicAlgCl l) (r g)) ∧
      ∀ R : Representation (Qbar l) (G ℚ Ω) (M4 (Qbar l)),
        Af.IsAdOf (r.toHomUnits.comp (resQ K)) (θ.comp (resQ K)) R → Af.BlochKatoSelmerVanishes l R := by
  have hG : D.Good := hD.elim (·.1) (·.1)
  obtain ⟨hlev, θ, hθ, hdual, hθv⟩ := level D hG N hN h1 h2 h3 r hr
  have hmul : D.Mult r := (ptIn D hG _ r hr).1
  have hm : ∀ g, IsGSp (θ g : PadicAlgCl l) (r g) := fun g => by
    rw [hθv]
    exact hmul g
  obtain ⟨T, hF, hDp, hT⟩ := spPt hU.coh Ω l c D hD r hr hirr
  obtain ⟨c₁, hc₁⟩ := _root_.UpperTheory.V.Ws.nonempty_link_of_fit_deep_unramified hU D T hF hDp
  obtain ⟨c', h, X, y, r₁, hle, hconj, -, hres, hw, hi₁⟩ := hT c₁
  obtain ⟨K⟩ := hc₁ c' h hle
  have hKL : T.K ≤ T.L := T.hL ▸ le_sup_right
  have hi : Irr (r.comp T.L.fixingSubgroup.subtype) := by
    obtain ⟨u, hu⟩ := hconj
    refine irr_conj ⟨u⁻¹, fun g => ?_⟩ hi₁
    simp only [MonoidHom.comp_apply, hu, inv_inv, ← mul_assoc, Units.inv_mul, one_mul, Units.inv_mul_cancel_right]
  have hiL : Af.IsIrr (r.toHomUnits.comp (resQ T.L)) :=
    (auIrr _ (r.comp (resQ T.L)) hi fun g => ⟨IntermediateField.fixingSubgroupEquiv T.L g, rfl⟩).1
  have hiK : Af.IsIrr (r.toHomUnits.comp (resQ T.K)) :=
    (auIrr _ (r.comp (resQ T.K)) hi fun g =>
      ⟨IntermediateField.fixingSubgroupEquiv T.K ⟨g, IntermediateField.fixingSubgroup_le hKL g.2⟩, rfl⟩).1
  have hanti : StrictAnti ![(D.e : ℤ) + 1, D.e, 1, 0] := by
    have := hG.two_le
    refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
    fin_cases i <;> simp <;> omega
  have hcK : Continuous (r.toHomUnits.comp (resQ T.K)) := hlev.cont.comp (Af.continuous_restrictScalarsHom ℚ T.K Ω)
  have hP := _root_.UpperTheory.GalN.V.autKQ0_alt hU.pr T.K Ω T.degK l ι 4 (by norm_num) r.toHomUnits _ hlev.cont (_root_.UpperTheory.GalN.V.isAutomorphicOverImagQuad_of_isAutQA haut) ⟨θ, hθ, hdual⟩ hiK
  have hf := _root_.UpperTheory.V.Z.Win.RR.freePUA_alt hU.pr T.K Ω T.degK l hG.l_odd ι 4 (by norm_num) _ N _ hN hanti hcK hP
    (_root_.UpperTheory.GalN.V.autQN'_alt hU.pr.toClassicalTheorems (by norm_num) ⟨θ, hθ, hdual⟩ haut hlev.cont T.K T.degK hiK).2
    ((unlRes T.K Ω l 4 N _ r.toHomUnits hN).1 (fun A hA g hg =>
      ⟨IntermediateField.fixingSubgroupEquiv T.K ⟨g, hF.1.split l hG.l_mem A hA hg⟩, rfl⟩) (spUnl D hG N hN h1 h2 h3 r hr))
  obtain ⟨π, hreg, -, hatt⟩ := hP
  obtain ⟨hgal, hsol⟩ := auGal D T
  have hL := _root_.automorphic_of_gsp4_rigid_solvable_galois hU.pr T.K T.L hKL T.degK hgal hsol ι r _ hlev.cont (_root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good hU.pr D hG ι) hmul D.cc hG.isCC hiL
    ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hU.pr T.K Ω l ι 4 _).2.1.2 ⟨π, hreg, hatt⟩)
  have hWit : _root_.UpperTheory.V.Z.Win.WitA ι (r.toHomUnits.comp (resQ T.L)) := by
    letI : Algebra T.K T.L := (IntermediateField.inclusion hKL).toAlgebra
    haveI : IsScalarTower T.K T.L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsGalois T.K T.L := IsGalois.tower_top_of_isGalois ℚ T.K T.L
    have hsol' : IsSolvable (T.L ≃ₐ[T.K] T.L) :=
      @solvable_of_solvable_injective _ _ _ _ (hf := (AlgEquiv.restrictScalarsHom_injective ℚ)) hsol
        (f := (AlgEquiv.restrictScalarsHom ℚ : (T.L ≃ₐ[T.K] T.L) →* (T.L ≃ₐ[ℚ] T.L)))
    obtain ⟨Q, hQ⟩ := auPair r (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th) hmul D.cc
    have hpol : Af.Sol.Pol ι (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) :=
      ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, _, D.cc, Q, _root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good hU.pr D hG ι, auSign _, hG.isCC, fun s s' h => by
          have h' : Af.resG ℚ T.K Ω s' = D.cc * Af.resG ℚ T.K Ω s * D.cc⁻¹ := h
          rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h']
          exact hQ _⟩
    exact _root_.UpperTheory.V.Z.Win.Dn.automorphy_up_base_change (r := r.toHomUnits.comp (resQ T.K)) T.L hU.pr hsol' (by norm_num) hcK hiL hpol ⟨π, hreg, hatt⟩
      (((flagLaws ℚ Ω l 4 r.toHomUnits).2.2.2 T.K).2.1 ((flagLaws ℚ Ω l 4 r.toHomUnits).2.2.1 N _ hN hlev).2)
      (_root_.UpperTheory.GalN.V.autQN'_alt hU.pr.toClassicalTheorems (by norm_num) ⟨θ, hθ, hdual⟩ haut hlev.cont T.K T.degK hiK).2
  obtain ⟨ρ, hρ, hz⟩ := _root_.adjoint_vanishing_gsp4_rigid_point hU hAd hG hF hDp K X y ι r r₁ hconj hres hw (Units.continuous_val.comp hlev.cont) hmul hi hL hWit hf
  refine ⟨T.K, inferInstance, inferInstance, θ, T.degK, hm, fun R hR => ?_⟩
  refine adDown Ω l T.K T.L T.degK (fun σ hσ x => hσ ⟨x.1, hKL x.2⟩) K.s K.V 4 _ _ R hcK hR ρ (K.twc 0)
    (fun g t e => ?_) (fun g g' t e e' => ?_) hz
  · refine (congrArg Units.val (DFunLike.congr_fun hρ g)).trans ((K.rho_val _ _ _).trans ?_)
    exact congrArg (fun σ => (K.twc 0 g : PadicAlgCl l) • r σ) e
  · have a1 := congrArg (algebraMap c'.O (PadicAlgCl l)) (K.conj g g' e).1
    rw [map_mul, map_mul, map_mul, map_pow, map_one] at a1
    have a2 : (θ.comp (resQ T.K) t : PadicAlgCl l) = algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.L g))) :=
      (congrArg (fun σ => (θ σ : PadicAlgCl l)) e'.symm).trans (hθv _)
    have a3 : (cycBar T.L Ω l g : PadicAlgCl l) = algebraMap c'.O (PadicAlgCl l) (chiO T.L Ω l c'.O g) := rfl
    have a4 : K.twc 0 g * K.twc 0 g' * θ.comp (resQ T.K) t * cycBar T.L Ω l g ^ 3 = 1 := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, K.twc_val, pow_zero, mul_one, Units.val_one]
      rw [a2, a3]
      exact a1
    rw [eq_inv_of_mul_eq_one_left a4, ← zpow_natCast, ← zpow_neg]
    rfl
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
section Alg
open Matrix
end Alg
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
end Gal
section Core
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
end Core
section Rg
open scoped Matrix TensorProduct
private theorem rg_twist {Γ k V : Type} [Group Γ] [CommRing k] [AddCommGroup V] [Module k V] (A : Representation k Γ V)
    (p : V →ₗ[k] V) (hp : ∀ x, p (p x) = p x) (hA : ∀ g x, p (A g x) = A g (p x)) (η : Γ →* kˣ) :
    ∃ ρ : Representation k Γ V, ∀ g x, ρ g x = A g (p x) + (η g : k) • A g (x - p x) := by
  refine ⟨{ toFun := fun g => A g ∘ₗ p + (η g : k) • (A g ∘ₗ (LinearMap.id - p))
            map_one' := ?_
            map_mul' := fun g h => ?_ }, fun g x => rfl⟩
  · ext x
    simp
  · ext x
    simp only [map_mul, Units.val_mul, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.id_apply, Module.End.mul_apply, map_add, map_smul, map_sub, hA, hp, sub_self, smul_zero, add_zero,
      mul_smul, smul_sub, smul_add, map_zero]
    module
private theorem rg_sign {K Ω : Type} [Field K] [NumberField K] [IsCMField K] (h : Module.finrank ℚ K = 2) [Field Ω]
    [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] (k : Type) [Field k] :
    ∃ η : G ℚ Ω →* kˣ, (∀ s : G K Ω, η (s.restrictScalars ℚ) = 1) ∧
      ∀ c : G ℚ Ω, (∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) → η c = -1 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : K, IsCMField.complexConj K x ≠ x := by
    by_contra hc
    push Not at hc
    exact IsCMField.complexConj_ne_one K (AlgEquiv.ext hc)
  set δ : K := x - IsCMField.complexConj K x with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 hx.symm
  have hδc : IsCMField.complexConj K δ = -δ := by simp [hδ]
  have hsq : δ * δ ∈ maximalRealSubfield K := (IsCMField.complexConj_eq_self_iff K _).1 (by rw [map_mul, hδc]; ring)
  obtain ⟨q, hq⟩ := Af.surjective_algebraMap_real K h ⟨_, hsq⟩
  have hq' : algebraMap ℚ K q = δ * δ := by
    have := congrArg (fun y : maximalRealSubfield K => (y : K)) hq
    simpa using this
  set d : Ω := algebraMap K Ω δ with hd
  have hd0 : d ≠ 0 := by simpa [hd] using hδ0
  have hdd : d * d = algebraMap ℚ Ω q := by rw [IsScalarTower.algebraMap_apply ℚ K Ω, hq', map_mul]
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hne : -d ≠ d := fun e => hd0 (by linear_combination (-1 / 2 : Ω) * e)
  have hpm : ∀ g : G ℚ Ω, g d = d ∨ g d = -d := fun g => by
    have : g d * g d = d * d := by rw [← map_mul, hdd, AlgEquiv.commutes]
    exact mul_self_eq_mul_self_iff.1 this
  refine ⟨{ toFun := fun g => if g d = d then 1 else -1
            map_one' := by simp
            map_mul' := fun g g' => ?_ }, fun s => ?_, fun c ⟨j, hj⟩ => ?_⟩
  · rcases hpm g with h1 | h1 <;> rcases hpm g' with h2 | h2 <;> simp [AlgEquiv.mul_apply, h1, h2, hne]
  · have : (s.restrictScalars ℚ) d = d := s.commutes δ
    simp [this]
  · have : c d = -d := by
      apply j.injective
      rw [hj, hd, ← map_neg (algebraMap K Ω), ← hδc]
      exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K Ω)) δ).symm
    simp [this, hne]
section BK
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
private theorem rg_bk {ρ ρ' : Representation C (G F Ω) V} (f : V →ₗ[C] V) (hf : ∀ g x, f (ρ g x) = ρ' g (f x))
    {z : G F Ω → V} (hz : ∀ g, f (z g) = z g) (h1 : z ∈ Z1 ρ) (h2 : Af.IsBK l ρ z) : z ∈ Z1 ρ' ∧ Af.IsBK l ρ' z := by
  have hc : ∀ g h, z (g * h) = z g + ρ' g (z h) := fun g h => by
    rw [← hz (g * h), h1.2, map_add, hf, hz, hz]
  refine ⟨⟨h1.1, hc⟩, fun w hw => ?_, fun τ => ?_⟩
  · obtain ⟨A, hA, x, hx⟩ := h2.away w hw
    exact ⟨A, hA, f x, fun s hs => by rw [← hz, hx s hs, map_sub, hf]⟩
  · obtain ⟨j, hj, ⟨hc1, -⟩, x, hx⟩ := h2.above τ
    refine ⟨j, hj, ⟨hc1, fun g h => hc g.1.1 h.1.1⟩,
      LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) x, fun g => ?_⟩
    have key : ∀ y : V ⊗[ℚ_[l]] Loc.Bcr l, LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l])
        (Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype) (ρ.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g y) =
        Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype) (ρ'.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g
          (LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Loc.actC, hf]
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
    simp [hz]
end BK
private def rgJ (k : Type) [CommRing k] : GL (Fin 4) k where
  val := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
  inv := !![0, 0, 0, -1; 0, 0, -1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
private theorem rgJ_adj {k : Type} [CommRing k] (X : M4 k) : Xᵀ * (rgJ k : M4 k) = (rgJ k : M4 k) * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rgJ, Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev]
private noncomputable def rgP (k : Type) [Field k] : M4 k →ₗ[k] M4 k where
  toFun X := (2 : k)⁻¹ • (X - adj X)
  map_add' X Y := by rw [(grp k).2.2.1, ← smul_add]; congr 1; abel
  map_smul' a X := by rw [(grp k).2.2.2.1, ← smul_sub, smul_comm]; rfl
private theorem rgP_apply {k : Type} [Field k] (X : M4 k) : rgP k X = (2 : k)⁻¹ • (X - adj X) := rfl
private theorem rgP_mem {k : Type} [Field k] (X : M4 k) : rgP k X ∈ sp4 k := by
  have h1 : adj (-adj X) = -X := by
    rw [← neg_one_smul k, (grp k).2.2.2.1, (grp k).2.1, neg_one_smul]
  show adj _ = -_
  rw [rgP_apply, (grp k).2.2.2.1, sub_eq_add_neg, (grp k).2.2.1, h1, ← smul_neg]
  congr 1
  abel
private theorem rgP_of_mem {k : Type} [Field k] [CharZero k] {X : M4 k} (h : X ∈ sp4 k) : rgP k X = X := by
  have h' : adj X = -X := h
  rw [rgP_apply, h', sub_neg_eq_add, ← two_smul k, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
private theorem rg_adjConj {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (θ : Γ →* kˣ) (hm : ∀ g, IsGSp (θ g : k) (r g))
    (g : Γ) (X : M4 k) : adj (r g * X * r g⁻¹) = r g * adj X * r g⁻¹ := by
  have h1 : adj (r g) = (θ g : k) • r g⁻¹ := (grp k).2.2.2.2.2.2.1 _ _ _ (hm g) (by rw [← map_mul]; simp)
  have h2 : adj (r g⁻¹) = (θ g⁻¹ : k) • r g := (grp k).2.2.2.2.2.2.1 _ _ _ (hm g⁻¹) (by rw [← map_mul]; simp)
  rw [(grp k).1, (grp k).1, h1, h2]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, ← Units.val_mul, ← map_mul]
  simp
private theorem rg_ad {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (g : Γ) (X : M4 k) :
    Loc.adGL r.toHomUnits g X = r g * X * r g⁻¹ := rfl
private theorem rg_pair {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (θ : Γ →* kˣ) (hm : ∀ g, IsGSp (θ g : k) (r g))
    (c s s' : Γ) (hs : s' = c * s * c⁻¹) :
    (r.toHomUnits s : M4 k)ᵀ * (rgJ k * (r.toHomUnits c)⁻¹ : GL (Fin 4) k) * (r.toHomUnits s' : M4 k) =
      (θ s : k) • ((rgJ k * (r.toHomUnits c)⁻¹ : GL (Fin 4) k) : M4 k) := by
  show (r s)ᵀ * ((rgJ k : M4 k) * r c⁻¹) * r s' = (θ s : k) • ((rgJ k : M4 k) * r c⁻¹)
  have h := hm s
  unfold IsGSp at h
  have e : r c⁻¹ * r s' = r s * r c⁻¹ := by
    rw [← map_mul, ← map_mul, hs]
    congr 1
    group
  rw [mul_assoc, mul_assoc, e, ← mul_assoc, rgJ_adj, mul_assoc, ← mul_assoc (adj _), h, smul_mul_assoc, one_mul, mul_smul_comm]
private theorem rg_alg {Γ k : Type} [Group Γ] [Field k] [CharZero k] (r : Γ →* M4 k) (θ : Γ →* kˣ)
    (hm : ∀ g, IsGSp (θ g : k) (r g)) (η : Γ →* kˣ) :
    ∃ ρ : Representation k Γ (M4 k),
      (∀ g X, η g = 1 → ρ g X = (r.toHomUnits g : M4 k) * X * ((r.toHomUnits g)⁻¹ : GL (Fin 4) k)) ∧
      (∀ g X, η g = -1 → ρ g X = -((((rgJ k * (r.toHomUnits g)⁻¹)⁻¹ : GL (Fin 4) k) : M4 k) * Xᵀ *
        (rgJ k * (r.toHomUnits g)⁻¹ : GL (Fin 4) k))) ∧
      (∀ g X, rgP k (Loc.adGL r.toHomUnits g X) = ρ g (rgP k X)) ∧
      ∀ g X Z, Z * r g⁻¹ ∈ sp4 k → Z * r g⁻¹ = ρ g X - X → Z = -rgP k X * r g - r g * -rgP k X := by
  have hpp : ∀ X, rgP k (rgP k X) = rgP k X := fun X => rgP_of_mem (rgP_mem X)
  have hpA : ∀ g X, rgP k (Loc.adGL r.toHomUnits g X) = Loc.adGL r.toHomUnits g (rgP k X) := fun g X => by
    rw [rgP_apply, rgP_apply, map_smul, map_sub, rg_ad, rg_ad, rg_adjConj r θ hm]
  obtain ⟨ρ, hρ⟩ := rg_twist (Loc.adGL r.toHomUnits) (rgP k) hpp hpA η
  refine ⟨ρ, fun g X h => ?_, fun g X h => ?_, fun g X => ?_, fun g X Z h1 h2 => ?_⟩
  · rw [hρ, h, Units.val_one, one_smul, ← map_add, add_sub_cancel]
    rfl
  · rw [mul_inv_rev, inv_inv]
    show _ = -((r g * ((rgJ k)⁻¹ : GL _ _)) * Xᵀ * ((rgJ k : M4 k) * r g⁻¹))
    have e : rgP k X - (X - rgP k X) = -adj X := by
      rw [rgP_apply]
      match_scalars <;> field_simp <;> ring
    rw [hρ, h, Units.val_neg, Units.val_one, neg_one_smul, ← sub_eq_add_neg, ← map_sub, e, map_neg, rg_ad,
      mul_assoc _ Xᵀ, ← mul_assoc Xᵀ, rgJ_adj]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  · rw [hρ, hpp, sub_self, map_zero, smul_zero, add_zero, hpA]
  · have e1 : Z * r g⁻¹ = r g * rgP k X * r g⁻¹ - rgP k X := by
      rw [← rgP_of_mem h1, h2, map_sub, hρ, map_add, map_smul, hpA, hpA, map_sub, hpp, sub_self, map_zero, smul_zero,
        add_zero, rg_ad]
    have := congrArg (· * r g) e1
    simp only [sub_mul, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
    rw [this]
    noncomm_ring
end Rg
theorem UpperTheory.V.Th.rigSp4_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.V.Th.RigiditySymplecticFour := by
  intro hU hAd Ω _ _ _ l _ c D hD N hN h1 h2 h3 ι r hr hirr haut r' hr' hfst
  have hG : D.Good := hD.elim (·.1) (·.1)
  obtain ⟨K, _, _, θ, hK, hm, hAd⟩ := _root_.UpperTheory.V.Z.Win.Dn.exists_cm_field_twist_h1 hU hAd D hD N hN h1 h2 h3 ι r hr hirr haut
  obtain ⟨hz, hbk, hsp⟩ := tanBK D hG hU.coh.loc r hr r' hr' hfst
  obtain ⟨η, hη1, hη2⟩ := rg_sign (Ω := Ω) hK (PadicAlgCl l)
  obtain ⟨ρ, ha, hb, hf, hd⟩ := rg_alg r θ hm η
  have hcc : ∃ j : Ω →+* ℂ, ∀ x, j (D.cc x) = starRingEnd ℂ (j x) := hG.isCC
  have hv := hAd ρ ⟨D.cc, rgJ _ * (r.toHomUnits D.cc)⁻¹, hcc, fun s s' hs => rg_pair r θ hm D.cc _ _ hs,
    fun s X => ha _ X (hη1 s), fun X => hb _ X (hη2 _ hcc)⟩
  obtain ⟨hz', hbk'⟩ := rg_bk (rgP _) hf (fun g => rgP_of_mem (hsp g)) hz hbk
  obtain ⟨X, hX⟩ := (mem_coboundaries1 _ _).1 (hv _ hz' hbk')
  exact ⟨-rgP (PadicAlgCl l) X, (sp4 (PadicAlgCl l)).neg_mem (rgP_mem (k := PadicAlgCl l) X), fun g i j => congrFun (congrFun (hd g X _ (hsp g) (hX g)) i) j⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.HV.DescentVanishingReductions
open UpperTheory.V.Lit UpperTheory.V.W
theorem adjoint_lift_of_prints (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Ws.UnramifiedInputs :=
  have hN := hH.litN
  ⟨⟨_root_.UpperTheory.V.W.locPrints_of_litN hN, hN.coh.pt, hN.coh.gf, hN.coh.ge, hN.coh.uo, hN.coh.gw⟩, hH, _root_.UpperTheory.V.HV.Core.modU_of_printsH hH, levEx, lamEx (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN),
    b0Ex (phiAll (_root_.UpperTheory.V.W.cohP_alt hN))⟩
theorem adjoint_lifting_of_cohomology (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Th.AdjointLiftingTheorem := _root_.UpperTheory.V.Th.adjoint_lifting_of_cohomology hH (_root_.UpperTheory.V.W.cohP_alt hH.litN)
theorem pmEx_of_printsH (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Ws.PMExAlt := _root_.UpperTheory.Gal.projectedFormsSystemPart.pm_exists_of_unramified_adjoint_lifting (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lift_of_prints hH) (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lifting_of_cohomology hH)
theorem countII_and_countIII_of_printsH_of_sp4In (hH : _root_.UpperTheory.V.Af.HypothesesH') (hK : ∃ CK : ℝ, LemmaK CK) (hS : _root_.UpperTheory.V.Aut.SymplecticFourImageDense) : CountII ∧ CountIII := by
  have hN := hH.litN
  obtain ⟨CK, hL⟩ := hK
  refine _root_.UpperTheory.V.Th.sp4Main_alt hS (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lift_of_prints hH).coh Alg.M.main_holds Alg.M.mprime_holds Alg.lemmaP (_root_.UpperTheory.GalN.V.numberSp4_n_alt hH.toClassicalTheorems)
    (_root_.UpperTheory.V.Th.rigSp4_alt (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lift_of_prints hH) (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lifting_of_cohomology hH)) (X.corX X.lemmaX X.residual_bernoulli_nonvanishing) fun Ω _ _ _ l _ => ⟨?_, fun c => ?_⟩
  · exact X.soBar CK hL (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK ℚ Ω l
  · exact X.soFin CK hL (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK ℚ Ω l c.O
end UpperTheory.V.HV.DescentVanishingReductions
end
end
