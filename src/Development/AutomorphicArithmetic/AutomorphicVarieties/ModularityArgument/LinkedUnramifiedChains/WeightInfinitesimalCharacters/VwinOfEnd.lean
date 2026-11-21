import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.VwinOfEnd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.BlockValuationRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.AdmissibleUnitaryThreePoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsCalcP
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.JumpsAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CountSys
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.KlevThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.EventuallyNotMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PureK
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IntK
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusTraceCountBoundOfCmEigensystemCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CountQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusTraceCountBoundOfRatEigensystemCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusTraceNormNonzeroLogBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.PropGKU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.OneCharU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.AdmissibleUnitaryOfInputs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.FreeCU

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.J

open UpperTheory.V.Af UpperTheory.V.Lev

variable {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r R : G K Ω →* GL (Fin n) (Qbar l)} {π : CuspSub K n}

private theorem frob_of_away (P : Hypotheses₂) (hc : Continuous R)
    (H : ∀ (w : HeightOneSpectrum (𝓞 K)), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion K) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι R (rc (algNorm σ)))
    (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∉ w.asIdeal) (B : Multiset ℂˣ) (hB : (CG.mk π).HasSat w B) :
    FrobEig ι R w (algSat n (normV w) B) := by
  obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
  exact satFrob P K Ω l ι n R hc w hw σ B (((satLoc P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
    fun A h rc hrc => H w hw A h rc hrc σ hσ

private theorem iso_of_away (P : Hypotheses₂) (hr : Continuous r) (ha : AttC ι r π) (hc : Continuous R) (hs : IsSSRep R)
    (H : ∀ (w : HeightOneSpectrum (𝓞 K)), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion K) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι R (rc (algNorm σ))) :
    RepIso r R := by
  refine isoOfFrob P K Ω l ι n r R hr hc ha.1 hs ((ha.2.and (eventually_not_mem K l)).mono ?_)
  rintro w ⟨⟨B, h1, h2⟩, hw⟩
  exact ⟨_, h2, frob_of_away P hc H w hw B h1⟩

private theorem infOf_of_weights {m : Fin n → ℤ} {x : Multiset ℂ}
    (h : (Finset.univ.val.map fun i => -m i).map (fun k : ℤ => (k : ℂ)) = x.map fun z => ((n : ℂ) - 1) / 2 - z) :
    x = infOf m := by
  have h2 := congrArg (Multiset.map fun z : ℂ => ((n : ℂ) - 1) / 2 - z) h
  simp only [Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id'] at h2
  rw [← h2, infOf]
  exact Multiset.map_congr rfl fun i _ => by push_cast; ring

end UpperTheory.V.Z.J

open UpperTheory.V.Af UpperTheory.V.Lev UpperTheory.V.Z.J in
theorem UpperTheory.V.Z.J.levelKU :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Z.J.LevelKU := by
  intro P K _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hreg hd ha
  have hC := P.ss
  have hF := UpperTheory.V.Lev.fixedAll P
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar K ^ n) :=
    ⟨fun v => by rw [locInf_pow, quadChar_locInf], by
      rw [map_pow, compNorm_quadChar, one_pow]; exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd⟩
  obtain ⟨R₁, wt, HT, H₁⟩ := P.litN.aut.gal K Ω l ι n (by omega) π _ hreg hpol
  obtain ⟨R, hc, hs, Haw, Hab⟩ := hC K Ω l ι n hn π hd (P.litN.aut.coh K n (by omega) π hreg)
  have hiso₁ := iso_of_away P hL.cont ha H₁.cont H₁.ss H₁.away
  have L₁ := hL.toLevel.of_iso hiso₁
  have hiso := iso_of_away P hL.cont ha hc hs Haw
  have L := hL.toLevel.of_iso hiso
  refine ⟨⟨fun φ => ?_, hd, ?_⟩, fun w hw B hB => (frob_of_away P hc Haw w hw B hB).of_iso hiso.symm'⟩
  · let τ : K →+* Qbar l := ι.symm.toRingHom.comp φ
    have hφ : ι.toRingHom.comp τ = φ := RingHom.ext fun x => ι.apply_symm_apply _
    obtain ⟨w, hw, hτ⟩ := GlobalTheory.GalFirstClause.existsIsInduced l K Ω τ
    obtain ⟨A, hA, χ, κ, h1, h2, h3, -⟩ := L₁.above w hw
    obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
    obtain ⟨τ', hτ'⟩ := hτ A hA O Bw hj
    have hJ := jumpsAbove P K Ω l hl n M hM m R₁ H₁.cont w A hA O Bw hj κ ⟨χ, h1, h2, h3⟩ τ _
      ((H₁.above _ _ (UpperTheory.V.Loc.tiedP l) w A hA O Bw hj).jumps τ _ τ' hτ')
    have hw := H₁.weights τ
    rw [hJ, hφ] at hw
    rw [← infOf_of_weights hw]
    exact ParLaws.hasInfChar_infChar (CG.mk π) φ
  · refine globFixed P K n M hM _ π.finPart π.isSmooth_finPart fun w => ?_
    obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
    refine ⟨σ, hi σ hσ, ?_⟩
    by_cases hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal
    · obtain ⟨A, hA, κ, ⟨χ, h1, h2, h3⟩, hu⟩ := hL.unl w hw
      obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
      obtain ⟨rc, hrc⟩ := P.exists_rec hA
      obtain ⟨hp, he⟩ := Hab _ _ (UpperTheory.V.Loc.tiedP l) w A hA O Bw hj
      exact hF K Ω l ι n M hM m R hc w A hA O Bw hj κ ⟨χ, h1, h2.of_iso hiso, h3⟩ hp rc hrc σ
        (fun ⟨μ, hμ⟩ => he σ hσ rc hrc (Or.inl ((ssCalc K Ω A w hA).1 n _ μ hμ))) (Or.inr (Or.inl hu))
    · obtain ⟨A, hA, χ, h1, h2⟩ := L.away w hw
      obtain ⟨rc, hrc⟩ := P.exists_rec hA
      exact locFixed P K Ω n M hM w A hA rc hrc σ
        (wdAway P K Ω l ι n M hM R hc w hw A hA χ h1 h2 _ (Haw w hw A hA rc hrc σ hσ))

end
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.J

open GlobalTheory.CuspRep in
theorem UpperTheory.V.Z.J.countKU :
    Af.Hypotheses₂ → CountKU := by
  intro hP K _ _ _ n hn
  classical
  obtain ⟨c, A, hcard⟩ := cardK hP K n hn
  refine ⟨c, A, fun m hm _ H hH M hM p w hp hw hpM hpd => ?_⟩
  have hwM : (M : 𝓞 K) ∉ w.asIdeal := natCast_notMem_of_not_dvd hp hw hpM
  let Wd := {v : HeightOneSpectrum (𝓞 K) // (M : 𝓞 K) ∉ v.asIdeal}
  let sys : CuspSub K n → Wd → Multiset ℂ := fun π v =>
    if h : ∃ B, (CG.mk π).HasSat v.1 B then algSat n (normV v.1) h.choose else 0
  have hsys : ∀ π (v : Wd) B, (CG.mk π).HasSat v.1 B → sys π v = algSat n (normV v.1) B := by
    intro π v B hB
    have h : ∃ B, (CG.mk π).HasSat v.1 B := ⟨B, hB⟩
    simp only [sys, dif_pos h]
    rw [h.choose_spec.unique hB]
  have hsat : ∀ π ∈ SigK K m M, ∀ v : Wd, ∃ B, (CG.mk π).HasSat v.1 B := fun π hπ v =>
    satK hP K n M π hπ.2.2 v.1 v.2
  obtain ⟨D, hD, cl, hcl, hβ⟩ := exists_eigData (SigK K m M) (fun π π' => π.Iso π') sys
    (fun π hπ π' _ h => funext fun v => by
      obtain ⟨B, hB⟩ := hsat π hπ v
      rw [hsys π v B hB, hsys π' v B (CuspSub.Iso.hasSatGL h hB)])
    (c * (M * (H + 1)) ^ A) (hcard m hm H hH M hM)
    (fun σ π hπ => by
      obtain ⟨π', hπ', h⟩ := conjK hP K n hn m hm M hM σ π hπ
      refine ⟨π', hπ', fun v => ?_⟩
      obtain ⟨B, hB⟩ := hsat π hπ v
      obtain ⟨B', hB', e⟩ := h v.1 B hB
      rw [hsys π v B hB, hsys π' v B' hB', e])
    ⟨w, hwM⟩ (n := n) (q := normV w) (m := m) (wt := 1 - n)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB, algSat, Multiset.card_map, ← hB.card]
      simp)
    (fun π hπ b hb => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB] at hb
      rw [pureK hP K n hn m hm M π hπ w B hB b hb]
      congr 1
      push_cast
      ring)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB]
      exact intK hP K n hn m hm M hM π hπ p w hp hw hpM hpd B hB)
  refine ⟨D, hD, fun l hl hl2 hlp Ω _ _ _ ι => ?_⟩
  have hform : ∀ r : {r : G K Ω →* GL (Fin n) (Qbar l) // AdmKU ι M m r}, ∃ π : ↥(SigK K m M), IsSSRep r.1 ∧
      ∀ v : Wd, (l : 𝓞 K) ∉ v.1.asIdeal → FrobEig ι r.1 v.1 (sys π v) := by
    intro r
    obtain ⟨π, h1, h2, h3⟩ := r.2.aut
    obtain ⟨hπ, hF⟩ := levelKU hP K n hn m hm M hM l hl2 Ω ι r.1 π r.2.level h1 h2 h3
    refine ⟨⟨π, hπ⟩, h3.1, fun v hv => ?_⟩
    obtain ⟨B, hB⟩ := hsat π hπ v
    rw [hsys π v B hB]
    exact hF v.1 hv B hB
  choose f hss hf using hform
  refine ⟨fun r => cl (f r), fun r r' h => ?_, fun r => ?_⟩
  · refine isoOfFrob hP K Ω l ι n r.1 r'.1 r.2.level.cont r'.2.level.cont (hss r) (hss r') ?_
    filter_upwards [eventually_natCast_notMem (F := K) (M := M) (by omega),
      eventually_natCast_notMem (F := K) hl.out.ne_zero] with v hvM hvl
    refine ⟨sys (f r) ⟨v, hvM⟩, hf r ⟨v, hvM⟩ hvl, ?_⟩
    rw [hcl _ _ h]
    exact hf r' ⟨v, hvM⟩ hvl
  · rw [hβ]
    refine hf r ⟨w, hwM⟩ (natCast_notMem_of_not_dvd hp hw fun h => hlp ?_)
    exact ((Nat.prime_dvd_prime_iff_eq hp hl.out).1 h).symm
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.J

private theorem prime_not_mem_of_other_prime {K : Type} [Field K] [NumberField K] {p l : ℕ} (w : HeightOneSpectrum (𝓞 K)) (hp : p.Prime)
    (hl : l.Prime) (hlp : l ≠ p) (hw : (p : 𝓞 K) ∈ w.asIdeal) : (l : 𝓞 K) ∉ w.asIdeal := by
  intro h
  have hc : IsCoprime (l : 𝓞 K) (p : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes hl hp).2 hlp)
  obtain ⟨a, b, hab⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left a h) (w.asIdeal.mul_mem_left b hw)))

private theorem conj_twist_matrix_eq_smul {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (g : GL (Fin n) k) (s : Γ) :
    ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (χ s : k) • ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]

private theorem is_flag_on_twist {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} (χ : Γ →* kˣ)
    {H : Subgroup Γ} {κ : Fin n → ↥H →* kˣ} (h : IsFlagOn r H κ) :
    IsFlagOn (tw r χ) H (fun i => κ i * χ.comp H.subtype) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => ⟨fun a b hab => ?_, fun a => ?_⟩⟩
  · have := (hg s).1 a b hab
    show ((g * tw r χ (s : Γ) * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a b = 0
    rw [conj_twist_matrix_eq_smul, Matrix.smul_apply]
    exact smul_eq_zero_of_right _ this
  · have := (hg s).2 a
    show ((g * tw r χ (s : Γ) * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a a = ((κ a s * χ (s : Γ) : kˣ) : k)
    rw [conj_twist_matrix_eq_smul, Matrix.smul_apply, smul_eq_mul, this, Units.val_mul]
    exact mul_comm _ _

private theorem flag_at_twist_cyclotomic {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n M : ℕ} {m : Fin n → ℤ} {r : G K Ω →* GL (Fin n) (Qbar l)} (j : ℤ)
    {A : ValuationSubring Ω} {κ : Fin n → ↥(Dec (F := K) A) →* (Qbar l)ˣ} (h : FlagAt M m r A κ) :
    FlagAt M (fun i => m i + j) (tw r (cycBar K Ω l ^ j)) A
      (fun i => κ i * (cycBar K Ω l ^ j).comp (Dec (F := K) A).subtype) := by
  obtain ⟨χ, hk, hf, hκ⟩ := h
  refine ⟨χ, hk, is_flag_on_twist _ hf, fun i s hs => ?_⟩
  show κ i s * cycBar K Ω l s ^ j = _
  rw [hκ i s hs, zpow_add, mul_right_comm]

private theorem unlocked_twist_cyclotomic {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n M : ℕ} {m : Fin n → ℤ} {r : G K Ω →* GL (Fin n) (Qbar l)} (j : ℤ)
    (h : Th.Unl l M m r) : Th.Unl l M (fun i => m i + j) (tw r (cycBar K Ω l ^ j)) := by
  intro w hw
  obtain ⟨A, hA, κ, hF, hq⟩ := h w hw
  refine ⟨A, hA, _, flag_at_twist_cyclotomic j hF, fun a b e => hq a b ?_⟩
  rw [mul_right_comm] at e
  exact mul_right_cancel e

private theorem admissible_twist_inverse_cyclotomic {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) (h : Adm3U ι e N ρ) :
    AdmKU ι N ![(e : ℤ) - 1, -1, -(e : ℤ) - 1] (tw ρ (cycBar K Ω l)⁻¹) := by
  have hm : ![(e : ℤ) - 1, -1, -(e : ℤ) - 1] = fun i => ![(e : ℤ), 0, -(e : ℤ)] i + (-1) := by
    funext i
    fin_cases i <;> simp <;> ring
  have h1 := UpperTheory.level_twist_cyclotomic_pow K Ω l 3 N _ ρ (-1) h.level
  have h2 := unlocked_twist_cyclotomic (-1) h.unl
  rw [zpow_neg_one] at h1 h2
  rw [hm]
  exact ⟨(UpperTheory.isIrr_twist_and_repIso_of_twist_repIso _ _ 3 _).1 ρ h.irr, h.aut, { h1 with unl := h2 }⟩

theorem UpperTheory.V.Z.J.tr3U :
    CountKU → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], ∃ c A : ℕ, ∀ e : ℕ, 1 ≤ e → ∀ N : ℕ, 1 ≤ N → ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ N → ¬ (p : ℤ) ∣ discr K → ∃ D : TrData (normV w) e, Nat.card D.S ≤ c * (N * (e + 1)) ^ A ∧ ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (B : ValuationSubring Ω), IsPlaceOver B w → ∀ σ : G K Ω, IsFrob B (normV w) σ → D.Classifies ι σ⁻¹ (Adm3U ι e N) := by
  intro hC K _ _ _
  obtain ⟨c, A, hK⟩ := hC K 3 (by norm_num)
  refine ⟨c * 2 ^ A, A, fun e he N hN p w hp hw hpN hpd => ?_⟩
  have hN' : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hq : 1 ≤ normV w := by
    rw [← hN']
    exact Nat.one_le_iff_ne_zero.2 fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hqC : ((normV w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : normV w ≠ 0)
  obtain ⟨D, hcard, hcl⟩ := hK ![(e : ℤ) - 1, -1, -(e : ℤ) - 1]
    (by
      refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
      fin_cases i <;> simp <;> omega)
    (by
      intro i
      fin_cases i <;> simp [Fin.rev] <;> ring)
    (e + 1)
    (by
      intro i
      rw [abs_le]
      fin_cases i <;> simp <;> omega)
    N hN p w hp hw hpN hpd
  obtain ⟨T, u, hT⟩ := UpperTheory.traces_from_eigenvalues_rank3 (normV w) e hq D
  refine ⟨T, ?_, fun l _ hl2 hlp Ω _ _ _ ι B hB σ hσ => ?_⟩
  · rw [← Nat.card_congr u, mul_assoc, ← mul_pow]
    refine hcard.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
    nlinarith
  · obtain ⟨cl, h1, h2⟩ := hcl l hl2 hlp Ω ι
    refine ⟨fun r => u (cl ⟨_, admissible_twist_inverse_cyclotomic ι e N r.1 r.2⟩), fun r r' H => ?_, fun r => ?_⟩
    · exact (UpperTheory.isIrr_twist_and_repIso_of_twist_repIso _ _ 3 _).2 _ _ (h1 _ _ (u.injective H))
    · have hl := prime_not_mem_of_other_prime w hp (Fact.out : l.Prime) hlp hw
      have e2 := ReciprocityTheory.Gal.cycZ_of_isFrob hl hB hσ
      have e3 : ((cycBar K Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
        change algebraMap ℚ_[l] (Qbar l) (((ReciprocityTheory.Gal.cycZ K Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = _
        rw [e2]; simp
      have h3 := (UpperTheory.map_trace_eq_sum_roots_of_charpoly_map _ ι.toRingHom _).1 _ ((h2 ⟨_, admissible_twist_inverse_cyclotomic ι e N r.1 r.2⟩ B hB).2 σ hσ)
      rw [tw_val, Matrix.trace_smul, MonoidHom.inv_apply, map_inv (cycBar K Ω l), inv_inv, e3, smul_eq_mul, map_mul,
        map_natCast] at h3
      rw [hT, eq_comm, RingEquiv.symm_apply_eq]
      simp only [mul_inv]
      rw [Multiset.sum_map_mul_left, ← h3, inv_mul_cancel_left₀ hqC]
      rfl
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.congruenceNumberUnitaryThree_of :
    Af.Hypotheses₂ → CongruenceNumberUnitaryThree := by
  intro hP K _ _ _ hK
  obtain ⟨c₁, A₁, h₁⟩ := tr3U (countKU hP) K
  obtain ⟨c₂, A₂, h₂⟩ := UpperTheory.frobenius_trace_count_bound_of_rat_eigensystem_count (countQ hP) (newformAut hP)
  set d := (discr K).natAbs with hd
  have hd1 : 1 ≤ d := Int.natAbs_pos.2 (discr_ne_zero K)
  refine ⟨5 * (c₁ + c₂ * d ^ A₂), A₁ + A₂ + 1, ?_⟩
  intro e he N hN p w hp hw h7 hpN hpd Orb _ z hz hc
  obtain ⟨h, hh1, hh2, hq⟩ := UpperTheory.exists_normV_eq_prime_pow_le_finrank K p w hp hw
  obtain ⟨D₁, hD₁, H₁⟩ := h₁ e he N hN p w hp hw hpN hpd
  have hpM : ¬ p ∣ N * d := fun H => (hp.dvd_mul.1 H).elim hpN fun H' => hpd (Int.natCast_dvd.2 H')
  have H₂' := h₂ K e he (N * d) (Nat.mul_pos hN hd1) p h w hp hw hpM
  rw [← hq] at H₂'
  obtain ⟨D₂, hD₂, H₂⟩ := H₂'
  have hq7 : 7 ≤ normV w := by
    rw [hq]; exact h7.trans (Nat.le_self_pow (by omega) p)
  obtain ⟨NN, h0, hb, H⟩ := UpperTheory.frobenius_trace_norm_nonzero_log_bound (normV w) e hq7 he (D₁.sum D₂) Orb z hz hc
  refine ⟨NN, h0, hb.trans ?_, fun l _ hl2 hlp Ω _ _ _ _ _ ι B hB σ hσ X hX hX' => ?_⟩
  · set Y : ℕ := N * (e + 1) with hY
    have hY1 : 1 ≤ Y := Nat.mul_pos hN (Nat.succ_pos e)
    have hcard : Nat.card (D₁.sum D₂).S ≤ (c₁ + c₂ * d ^ A₂) * Y ^ (A₁ + A₂) := by
      rw [TrData.card_sum, add_mul]
      refine add_le_add (hD₁.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 (by omega)))) (hD₂.trans ?_)
      rw [show N * d * (e + 1) = d * Y by rw [hY]; ring, mul_pow, ← mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 (by omega))
    have hp1 : (1 : ℝ) ≤ Real.log p := by
      rw [Real.le_log_iff_exp_le (by exact_mod_cast hp.pos)]
      have h7' : (7 : ℝ) ≤ p := by exact_mod_cast h7
      linarith [Real.exp_one_lt_d9]
    have hlq : Real.log (normV w) ≤ 2 * Real.log p := by
      rw [hq, Nat.cast_pow, Real.log_pow]
      have : (h : ℝ) ≤ 2 := by exact_mod_cast hK ▸ hh2
      nlinarith
    have heY : (e : ℝ) + 1 ≤ Y := by
      have : e + 1 ≤ Y := Nat.le_mul_of_pos_left _ hN
      exact_mod_cast this
    have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    have hf : 2 * e * Real.log (normV w) + 1 ≤ 5 * Y * Real.log p := by nlinarith
    have hf0 : 0 ≤ 2 * e * Real.log (normV w) + 1 := by positivity
    have hcard' : (Nat.card (D₁.sum D₂).S : ℝ) ≤ ((c₁ + c₂ * d ^ A₂) * Y ^ (A₁ + A₂) : ℕ) := by exact_mod_cast hcard
    have hYc : (N : ℝ) * (e + 1) = Y := by rw [hY]; push_cast; ring
    rw [hYc]
    calc (Fintype.card Orb : ℝ) * Nat.card (D₁.sum D₂).S * (2 * e * Real.log (normV w) + 1)
        ≤ Fintype.card Orb * ((c₁ + c₂ * d ^ A₂) * Y ^ (A₁ + A₂) : ℕ) * (5 * Y * Real.log p) := by gcongr
      _ = _ := by push_cast; ring
  · have hlq : ¬ l ∣ normV w := fun H' => by
      rw [hq] at H'
      exact hlp ((Nat.prime_dvd_prime_iff_eq Fact.out hp).1 ((Fact.out : l.Prime).dvd_of_dvd_pow H'))
    exact H l hlq ι _ σ⁻¹ _ ((H₁ l hl2 hlp Ω ι B hB σ hσ).sum (H₂ l hl2 hlp Ω ι B hB σ hσ)) X hX hX'
end

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

section SlopeTestRemainingChoices

open IsLocalRing UpperTheory.V UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

private theorem int_of_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
  exact ⟨q, hqm, by
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem loc_of_int {O R A : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing A]
    [Nontrivial A] [Algebra O A] [Algebra.IsIntegral O A] (f : R →ₐ[O] A) : IsLocalHom f := by
  let g : R →+* f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' g hg
  have hl : IsLocalHom g := IsLocalHom.of_surjective _ hg
  haveI : Algebra.IsIntegral f.range A := Algebra.IsIntegral.tower_top (R := O)
  have h2 : IsLocalHom (algebraMap f.range A) := Algebra.IsIntegral.isLocalHom _ _
  exact ⟨fun x hx => hl.map_nonunit x (h2.map_nonunit (g x) hx)⟩

private theorem norm_le {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]
    {f : R →ₐ[c.O] PadicAlgCl l} (hf : IsLocPt f) (x : R) : ‖f x‖ ≤ 1 := by
  obtain ⟨-, -, hl, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  have hz : (l : R) ∈ maximalIdeal R := fun h => by
    have h1 : IsUnit (algebraMap c.O R (l : c.O)) := by rwa [map_natCast]
    exact hl (IsLocalHom.map_nonunit _ h1)
  have hp : 0 < ‖((l : ℕ) : PadicAlgCl l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  by_contra hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖((l : ℕ) : PadicAlgCl l)‖⁻¹) (not_le.1 hx)
  have h1 := hf (x ^ n * l) (Ideal.mul_mem_left _ _ hz)
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h1
  have h2 := mul_lt_mul_of_pos_right hn hp
  rw [inv_mul_cancel₀ hp.ne'] at h2
  exact lt_asymm h1 h2

private theorem factor {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]
    (f : R →ₐ[c.O] PadicAlgCl l) (hf : IsLocPt f) :
    ∃ (A : Subalgebra c.O (PadicAlgCl l)) (h : IsDiscreteValuationRing A) (_ : Module.Finite c.O A) (f' : R →ₐ[c.O] A),
      IsAdicComplete (@maximalIdeal A _ h.toIsLocalRing) A ∧ ∀ x, (f' x : PadicAlgCl l) = f x := by
  haveI := (UpperTheory.V.abelian₂.dvr_finite l c.O).1
  obtain ⟨E, hE⟩ := Loc.ptFin (l := l) R ((TrivSqZeroExt.inlAlgHom c.O _ _).comp f) hf
  have hE' : ∀ a, f a ∈ E.1 := fun a => (hE a).1
  haveI := E.2
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l E.1
  let j : E.1 →ₐ[ℤ_[l]] PadicAlgCl l := E.1.val.restrictScalars ℤ_[l]
  have hj : Function.Injective j := Subtype.val_injective
  let e := (integralClosure ℤ_[l] E.1).equivMapOfInjective j hj
  let B := (integralClosure ℤ_[l] E.1).map j
  have hB : ∀ x, f x ∈ B := fun x =>
    ⟨⟨f x, hE' x⟩, (isIntegral_algHom_iff j hj).1 (int_of_norm _ (norm_le hf x)), rfl⟩
  let A : Subalgebra c.O (PadicAlgCl l) := { B.toSubsemiring with algebraMap_mem' := fun a => f.commutes a ▸ hB _ }
  have d1 : IsDiscreteValuationRing B := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have d2 : Module.Finite ℤ_[l] B := Module.Finite.equiv e.toLinearEquiv
  haveI : Module.Finite ℤ_[l] A := d2
  haveI d3 : IsDiscreteValuationRing A := d1
  exact ⟨A, d3, Module.Finite.of_restrictScalars_finite ℤ_[l] c.O A, f.codRestrict A hB, (UpperTheory.V.abelian₂.dvr_finite l A).1,
    fun _ => rfl⟩

end SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Z.J

open Formalism.GaloisCohomology Polynomial UpperTheory.V.Th in
theorem UpperTheory.V.Z.J.rigIU :
    U3.CohInp → Af.HypothesesH → Th.AdL → UnlEnd3 → Th.RigI := by
  intro hI hH hL hU Ω _ _ _ K _ _ _ _ l hl c N _ e ψ D U g₁ hM S f hf hr ι hT hA
  have hN := hH.litN
  have hσ : Sd.IsCC D.cc := D.conj
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨B, hB, -, -, -, hB', -⟩ := U3.dat_loc D
  have hF := Fr.gd_ex ⟨⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.pt⟩, hN.coh.uo, hN.coh.gw⟩
    Ω K l c N e ψ D B hB
  have hσ' : IsConjOm D.cc.toRingEquiv := hσ
  have hΨ : Chr.Psi l e (Chr.dirG ℚ Ω ψ) D.cc = 1 := by
    have h1 : cycZ ℚ Ω l D.cc = -1 := hσ'.cyc (E := ℚ)
    have h2 : chiO ℚ Ω l c.O D.cc = -1 := by
      show Units.map (algebraMap ℤ_[l] c.O).toMonoidHom (cycZ ℚ Ω l D.cc) = -1
      rw [h1]
      apply Units.ext
      simp
    have h3 : (Chr.dirG ℚ Ω ψ D.cc : c.O) = (-1) ^ e := by
      rw [Chr.dirG, MonoidHom.comp_apply, (Chr.clsFacts ℚ Ω N).2.2.2.1 D.cc hσ', MulChar.coe_toUnitHom]
      exact D.gd.par
    apply Units.ext
    show ((chiO ℚ Ω l c.O D.cc ^ (e : ℤ) * Chr.dirG ℚ Ω ψ D.cc : c.Oˣ) : c.O) = 1
    rw [h2, zpow_natCast, Units.val_mul, h3, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← mul_pow]
    simp
  have hram : ∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ D.η.ker →
      B'.valuation ((l * N * (discr K).natAbs : ℕ) : Ω) < 1 := by
    intro B' h
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    have hd : B'.valuation ((discr K : ℤ) : Ω) < 1 := by
      by_contra h4
      refine h fun s hs => ?_
      rw [D.η_ker]
      have key := GlobalTheory.UnramDiscr.embedding_eq B' h4 ((s : Ω →+* Ω).comp (algebraMap K Ω)) (algebraMap K Ω) (fun x => by
        refine hs.2 _ ((B'.valuation_le_one_iff _).mpr (GlobalTheory.UnramDiscr.mem_of_isIntegral B' ?_))
        exact (RingOfIntegers.isIntegral_coe x).map (algebraMap K Ω).toIntAlgHom)
      exact fun x => DFunLike.congr_fun key x
    have hd' : B'.valuation (((discr K).natAbs : ℕ) : Ω) < 1 := by
      rcases Int.natAbs_eq (discr K) with h1 | h1
      · rw [h1, Int.cast_natCast] at hd; exact hd
      · rw [h1, Int.cast_neg, Int.cast_natCast, Valuation.map_neg] at hd; exact hd
    rw [Nat.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((B'.valuation_le_one_iff _).2 (natCast_mem B' _))) hd'
  have hk : Pr.LinkHyp c N e D.η D.cc B (l * N * (discr K).natAbs) :=
    ⟨D.gd.e_pos, dvd_mul_right _ _,
      mul_ne_zero (mul_ne_zero hl.out.ne_zero (NeZero.ne N)) (Int.natAbs_ne_zero.2 (discr_ne_zero K)), hram, hB, hσ⟩
  obtain ⟨A, hA1, hA2, f', hA3, hf'⟩ := factor f hf
  haveI : IsLocalRing A := hA1.toIsLocalRing
  have ho := Pr.ordPt_of_gd hI.loc D g₁ hM U S B hB' A f' (loc_of_int f')
  have e1 : UnitaryThreeInertia.push A.val (U3.push f' S.r.hom) = U3.push f S.r.hom :=
    MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => hf' _)) rfl
  have had := admissible_unitary_of_inputs hI hH hU D hM S f hf hr ι hT hA
  have he := D.gd.e_pos
  have hfr : FreeAt l (D.rhoK _ hr) :=
    freeCU hH K Ω l D.gd.l_odd ι 3 (by decide) _ (-1) N _ had.level.cont (by rw [_root_.zpow_neg_one]; exact had.aut)
      (NeZero.one_le) (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega) had.unl
  have key := rigEnd3 hH hL Ω l ι c N e ψ D.η D.cc g₁ B _ hk hΨ hF A _ ho
    (Pr.matIrr_open_gd D g₁ hM B hB A _ ho (by rw [e1]; exact hT)) K D.gd.quad D.η_ker (D.rhoK _ hr)
    (fun s => by rw [e1]; rfl) hA hfr
  rwa [e1] at key
end

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy

namespace UpperTheory.V.Z.J

open UpperTheory.V.HV UpperTheory.V.Lit UpperTheory.V.W

theorem countI (hH : Af.HypothesesH) (hK : ∃ CK : ℝ, LemmaK CK) (hKa : Z.Kato.KatoTwo) (hU : LinkedUnl) (h3 : Aut.AutomorphyUnramifiedCoefficients) : CountI :=
  have hC := Core0.cohInp hH.litN hK
  have hE := unlEnd3 hU
  U3.countI (U3.corGK (propGKU (congruenceNumberUnitaryThree_of hH.toClassicalTheorems)
    (oneCharU hC Alg.M.main_holds Alg.M.mprime_holds Alg.lemmaP hKa (rigIU hC hH (DescentVanishingReductions.adL hH) hE)
      (Th.rigII hC hH (DescentVanishingReductions.adL hH)) (admissible_unitary_of_inputs hC hH hE) h3)))

end UpperTheory.V.Z.J
end
