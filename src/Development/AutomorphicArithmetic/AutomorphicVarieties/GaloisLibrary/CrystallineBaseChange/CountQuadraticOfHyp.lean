import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.KlevThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.EventuallyNotMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LevelP
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CountSys
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SignNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.TwCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ResTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.FrobEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelFRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.UnderCPl
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNormVEqPrimePowLeFinrank
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp

open UpperTheory.V.Af

namespace UpperTheory.V.Br

private theorem inv_mem_eig {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (x : WD h) (φ : Weil h) {b : ℂ}
    (hb : (x.charPol φ⁻¹).IsRoot b) : b ≠ 0 ∧ b⁻¹ ∈ x.eig φ := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  rw [WD.charPol_mk, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hb
  obtain ⟨v, hv⟩ := hb.exists_hasEigenvector
  have h1 : v = b • a.ρ φ v := by
    rw [← map_smul, ← hv.apply_eq_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hv.2 (by simpa using h1)
  refine ⟨hb0, ?_⟩
  rw [WD.eig_mk, mem_roots (LinearMap.charpoly_monic _).ne_zero, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨Module.End.mem_eigenspace_iff.2 ?_, hv.2⟩
  conv_rhs => rw [h1]
  rw [smul_smul, inv_mul_cancel₀ hb0, one_smul]

private theorem norm_of_pure {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    {B : Multiset ℂ} (hB : FrobEig ι r w B) {x : WD h} (hx : IsWDOf ι r x) {s : ℝ} (ht : (x.lpTw s).tempered) :
    ∀ b ∈ B, ‖b‖ = (normV w : ℝ) ^ s := by
  intro b hb
  obtain ⟨hu, hf⟩ := hB A h
  have e := hx.wdOf_eq hl
  obtain ⟨t, ht', φ, hφ, N, a, hN, -, -⟩ := id hx
  have hxu : x.unr := e ▸ (hN.unr_wdOf_iff hl ht' ι).2 hu
  have hc := hN.charPol_wdOf (h := h) hl ht' ι (frob h)⁻¹
  rw [e] at hc
  have hr : (x.charPol (frob h)⁻¹).IsRoot b := by
    rw [hc]
    erw [hf _ isFrob_frob]
    have := (mem_roots (Polynomial.monic_multiset_prod_of_monic B (fun b => X - C b)
      fun b _ => monic_X_sub_C b).ne_zero).1 ((roots_multiset_prod_X_sub_C B).symm ▸ hb)
    exact this
  obtain ⟨hb0, hm⟩ := inv_mem_eig x _ hr
  have h1 := (WD.tempered_unr _ ((WD.unr_tw x s).2 hxu)).1 ht (b⁻¹ * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) (by
    rw [WD.frobEig_tw x s hxu]
    exact Multiset.mem_map_of_mem _ hm)
  rw [norm_mul, norm_inv, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans (GlobalTheory.WeilDeligne.one_lt_normV w)), Complex.ofReal_re,
    inv_mul_eq_one₀ (norm_ne_zero_iff.2 hb0)] at h1
  exact h1

private theorem wt_eq {n : ℕ} (hn : 1 ≤ n) {m : Fin n → ℤ} {wt wt' : ℤ} (hm : ∀ i, m i + m i.rev = wt) {H : Multiset ℤ}
    (h1 : H.map (fun n : ℤ => (n : ℂ)) = (infOf m).map fun z => ((n : ℂ) - 1) / 2 - z) (h2 : H = H.map (wt' - ·)) :
    wt' = -wt := by
  have e : H = Finset.univ.val.map fun i => -m i := by
    refine Multiset.map_injective (Int.cast_injective (α := ℂ)) ?_
    rw [h1, infOf, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp
  have s1 := congrArg Multiset.sum h2
  rw [e, Multiset.map_map] at s1
  change ∑ i, -m i = ∑ i, (wt' - -m i) at s1
  have s2 : ∑ i : Fin n, (m i + m i.rev) = ∑ _i : Fin n, wt := Finset.sum_congr rfl fun i _ => hm i
  have s3 : ∑ i : Fin n, m i.rev = ∑ i, m i := Equiv.sum_comp Fin.revPerm m
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, s3] at s1 s2
  have hn' : (n : ℤ) ≠ 0 := by omega
  refine mul_left_cancel₀ hn' ?_
  linarith

private theorem exists_prime_not_mem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    ∃ l : ℕ, l.Prime ∧ ((l : ℕ) : 𝓞 K) ∉ w.asIdeal := by
  by_contra H
  push_neg at H
  have h2 := H 2 Nat.prime_two
  have h3 := H 3 Nat.prime_three
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  have := w.asIdeal.sub_mem h3 h2
  norm_num at this
  exact this

end UpperTheory.V.Br

theorem UpperTheory.V.Br.pureP :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.PureP := by
  intro P K _ _ _ n hn m wt hm hwt M π hπ w B hB
  obtain ⟨hinf, ⟨χ, hχ⟩, -⟩ := hπ
  obtain ⟨l, hlp, hl⟩ := UpperTheory.V.Br.exists_prime_not_mem w
  haveI : Fact l.Prime := ⟨hlp⟩
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  have hic : ∀ τ, (CG.mk π).infChar τ = UpperTheory.V.Af.infOf m := fun τ => CG.HasInfChar.infChar_eq (hinf τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hic]
    refine ⟨Finset.univ.nodup.map fun i j e => hm.injective ?_, fun z hz => ?_⟩
    · exact_mod_cast add_left_cancel e
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
      exact ⟨m i, add_comm _ _⟩
  obtain ⟨r, wt', HT, hr⟩ := P.litN.aut.gal K (AlgebraicClosure K) l ι n (by omega) π χ hreg hχ
  have hHT : ∀ τ, (HT τ).map (fun n : ℤ => (n : ℂ)) = (UpperTheory.V.Af.infOf m).map fun z => ((n : ℂ) - 1) / 2 - z := fun τ => by
    rw [hr.weights τ, hic]
  obtain ⟨τ₀⟩ : Nonempty (K →+* ℂ) := inferInstance
  have e : wt' = -wt := by
    refine UpperTheory.V.Br.wt_eq (by omega) hwt (hHT (ι.symm.toRingHom.comp τ₀)) ?_
    rw [← hr.weights_conj]
    exact Multiset.map_injective (Int.cast_injective (α := ℂ)) ((hHT _).trans (hHT _).symm)
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := UpperTheory.V.Af.locCompC P K n π w
  have hs := ((UpperTheory.V.Af.satLoc P K n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  have hF := UpperTheory.V.Af.satFrob P K (AlgebraicClosure K) l ι n r hr.cont w hl σ B hs
    fun A h rc hrc => hr.away w hl A h rc hrc σ hσ
  obtain ⟨A, hA⟩ := exists_isPlaceOver (AlgebraicClosure K) w
  obtain ⟨x, hx, ht⟩ := hr.pure w hl A hA
  have := UpperTheory.V.Br.norm_of_pure hl hF hx ht
  rw [e] at this
  simpa using this
end
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.CuspRep UpperTheory.V.Af in
theorem UpperTheory.V.Br.countP :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.CountP := by
  intro hP K _ _ _ hK n hn
  classical
  obtain ⟨c, A, hcard⟩ := cardP hP K n hn
  refine ⟨c, A, fun m wt hm hwt H hH M hM p w hp hw hpM hpd => ?_⟩
  have hwM : (M : 𝓞 K) ∉ w.asIdeal := natCast_notMem_of_not_dvd hp hw hpM
  let Wd := {v : HeightOneSpectrum (𝓞 K) // (M : 𝓞 K) ∉ v.asIdeal}
  let sys : CuspSub K n → Wd → Multiset ℂ := fun π v =>
    if h : ∃ B, (CG.mk π).HasSat v.1 B then algSat n (normV v.1) h.choose else 0
  have hsys : ∀ π (v : Wd) B, (CG.mk π).HasSat v.1 B → sys π v = algSat n (normV v.1) B := by
    intro π v B hB
    have h : ∃ B, (CG.mk π).HasSat v.1 B := ⟨B, hB⟩
    simp only [sys, dif_pos h]
    rw [h.choose_spec.unique hB]
  have hsat : ∀ π ∈ SigP K m M, ∀ v : Wd, ∃ B, (CG.mk π).HasSat v.1 B := fun π hπ v =>
    satK hP K n M π hπ.2.2 v.1 v.2
  obtain ⟨D, hD, cl, hcl, hβ⟩ := exists_eigData (SigP K m M) (fun π π' => π.Iso π') sys
    (fun π hπ π' _ h => funext fun v => by
      obtain ⟨B, hB⟩ := hsat π hπ v
      rw [hsys π v B hB, hsys π' v B (CuspSub.Iso.hasSatGL h hB)])
    (c * (M * (H + 1)) ^ A) (hcard m hm H hH M hM)
    (fun σ π hπ => by
      obtain ⟨π', hπ', h⟩ := conjPrime₂ hP K hK n hn m hm M hM σ π hπ
      refine ⟨π', hπ', fun v => ?_⟩
      obtain ⟨B, hB⟩ := hsat π hπ v
      obtain ⟨B', hB', e⟩ := h v.1 B hB
      rw [hsys π v B hB, hsys π' v B' hB', e])
    ⟨w, hwM⟩ (n := n) (q := normV w) (m := m) (wt := wt)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB, algSat, Multiset.card_map, ← hB.card]
      simp)
    (fun π hπ b hb => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB] at hb
      exact pureP hP K n hn m wt hm hwt M π hπ w B hB b hb)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB]
      exact intP hP K n hn m hm M hM π hπ p w hp hw hpM hpd B hB)
  refine ⟨D, hD, fun l hl hl2 hlp Ω _ _ _ ι => ?_⟩
  have hform : ∀ r : {r : G K Ω →* GL (Fin n) (Qbar l) // AdmP ι M m r}, ∃ π : ↥(SigP K m M), IsSSRep r.1 ∧
      ∀ v : Wd, (l : 𝓞 K) ∉ v.1.asIdeal → FrobEig ι r.1 v.1 (sys π v) := by
    intro r
    obtain ⟨π, h1, h2, h3⟩ := r.2.aut
    obtain ⟨hπ, hF⟩ := levelP hP K hK n hn m hm M hM l hl2 Ω ι r.1 π r.2.level h1 h2 h3
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
open UpperTheory.V.Af

namespace UpperTheory.V.Br

private theorem roots_finset (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) (B : Multiset ℂ) :
    ∃ T : Finset (Multiset ℂ), T.card ≤ 2 ^ B.card ∧ ∀ C : Multiset ℂ, C.map (· ^ f) = B → C ∈ T := by
  classical
  induction B using Multiset.induction_on with
  | empty =>
    refine ⟨{0}, by simp, fun C hC => ?_⟩
    simpa using hC
  | cons b B ih =>
    obtain ⟨T, hT, hm⟩ := ih
    refine ⟨((Polynomial.nthRoots f b).toFinset ×ˢ T).image fun x => x.1 ::ₘ x.2, ?_, fun C hC => ?_⟩
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_product, Multiset.card_cons, pow_succ']
      exact Nat.mul_le_mul (((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots f b)).trans h2) hT
    · obtain ⟨a, ha, hab, hr⟩ := (Multiset.map_eq_cons _ _ _ _).2 hC
      refine Finset.mem_image.2 ⟨(a, C.erase a), Finset.mem_product.2 ⟨?_, hm _ hr⟩, Multiset.cons_erase ha⟩
      exact Multiset.mem_toFinset.2 ((Polynomial.mem_nthRoots h1).2 hab)

private theorem roots_card (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) (B : Multiset ℂ) :
    Finite {C : Multiset ℂ // C.map (· ^ f) = B} ∧ Nat.card {C : Multiset ℂ // C.map (· ^ f) = B} ≤ 2 ^ B.card := by
  obtain ⟨T, hT, hm⟩ := roots_finset f h1 h2 B
  let g : {C : Multiset ℂ // C.map (· ^ f) = B} → T := fun C => ⟨C.1, hm _ C.2⟩
  have hg : Function.Injective g := fun x y h => Subtype.ext (congrArg Subtype.val h :)
  refine ⟨Finite.of_injective g hg, (Nat.card_le_card_of_injective g hg).trans ?_⟩
  simpa using hT

private theorem pairs_card {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt) (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) :
    Finite {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} ∧
      Nat.card {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} ≤ 2 ^ n * Nat.card D.S := by
  haveI := D.fin
  haveI := Fintype.ofFinite D.S
  haveI : ∀ s, Finite {C : Multiset ℂ // C.map (· ^ f) = D.β s} := fun s => (roots_card f h1 h2 _).1
  let e := Equiv.subtypeProdEquivSigmaSubtype fun (s : D.S) (C : Multiset ℂ) => C.map (· ^ f) = D.β s
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, Nat.card_sigma]
  refine (Finset.sum_le_card_nsmul _ _ (2 ^ n) fun s _ => ?_).trans ?_
  · have := (roots_card f h1 h2 (D.β s)).2
    rwa [D.card] at this
  · simp [mul_comm]

private theorem pairs_conj {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt) (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2)
    (σ : ℂ ≃+* ℂ) :
    ∃ e : {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} ≃ {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1},
      ∀ x, (e x).1.2 = x.1.2.map σ := by
  haveI := (pairs_card D f h1 h2).1
  obtain ⟨e, he⟩ := D.conj σ
  let g : {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} → {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} :=
    fun x => ⟨(e x.1.1, x.1.2.map σ), by
      show (x.1.2.map σ).map (· ^ f) = D.β (e x.1.1)
      rw [he, ← x.2, Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl fun b _ => by simp⟩
  have hg : Function.Injective g := fun x y h => by
    have h' := congrArg Subtype.val h
    simp only [g, Prod.mk.injEq] at h'
    exact Subtype.ext (Prod.ext (e.injective h'.1) (Multiset.map_injective σ.injective h'.2))
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hg), fun _ => rfl⟩

private theorem int_root (p f : ℕ) (h1 : 1 ≤ f) (a : ℤ) (b : ℂ) (h : IsIntegral ℤ (((p ^ f : ℕ) : ℂ) ^ a * b ^ f)) :
    IsIntegral ℤ ((p : ℂ) ^ a * b) := by
  refine IsIntegral.of_pow (n := f) h1 ?_
  convert h using 1
  rw [mul_pow, Nat.cast_pow, ← zpow_natCast, ← zpow_natCast (p : ℂ), ← zpow_mul, ← zpow_mul, mul_comm a]

end UpperTheory.V.Br

open UpperTheory.V.Br in
theorem UpperTheory.V.Br.rootSum :
    UpperTheory.V.Br.RootSum := by
  intro n p hp m wt I _ q f hf D
  haveI : ∀ i, Finite {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} :=
    fun i => (pairs_card (D i) (f i) (hf i).1 (hf i).2.1).1
  have hmem : ∀ i (x : {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1}), ∀ b ∈ x.1.2,
      b ^ f i ∈ (D i).β x.1.1 := fun i x b hb => by
    rw [← x.2]
    exact Multiset.mem_map_of_mem _ hb
  refine ⟨⟨Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool, inferInstance,
    fun x => x.2.1.1.2, ?_, ?_, ?_, ?_, ?_⟩, ?_, id, Function.injective_id, fun _ => rfl⟩
  · rintro ⟨i, x, t⟩
    have := (D i).card x.1.1
    rw [← x.2, Multiset.card_map] at this
    exact this
  · intro σ
    choose e he using fun i => pairs_conj (D i) (f i) (hf i).1 (hf i).2.1 σ
    exact ⟨Equiv.sigmaCongrRight fun i => (e i).prodCongr (Equiv.refl _), fun x => he x.1 x.2.1⟩
  · rintro ⟨i, x, t⟩ b hb
    have h := (D i).pure _ _ (hmem i x b hb)
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hq : ((q i : ℕ) : ℝ) = (p : ℝ) ^ f i := by rw [(hf i).2.2, Nat.cast_pow]
    rw [norm_pow, hq, ← Real.rpow_natCast (p : ℝ), ← Real.rpow_mul hp0, mul_comm, Real.rpow_mul hp0, Real.rpow_natCast] at h
    exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hp0 _) (by have := (hf i).1; omega)).1 h
  · rintro a ha ⟨i, x, t⟩ b hb
    have h := (D i).int a ha _ _ (hmem i x b hb)
    refine int_root p (f i) (hf i).1 a b ?_
    rw [← (hf i).2.2]
    exact h
  · rintro a ha ⟨i, x, t⟩ b hb
    have h := (D i).intInv a ha _ _ (hmem i x b hb)
    refine int_root p (f i) (hf i).1 a b⁻¹ ?_
    rw [← (hf i).2.2, inv_pow]
    exact h
  · show Nat.card (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) ≤ _
    rw [Nat.card_sigma, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
    have := (pairs_card (D i) (f i) (hf i).1 (hf i).2.1).2
    calc _ ≤ 2 ^ n * Nat.card (D i).S * 2 := Nat.mul_le_mul_right _ this
      _ = _ := by ring
end

section
theorem UpperTheory.V.Br.isCrys_isDR_restrict_openSubgroup :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.AdmRes := by
  intro hP K _ _ _ hK n hn m wt hm M hM l _ hl Ω _ _ _ _ _ _ ι r hr hirr
  have hC := UpperTheory.V.Lev.LevelF.of_level hr.level
  have hF := UpperTheory.V.Lev.levelFRes ℚ K Ω l n M m r hC
  obtain ⟨P, hreg, hA⟩ := hr.aut hC.cont K hK hirr
  obtain ⟨θ, hθ, hd⟩ := hr.dual
  obtain ⟨χ, μ, hpol, -, -⟩ := UpperTheory.V.Z.Bc.polK hP K hK n (by omega) l Ω ι r wt θ P hθ hd hA
  exact ⟨hirr, ⟨P, hreg, ⟨χ, hpol⟩, hA⟩, hF.cont, hF.away, hF.above, hr.safe⟩
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
  UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Br

private theorem bit_of_fibre {X U : Type} (R : X → X → Prop) (hs : ∀ x y, R x y → R y x)
    (ht : ∀ x y z, R x y → R y z → R x z) (Q : X → U → Prop) (hQ : ∀ x, ∃ u, Q x u)
    (h2 : ∀ u x₀ x x', Q x₀ u → Q x u → Q x' u → ¬ R x₀ x → ¬ R x₀ x' → R x x') :
    ∃ g : X → U × Bool, (∀ x x', g x = g x' → R x x') ∧ ∀ x, Q x (g x).1 := by
  classical
  choose u hu using hQ
  have hex : ∀ x : X, ∃ y, Q y (u x) := fun x => ⟨x, hu x⟩
  refine ⟨fun x => (u x, decide (R (Classical.epsilon (α := X) (h := ⟨x⟩) fun y => Q y (u x)) x)), fun x x' h => ?_, hu⟩
  obtain ⟨h1, h3⟩ := Prod.ext_iff.1 h
  simp only at h1 h3
  have h0 := Classical.epsilon_spec (hex x)
  rw [← h1, decide_eq_decide] at h3
  have hx' : Q x' (u x) := h1 ▸ hu x'
  by_cases hc : R (Classical.epsilon (α := X) (h := ⟨x⟩) fun y => Q y (u x)) x
  · exact ht _ _ _ (hs _ _ hc) (h3.1 hc)
  · exact h2 _ _ _ _ h0 (hu x) hx' hc fun h4 => hc (h3.2 h4)

private theorem iso_symm {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r') :
    RepIso r' r := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, fun s => by rw [hg s]; group⟩

private theorem iso_trans {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' r'' : Γ →* GL (Fin n) k} (h : RepIso r r')
    (h' : RepIso r' r'') : RepIso r r'' := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  exact ⟨g' * g, fun s => by rw [hg' s, hg s]; group⟩

private theorem normV_rat {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  obtain ⟨h, h1, h2, h3⟩ := UpperTheory.exists_normV_eq_prime_pow_le_finrank ℚ p w hp hw
  rw [Module.finrank_self] at h2
  rw [h3, le_antisymm h2 h1, pow_one]

private theorem exists_over (K : Type) [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (f : ℕ), v.under (𝓞 ℚ) = w ∧ (p : 𝓞 K) ∈ v.asIdeal ∧ 1 ≤ f ∧ f ≤ 2 ∧ normV v = p ^ f := by
  haveI := w.isMaximal
  obtain ⟨Q, hQ, hL⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) w.asIdeal
  have hpQ : (p : 𝓞 K) ∈ Q := by
    have : (p : 𝓞 ℚ) ∈ Q.under (𝓞 ℚ) := hL.over ▸ hw
    simpa [Ideal.under, Ideal.mem_comap] using this
  have h0 : Q ≠ ⊥ := by
    rintro rfl
    exact hp.ne_zero (by simpa using hpQ)
  obtain ⟨f, f1, f2, f3⟩ := UpperTheory.exists_normV_eq_prime_pow_le_finrank K p ⟨Q, hQ.isPrime, h0⟩ hp hpQ
  exact ⟨⟨Q, hQ.isPrime, h0⟩, f, HeightOneSpectrum.ext hL.over.symm, hpQ, f1, h2 ▸ f2, f3⟩

private theorem not_mem_of_coprime {F : Type} [Field F] [NumberField F] {p a : ℕ} (h : p.Coprime a)
    (w : HeightOneSpectrum (𝓞 F)) (hw : (p : 𝓞 F) ∈ w.asIdeal) : (a : 𝓞 F) ∉ w.asIdeal := fun ha => by
  obtain ⟨x, y, e⟩ : IsCoprime (p : 𝓞 F) (a : 𝓞 F) := Nat.Coprime.cast h
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw)
    (w.asIdeal.mul_mem_left _ ha)))

private theorem exists_avoid {N : ℕ} (d : Fin (N + 1) → ℤ) (hd : ∀ i j, i ≠ j → IsCoprime (d i) (d j)) {p : ℕ} (hp : p.Prime) :
    ∃ u : Fin N → Fin (N + 1), Function.Injective u ∧ ∀ i, ¬ (p : ℤ) ∣ d (u i) := by
  by_cases h : ∃ j, (p : ℤ) ∣ d j
  · obtain ⟨j, hj⟩ := h
    refine ⟨j.succAbove, Fin.succAbove_right_injective, fun i hi => ?_⟩
    have := (hd _ _ (Fin.succAbove_ne j i)).isUnit_of_dvd' hi hj
    exact (Nat.prime_iff_prime_int.1 hp).not_unit this
  · exact ⟨Fin.succ, Fin.succ_injective _, fun i hi => h ⟨_, hi⟩⟩

private theorem map_inv_inv (B : Multiset ℂ) : (B.map (·⁻¹)).map (·⁻¹) = B := by
  rw [Multiset.map_map]
  simp

theorem UpperTheory.V.Br.count_quadratic_of_hypotheses :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.CountQ := by
  intro hP n hn
  classical
  obtain ⟨K₀, _, _, _, hK2, hKc⟩ := quadFam (n ^ 2 + 1 + 1)
  choose c A hcA using fun i => countP hP (K₀ i) (hK2 i) n hn
  refine ⟨2 ^ (n + 1) * ((n ^ 2 + 1) * ∑ i, c i), ∑ i, A i, ?_⟩
  intro m wt hm hwt H hH M hM p w hp hpw hpM
  obtain ⟨u, hu, hup⟩ := exists_avoid (fun i => discr (K₀ i)) hKc hp
  choose v f hvw hpv hf1 hf2 hvf using fun i => exists_over (K₀ (u i)) (hK2 _) hp w hpw
  choose D hDc hD using fun i => hcA (u i) m wt hm hwt H hH M hM p (v i) hp (hpv i) hpM (hup i)
  obtain ⟨D', hD', e, he, heβ⟩ := rootSum n p hp.pos m wt (Fin (n ^ 2 + 1)) (fun i => normV (v i)) f
    (fun i => ⟨hf1 i, hf2 i, hvf i⟩) D
  refine ⟨D', hD'.trans ?_, ?_⟩
  · rw [mul_assoc, mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    have hb : ∀ i, Nat.card (D i).S ≤ (∑ i, c i) * (M * (H + 1)) ^ (∑ i, A i) := fun i =>
      (hDc i).trans (Nat.mul_le_mul (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
        (Nat.pow_le_pow_right (Nat.mul_pos hM (Nat.succ_pos _))
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))))
    refine (Finset.sum_le_sum fun i _ => hb i).trans ?_
    simp
  intro l _ hl2 hlp Ω _ _ _ ι
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let emb : ∀ i, K₀ (u i) →ₐ[ℚ] Ω := fun i => IsAlgClosed.lift
  letI alg : ∀ i, Algebra (K₀ (u i)) Ω := fun i => (emb i).toRingHom.toAlgebra
  haveI tow : ∀ i, IsScalarTower ℚ (K₀ (u i)) Ω := fun i =>
    IsScalarTower.of_algebraMap_eq fun x => ((emb i).commutes x).symm
  haveI clo : ∀ i, IsAlgClosure (K₀ (u i)) Ω := fun i => ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  choose δ _ _ hδ _ using fun i => UpperTheory.exists_quadratic_sign_character ℚ (K₀ (u i)) Ω l (hK2 _)
  have hδi : Function.Injective δ := fun i j hij => by
    by_contra hne
    refine signNe (K₀ (u i)) (K₀ (u j)) Ω (hK2 _) (hKc _ _ fun h => hne (hu h)) (Subgroup.ext fun s => ?_)
    rw [← (hδ i).1, ← (hδ j).1, hij]
  choose cl hcl hclβ using fun i => hD i l hl2 hlp Ω ι
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal :=
    not_mem_of_coprime ((Nat.coprime_primes hp Fact.out).2 hlp.symm) w hpw
  have hMw : ((M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := not_mem_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM) w hpw
  refine Exists.elim (bit_of_fibre (X := {r : G ℚ Ω →* GL (Fin n) (Qbar l) // AdmR ι M m wt r})
    (U := Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1})
    (fun r r' => RepIso r.1 r'.1) (fun _ _ => iso_symm) (fun _ _ _ => iso_trans)
    (fun r t => (∃ h : AdmP ι M m (r.1.comp (res ℚ Ω (K₀ (u t.1)))), cl t.1 ⟨_, h⟩ = t.2.1.1) ∧
      FrobEig ι r.1 w (t.2.1.2.map (·⁻¹))) ?ex ?two) ?main
  case main =>
    rintro g ⟨hg, hgQ⟩
    refine ⟨fun r => e ⟨(g r).1.1, (g r).1.2, (g r).2⟩, fun r r' h => hg r r' ?_, fun r => ?_⟩
    · have h1 := congrArg (fun x : (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) =>
        ((⟨x.1, x.2.1⟩ : Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1}), x.2.2)) (he h)
      exact h1
    · rw [heβ]
      exact (hgQ r).2
  case ex =>
    rintro ⟨r, hr⟩
    obtain ⟨i, hi⟩ : ∃ i, ¬ RepIso r (tw r (δ i)) := by
      by_contra hall
      have h1 := twCard _ _ n r hr.irr (Finset.univ.image δ) fun d hd => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hd
        by_contra h
        exact hall ⟨i, h⟩
      rw [Finset.card_image_of_injective _ hδi, Finset.card_univ, Fintype.card_fin] at h1
      omega
    have hirr := (resTwo _ _ _ n (res ℚ Ω (K₀ (u i))) (δ i) (hδ i).1 (hδ i).2 r).1 hr.irr hi
    have hadm := isCrys_isDR_restrict_openSubgroup hP (K₀ (u i)) (hK2 _) n hn m wt hm M hM l hl2 Ω ι r hr hirr
    obtain ⟨B, hB⟩ := (frobEx ℚ Ω l ι n r w).2 M hr.level.away hlw hMw
    have h1 := (UpperTheory.frobenius_power_compatibility ℚ (K₀ (u i)) Ω l ι (v i) (f i) (by rw [hvw, hvf, normV_rat hp w hpw])).1 n r B
      (by rw [hvw]; exact hB)
    have h2 := (frobEx (K₀ (u i)) Ω l ι n _ (v i)).1 _ _ h1 (hclβ i ⟨_, hadm⟩)
    refine ⟨⟨i, ⟨(cl i ⟨_, hadm⟩, B.map (·⁻¹)), ?_⟩⟩, ⟨hadm, rfl⟩, ?_⟩
    · show (B.map (·⁻¹)).map (· ^ f i) = (D i).β (cl i ⟨_, hadm⟩)
      rw [← map_inv_inv ((D i).β _), ← h2, Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl fun b _ => inv_pow b (f i)
    · show FrobEig ι r w ((B.map (·⁻¹)).map (·⁻¹))
      rw [map_inv_inv]
      exact hB
  case two =>
    rintro ⟨i, t⟩ r₀ r r' ⟨⟨a₀, e₀⟩, -⟩ ⟨⟨a, e₁⟩, -⟩ ⟨⟨a', e₂⟩, -⟩ n1 n2
    have hR := (resTwo _ _ _ n (res ℚ Ω (K₀ (u i))) (δ i) (hδ i).1 (hδ i).2 r₀.1).2
    have k1 := (hR r.1 a₀.irr (hcl i _ _ (e₀.trans e₁.symm))).resolve_left n1
    have k2 := (hR r'.1 a₀.irr (hcl i _ _ (e₀.trans e₂.symm))).resolve_left n2
    exact iso_trans (iso_symm k1) k2
end
