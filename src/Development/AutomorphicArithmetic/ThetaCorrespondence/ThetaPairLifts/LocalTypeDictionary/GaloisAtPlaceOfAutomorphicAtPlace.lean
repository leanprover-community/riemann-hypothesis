import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStatementOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BciNarrowSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStatementOfSmallStatement

section
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.GalAut
end GlobalTheory.GalAut
namespace GlobalTheory.GalAut
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n c : ℕ} {π : Submodule ℂ (UA E n → ℂ)} {a d : Fin c → ℕ}
  {h : ∑ i, d i * a i = n} {P : ∀ i, CuspSub E (a i)} {ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i)}
  {m : Fin c → (E →+* ℂ) → Multiset ℂ}
end GlobalTheory.GalAut
namespace GlobalTheory.GalAut
end GlobalTheory.GalAut
theorem GlobalTheory.GalAut.exists_galoisRep_of_definiteUnitary : _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal →
  GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered → GlobalTheory.Published.HeckeLAdicCharacter →
  GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.BhattScholzeCrystallineLattices →
  GlobalTheory.Published.LocalLanglandsGL →
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (n : ℕ), 1 ≤ n → ∀ π : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ), GlobalTheory.UnitaryBC.IsAutRepU π →
    ∀ lam : (E →+* ℂ) → Formalism.BasicNotions.DomWeight n, (∀ τ, GlobalTheory.UnitaryBC.HasWeightAt π τ (lam τ)) →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
      (∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsUnramU π w) →
      (∃ r : G E Ω →* GL (Fin n) (Qbar l),
        GlobalTheory.ExpFrame.CrysWith r (GlobalTheory.GalDef.jumpsOf ι lam) ∧ GlobalTheory.GalDef.FrobSat ι π (-1) fun g => (r g).val.charpoly) ∧
      ∀ t : ℕ, n < 2 * t → (∀ τ, ∃ p, GlobalTheory.GalDef.IsRunAt (lam τ) p t) → GlobalTheory.GalDef.HasString l π t →
        ∃ (a : ℕ) (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : Fin t → G E Ω →* (Qbar l)ˣ)
          (bot : (E →+* Qbar l) → ℤ),
          a + t = n ∧ Continuous ρ ∧ (∀ s, GlobalTheory.ExpFrame.CrysWith (GlobalTheory.TripleGal.rk1 (χ s)) fun τ => {bot τ + ((s : ℕ) : ℤ)}) ∧
          (∀ τ p, GlobalTheory.GalDef.IsRunAt (lam (ι.toRingHom.comp τ)) p t → bot τ = (p : ℤ) - GlobalTheory.GalDef.wAt (lam (ι.toRingHom.comp τ)) p) ∧
          GlobalTheory.GalDef.FrobSat ι π (-1) fun g =>
            (ρ g).val.charpoly * ∏ s, (Polynomial.X - Polynomial.C ((χ s g : (Qbar l)ˣ) : Qbar l)) := by
  intro H1 H3 H4 H5 H6 H7 H8 H9 H10 E Ω _ _ _ _ _ _ hE n hn π hπ lam hlam l _ ι hunr
  obtain ⟨c, a, d, h, P, ρ, m, σ, hP, hloc, hsplit⟩ := _root_.UpperTheory.BaseChangeIdentities.base_change_speh_narrow_swap H1 E hE n hn π hπ
  let J : (Σ i : Fin c, Fin (d i)) → (E →+* Qbar l) → Multiset ℤ := fun x τ =>
    (m x.1 (ι.toRingHom.comp τ)).map (fun z => ⌊(GlobalTheory.GalAut.shiftF n (d x.1) x.2 - z).re⌋)
  have hJ : ∀ x τ, (J x τ).map (fun k : ℤ => (k : ℂ)) =
      (m x.1 (ι.toRingHom.comp τ)).map (fun z => GlobalTheory.GalAut.shiftF n (d x.1) x.2 - z) := by
    intro x τ
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun z hz => ?_
    obtain ⟨j, hj⟩ := GlobalTheory.GalAut.int_shift hP (hlam _) x.1 x.2 hz
    exact GlobalTheory.GalAut.cast_floor_re hj
  have hnd : ∀ i τ, (m i τ).Nodup := fun i τ => GlobalTheory.GalAut.nodup_of_parts hP (hlam τ) i
  have hsph : ∀ i (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal →
      ∀ σ' : SmIrr (GL (Fin (a i)) (w.adicCompletion E)), (P i).IsLocComp w σ' →
        GlobalTheory.LGrp.IsSpherical σ'.ρ (GlobalTheory.LFun.KGL w (a i)) := fun i w hw σ' h' =>
    GlobalTheory.SphBC.isSpherical_of_isUnramU E hE n π hπ c a d h P ρ m σ hP hloc hsplit w (hunr w hw) i σ' h'
  have hpc := fun x : (Σ i : Fin c, Fin (d i)) => GlobalTheory.T.cm_galois_representation_crystalline H3 H6 H7 H8 H9 H10 E Ω hE l ι (a x.1) (hP.pos x.1).1 (P x.1)
    (hP.csd x.1) (m x.1) (hP.inf x.1) (hnd x.1) (GlobalTheory.GalAut.shiftF n (d x.1) x.2) (J x) (hJ x)
  choose r hrc hrcrys hrfrob using hpc
  have hsize : ∑ x : (Σ i : Fin c, Fin (d i)), a x.1 = n := by
    rw [Fintype.sum_sigma, ← h]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  obtain ⟨R, hRc, hRcrys, hRch⟩ := GlobalTheory.BlockSum.main H9 E Ω l (Σ i : Fin c, Fin (d i)) (fun x => a x.1) n hsize r hrc
  have hS : ∀ w, IsSplitAt w → ∀ (σw : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σw.ρ → GlobalTheory.LFun.HasSatGL w σw.ρ T →
      ∃ S : Fin c → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ (S i)) ∧
        ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) =
          T.map (fun z => (z : ℂ)) := fun w hs σw T hc ht =>
    GlobalTheory.SatInd.satake_locProd_speh E w c n a d h (ρ · w) (σ · w) (fun i => (hP.pos i).2) (fun i => (hloc i w).2.2) T
      (GlobalTheory.SplitSatake.hasSatGL_of_isCompAlong_split E n π hπ w hs _ _ σw.ρ (locProd h w (σ · w)) hc (hsplit w hs) T ht)
  have hq : ∀ w : HeightOneSpectrum (𝓞 E), (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := fun w h0 =>
    w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hprod : ∀ w, IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (σw : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σw.ρ → GlobalTheory.LFun.HasSatGL w σw.ρ T →
      ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g →
      ∏ x, (r x (g ^ (-1 : ℤ))).val.charpoly = (T.map fun z : ℂˣ =>
          Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod := by
    intro w hs hl σw T hc ht B g hB hg
    obtain ⟨S, hS1, hS2⟩ := hS w hs σw T hc ht
    rw [GlobalTheory.satake_linear_factors_regroup (Qbar l) ι c d S T _ (hq w) (((n : ℂ) - 1) / 2) hS2, Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ =>
      hrfrob ⟨i, k⟩ w hs hl (ρ i w) (hP.loc i w) (S i) (hS1 i) B g hB hg
  have hsg : ((-1 : ℤˣ) : ℤ) = -1 := rfl
  refine ⟨⟨R, ?_, ?_⟩, ?_⟩
  · have hj : (fun τ => ∑ x, J x τ) = GlobalTheory.GalDef.jumpsOf ι lam := by
      funext τ
      apply Multiset.map_injective (f := fun k : ℤ => (k : ℂ)) Int.cast_injective
      rw [GlobalTheory.GalAut.map_cast_sum]
      simp only [hJ]
      rw [Fintype.sum_sigma]
      have e1 : ∀ i : Fin c, ∑ k : Fin (d i), (m i (ι.toRingHom.comp τ)).map (fun z => GlobalTheory.GalAut.shiftF n (d i) k - z) =
          (spehInf (d i) (m i (ι.toRingHom.comp τ))).map (fun z => ((n : ℂ) - 1) / 2 - z) := fun i =>
        GlobalTheory.DefiniteBC.spehInf_map_sub_eq_sum_twists (d i) (m i (ι.toRingHom.comp τ)) (((n : ℂ) - 1) / 2)
      rw [Finset.sum_congr rfl fun i _ => e1 i, ← GlobalTheory.GalAut.map_sub_sum, hP.weight _ _ (hlam _)]
      unfold GlobalTheory.GalDef.jumpsOf infOfWeight
      rw [Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun k _ => ?_
      simp only [Function.comp_apply]
      push_cast; ring
    rw [← hj]
    exact hRcrys J fun x => hrcrys x fun w hw => ⟨ρ x.1 w, hP.loc x.1 w, hsph x.1 w hw _ (hP.loc x.1 w)⟩
  · intro w hs hl hU σw T hc ht B g hB hg
    rw [hsg]
    show (R (g ^ (-1 : ℤ))).val.charpoly = _
    rw [hRch]
    exact hprod w hs hl σw T hc ht B g hB hg
  · intro t ht hrun hstr
    obtain ⟨w, hs, hl, hU, σw, T, ν, hc, ht', hν, hle⟩ := hstr
    obtain ⟨S, hS1, hS2⟩ := hS w hs σw T hc ht'
    have hfz : ∀ i τ, ∀ z ∈ m i τ, ∃ k : ℤ, z = (((n : ℂ) - 1) / 2 - ((d i : ℂ) - 1) / 2) + k := by
      intro i τ z hz
      obtain ⟨j, hj⟩ := GlobalTheory.GalAut.int_of_parts hP (hlam τ) i hz (k := 0) (hP.pos i).2
      refine ⟨-j, ?_⟩
      push_cast at hj ⊢
      linear_combination -hj
    have htemp : ∀ i, ∀ s ∈ S i, ‖(s : ℂ)‖ = 1 := fun i =>
      GlobalTheory.T.cohomological_local_component_exponents H4 H5 E (a i) (hP.pos i).1 (P i) (hP.csd i) (m i) (hP.inf i) (hnd i) _ (hfz i) w (ρ i w)
        (hP.loc i w) (S i) (hS1 i)
    have ht1 : 1 ≤ t := by omega
    obtain ⟨i0, hi0⟩ := GlobalTheory.unitary_string_forces_long_part E w c d S T t ν ht1 htemp hν hS2 (by rw [GlobalTheory.GalAut.lift_eq]; exact hle)
    have hne : ∀ i τ, m i τ ≠ 0 := fun i τ h0 => by
      have h1 := (hP.inf i τ).1
      rw [h0, Multiset.card_zero] at h1
      have := (hP.pos i).1
      omega
    have hrunP : ∀ τ' p, GlobalTheory.GalDef.IsRunAt (lam τ') p t → d i0 = t ∧
        m i0 τ' = {(GlobalTheory.GalDef.wAt (lam τ') p : ℂ) + ((n : ℂ) - 1) / 2 - (p : ℕ) - ((t : ℂ) - 1) / 2} ∧
          ∀ j, j ≠ i0 → d j < t :=
      fun τ' p hp => GlobalTheory.GalDef.spehPart_is_run n t (lam τ') p ht hp c d (fun i => m i τ') (fun i => (hP.pos i).2)
        (fun i => hne i τ') (hP.weight τ' _ (hlam τ')) i0 hi0
    obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨p0, hp0⟩ := hrun τ0
    obtain ⟨hd0, hm0, -⟩ := hrunP τ0 p0 hp0
    have ha0 : a i0 = 1 := by
      have h1 := (hP.inf i0 τ0).1
      rw [hm0] at h1
      simpa using h1.symm
    let pp : (E →+* Qbar l) → ℕ := fun τ => (hrun (ι.toRingHom.comp τ)).choose
    have hpp : ∀ τ, GlobalTheory.GalDef.IsRunAt (lam (ι.toRingHom.comp τ)) (pp τ) t := fun τ => (hrun _).choose_spec
    let bot : (E →+* Qbar l) → ℤ := fun τ => (pp τ : ℤ) - GlobalTheory.GalDef.wAt (lam (ι.toRingHom.comp τ)) (pp τ)
    obtain ⟨ρR, hρc, -, hρch⟩ := GlobalTheory.BlockSum.main H9 E Ω l (Σ i : {i : Fin c // i ≠ i0}, Fin (d i)) (fun x => a x.1.1) _ rfl
      (fun x => r ⟨x.1.1, x.2⟩) (fun x => hrc _)
    let kk : Fin t → Σ i : Fin c, Fin (d i) := fun s => ⟨i0, Fin.cast hd0.symm (Fin.rev s)⟩
    refine ⟨_, ρR, fun s => Matrix.GeneralLinearGroup.det.comp (r (kk s)), bot, ?_, hρc, ?_, ?_, ?_⟩
    · rw [← hsize, Fintype.sum_sigma (fun x : Σ i : Fin c, Fin (d i) => a x.1), Fintype.sum_eq_add_sum_subtype_ne _ i0,
        Fintype.sum_sigma (fun x : Σ i : {i : Fin c // i ≠ i0}, Fin (d i) => a x.1.1)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hd0, ha0, mul_one]
      ring
    · intro s
      have hJk : ∀ τ, J (kk s) τ = {bot τ + ((s : ℕ) : ℤ)} := by
        intro τ
        show (m i0 (ι.toRingHom.comp τ)).map _ = _
        rw [(hrunP _ _ (hpp τ)).2.1, Multiset.map_singleton, Multiset.singleton_inj]
        have hs1 : (s : ℕ) + 1 ≤ t := s.isLt
        have e : GlobalTheory.GalAut.shiftF n (d i0) (kk s).2 - ((GlobalTheory.GalDef.wAt (lam (ι.toRingHom.comp τ)) (pp τ) : ℂ) +
            ((n : ℂ) - 1) / 2 - (pp τ : ℕ) - ((t : ℂ) - 1) / 2) = ((bot τ + ((s : ℕ) : ℤ) : ℤ) : ℂ) := by
          simp only [GlobalTheory.GalAut.shiftF, kk, bot, Fin.coe_cast, Fin.val_rev, hd0]
          rw [Nat.cast_sub hs1]
          push_cast
          ring
        rw [e]
        simp
      rw [show (fun τ => ({bot τ + ((s : ℕ) : ℤ)} : Multiset ℤ)) = J (kk s) from funext fun τ => (hJk τ).symm]
      exact GlobalTheory.GalAut.crystallineHodgeTate_det_rankOne ha0 (r (kk s)) (J (kk s)) (hrcrys (kk s) fun w hw => ⟨ρ i0 w, hP.loc i0 w, hsph i0 w hw _ (hP.loc i0 w)⟩)
    · intro τ p hp
      have e1 := (hrunP _ _ (hpp τ)).2.1
      have e2 := (hrunP _ _ hp).2.1
      rw [e1, Multiset.singleton_inj] at e2
      have e3 : (((pp τ : ℤ) - GlobalTheory.GalDef.wAt (lam (ι.toRingHom.comp τ)) (pp τ) : ℤ) : ℂ) =
          (((p : ℤ) - GlobalTheory.GalDef.wAt (lam (ι.toRingHom.comp τ)) p : ℤ) : ℂ) := by
        push_cast
        linear_combination -e2
      exact_mod_cast e3
    · intro w' hs' hl' hU' σ' T' hc' ht'' B g hB hg
      rw [hsg]
      show (ρR (g ^ (-1 : ℤ))).val.charpoly * ∏ s, (Polynomial.X - Polynomial.C
        (((Matrix.GeneralLinearGroup.det.comp (r (kk s))) (g ^ (-1 : ℤ)) : (Qbar l)ˣ) : Qbar l)) = _
      have e3 : ∏ x, (r x (g ^ (-1 : ℤ))).val.charpoly =
          (∏ k : Fin (d i0), (r ⟨i0, k⟩ (g ^ (-1 : ℤ))).val.charpoly) *
            ∏ x : (Σ i : {i : Fin c // i ≠ i0}, Fin (d i)), (r ⟨x.1.1, x.2⟩ (g ^ (-1 : ℤ))).val.charpoly := by
        rw [Fintype.prod_sigma, Fintype.prod_eq_mul_prod_subtype_ne _ i0, Fintype.prod_sigma]
      have e4 : ∏ s : Fin t, (Polynomial.X - Polynomial.C
          (((Matrix.GeneralLinearGroup.det.comp (r (kk s))) (g ^ (-1 : ℤ)) : (Qbar l)ˣ) : Qbar l)) =
          ∏ k : Fin (d i0), (r ⟨i0, k⟩ (g ^ (-1 : ℤ))).val.charpoly :=
        Fintype.prod_equiv (Fin.revPerm.trans (finCongr hd0.symm)) _ _ fun s =>
          (GlobalTheory.GalAut.charpoly_eq_of_one ha0 _).symm
      rw [← hprod w' hs' hl' σ' T' hc' ht'' B g hB hg, e3, hρch, e4, mul_comm]
end
end

section
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FrameGal
section Poly
open Polynomial Formalism.L2.Col
variable {K : Type} [Field K]
end Poly
section Runs
open Formalism.BasicNotions Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds GlobalTheory.GalDef
end Runs
section Galois
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.ExpFrame GlobalTheory.TripleGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
variable [IsCMField E]
end Galois
section Side
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.ExpFrame GlobalTheory.TripleGal GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.GalDef
open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.L2.Col Polynomial
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] [IsCMField E]
variable (Ω) in
theorem galois_side_of_compatible_systems (p1 : GlobalTheory.Published.ClozelCohomological) (p2 : GlobalTheory.Published.CohomologicalCsdTempered)
    (p3 : GlobalTheory.Published.HeckeLAdicCharacter) (p4 : GlobalTheory.Published.ChebotarevDegreeOne)
    (p6 : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (p7 : _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup)
    (p8 : GlobalTheory.Published.BhattScholzeCrystallineLattices) (p9 : GlobalTheory.Published.HeckeLAdicCharacterAbove) (p10 : GlobalTheory.Published.LocalLanglandsGL)
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal)
    (ι : Qbar l ≃+* ℂ) {T : Type} [DecidableEq T] {inc : T → (E →+* Qbar l)} (half : IsHalf inc) (s : T → ℤ)
    {P : Par} {W : Wts T} (hP : P.Hyp) (hL : P.Large) (hW : W.Ok P) (F : Frame l T P.Nr) (Bk : (F.I → Qbar l) → Prop)
    {Pl : Type} (pt : Pl → Fin P.Nr → F.I) (lab : Pl → HeightOneSpectrum (𝓞 E))
    (cofin : {v : HeightOneSpectrum (𝓞 E) | (Ideal.absNorm v.asIdeal).Prime ∧ v ∉ Set.range lab}.Finite)
    (hlab : ∀ Q, IsSplitAt (lab Q) ∧ ((l : ℕ) : 𝓞 E) ∉ (lab Q).asIdeal)
    (haut : ∀ mu θ, (∀ τ, Antitone (res P.Nr (mu τ))) → F.IsEig mu θ → ∃ π, SystemOf ι inc s lab P.Nr mu (sysOf P.Nr pt θ) π)
    (hblk : ∀ θ, Bk θ → ∀ Q, ∃ ν : Qbar l, ‖ι ν‖ ^ 2 = (Ideal.absNorm (lab Q).asIdeal : ℝ) ^ (P.Nr - P.t) ∧
      blockPoly ν (Ideal.absNorm (lab Q).asIdeal) P.t ∣ heckePolyOf P.Nr (Ideal.absNorm (lab Q).asIdeal) (sysOf P.Nr pt θ Q)) :
    GalSide Ω inc P W F Bk := by
  have hN := hP.Nr_eq
  have ht := hP.t_ge
  have hm := hP.m_pos
  have hk := hP.m_le
  obtain ⟨c, hc, hc'⟩ := exists_of_half half (fun τ => (h0 P : ℤ) - P.Nr + 1 + s τ) fun τ => -s τ
  obtain ⟨tw, htw, hcr⟩ := exists_crys_char Ω p3 p9 ι c ((h0 P : ℤ) - P.Nr + 1) fun i => by
    obtain ⟨τ, rfl | rfl⟩ := half.2.2 i
    · rw [hc, hc']; ring
    · rw [cj_cj, hc, hc']; ring
  let Fn : FrobNorm E Ω l Pl := ⟨lab, -1, tw, htw, cofin⟩
  have main := _root_.GlobalTheory.GalAut.exists_galoisRep_of_definiteUnitary p7 p6 p1 p2 p3 p9 p4 p8 p10 E Ω hE P.Nr (by omega)
  refine ⟨Pl, pt, Fn, cj, Or.inr rfl, fun mu θ ha hθ => ?_, fun θ hθ hB => ?_⟩
  · obtain ⟨π, hπ⟩ := haut mu θ ha hθ
    obtain ⟨lam, hl, hl1, hl2, -⟩ := hπ.weights half
    obtain ⟨⟨r, hr, hf⟩, -⟩ := main π hπ.1 lam hl l ι hπ.2.2.1
    refine ⟨GlobalTheory.TwistAbove.twGL tw r,
      fun τ a => ((Fin.rev a : ℕ) : ℤ) - (lam (ι.toRingHom.comp τ)).w (Fin.rev a) + c τ, fun τ a => ⟨?_, ?_⟩, ?_,
      SystemOf.reads Fn hlab hπ hf fun g => charpoly_smul _ (Units.ne_zero _)⟩
    · have := a.2
      simp only [hl2, hc', DomWeight.dual, Fin.rev_rev, hl1, Formalism.CohomologicalDescent.UnitNormBounds.UN]
      rw [Fin.val_rev]
      omega
    · have := a.2
      simp only [cj_cj, hc, hl1, Formalism.CohomologicalDescent.UnitNormBounds.UN, Fin.val_rev]
      omega
    · convert crysWith_twist (r' := GlobalTheory.TwistAbove.twGL tw r) (fun _ => rfl) hr htw hcr using 2 with τ
      rw [jumpsOf, Multiset.map_map]
      conv_rhs => rw [← Multiset.map_univ_val_equiv Fin.revPerm, Multiset.map_map]
      rfl
  · have ha : ∀ τ, Antitone (res P.Nr (W.lam τ)) := fun τ a b h => hW.anti τ a b h b.2
    obtain ⟨π, hπ⟩ := haut W.lam θ ha hθ
    obtain ⟨lam, hl, hl1, hl2, hl3⟩ := hπ.weights half
    have r1 := fun τ => isRunAt_block hP hL hW τ _ _ (hl1 τ)
    have r2 := fun τ => isRunAt_dual (by omega) (r1 τ).1
    obtain ⟨-, v, hv, hd, -⟩ := (p4.dense (Ω := Ω) cofin).nonempty
    obtain ⟨Q, -⟩ : v ∈ Set.range lab := by
      by_contra h
      exact hv ⟨((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd, h⟩
    have hstr : HasString l π P.t := by
      obtain ⟨hu, σ, S, h1, h2, h3⟩ := hπ.2.2.2 Q
      obtain ⟨ν, hν, hdv⟩ := hblk θ hB Q
      obtain ⟨u, hu1, hu2⟩ := string_of_dvd ι (absNorm_ne_zero _) (by omega) S (card_of_hasSat h2) _ h3 ν hν hdv
      exact ⟨lab Q, (hlab Q).1, (hlab Q).2, hu, σ, S, u, h1, h2, hu1, hu2⟩
    obtain ⟨a, ρ, χ, bot, h1, h2, h3, h4, h5⟩ := (main π hπ.1 lam hl l ι hπ.2.2.1).2 P.t (by omega) (fun φ => by
      obtain ⟨τ, rfl | rfl⟩ := hl3 φ
      · exact ⟨_, (r1 τ).1⟩
      · exact ⟨_, hl2 τ ▸ (r2 τ).1⟩) hstr
    refine ⟨a, GlobalTheory.TwistAbove.twGL tw ρ, fun j => χ j * tw, fun τ => bot τ + c τ, h1,
      continuous_twist (fun _ => rfl) h2 htw, fun j => ?_, fun τ => ⟨?_, ?_⟩, SystemOf.reads Fn hlab hπ h5 fun g => ?_⟩
    · convert crysWith_twist (r' := rk1 (χ j * tw)) (fun g => ?_) (h3 j) htw hcr using 2 with τ
      · rw [Multiset.map_singleton, add_right_comm]
      · ext x y
        simp [rk1, Matrix.diagonal_apply, mul_comm]
    · have := hW.what₂ τ
      beta_reduce
      rw [h4 _ _ (hl2 τ ▸ (r2 τ).1), hl2, (r2 τ).2, (r1 τ).2, hc']
      omega
    · beta_reduce
      rw [cj_cj, h4 _ _ (r1 τ).1, (r1 τ).2, hc]
      omega
    · have e := scaleRoots_prod (Finset.univ.val.map fun j => ((χ j g : (Qbar l)ˣ) : Qbar l)) ((tw g : (Qbar l)ˣ) : Qbar l)
      rw [Multiset.map_map, Multiset.map_map] at e
      rw [mul_scaleRoots_of_noZeroDivisors, ← charpoly_smul _ (Units.ne_zero _)]
      exact congrArg₂ (· * ·) rfl e.symm
end Side
section Point
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame GlobalTheory.FrameAut
open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.L2.Col
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
set_option maxHeartbeats 1600000 in
theorem galois_at_place_of_automorphic_at_place (p1 : GlobalTheory.Published.ClozelCohomological) (p2 : GlobalTheory.Published.CohomologicalCsdTempered)
    (p3 : GlobalTheory.Published.HeckeLAdicCharacter) (p4 : GlobalTheory.Published.ChebotarevDegreeOne)
    (p6 : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (p7 : _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup)
    (p8 : GlobalTheory.Published.BhattScholzeCrystallineLattices) (p9 : GlobalTheory.Published.HeckeLAdicCharacterAbove) (p10 : GlobalTheory.Published.LocalLanglandsGL)
    {j : Fin D.R.m} {P : Par} {W : Wts D.what₂.Tau} (hD : Dict L j P W) (hN : NumOk P W) {w : HeightOneSpectrum (𝓞 D.what₂.LL)}
    (h : AutAt p j P W w) : GalAt p j P W w := by
  classical
  intro _ F R inc _ T
  obtain ⟨⟨hpl, hcof, hbl⟩, haut⟩ := h
  obtain ⟨hn, ht, ν, hν⟩ := blk_numbers p hD hN.1 (p.R.mu w)
  let Pl := {Q : (blk p j (p.R.mu w)).Pl // ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal}
  have hpt : ∀ (Q : Pl) (k : Fin P.Nr), ∃ i, R.ix i = (Q.1, (k : ℕ) + 1) := fun Q k =>
    (T.ix_range (Q.1, (k : ℕ) + 1)).2 ⟨Nat.le_add_left _ _, k.2, Q.2⟩
  choose pt hpt using hpt
  refine _root_.GlobalTheory.FrameGal.galois_side_of_compatible_systems _ p1 p2 p3 p4 p6 p7 p8 p9 p10 (GlobalTheory.DefiniteBC.host_unramified D.host) T.io T.half T.sh hN.1 hN.2.1
    hN.2.2.1 F _ pt (fun Q => labOf p j (p.R.mu w) Q.1) (hcof.subset fun v hv => ⟨hv.1, fun ⟨Q, h1, h2⟩ => hv.2 ⟨⟨Q, h1⟩, h2⟩⟩)
    (fun Q => ⟨(hpl Q.1).1, fun h => Q.2 ((hpl Q.1).2.2.2.1 h)⟩) (fun mu θ ha hθ => ?_) fun θ hθ Q => ?_
  · obtain ⟨π, h1, h2, h3, h4⟩ := haut F R inc T mu θ ha hθ
    refine ⟨π, h1, h2, h3, fun Q => ?_⟩
    obtain ⟨hu, σ, S, a, b, c⟩ := h4 Q.1
    refine ⟨hu, σ, S, a, b, fun k hk => ?_⟩
    rcases k with _ | k
    · rw [sysOf_zero, map_one, GlobalTheory.LFun.satEig]
      simp [Multiset.esymm]
    · have e := c (pt Q ⟨k, hk⟩) (by rw [hpt])
      rw [hpt] at e
      exact (congrArg T.io (sysOf_succ P.Nr pt θ Q ⟨k, hk⟩)).trans e
  · refine ⟨R.e0 (ν Q.1), ?_, ?_⟩
    · rw [T.liftFrame_embedding_base, hbl ν hν, (hpl Q.1).2.2.1, hn, ht]
    · rw [(hpl Q.1).2.2.1, ← ht]
      exact block_dvd hθ hn pt Q Q.1 (hpt Q) hν
end Point
end GlobalTheory.FrameGal
open Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie in
theorem GlobalTheory.FrameGal.galois_steinberg_local : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered → GlobalTheory.Published.HeckeLAdicCharacter →
    GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal →
    _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove →
    GlobalTheory.Published.LocalLanglandsGL → SmallSt → GlobalTheory.ExpTie.GalSt := by
  intro p1 p2 p3 p4 p6 p7 p8 p9 p10 hS
  refine Closed.imp (GlobalTheory.T.small_estimate_implies_frame_automorphy hS) fun Fm _ _ H => ?_
  obtain ⟨a, ha⟩ := H
  exact ⟨a, fun x hx hle i p hp hm j P W hD hN w hw hR =>
    _root_.GlobalTheory.FrameGal.galois_at_place_of_automorphic_at_place p p1 p2 p3 p4 p6 p7 p8 p9 p10 hD hN (ha x hx hle i p hp hm j P W hD hN w hw hR)⟩
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_frame_compatibility : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered → GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.LocalLanglandsGL → SmallSt → GlobalTheory.ExpTie.GalSt := by
  first | exact @_root_.GlobalTheory.FrameGal.galois_steinberg_local | exact _root_.GlobalTheory.FrameGal.galois_steinberg_local | (intros; apply _root_.GlobalTheory.FrameGal.galois_steinberg_local <;> assumption)
end
end
