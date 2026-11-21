import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DenseRangeUnitsR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AutBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.JumpsOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsCalcP
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.UnramifiedAlgebraicWeights
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FlagPol
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CompatAtLQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.WeilDeligneFrobeniusEigenvalueOfFullFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.ExistsCuspidalSatakeAtPrimeToLevelOfNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewformNormCoeffPrimeLeOfNotDvdLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.AdmissibleTwistByDet

section
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp Formalism.WeaklyAdmissibleFiltrations
open scoped Matrix

open private UpperTheory.V.Af.infOf_of_weights UpperTheory.V.Af.exists_over from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelQ
open private UpperTheory.V.Af.NewformAutomorphy.ev_not_mem UpperTheory.V.Af.NewformAutomorphy.normV_eq UpperTheory.V.Af.NewformAutomorphy.scale_charpoly
  UpperTheory.V.Af.NewformAutomorphy.ss_of_tw from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Ord2.AutNewformCopy

open UpperTheory.V UpperTheory.V.Af

private theorem flag_stable {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) (D N N' : Subgroup Γ) (hN : N ≤ N')
    (hc : ∀ d ∈ D, ∀ s ∈ N, d⁻¹ * s * d ∈ N) (χ : Fin 2 → Γ →* kˣ) (hne : ∃ s ∈ N, χ 0 s ≠ χ 1 s)
    (h : IsFlagOn r N' fun i => (χ i).comp N'.subtype) :
    ∃ κ, IsFlagOn r D κ ∧ ∀ i (s : ↥D), (s : Γ) ∈ N → κ i s = χ i s := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨s0, hs0, hne⟩ := hne
  let M : Γ →* GL (Fin 2) k := (MulAut.conj g).toMonoidHom.comp r
  have hM : ∀ s, M s = g * r s * g⁻¹ := fun _ => rfl
  have h1 : ∀ s ∈ N, M s 1 0 = 0 := fun s hs => (hg ⟨s, hN hs⟩).1 1 0 (by decide)
  have h2 : ∀ s ∈ N, ∀ i, M s i i = χ i s := fun s hs i => (hg ⟨s, hN hs⟩).2 i
  have hmul : ∀ s t i j, M (s * t) i j = M s i 0 * M t 0 j + M s i 1 * M t 1 j := fun s t i j => by
    rw [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h3 : ∀ d ∈ D, M d 1 0 = 0 := fun d hd => by
    have e : s0 * d = d * (d⁻¹ * s0 * d) := by group
    have e2 := hmul s0 d 1 0
    have e3 : χ 0 (d⁻¹ * s0 * d) = χ 0 s0 := by rw [map_mul, map_mul, map_inv, mul_right_comm]; simp
    rw [e, hmul, h1 _ (hc d hd s0 hs0), h1 _ hs0, h2 _ (hc d hd s0 hs0), h2 _ hs0, e3] at e2
    have : (χ 0 s0 : k) - χ 1 s0 ≠ 0 := sub_ne_zero.2 fun h => hne (Units.ext h)
    apply mul_left_cancel₀ this
    linear_combination e2
  refine ⟨fun i => MonoidHom.toHomUnits
    { toFun := fun s => M s i i
      map_one' := by simp
      map_mul' := fun s t => by
        rw [Subgroup.coe_mul, hmul]
        fin_cases i
        · simp [h3 _ t.2]
        · simp [h3 _ s.2] }, ⟨g, fun s => ⟨fun i j hij => ?_, fun i => rfl⟩⟩, fun i s hs => Units.ext (h2 _ hs i)⟩
  fin_cases i <;> fin_cases j
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact h3 _ s.2
  · exact absurd hij (by decide)

private theorem dual_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, fun s => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

private theorem det_flag {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) (H : Subgroup Γ) (κ : Fin 2 → ↥H →* kˣ)
    (h : IsFlagOn r H κ) (s : ↥H) : Matrix.GeneralLinearGroup.det (r s) = κ 0 s * κ 1 s := by
  obtain ⟨g, hg⟩ := h
  have : Matrix.GeneralLinearGroup.det (r s) = Matrix.GeneralLinearGroup.det (g * r s * g⁻¹) := by
    rw [map_mul, map_mul, map_inv, mul_right_comm]; simp
  rw [this]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, (hg s).1 1 0 (by decide), (hg s).2, (hg s).2]
  simp

private theorem ss_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep r) : IsSSRep (tw r χ) := by
  refine UpperTheory.V.Af.NewformAutomorphy.ss_of_tw _ χ⁻¹ ?_
  convert h
  ext s : 2
  rw [tw_val, tw_val, smul_smul]
  simp

private theorem place_of {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {p : ℕ} [hp : Fact p.Prime]
    {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    IsPlaceOver A w := by
  obtain ⟨p1, p2, p3, -⟩ := UpperTheory.V.Base.places ℚ Ω p A
  obtain ⟨v, hv⟩ := p1 fun h => (p2 h).2 hA
  have hpr : Prime (p : 𝓞 ℚ) := by
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp.out)
  have hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  have e : v = w := HeightOneSpectrum.ext
    ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 ((p3 v hv).1 hA))).symm.trans
      (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))
  exact e ▸ hv

private theorem cont_cycBar (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)

private theorem cyc_inf {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]
    {A : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Ine (F := ℚ) A, ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l s ^ k ≠ 1 := by
  have hu : IsUnit ((l + 1 : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
  obtain ⟨s, hs, he⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  refine ⟨s, hs, fun k hk h => ?_⟩
  have h2 : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = (l + 1 : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [he, hu.unit_spec, map_natCast, map_natCast]
  have h3 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, h2, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h3
  have := hl.out.pos
  omega

private theorem inf_char (P : HypothesesH) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) {e : ℕ} (he : 1 ≤ e) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hW : Continuous W)
    (π : TR.CuspSub ℚ 2) (hreg : π.IsRegAlg) (hatt : AttR ι W π)
    {B : ValuationSubring Ω} (hB : B.valuation (l : Ω) < 1) (H : Subgroup (G ℚ Ω)) (hH : IsOpen (H : Set (G ℚ Ω)))
    (hfl : IsFlagOn W (H ⊓ Ine (F := ℚ) B)
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H ⊓ Ine (F := ℚ) B).subtype)) :
    (∃ wt HT, Published.IsGalRepOfR π ι W wt HT) ∧ ∀ v, π.HasInfChar v (infOf ![(e : ℤ), -(e : ℤ)]) := by
  have : IsGalois ℚ Ω := {}
  have := Subgroup.quotient_finite_of_isOpen H hH
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : H.normalCore.Normal := H.normalCore_normal
  have hH' : IsOpen (H.normalCore : Set (G ℚ Ω)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed (H.isClosed_of_isOpen hH))
  have hk : H.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : ∀ s ∈ Ine (F := ℚ) B, s ^ H.normalCore.index ∈ H.normalCore ⊓ Ine (F := ℚ) B := fun s hs =>
    ⟨@Subgroup.pow_index_mem _ _ _ hn s, Subgroup.pow_mem _ hs _⟩
  have hle : H.normalCore ⊓ Ine (F := ℚ) B ≤ H ⊓ Ine (F := ℚ) B := inf_le_inf_right _ H.normalCore_le
  have halg : IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W * cycBar ℚ Ω l ^ (((2 : ℕ) : ℤ) - 1)) := by
    refine (algOfCyc P ℚ Ω l ι).1 _ ?_ fun w hw => ⟨B, place_of hB hw, ((2 : ℕ) : ℤ) - 1, H.normalCore.index,
      Nat.pos_of_ne_zero hk, fun s hs => ?_⟩
    · have h1 : Continuous fun s => Matrix.GeneralLinearGroup.det (W s) * cycBar ℚ Ω l s ^ (((2 : ℕ) : ℤ) - 1) :=
        (Matrix.GeneralLinearGroup.continuous_det.comp hW).mul ((continuous_zpow _).comp (cont_cycBar ℚ Ω l))
      exact h1
    · have h1 := det_flag W _ _ hfl ⟨_, hle (hpow s hs)⟩
      rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one,
        ← map_pow, MonoidHom.comp_apply, h1]
      change cycBar ℚ Ω l _ ^ (e : ℤ) * cycBar ℚ Ω l _ ^ (-(e : ℤ)) = 1
      rw [← zpow_add, add_neg_cancel, zpow_zero]
  obtain ⟨χ, hχ⟩ := halg
  have hsd := (selfDualR P ℚ Ω l ι 2 (by omega) W π hatt _ χ (dual_det W) hχ).1
  obtain ⟨-, wt, HT, -, -, hall⟩ := exR P ℚ Ω l ι 2 (by omega) π χ hreg ⟨fun v v' => by rw [Subsingleton.elim v v'], hsd⟩
  have hG := hall W hW hatt
  refine ⟨⟨wt, HT, hG⟩, fun v => ?_⟩
  obtain ⟨κ, hκ, hI⟩ := flag_stable W (Dec (F := ℚ) B) _ _ hle
    (fun d hd s hs => ⟨hn.conj_mem' s hs.1 d,
      by simpa using conj_mem_Ine ((Dec (F := ℚ) B).inv_mem hd) hs.2⟩)
    (fun i => (cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) (by
      obtain ⟨s, hs, h⟩ := cyc_inf hB
      refine ⟨_, hpow s hs, fun h1 => h (H.normalCore.index * (e + e)) (mul_ne_zero hk (by omega)) ?_⟩
      rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, map_pow] at h1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast] at h1
      rw [pow_mul, pow_add]
      exact mul_eq_one_iff_eq_inv.2 h1) hfl
  obtain ⟨w, hw⟩ := UpperTheory.V.Af.exists_over ℚ l
  have h := place_of hB hw
  obtain ⟨j, L0, hj, hBw⟩ := GlobalTheory.PlaceBridge.exists_locBridge l ℚ Ω w B hw h
  obtain ⟨Bw, hBj, -⟩ := hBw L0 le_rfl
  have hInd : Induces Bw := fun x => by rw [hBj]; exact hj x
  have hJ := (hG.above _ _ (Loc.tiedP l) w B h _ Bw hInd).2.1 (Bw.j.comp (algebraMap ℚ Ω)) Bw.Kw (AlgHom.id _ _)
    fun _ => rfl
  have hH2 := jumpsOpen ![(e : ℤ), -(e : ℤ)] W hW B Bw hInd κ _ hH' hκ hI _ _ hJ
  obtain ⟨μ, hμ, -⟩ := hreg v
  have hW := hG.weights (Bw.j.comp (algebraMap ℚ Ω)) μ (by rwa [Subsingleton.elim (InfinitePlace.mk _) v])
  rw [hH2] at hW
  rwa [UpperTheory.V.Af.infOf_of_weights _ μ hW] at hμ

private theorem charpoly_smul {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : M.charpoly.map φ = (B.map fun b => X - C b).prod) :
    (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod := by
  have hc' : φ c ≠ 0 := by simpa using hc
  have := UpperTheory.V.Af.NewformAutomorphy.scale_charpoly φ (c • M) c⁻¹ (inv_ne_zero hc) (B.map (φ c * ·)) (by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, h, Multiset.map_map]
    simp only [Function.comp_def, map_inv₀, inv_mul_cancel_left₀ hc'])
  rwa [Multiset.map_map] at this

end GlobalTheory.Ord2.AutNewformCopy

open UpperTheory.V UpperTheory.V.Af GlobalTheory.Ord2.AutNewformCopy in

theorem GlobalTheory.Ord2.autNewformOfKnownTheorems :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Published.RepNewform → UpperTheory.V.Pr.AutNewform := by
  rintro P hN Ω _ _ _ l hl ι e he W hW - ⟨π, hreg, hatt⟩ B hB H hH hfl
  obtain ⟨⟨wt, HT, hG⟩, hinf⟩ := inf_char P ι he W hW π hreg hatt hB H hH hfl
  obtain ⟨f, hf⟩ := hN (2 * e + 1) (by omega) e π fun v => by
    convert hinf v using 1
    simp only [infOf, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Multiset.insert_eq_cons, ← Multiset.cons_coe,
      Multiset.coe_nil, Multiset.cons_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    congr 2 <;> push_cast <;> ring
  have hfrob : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → ∀ B, π.HasSat w B →
      FrobEig ι W w (algSat 2 (normV w) B) := by
    intro w hw B hB
    obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P.toClassicalTheorems ℚ 2 π w
    exact satFrob P.toClassicalTheorems ℚ Ω l ι 2 W hW w hw σ B
      (((satLoc P.toClassicalTheorems ℚ 2 w σ).2 _ π.finPart (hiso σ hσ) B).1 hB) fun A h rc hrc => hG.away w hw A h rc hrc σ hσ
  refine ⟨f, ss_tw _ _ hatt.1, ?_⟩
  filter_upwards [UpperTheory.V.Af.NewformAutomorphy.ev_not_mem l hl.out.ne_zero,
    UpperTheory.V.Af.NewformAutomorphy.ev_not_mem f.M f.pos.ne'] with w hwl hwM A hA
  have hM : ¬ normV w ∣ f.M := by
    rintro ⟨c, hc⟩
    apply hwM
    rw [hc, Nat.cast_mul, UpperTheory.V.Af.NewformAutomorphy.normV_eq]
    exact w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)
  obtain ⟨S, hS, hpoly⟩ := hf w hM
  obtain ⟨h1, h2⟩ := hfrob w hwl S hS A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h3 : cycZ ℚ Ω l s = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
      rw [cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
      simp
    apply Units.ext
    rw [tw_val, h1 s hs, MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h3, map_one, one_zpow, Units.val_one, one_smul]
  · have h3 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
      change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
      rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
    have h4 : ι.toRingHom (((cycBar ℚ Ω l ^ (-(e : ℤ))) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (e : ℤ) := by
      rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h3, map_zpow₀,
        map_inv₀, map_natCast, inv_zpow', neg_neg]
    rw [tw_val, charpoly_smul _ _ _ (Units.ne_zero _) _ (h2 σ hσ), h4, hpoly]

end
end

section
section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.TwNewform

instance (priority := high + 1) torsionFree (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

theorem tw_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (a b : Γ →* kˣ) :
    tw (tw r a) b = tw r (b * a) := by
  ext1 s
  apply Units.ext
  simp only [tw_val, smul_smul, MonoidHom.mul_apply, Units.val_mul]

theorem kills_dvd {Ω : Type} [Field Ω] [Algebra ℚ Ω] {C : Type} [Monoid C] {M N : ℕ} {χ : G ℚ Ω →* C}
    (h : KillsMu M χ) (hMN : M ∣ N) : KillsMu N χ := fun s hs => h s fun ζ hζ => hs ζ (by
  obtain ⟨c, rfl⟩ := hMN
  rw [pow_mul, hζ, one_pow])

theorem kills_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {C : Type} [CommMonoid C] {M : ℕ} {χ ψ : G ℚ Ω →* C}
    (h : KillsMu M χ) (h' : KillsMu M ψ) : KillsMu M (χ * ψ) := fun s hs => by
  rw [MonoidHom.mul_apply, h s hs, h' s hs, one_mul]

theorem kills_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {C : Type} [CommGroup C] {M : ℕ} {χ : G ℚ Ω →* C}
    (h : KillsMu M χ) : KillsMu M χ⁻¹ := fun s hs => by
  rw [MonoidHom.inv_apply, h s hs, inv_one]

theorem kills_open {Ω C : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Group C] {M : ℕ} (hM : 1 ≤ M)
    {φ : G ℚ Ω →* C} (hφ : KillsMu M φ) : IsOpen (φ.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ s fun ζ hζ => hs ζ hζ

theorem cont_kills {Ω C : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Group C] [TopologicalSpace C]
    [IsTopologicalGroup C] {M : ℕ} (hM : 1 ≤ M) {φ : G ℚ Ω →* C} (hφ : KillsMu M φ) : Continuous φ := by
  refine continuous_of_continuousAt_one φ ?_
  refine (continuousAt_const (y := (1 : C))).congr ?_
  filter_upwards [(kills_open hM hφ).mem_nhds φ.ker.one_mem] with s hs
  exact hs.symm

theorem kills_pow {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {C : Type} [CommGroup C] {M : ℕ} (hM : 1 ≤ M)
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

theorem irr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (H : Subgroup Γ) (φ : Γ →* kˣ)
    (h : IsIrr (r.comp H.subtype)) : IsIrr (tw r φ) := by
  obtain ⟨hne, -, hmin⟩ := h
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W' _ hW' => hmin W' le_top fun s v hv => ?_⟩
  have e : ((r.comp H.subtype) s : Matrix (Fin n) (Fin n) k).mulVec v =
      ((φ s)⁻¹ : kˣ).val • (tw r φ (s : Γ) : Matrix (Fin n) (Fin n) k).mulVec v := by
    rw [tw_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rfl
  rw [e]
  exact W'.smul_mem _ (hW' _ v hv)

end GlobalTheory.Ord2.TwNewform

namespace GlobalTheory.Ord2

open GlobalTheory.Ord2.TwNewform in

theorem newform_twist_of_admissible (P : Af.HypothesesH) (hR : Published.RepNewform) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l) (he : 1 ≤ e) (hA : admitted ι e W) (M : ℕ)
    (φ : G ℚ Ω →* (Qbar l)ˣ) (hM : 1 ≤ M) (hφ : KillsMu M φ) :
    ∃ g : Newform (2 * e + 1), g.Att ι (tw (tw W φ) (cycBar ℚ Ω l ^ (-(e : ℤ)))) := by
  obtain ⟨f, M', φ', hM', hφ', hf⟩ := hA.modular

  have h1 : IsAutR ι (tw W φ') :=
    newformAutR P.toClassicalTheorems (2 * e + 1) (by omega) f l Ω ι (tw W φ') (-(e : ℤ)) (by rwa [tw_tw])

  set κ : G ℚ Ω →* (Qbar l)ˣ := φ * φ'⁻¹ with hκ
  have hMM : 1 ≤ M * M' := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hκM : KillsMu (M * M') κ :=
    kills_mul (kills_dvd hφ (dvd_mul_right M M')) (kills_inv (kills_dvd hφ' (dvd_mul_left M' M)))
  obtain ⟨k, hk, hpow⟩ := kills_pow hMM hκM
  have halg : IsAlgChar ι κ := by
    refine (algOfCyc P ℚ Ω l ι).1 κ (cont_kills hMM hκM) fun w _ => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    exact ⟨A, hA, 0, k, hk, fun s _ => by rw [neg_zero, zpow_zero, mul_one, hpow]⟩
  have h2 : IsAut ι (tw (tw W φ') κ) :=
    twi P ℚ Ω l ι 2 (tw W φ') κ ((autBridge P ℚ Ω l ι 2 (tw W φ')).1.2 h1) halg
  have e1 : tw (tw W φ') κ = tw W φ := by
    rw [tw_tw, hκ, inv_mul_cancel_right]
  rw [e1] at h2
  have h3 : IsAutR ι (tw W φ) := (autBridge P ℚ Ω l ι 2 (tw W φ)).1.1 h2

  have hc : Continuous (tw W φ) := by
    have hφc : Continuous φ := cont_kills hM hφ
    refine cont_units _ ?_
    simp only [tw_val]
    exact (Units.continuous_val.comp hφc).smul (Units.continuous_val.comp hA.cont)
  have hirr : IsIrr (tw W φ) := irr_tw W (H0g W) φ hA.irr

  obtain ⟨A, χ, κ', hAl, hχ, ⟨g, hg⟩, -, hin⟩ := hA.flag
  obtain ⟨v, hAv, hlv⟩ := hAl
  have hval : A.valuation (l : Ω) < 1 := by
    have := (hAv ((l : ℕ) : 𝓞 ℚ)).2 hlv
    simpa using this
  have hχφ : KillsMu (l * M) (χ * φ) :=
    kills_mul (kills_dvd hχ (dvd_mul_right l M)) (kills_dvd hφ (dvd_mul_left M l))
  have hlM : 1 ≤ l * M := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Fact.out : l.Prime).ne_zero (by omega))
  refine autNewformOfKnownTheorems P hR Ω l ι e he (tw W φ) hc hirr h3 A hval (χ * φ).ker (kills_open hlM hχφ) ⟨g, fun s => ?_⟩
  have hsD : (s : G ℚ Ω) ∈ Dec (F := ℚ) A := Ine_le_Dec A s.2.2
  have hsk : χ s * φ s = 1 := s.2.1
  have hmat : (g * tw W φ (s : G ℚ Ω) * g⁻¹).val = (φ (s : G ℚ Ω) : Qbar l) • (g * W (s : G ℚ Ω) * g⁻¹).val := by
    simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]
  have hlow : ∀ i j : Fin 2, j < i → (g * W (s : G ℚ Ω) * g⁻¹).val i j = 0 := (hg ⟨s, hsD⟩).1
  have hdiag : ∀ i : Fin 2, (g * W (s : G ℚ Ω) * g⁻¹).val i i = (κ' i ⟨s, hsD⟩ : Qbar l) := (hg ⟨s, hsD⟩).2
  obtain ⟨h0, h1'⟩ := hin ⟨s, hsD⟩ s.2.2
  have hsk' : (χ s : Qbar l) * (φ s : Qbar l) = 1 := by rw [← Units.val_mul, hsk, Units.val_one]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hmat, Matrix.smul_apply, smul_eq_mul, hlow i j hij, mul_zero]
  · rw [hmat, Matrix.smul_apply, smul_eq_mul, hdiag i]
    fin_cases i
    · show (φ s : Qbar l) * (κ' 0 ⟨s, hsD⟩ : Qbar l) = ((cycBar ℚ Ω l (s : G ℚ Ω) ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l)
      rw [h0, Units.val_mul]
      linear_combination ((cycBar ℚ Ω l (s : G ℚ Ω) ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l) * hsk'
    · show (φ s : Qbar l) * (κ' 1 ⟨s, hsD⟩ : Qbar l) = ((cycBar ℚ Ω l (s : G ℚ Ω) ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l)
      rw [h1', Units.val_mul]
      linear_combination ((cycBar ℚ Ω l (s : G ℚ Ω) ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l) * hsk'

theorem twNewform : Af.HypothesesH → Published.RepNewform → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → ∀ (M : ℕ)
    (φ : G ℚ Ω →* (Qbar l)ˣ), 1 ≤ M → KillsMu M φ →
    ∃ g : Newform (2 * e + 1), g.Att ι (tw (tw W φ) (cycBar ℚ Ω l ^ (-(e : ℤ)))) := by
  intro P hR l _ Ω _ inst _ ι e W _ he hA M φ hM hφ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact newform_twist_of_admissible P hR l Ω ι e W he hA M φ hM hφ

end GlobalTheory.Ord2

end

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_of_admissible_twist : Af.HypothesesH → Published.RepNewform → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → ∀ (M : ℕ) (φ : G ℚ Ω →* (Qbar l)ˣ), 1 ≤ M → KillsMu M φ → ∃ g : Newform (2 * e + 1), g.Att ι (tw (tw W φ) (cycBar ℚ Ω l ^ (-(e : ℤ)))) := by
  first | exact @GlobalTheory.Ord2.twNewform | exact GlobalTheory.Ord2.twNewform | (intros; apply GlobalTheory.Ord2.twNewform <;> assumption)

end
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.UnramAtL

theorem dualTw_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, fun s => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem place_unique (l : ℕ) [hl : Fact l.Prime] {v w : Pl} (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  have hpr : Prime (l : 𝓞 ℚ) := by
    have e : (l : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (l : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hl.out)
  have hm : (Ideal.span {(l : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  exact HeightOneSpectrum.ext
    ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv)).symm.trans
      (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))

end GlobalTheory.Ord2.UnramAtL

open GlobalTheory.Ord2.UnramAtL in

theorem GlobalTheory.Ord2.unram_at_l : Af.Hypotheses₂ → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (V : R2 Ω l) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ) (g : Newform (2 * e + 1)), l ≠ 2 → 1 ≤ e → Continuous V → IsIrr V → (∃ M : ℕ, 1 ≤ M ∧ LevelAway l M V) → (∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt V)) → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ → (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) → g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ∀ π : TR.CuspSub ℚ 2, π.IsRegAlg → AttR ι V π → ∀ w : Pl, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → ∃ Bs, π.HasSat w Bs := by
  intro P l _ Ω _ _ _ ι e V A κ g hl he hcont hirr hAway hKill hOver hfl hκ _ π hreg hatt w hw
  obtain ⟨M, hM, haway⟩ := hAway
  obtain ⟨M', hM', hkill⟩ := hKill
  obtain ⟨v, hAv, hlv⟩ := hOver
  obtain rfl : w = v := place_unique l hw hlv
  have hAl : A.valuation (l : Ω) < 1 := by simpa using (hAv _).2 hlv
  let m : Fin 2 → ℤ := ![(e : ℤ), -(e : ℤ)]
  have hκm : ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      κ i s = cycBar ℚ Ω l s ^ m i * (1 : G ℚ Ω →* (Qbar l)ˣ) s := by
    intro i s hs
    fin_cases i
    · simpa [m] using (hκ s hs).1
    · simpa [m] using (hκ s hs).2
  have hor : ∀ i j, κ i ≠ κ j * (cycBar ℚ Ω l).comp (Dec (F := ℚ) A).subtype := by
    intro i j hij
    obtain ⟨s, hs, hne⟩ := UpperTheory.V.Ws.Pt.cycIne ℚ Ω l A hAl (m i - m j - 1) (by
      fin_cases i <;> fin_cases j <;> simp [m] <;> omega)
    have h1 := congrArg (fun f => f ⟨s, Ine_le_Dec A hs⟩) hij
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1
    rw [hκm i _ hs, hκm j _ hs] at h1
    apply hne
    simp only [MonoidHom.one_apply, mul_one] at h1
    rw [zpow_sub, zpow_sub, h1, zpow_one]
    group
  have hlev : Level l M m V := ⟨hcont, haway, fun w' hw' => by
    obtain rfl : w = w' := place_unique l hlv hw'
    exact ⟨A, hAv, fun _ => 1, κ, fun _ _ _ => rfl, hfl, hκm, Or.inl hor⟩⟩
  have hdual : ∃ θ, IsCycWt l 0 θ ∧ DualTw V θ :=
    ⟨dt V, ⟨M', dt V, hM', hkill, by simp⟩, dualTw_det V⟩
  have hanti : StrictAnti m := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [m] at hij ⊢ <;> omega
  have hL : GlobalTheory.Published.LocalLanglandsGL :=
    GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein P.litN.loc.llc P.litN.loc.conv P.litN.loc.dzc P.litN.loc.dzi
      P.litN.loc.brauer P.litN.loc.chev P.litN.aut.art P.litN.loc.exh P.litN.loc.multi P.litN.loc.cos P.litN.loc.zel
      P.litN.loc.geo P.litN.loc.bz
  obtain ⟨rc, hrc, -⟩ := hL.1 ℚ Ω A w hAv
  obtain ⟨j, L0, hj, hB⟩ := GlobalTheory.PlaceBridge.exists_locBridge l ℚ Ω w A hw hAv
  obtain ⟨Bw, hBj, -⟩ := hB L0 le_rfl
  have hI : GlobalTheory.Pst.Induces Bw := fun x => by rw [hBj]; exact hj x
  obtain ⟨c1, c2⟩ := compatAtLQ P 2 le_rfl 0 l hl Ω ι V π hcont hirr M m hM hanti hlev hdual hreg hatt w A hAv _ Bw hI
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P ℚ 2 π w
  obtain ⟨x, hx0, hx⟩ := Lev.fixedAll P ℚ Ω l ι 2 1 le_rfl m V hcont w A hAv _ Bw hI κ
    ⟨fun _ => 1, fun _ _ _ => rfl, hfl, hκm⟩ c1 rc hrc σ
    (fun ⟨μ, hμ⟩ => c2 σ hσ rc hrc (Or.inl ((Lev.ssCalc ℚ Ω A w hAv).1 2 _ μ hμ))) (Or.inr (Or.inl hor))
  have hK : HasFixed σ.ρ (GlobalTheory.LFun.KGL w 2) := ⟨x, hx0, fun u hu => hx u (locGL_mem_KLev 2 w (by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top) hu)⟩
  obtain ⟨B, hB⟩ := (satLoc P ℚ 2 w σ).1 hK
  exact ⟨B, ((satLoc P ℚ 2 w σ).2 _ π.finPart (hiso σ hσ) B).2 hB⟩

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_flag_local_of_irreducible : Af.Hypotheses₂ → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (V : R2 Ω l) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ) (g : Newform (2 * e + 1)), l ≠ 2 → 1 ≤ e → Continuous V → IsIrr V → (∃ M : ℕ, 1 ≤ M ∧ LevelAway l M V) → (∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt V)) → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ → (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) → g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ∀ π : TR.CuspSub ℚ 2, π.IsRegAlg → AttR ι V π → ∀ w : Pl, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → ∃ Bs, π.HasSat w Bs := by
  first | exact @GlobalTheory.Ord2.unram_at_l | exact GlobalTheory.Ord2.unram_at_l | (intros; apply GlobalTheory.Ord2.unram_at_l <;> assumption)

end
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FrobRec

open Polynomial

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem rec_algNorm_diag {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
  obtain ⟨hu, -⟩ := GlobalTheory.RecLaws.rec_hasSatGL H σ B hB
  obtain ⟨α, hα⟩ := ParLaws.exists_hasSatake_of_unr H hu
  refine ⟨α, hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα), ?_⟩
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    ParLaws.rec_eq_diag H hα
  rw [rec_algNorm H, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]

theorem val_inv_eq (n : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((1 - (n : ℝ)) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (a : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, mul_comm]
  congr 2
  push_cast
  ring

end GlobalTheory.FrobRec

open GlobalTheory.FrobRec Polynomial in

theorem GlobalTheory.recFrob_root_inv_algSat : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
    ∀ φ : ↥(Weil h), deg φ = 1 → ∀ z : ℂ, (WD.charPol (rc (algNorm σ)) φ).IsRoot z →
      ∃ b ∈ algSat n (normV w) B, z * b = 1 := by
  intro E Ω _ _ _ _ _ A w h rc H n σ B hB φ hd z hz
  obtain ⟨α, rfl, e⟩ := rec_algNorm_diag H σ B hB
  rw [e, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hd] at hz
  rw [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hz
  obtain ⟨i, -, hi⟩ := hz
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, zpow_one] at hi
  refine ⟨((((α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ), ?_, ?_⟩
  · rw [val_inv_eq, algSat, Multiset.mem_map]
    refine ⟨(α i : ℂ), ?_, rfl⟩
    simp only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, Multiset.map_map]
    exact Multiset.mem_map_of_mem (fun j => ((α j : ℂˣ) : ℂ)) (Finset.mem_univ i)
  · rw [hi, zpow_neg_one, mul_inv_cancel₀ (Units.ne_zero _)]

end

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_roots_local_correspondence : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
    ∀ φ : ↥(Weil h), deg φ = 1 → ∀ z : ℂ, (WD.charPol (rc (algNorm σ)) φ).IsRoot z →
      ∃ b ∈ algSat n (normV w) B, z * b = 1 := by
  first | exact @GlobalTheory.recFrob_root_inv_algSat | exact GlobalTheory.recFrob_root_inv_algSat | (intros; apply GlobalTheory.recFrob_root_inv_algSat <;> assumption)

end
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Ord2.LevelOfOrd

theorem asIdeal_eq_span (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (h : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    v.asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} := by
  have hp : Prime ((l : ℕ) : 𝓞 ℚ) := by
    rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
    exact Nat.prime_iff_prime_int.1 Fact.out
  exact ((((Ideal.span_singleton_prime hp.ne_zero).2 hp).isMaximal
    (mt Ideal.span_singleton_eq_bot.1 hp.ne_zero)).eq_of_le v.isPrime.ne_top
    ((Ideal.span_singleton_le_iff_mem _).2 h)).symm

theorem main : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e M : ℕ)
    (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ),
    1 ≤ e → 1 ≤ M → Continuous V → LevelAway l M V → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ →
    (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) →
    Level l M ![(e : ℤ), -(e : ℤ)] V := by
  intro l _ Ω _ _ _ e M V A κ he _ hcont haway hA hflag hine
  obtain ⟨v, hvA, hlv⟩ := hA
  have hval : A.valuation (l : Ω) < 1 := by
    have := (hvA ((l : ℕ) : 𝓞 ℚ)).2 hlv
    simpa using this
  let m : Fin 2 → ℤ := ![(e : ℤ), -(e : ℤ)]
  have hm : ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ i s = cycBar ℚ Ω l s ^ m i := by
    intro i s hs
    fin_cases i
    · exact (hine s hs).1
    · exact (hine s hs).2
  refine ⟨hcont, haway, ?_⟩
  intro w hw
  have hwv : w = v := HeightOneSpectrum.ext ((asIdeal_eq_span l w hw).trans (asIdeal_eq_span l v hlv).symm)
  subst hwv
  refine ⟨A, hvA, fun _ => 1, κ, fun i s _ => rfl, hflag, fun i s hs => by rw [hm i s hs]; exact (mul_one _).symm, Or.inl ?_⟩
  intro i j h
  have hn : m i - m j - 1 ≠ 0 := by
    have : (1 : ℤ) ≤ e := by exact_mod_cast he
    fin_cases i <;> fin_cases j <;> simp [m] <;> omega
  obtain ⟨g, hg, hgn⟩ := UpperTheory.V.Ws.Pt.cycIne ℚ Ω l A hval _ hn
  apply hgn
  have hD : g ∈ Dec (F := ℚ) A := Ine_le_Dec A hg
  have h1 := DFunLike.congr_fun h ⟨g, hD⟩
  rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hm i ⟨g, hD⟩ hg, hm j ⟨g, hD⟩ hg] at h1
  change cycBar ℚ Ω l g ^ m i = cycBar ℚ Ω l g ^ m j * cycBar ℚ Ω l g at h1
  rw [sub_sub, zpow_sub, zpow_add_one, ← h1, mul_inv_cancel]

end GlobalTheory.Ord2.LevelOfOrd

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_flag_inertia_weights : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e M : ℕ)
    (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ),
    1 ≤ e → 1 ≤ M → Continuous V → LevelAway l M V → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ →
    (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) →
    Level l M ![(e : ℤ), -(e : ℤ)] V := by
  first | exact @GlobalTheory.Ord2.LevelOfOrd.main | exact GlobalTheory.Ord2.LevelOfOrd.main | (intros; apply GlobalTheory.Ord2.LevelOfOrd.main <;> assumption)

end
end

section
section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FrobHecke

theorem normV_rat {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
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

theorem dualTw_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], ?_, ?_⟩, fun s => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two]
  · have e : (r s : Matrix (Fin 2) (Fin 2) k) = !![(r s : Matrix (Fin 2) (Fin 2) k) 0 0, (r s : Matrix (Fin 2) (Fin 2) k) 0 1;
        (r s : Matrix (Fin 2) (Fin 2) k) 1 0, (r s : Matrix (Fin 2) (Fin 2) k) 1 1] := Matrix.eta_fin_two _
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, Matrix.coe_units_inv]
    rw [e, Matrix.det_fin_two_of]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem frobValue_isRoot_heckePoly : Af.Hypotheses₂ → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (V : R2 Ω l) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ) (g : Newform (2 * e + 1)), l ≠ 2 → 1 ≤ e → Continuous V → IsIrr V → (∃ M : ℕ, 1 ≤ M ∧ LevelAway l M V) → (∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt V)) → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ → (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) → g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ¬ l ∣ g.M → ∀ σ : ↥(Dec (F := ℚ) A), IsFrob A l (σ : G ℚ Ω) → ∃ α : ℂ, (g.heckePoly l).IsRoot α ∧ (α = ι ((κ 0 σ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l) ∨ α⁻¹ = ι ((κ 0 σ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l)) := by
  intro P l _ Ω _ _ _ ι e V A κ g hl he hc hirr hway hdet hA hfl hI hatt hgM σ hσ
  obtain ⟨M, hM, haway⟩ := hway
  obtain ⟨M', hM', hdet⟩ := hdet
  obtain ⟨π, hreg, hattR, hsat⟩ := GlobalTheory.T.exists_cuspidal_satake_at_prime_to_level_of_newform P e g l Ω ι V he hatt hgM
  have hlev := GlobalTheory.T.ordinary_flag_inertia_weights l Ω e M V A κ he hM hc haway hA hfl hI
  obtain ⟨v, hv, hlv⟩ := hA
  have hnv : normV v = l := normV_rat (Fact.out) v hlv
  have hdual : ∃ θ, IsCycWt l 0 θ ∧ DualTw V θ :=
    ⟨dt V, ⟨M', dt V, hM', hdet, by rw [zpow_zero, one_mul]⟩, dualTw_det V⟩
  obtain ⟨j, L0, hj0, hL⟩ := GlobalTheory.PlaceBridge.exists_locBridge l ℚ Ω v A hlv hv
  obtain ⟨Bw, hB, -⟩ := hL L0 le_rfl
  have hj : Induces Bw := fun x => by rw [hB]; exact hj0 x
  have hm : StrictAnti ![(e : ℤ), -(e : ℤ)] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all <;> omega
  obtain ⟨hpst, hcomp⟩ := compatAtLQ P 2 le_rfl 0 l hl Ω ι V π hc hirr M ![(e : ℤ), -(e : ℤ)] hM hm hlev hdual hreg
    hattR v A hv _ Bw hj
  obtain ⟨B, hB, hpoly⟩ := hsat v hlv
  obtain ⟨⟨τ, hτ⟩, hiso⟩ := locCompR P ℚ 2 π v
  have hBτ := ((satLoc P ℚ 2 v τ).2 _ π.finPart (hiso τ hτ) B).1 hB
  have L := P.litN.loc
  obtain ⟨rc, hrc⟩ := L.llc ℚ Ω A v hv
  have hrec : IsRec hv rc := GlobalTheory.T.rec_of_rec_literal L.dzc L.dzi L.exh L.multi L.cos L.zel L.geo L.bz ℚ Ω A v hv rc hrc
  have heq := hcomp τ hτ rc hrec
  have hσ' : IsFrob A (normV v) (σ : G ℚ Ω) := by rw [hnv]; exact hσ
  let φ : ↥(Weil hv) := ⟨σ, mem_Weil_of_isFrob hv hσ'⟩
  have hd : deg φ = 1 := deg_eq_one_iff.2 hσ'
  have hfa : FlagAt M ![(e : ℤ), -(e : ℤ)] V A κ := by
    refine ⟨fun _ => 1, fun _ _ _ => rfl, hfl, fun i s hs => ?_⟩
    fin_cases i
    · simpa using (hI s hs).1
    · simpa using (hI s hs).2
  have h1 := GlobalTheory.T.weilDeligne_frobenius_eigenvalue_of_full_flag ℚ Ω l ι 2 M hM _ V hc v A hv _ Bw hj κ hfa hpst 0 φ hd
  obtain ⟨μ, hμ, -⟩ := Lev.flagPol ℚ Ω l ι 2 M hM _ V hc v A hv _ Bw hj κ hfa hpst
  rw [heq (Or.inl ((Lev.ssCalc ℚ Ω A v hv).1 2 _ μ hμ))] at h1
  obtain ⟨b, hb, hzb⟩ := GlobalTheory.T.satake_roots_local_correspondence ℚ Ω A v hv rc hrec 2 τ B hBτ φ hd _ h1
  rw [hnv] at hb
  have hinc : Subgroup.inclusion (Weil_le_Dec hv) φ = σ := rfl
  refine ⟨(l : ℂ) ^ e * b, ?_, Or.inr ?_⟩
  · rw [← hpoly, Polynomial.IsRoot, Polynomial.eval_multiset_prod]
    refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, Multiset.mem_map_of_mem _ hb, ?_⟩)
    simp
  · rw [hinc, hnv] at hzb
    simp only [Matrix.cons_val_zero] at hzb
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [zpow_natCast] at hzb
    linear_combination hzb

end GlobalTheory.FrobHecke

end

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_flag_local_of_level : Af.Hypotheses₂ → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (V : R2 Ω l) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ) (g : Newform (2 * e + 1)), l ≠ 2 → 1 ≤ e → Continuous V → IsIrr V → (∃ M : ℕ, 1 ≤ M ∧ LevelAway l M V) → (∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt V)) → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ → (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) → g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ¬ l ∣ g.M → ∀ σ : ↥(Dec (F := ℚ) A), IsFrob A l (σ : G ℚ Ω) → ∃ α : ℂ, (g.heckePoly l).IsRoot α ∧ (α = ι ((κ 0 σ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l) ∨ α⁻¹ = ι ((κ 0 σ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l)) := by
  first | exact @GlobalTheory.FrobHecke.frobValue_isRoot_heckePoly | exact GlobalTheory.FrobHecke.frobValue_isRoot_heckePoly | (intros; apply GlobalTheory.FrobHecke.frobValue_isRoot_heckePoly <;> assumption)

end
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem norm_eq_one_of_pow_eq_one' {R : Type} [NormedDivisionRing R] {z : R} {n : ℕ} (hn : 0 < n)
    (h : z ^ n = 1) : ‖z‖ = 1 := by
  have h1 : ‖z‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn.ne').1 h1

theorem dirichlet_pow_card_eq_one {M : ℕ} (hM : 0 < M) (χ : DirichletCharacter ℂ M) (l : ℕ) (h : l.Coprime M) :
    ∃ n : ℕ, 0 < n ∧ χ (l : ZMod M) ^ n = 1 := by
  haveI : NeZero M := ⟨hM.ne'⟩
  refine ⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, ?_⟩
  rw [← ZMod.coe_unitOfCoprime l h, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one,
    map_one]

theorem hecke_gap (L : ℝ) (hL : 3 ≤ L) (e : ℕ) (he : 1 ≤ e) :
    L ^ (((2 * e + 1 : ℕ) : ℝ) / 2) + L ^ (((2 * e + 1 : ℕ) : ℝ) / 2 - 1) < L ^ (2 * e) - 1 := by
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg L
  have hss : s * s = L := Real.mul_self_sqrt hL0.le
  have h1 : L ^ (((2 * e + 1 : ℕ) : ℝ) / 2) = L ^ e * s := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast L e, ← Real.rpow_add hL0]
    congr 1; push_cast; ring
  have h2 : L ^ (((2 * e + 1 : ℕ) : ℝ) / 2 - 1) = L ^ e * s / L := by
    rw [Real.rpow_sub hL0, Real.rpow_one, h1]
  rw [h1, h2]
  set N := L ^ e with hN
  have hNL : L ≤ N := by
    rw [hN]; calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ e := pow_le_pow_right₀ (by linarith) he
  have hsL : s < L - 1 := by nlinarith
  have key : N * s * (L + 1) < L * (N ^ 2 - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hNL) (show 0 ≤ L * (N + L) - (L + 1) * s by nlinarith),
      mul_pos (mul_pos (show (0:ℝ) < L + 1 by linarith) hL0) (show 0 < L - 1 - s by linarith)]
  have : N * s + N * s / L = N * s * (L + 1) / L := by field_simp
  rw [this, div_lt_iff₀ hL0]
  have : L ^ (2 * e) = N ^ 2 := by rw [hN, ← pow_mul, mul_comm]
  rw [this]; linarith

theorem heckePoly_root_eq {k : ℕ} (g : Newform k) (p : ℕ) (α : ℂ) (h : (g.heckePoly p).IsRoot α) :
    g.a p * α = α ^ 2 + g.χ (p : ZMod g.M) * (p : ℂ) ^ (k - 1) := by
  have := h.eq_zero
  simp only [Newform.heckePoly, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C] at this
  linear_combination -this

theorem root_facts_of_bound
    (hbd : ∀ (k : ℕ) (g : Newform k) (p : ℕ), p.Prime → ¬ p ∣ g.M →
      ‖g.a p‖ ≤ (p : ℝ) ^ ((k : ℝ) / 2) + (p : ℝ) ^ ((k : ℝ) / 2 - 1)) :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (g : Newform (2 * e + 1)) (α : ℂ), l ≠ 2 → 1 ≤ e → ¬ l ∣ g.M →
      (g.heckePoly l).IsRoot α → ‖ι.symm α‖ = 1 → ‖ι.symm (g.a l)‖ = 1 ∧ ∀ m : ℕ, 1 ≤ m → α ^ m ≠ 1 := by
  intro l _ ι e g α hl2 he hdiv hroot hα
  have hp : l.Prime := Fact.out
  have hcop : l.Coprime g.M := (Nat.Prime.coprime_iff_not_dvd hp).2 hdiv
  obtain ⟨n, hn, hχn⟩ := dirichlet_pow_card_eq_one g.pos g.χ l hcop
  have hrel := heckePoly_root_eq g l α hroot
  have hk : 2 * e + 1 - 1 = 2 * e := by omega
  rw [hk] at hrel
  set c := g.χ (l : ZMod g.M) with hc
  have hα0 : α ≠ 0 := by
    rintro rfl; simp at hα
  refine ⟨?_, ?_⟩
  ·
    have hA0 : ι.symm α ≠ 0 := by rw [Ne, map_eq_zero_iff _ ι.symm.injective]; exact hα0
    have hrel' : ι.symm (g.a l) = ι.symm α + ι.symm c * (l : Qbar l) ^ (2 * e) / ι.symm α := by
      field_simp
      have := congrArg ι.symm hrel
      simp only [map_mul, map_add, map_pow, map_natCast] at this
      linear_combination this
    have hcn : ‖ι.symm c‖ = 1 :=
      norm_eq_one_of_pow_eq_one' hn (by rw [← map_pow, hχn, map_one])
    have hln : ‖(l : Qbar l)‖ < 1 := by
      have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
      rw [h, PadicAlgCl.norm_extends]; exact Padic.norm_p_lt_one
    have hB : ‖ι.symm c * (l : Qbar l) ^ (2 * e) / ι.symm α‖ < 1 := by
      rw [norm_div, norm_mul, norm_pow, hcn, hα, one_mul, div_one]
      exact pow_lt_one₀ (norm_nonneg _) hln (by omega)
    rw [hrel', IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hα]; exact hB.ne'), hα]
    exact max_eq_left hB.le
  ·
    intro m hm hαm
    have hαn : ‖α‖ = 1 := norm_eq_one_of_pow_eq_one' hm hαm
    have hcn : ‖c‖ = 1 := norm_eq_one_of_pow_eq_one' hn hχn
    have hb := hbd (2 * e + 1) g l hp hdiv
    have ha : g.a l = α + c * (l : ℂ) ^ (2 * e) / α := by
      field_simp; linear_combination hrel
    have hlow : (l : ℝ) ^ (2 * e) - 1 ≤ ‖g.a l‖ := by
      have h1 : ‖c * (l : ℂ) ^ (2 * e) / α‖ = (l : ℝ) ^ (2 * e) := by
        rw [norm_div, norm_mul, norm_pow, hcn, hαn, one_mul, div_one, Complex.norm_natCast]
      have h2 := norm_sub_norm_le (c * (l : ℂ) ^ (2 * e) / α) (-α)
      rw [h1, norm_neg, hαn, sub_neg_eq_add, add_comm] at h2
      rw [ha]; exact h2
    have hl3 : (3 : ℝ) ≤ l := by
      have := hp.two_le
      have : 3 ≤ l := by omega
      exact_mod_cast this
    have := hecke_gap (l : ℝ) hl3 e he
    linarith

theorem root_facts :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (g : Newform (2 * e + 1)) (α : ℂ), l ≠ 2 → 1 ≤ e → ¬ l ∣ g.M →
      (g.heckePoly l).IsRoot α → ‖ι.symm α‖ = 1 → ‖ι.symm (g.a l)‖ = 1 ∧ ∀ m : ℕ, 1 ≤ m → α ^ m ≠ 1 :=
  root_facts_of_bound GlobalTheory.T.newform_norm_coeff_prime_le_of_not_dvd_level

end GlobalTheory.Ord2

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_unit_root_not_root_of_unity_odd_weight : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (g : Newform (2 * e + 1)) (α : ℂ), l ≠ 2 → 1 ≤ e → ¬ l ∣ g.M → (g.heckePoly l).IsRoot α → ‖ι.symm α‖ = 1 → ‖ι.symm (g.a l)‖ = 1 ∧ ∀ m : ℕ, 1 ≤ m → α ^ m ≠ 1 := by
  first | exact @GlobalTheory.Ord2.root_facts | exact GlobalTheory.Ord2.root_facts | (intros; apply GlobalTheory.Ord2.root_facts <;> assumption)

end
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

open Polynomial Pointwise

namespace GlobalTheory.Ord2.SrcForm

open TwDet

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem isInv_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (W : Submodule k (Fin n → k)) : IsInv (tw r χ) W ↔ IsInv r W := by
  constructor
  · intro h g v hv
    have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
    rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
  · intro h g v hv
    rw [tw_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem ss_of_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep (tw r χ)) : IsSSRep r := by
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((isInv_tw r χ W).2 hW)
  exact ⟨W', (isInv_tw r χ W').1 hW', hc⟩

theorem irr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (H : Subgroup Γ)
    (h : IsIrr (r.comp H.subtype)) : IsIrr (tw r χ) :=
  ⟨h.1, fun _ _ _ => trivial, fun W' hW' hi => h.2.2 W' hW' fun g v hv => (isInv_tw r χ W').1 hi g v hv⟩

theorem ev_not_mem (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw

theorem normV_eq (w : HeightOneSpectrum (𝓞 ℚ)) : normV w = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem not_dvd_of_not_mem {M : ℕ} {w : Pl} (hwM : ((M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) : ¬ normV w ∣ M := by
  rintro ⟨c, hc⟩
  apply hwM
  rw [hc, Nat.cast_mul, normV_eq]
  exact w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)

theorem asIdeal_eq {p : ℕ} (hp : p.Prime) {w : Pl} (hw : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) :
    w.asIdeal = Ideal.span {((p : ℕ) : 𝓞 ℚ)} := by
  have hpr : Prime (p : 𝓞 ℚ) := by
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp)
  have hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  exact (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)).symm

theorem normV_of_mem {p : ℕ} (hp : p.Prime) {w : Pl} (hw : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : normV w = p := by
  rw [normV_eq, asIdeal_eq hp hw, Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]

theorem scale_charpoly {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod) :
    M.charpoly.map φ = (B.map fun b => X - C b).prod := by
  have hc' : φ c ≠ 0 := by simpa using hc
  have hcard : B.card = 2 := by
    have h1 := congrArg natDegree h
    rw [natDegree_map, Matrix.charpoly_natDegree_eq_dim] at h1
    have h2 := natDegree_multiset_prod_X_sub_C_eq_card (B.map (φ c * ·))
    rw [Multiset.map_map] at h2
    simp only [Function.comp_def, Multiset.card_map] at h2
    rw [h2] at h1
    simpa using h1.symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have e0 := congrArg (eval 0) h
  have e1 := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : φ M.det = x * y := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hc')
    linear_combination e0
  have ht : φ M.trace = x + y := by
    apply mul_left_cancel₀ hc'
    linear_combination e0 - e1
  rw [hd, ht, C_add, C_mul]
  ring

theorem exists_rep (P : Af.Hypotheses₂) [IsAlgClosure ℚ Ω] {k : ℕ} (hk : 2 ≤ k) (f : Newform k) (ι : Qbar l ≃+* ℂ) (W : R2 Ω l) (j : ℤ)
    (hf : f.Att ι (tw W (cycBar ℚ Ω l ^ j))) :
    ∃ π : TR.CuspSub ℚ 2, π.IsRegAlg ∧ AttR ι W π ∧ ∀ᶠ w : Pl in Filter.cofinite, ∃ Bs, π.HasSat w Bs ∧
      ((algSat 2 (normV w) Bs).map fun b => X - C ((normV w : ℂ) ^ (-j) * b)).prod = f.heckePoly (normV w) := by
  have hl : Fact l.Prime := inferInstance
  obtain ⟨π, hinf, hsat⟩ := P.newform k hk f (-j)
  refine ⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ⟨ss_of_tw _ _ hf.1, ?_⟩, ?_⟩
  · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]
    intro h
    have h1 : (k : ℂ) = 1 := by linear_combination h
    have h2 : k = 1 := by exact_mod_cast h1
    omega
  · intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨-j, by push_cast; ring⟩
    · exact ⟨1 - k - j, by push_cast; ring⟩
  · filter_upwards [hf.2, ev_not_mem l hl.out.ne_zero, ev_not_mem f.M f.pos.ne'] with w hw hwl hwM
    obtain ⟨B, hB, hpoly⟩ := hsat w (not_dvd_of_not_mem hwM)
    refine ⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
    · have h1 := (hw A hA).1 s hs
      have h2 : cycZ ℚ Ω l s = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
        rw [cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
        simp
      have h3 : (cycBar ℚ Ω l ^ j) s = 1 := by
        rw [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]
      apply Units.ext
      have h4 := congrArg Units.val h1
      rwa [tw_val, h3, Units.val_one, one_smul] at h4
    · have h1 := (hw A hA).2 σ hσ
      rw [tw_val, ← hpoly] at h1
      refine scale_charpoly ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ j) σ⁻¹)) _ ?_
      rw [h1]
      have h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
      have h3 : ι.toRingHom (((cycBar ℚ Ω l ^ j) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (-j) := by
        rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀,
          map_inv₀, map_natCast, inv_zpow']
      rw [h3]
  · filter_upwards [ev_not_mem f.M f.pos.ne'] with w hwM
    exact hsat w (not_dvd_of_not_mem hwM)

theorem pow_eq_one_of_kills [IsAlgClosure ℚ Ω] {C : Type} [CommGroup C] {N : ℕ} (hN : 0 < N) {φ : G ℚ Ω →* C}
    (h : KillsMu N φ) : ∃ m : ℕ, 1 ≤ m ∧ ∀ s, φ s ^ m = 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  refine ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, fun s => ?_⟩
  rw [← map_pow]
  refine h _ fun ζ hζ => ?_
  obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hζ
  have h1 := hz.autToPow_spec ℚ (s ^ Fintype.card (ZMod N)ˣ)
  rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hz.pow_eq_one, pow_one] at h1
  rw [map_pow, ← h1]

theorem isOpen_ker_kills [IsAlgClosure ℚ Ω] {C : Type} [Group C] {M : ℕ} (hM : 0 < M) {φ : G ℚ Ω →* C} (hφ : KillsMu M φ) :
    IsOpen (φ.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ s fun ζ hζ => hs ζ hζ

theorem cont_of_kills [IsAlgClosure ℚ Ω] {M : ℕ} (hM : 0 < M) {φ : G ℚ Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) :
    Continuous fun s => (φ s : Qbar l) := by
  refine Units.continuous_val.comp (continuous_of_continuousAt_one φ ?_)
  refine (continuousAt_const (y := (1 : (Qbar l)ˣ))).congr ?_
  filter_upwards [(isOpen_ker_kills hM hφ).mem_nhds (Subgroup.one_mem _)] with s hs
  exact (MonoidHom.mem_ker.1 hs).symm

theorem kills_inv {M : ℕ} {φ : G ℚ Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) : KillsMu M φ⁻¹ := by
  intro s hs
  simp [hφ s hs]

theorem cyc_inf [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω} (hA : OverL l A) :
    ∃ s ∈ Ine (F := ℚ) A, ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l s ^ k ≠ 1 := by
  have hl : Fact l.Prime := inferInstance
  obtain ⟨v, hv, hlv⟩ := hA
  have hA : A.valuation (l : Ω) < 1 := by simpa using (hv (l : 𝓞 ℚ)).2 hlv
  have hu : IsUnit ((l + 1 : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
  obtain ⟨s, hs, he⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  refine ⟨s, hs, fun k hk h => ?_⟩
  have h2 : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = (l + 1 : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [he, hu.unit_spec, map_natCast, map_natCast]
  have h3 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, h2, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h3
  have := hl.out.pos
  omega

theorem norm_cyc (s : G ℚ Ω) : ‖((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
  change ‖algebraMap ℚ_[l] (Qbar l) (((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ = 1
  rw [PadicAlgCl.norm_extends, ← PadicInt.norm_def]
  exact PadicInt.norm_units _

theorem norm_flag [IsAlgClosure ℚ Ω] {W : R2 Ω l} (hW : Continuous W) {H : Subgroup (G ℚ Ω)} {κ : Fin 2 → ↥H →* (Qbar l)ˣ}
    (h : IsFlagOn W H κ) (i : Fin 2) (s : ↥H) : ‖(κ i s : Qbar l)‖ = 1 := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : CompactSpace (G ℚ Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))
  obtain ⟨g, hg⟩ := h
  have hc : Continuous fun t : G ℚ Ω => ‖(g * W t * g⁻¹ : GL (Fin 2) (Qbar l)) i i‖ := by
    refine Continuous.norm ?_
    have h1 : Continuous fun t : G ℚ Ω => (g * W t * g⁻¹ : GL (Fin 2) (Qbar l)).val :=
      Units.continuous_val.comp ((continuous_const.mul hW).mul continuous_const)
    exact h1.matrix_elem i i
  obtain ⟨C, hC⟩ := (isCompact_range hc).bddAbove
  have hb : ∀ t : ↥H, ‖(κ i t : Qbar l)‖ ≤ 1 := by
    intro t
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
    have := hC ⟨((t ^ n : ↥H) : G ℚ Ω), rfl⟩
    simp only at this
    rw [(hg (t ^ n)).2 i, map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
    linarith
  have h1 := hb s
  have h2 := hb s⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have h0 : 0 < ‖(κ i s : Qbar l)‖ := norm_pos_iff.2 (Units.ne_zero _)
  exact le_antisymm h1 ((inv_le_one₀ h0).1 h2)

theorem flag_twist {W : R2 Ω l} (φ : G ℚ Ω →* (Qbar l)ˣ) {H : Subgroup (G ℚ Ω)} {κ : Fin 2 → ↥H →* (Qbar l)ˣ}
    (h : IsFlagOn W H κ) : IsFlagOn (tw W φ) H (fun i => κ i * φ.comp H.subtype) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · rw [conj_tw, Matrix.smul_apply, (hg s).1 i j hij, smul_zero]
  · rw [conj_tw, Matrix.smul_apply, (hg s).2 i]
    simp [mul_comm]

theorem diag_twist {W : R2 Ω l} (φ : G ℚ Ω →* (Qbar l)ˣ) {H : Subgroup (G ℚ Ω)} {χ : Fin 2 → G ℚ Ω →* (Qbar l)ˣ}
    (h : IsDiagOn W H χ) : IsDiagOn (tw W φ) H (fun i => χ i * φ) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s hs => ?_⟩
  rw [conj_tw, hg s hs]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.diagonal_apply]; ring
  · simp [Matrix.diagonal_apply, hij]

theorem charpoly_flag {W : R2 Ω l} {H : Subgroup (G ℚ Ω)} {κ : Fin 2 → ↥H →* (Qbar l)ˣ} (h : IsFlagOn W H κ) (s : ↥H) :
    (mat W s).charpoly = (X - C (κ 0 s : Qbar l)) * (X - C (κ 1 s : Qbar l)) := by
  obtain ⟨g, hg⟩ := h
  have e : (mat W s).charpoly = (g * W s * g⁻¹ : GL (Fin 2) (Qbar l)).val.charpoly := by
    rw [Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  rw [e, Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, (hg s).1 1 0 (by decide), (hg s).2, (hg s).2]
  simp only [mul_zero, sub_zero, C_add, C_mul]
  ring

theorem charpoly_conj (W : R2 Ω l) (γ s : G ℚ Ω) : (mat W (γ * s * γ⁻¹)).charpoly = (mat W s).charpoly := by
  simp only [mat, map_mul, map_inv]
  rw [Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]

theorem eq_or_eq {H C : Type} [Group H] [CommGroup C] (a b c : H →* C) (h : ∀ s, a s = b s ∨ a s = c s) :
    (∀ s, a s = b s) ∨ ∀ s, a s = c s := by
  by_contra hn
  push Not at hn
  obtain ⟨⟨s, hs⟩, t, ht⟩ := hn
  have h1 := (h s).resolve_left hs
  have h2 := (h t).resolve_right ht
  rcases h (s * t) with h3 | h3
  · rw [map_mul, map_mul, h2] at h3
    exact hs (mul_right_cancel h3)
  · rw [map_mul, map_mul, h1] at h3
    exact ht (mul_left_cancel h3)

theorem eps_mem [IsAlgClosure ℚ Ω] {W : R2 Ω l} {A A' : ValuationSubring Ω} (hA : OverL l A) (hA' : OverL l A')
    {κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ} {κ' : Fin 2 → ↥(Dec (F := ℚ) A') →* (Qbar l)ˣ}
    (h : IsFlagOn W (Dec (F := ℚ) A) κ) (h' : IsFlagOn W (Dec (F := ℚ) A') κ')
    (he : ∀ s : ↥(Dec (F := ℚ) A'), κ' 0 s = cycBar ℚ Ω l s) :
    (∀ s : ↥(Dec (F := ℚ) A), cycBar ℚ Ω l s = κ 0 s) ∨ ∀ s : ↥(Dec (F := ℚ) A), cycBar ℚ Ω l s = κ 1 s := by
  obtain ⟨v, hv, hlv⟩ := hA
  obtain ⟨v', hv', hlv'⟩ := hA'
  obtain rfl : v = v' := HeightOneSpectrum.ext ((asIdeal_eq Fact.out hlv).trans (asIdeal_eq Fact.out hlv').symm)
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver hv hv'
  refine eq_or_eq ((cycBar ℚ Ω l).comp (Dec (F := ℚ) A).subtype) (κ 0) (κ 1) fun s => ?_
  have hs : γ * (s : G ℚ Ω) * γ⁻¹ ∈ Dec (F := ℚ) A' := by
    have hs' := mem_Dec.1 s.2
    rw [mem_Dec, mul_smul, mul_smul, ← hγ, inv_smul_smul, hs']
  have h1 := charpoly_flag h' ⟨_, hs⟩
  rw [he] at h1
  simp only at h1
  have hc : cycBar ℚ Ω l (γ * (s : G ℚ Ω) * γ⁻¹) = cycBar ℚ Ω l s := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  rw [charpoly_conj, charpoly_flag h s, hc] at h1
  have h2 := congrArg (eval ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l)) h1
  simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, mul_eq_zero, sub_eq_zero] at h2
  exact h2.imp Units.ext Units.ext

end GlobalTheory.Ord2.SrcForm

namespace GlobalTheory.Ord2

open TwDet SrcForm


end GlobalTheory.Ord2

end

end
end
