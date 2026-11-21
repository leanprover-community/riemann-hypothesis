import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLettersHarmMemHHa
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSumAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowestWeightVectorsAtRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralValuesAlgebraicPointsIffValueNonnegStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IntegralValueOfChartValues
import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNumerator
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerImagesOrthogonalDisjointSplitSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralFlipThetaTranslateHalfLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelSeriesTranslateBoundedDenominator
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealRationalPointActsHarmonicSubstitution
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelPointsTranslateMeanOfIntegralCombinat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFormsThetaShortSeriesIdentity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitSupportedClassScalarMemValuationRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedCoverIsDictionaryFrameCompatible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenReadsOfUnitAt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalSourceActsOnOrientedThetaBySubstitution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyPvNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumIdentityConstantsCoverOfDominantPins
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicMapExtremalVectorEqPhaseSmulLetters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsLinearIndependentAdelicReadings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTwistProps
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesMemOfContainsRayFieldStatement

section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ConstBound

theorem isTorsionFree_int_of {E : Type} [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.IsTorsionFree (𝓞 E) X] : Module.IsTorsionFree ℤ X :=
  Module.IsTorsionFree.trans_faithfulSMul ℤ (𝓞 E) X

theorem datum_free {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (Dw : Datum H) :
    Module.Free ℤ Dw.La ∧ Module.Finite ℤ Dw.La := by
  have := Dw.fin
  have := Dw.proj
  have : Module.IsTorsionFree ℤ Dw.La := isTorsionFree_int_of (E := E) Dw.La
  have : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
  exact ⟨inferInstance, inferInstance⟩

theorem card_levQ_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (Dw : Datum H)
    (l : Geo.Tor.Level H) : Nat.card (LevQ Dw l) ∣ l.M ^ Module.finrank ℤ Dw.La := by
  obtain ⟨hfree, hfin⟩ := datum_free Dw
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at h1
    exact (Ideal.mul_le_inf.trans inf_le_left) h1
  have hle : (nsmulAddMonoidHom (α := Dw.La) l.M).range ≤ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).toAddSubgroup := by
    rintro x ⟨y, rfl⟩
    simp only [nsmulAddMonoidHom_apply, Submodule.mem_toAddSubgroup]
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hM Submodule.mem_top
  have key := AddSubgroup.index_dvd_of_le hle
  rw [AddSubgroup.index_range_nsmul] at key
  unfold LevQ
  exact key

private theorem relIndex_span_smul_stdLat {E : Type} [Field E] [NumberField E] {n : ℕ} (N : ℕ) :
    (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup.relIndex
      (Formalism.L2.Pj.stdLat E n).toAddSubgroup = N ^ (Module.finrank ℚ E * n) := by
  have hmem : ∀ v : Fin n → E, v ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, ∃ a : 𝓞 E, (a : E) = v i := by
    intro v
    simp only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  set L := (Formalism.L2.Pj.stdLat E n).toAddSubgroup with hL
  have hmap : (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup =
      L.map (nsmulAddMonoidHom N) := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, nsmulAddMonoidHom_apply,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists, hL]
    simp only [Nat.cast_smul_eq_nsmul]
  let g : (Fin n → 𝓞 E) →+ L :=
    { toFun := fun a => ⟨fun i => (a i : E), (hmem _).2 fun i => ⟨a i, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      funext i
      have := congrArg (fun v : L => (v : Fin n → E) i) hab
      exact RingOfIntegers.coe_injective this
    · rintro ⟨v, hv⟩
      choose a ha using (hmem v).1 hv
      exact ⟨a, Subtype.ext (funext ha)⟩
  let e : (Fin n → 𝓞 E) ≃ₗ[ℤ] L := (AddEquiv.ofBijective g hg).toIntLinearEquiv
  have : Module.Free ℤ L := Module.Free.of_equiv e
  have : Module.Finite ℤ L := Module.Finite.equiv e
  have hrank : Module.finrank ℤ L = Module.finrank ℚ E * n := by
    rw [← e.finrank_eq, Module.finrank_pi_fintype]
    simp [NumberField.RingOfIntegers.rank, mul_comm]
  rw [hmap, AddSubgroup.relIndex, AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range,
    AddSubgroup.index_range_nsmul, hrank]

theorem relIndex_dvd {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) (N : ℕ) (hN : 0 < N)
    (h : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ.Ln) :
    (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ∣ N ^ (Module.finrank ℚ E * n) := by
  have hHK : (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup ≤ Λ.Ln.toAddSubgroup :=
    fun x hx => h hx
  have hKL : Λ.Ln.toAddSubgroup ≤ (Formalism.L2.Pj.stdLat E n).toAddSubgroup :=
    fun x hx => (inf_le_right : Λ.La ⊓ Formalism.L2.Pj.stdLat E n ≤ _) hx
  rw [← relIndex_span_smul_stdLat N]
  exact Dvd.intro _ (AddSubgroup.relIndex_mul_relIndex _ _ _ hHK hKL)

theorem mIdx_dvd {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) (N r : ℕ) (hN : 0 < N)
    (h : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ.Ln) : Λ.mIdx N r ∣ N ^ (Module.finrank ℚ E * n * r) := by
  have key := relIndex_dvd Λ N hN h
  rw [AddSubgroup.relIndex] at key
  rw [Formalism.L2.Pj.GenLat.mIdx, pow_mul]
  exact pow_dvd_pow_of_dvd key r

theorem const_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (n d M p : ℕ), p.Prime → M ≠ 0 → ∃ c : ℕ, ∀ (l₂ : Geo.Tor.Level H) (pd u : ℕ) (Λ : GenLat E n), l₂.M = M * pd → ¬ p ∣ pd → Nat.Coprime u p → Λ.LevOK (l₂.M * u) l₂.M → ∃ u' : ℕ, Nat.Coprime u' p ∧ ((Λ.mIdx (l₂.M * u) (Dw.p + Dw.q) * Nat.card (Fin n → LevQ Dw l₂) : ℕ) : ℤ) * (2 * NumberField.discr E * (l₂.M * u : ℕ)) ^ d ∣ ((p ^ c * u' : ℕ) : ℤ) := by
  intro E _ _ _ H Dw n d M p hp hM
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hdisc : NumberField.discr E ≠ 0 := NumberField.discr_ne_zero E
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = (M : ℤ) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) *
      (M : ℤ) ^ (Module.finrank ℤ Dw.La * n) * (2 * NumberField.discr E * M) ^ d := ⟨_, rfl⟩
  have hK0 : K.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero, hK]
    have hM' : (M : ℤ) ≠ 0 := by exact_mod_cast hM
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hM') (pow_ne_zero _ hM'))
      (pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero hdisc) hM'))
  obtain ⟨c, k, hk, hKk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hK0 p hp1
  refine ⟨c, ?_⟩
  intro l₂ pd u Λ hl hpd hu hΛ
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hp1 (Nat.coprime_zero_left p |>.mp hu)
  have hN : 0 < l₂.M * u := Nat.mul_pos (by have := l₂.three_le; omega) (Nat.pos_of_ne_zero hu0)
  have h1 : Λ.mIdx (l₂.M * u) (Dw.p + Dw.q) ∣ (l₂.M * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) :=
    mIdx_dvd Λ _ _ hN hΛ.2.2
  have h2 : Nat.card (Fin n → LevQ Dw l₂) ∣ l₂.M ^ (Module.finrank ℤ Dw.La * n) := by
    rw [Nat.card_fun, Nat.card_fin, pow_mul]
    exact pow_dvd_pow_of_dvd (card_levQ_dvd Dw l₂) n
  have hcop : ∀ m : ℕ, ¬ p ∣ m → Nat.Coprime m p := fun m hm =>
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  have hpd' := hcop pd hpd
  refine ⟨k * ((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) *
    (pd * u) ^ d), ?_, ?_⟩
  · exact Nat.Coprime.mul_left (hcop k hk) (Nat.Coprime.mul_left (Nat.Coprime.mul_left
      (Nat.Coprime.pow_left _ (Nat.Coprime.mul_left hpd' hu)) (Nat.Coprime.pow_left _ hpd'))
      (Nat.Coprime.pow_left _ (Nat.Coprime.mul_left hpd' hu)))
  · have hKd : K ∣ (K.natAbs : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
    have h12 := Int.natCast_dvd_natCast.mpr (Nat.mul_dvd_mul h1 h2)
    have hprod : ((l₂.M * u : ℕ) : ℤ) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * ((l₂.M : ℕ) : ℤ) ^ (Module.finrank ℤ Dw.La * n) *
        (2 * NumberField.discr E * ((l₂.M * u : ℕ) : ℤ)) ^ d =
        K * (((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) *
          (pd * u) ^ d : ℕ) : ℤ) := by
      rw [hK, hl]
      push_cast
      ring
    have hfin : ((p ^ c * (k * ((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) *
        (pd * u) ^ d)) : ℕ) : ℤ) = (K.natAbs : ℤ) * (((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) *
          pd ^ (Module.finrank ℤ Dw.La * n) * (pd * u) ^ d : ℕ) : ℤ) := by
      rw [hKk]
      push_cast
      ring
    rw [hfin]
    refine dvd_trans ?_ (mul_dvd_mul_right hKd _)
    rw [← hprod]
    push_cast at h12 ⊢
    exact mul_dvd_mul h12 dvd_rfl

end GlobalTheory.ConstBound
end

section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ConjLatSplit

open GlobalTheory.UnRep GlobalTheory.UnRep.FullReps GlobalTheory.AdLat GlobalTheory.AdLat.Translate GlobalTheory.UnRep.SmallMat

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_conjLat_unimod_bd (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (bad : ℕ)
    (h : GL (Fin n) (RA (maximalRealSubfield E) E)) (hh : IsUnA (IsCMField.complexConj E) 1 h.1)
    (hs : SuppSplit (IsCMField.complexConj E) bad h.1) :
    ∃ (Λ : Submodule (𝓞 E) (Fin n → E)) (k : ℕ),
      (Λ : Set (Fin n → E)) = latOf (maximalRealSubfield E) h.1 (Formalism.L2.Pj.stdLat E n) ∧ (conjLat H Λ).Unimod ∧
      k.Coprime bad ∧ ∀ u : ℕ, Ideal.span {((u * k : ℕ) : 𝓞 E)} • (conjLat H Λ).La ≤ Formalism.L2.Pj.stdLat E n ∧
        Ideal.span {((u * k : ℕ) : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ (conjLat H Λ).La := by
  obtain ⟨-, -, hfg, hsp, -⟩ := StdInhab.main E H n
  obtain ⟨Λ, hΛ, -⟩ := exists_lattice_latOf (maximalRealSubfield E) E n (Formalism.L2.Pj.stdLat E n) h hfg hsp
  obtain ⟨e, -, -, he, hcut⟩ := hs
  have hcut' := cut_inv h _ hcut
  have he' : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      ((bad : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal → e v = 0 := fun v hv => by
    by_contra h0
    exact (he v h0).2 hv
  obtain ⟨t, ht, hb⟩ := exists_nat_bd _ hfg hsp _ e he' _ hcut
  obtain ⟨t', ht', hb'⟩ := exists_nat_bd _ hfg hsp _ e he' _ hcut'
  refine ⟨Λ, t' * t, hΛ, conjLat_unimod H hh hΛ, Nat.Coprime.mul_left ht' ht, fun u => ?_⟩
  refine conjLat_le H (by rw [← H.bar_eq, map_natCast]) (smul_mem_of_bd hfg hsp hΛ ?_ ?_)
  · have := hb.mul ((u * t' : ℕ) : 𝓞 E)
    rwa [← Nat.cast_mul, mul_assoc] at this
  · have := hb'.mul ((u * t : ℕ) : 𝓞 E)
    rwa [← Nat.cast_mul, mul_assoc, mul_comm t] at this

end General

end GlobalTheory.ConjLatSplit

open GlobalTheory.ConjLatSplit in

theorem GlobalTheory.SingleDatum.exists_conjLat_levOK : ∀ (D : D7) (V : HSp D), V.gram = 1 → L0c D V = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → ∀ (bad M p : ℕ), Odd M → 2 ∣ bad → M ∣ bad → p ∣ bad → ∀ h : GA D V, SplitOffBad V bad h → ∃ (Λ : GenLat D.host.E V.rank) (u : ℕ), (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (finPt V h)) ∧ Λ.Unimod ∧ Λ.TrivAt M ∧ Nat.Coprime u p ∧ Λ.LevOK (M * u) M := by
  intro D V hg hL0 bad M p hM h2 hMb hpb h hs
  have hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank :=
    SetLike.coe_injective ((GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice V).trans hL0)
  have hc : GlobalTheory.Member.cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
  have hu := GlobalTheory.UnRep.Space.isUnA_finHom V h
  rw [show (HSpace.gram V)ᵀ = 1 by rw [hg, Matrix.transpose_one], hc] at hu
  have hs' : GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) bad (finHom V h).1 :=
    (GlobalTheory.RepsCompare.suppSplitOff_iff _ _ _).1 (GlobalTheory.RepsCompare.suppSplitOff_of_splitOffBad _ _ _ hs)
  rw [hc] at hs'
  obtain ⟨Λ, k, h1, hU, hk, hnat⟩ := exists_conjLat_unimod_bd (Formalism.L2.Pj.hostOfRecord D) bad (finHom V h) hu hs'
  rw [GlobalTheory.SplitReps.hLat_one] at hL
  have e := GlobalTheory.SplitReps.hLat_eq V (FWT.fin V h) Λ (by rw [hL]; exact h1)
  have hk1 := hnat 1
  rw [one_mul] at hk1
  refine ⟨GlobalTheory.UnRep.FullReps.conjLat (Formalism.L2.Pj.hostOfRecord D) Λ, k, fun v => ?_, hU,
    ⟨k, hk.coprime_dvd_right hMb, hk1⟩, hk.coprime_dvd_right hpb,
    ⟨hM.mul (Nat.Coprime.odd_of_right (hk.coprime_dvd_right h2)), dvd_mul_right _ _,
      le_inf (hnat M).2 Submodule.smul_le_right⟩⟩
  change _ ↔ _ ∈ Bridge.hLat V (FWT.fin V h)
  rw [e]
  exact Iff.rfl
end
end

section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SingleDatum

theorem exists_isHalfIdem : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l : Geo.Tor.Level H), ∃ e : AE D, IsHalfIdem l e := by
  intro D H l
  classical
  have hbar : ∀ x : 𝓞 D.host.E, H.bar x = GlobalTheory.IdemSupport.cO D x := fun x =>
    RingOfIntegers.ext (by rw [H.bar_eq, GlobalTheory.IdemSupport.cO_coe]; rfl)
  have key : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), l.Mb ≤ Q.asIdeal → ¬ l.Mb ≤ (GlobalTheory.IdemSupport.cP Q).asIdeal := by
    intro Q h1 h2
    apply Q.isPrime.ne_top
    rw [eq_top_iff, ← l.coprime]
    refine sup_le h1 (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)
    have h3 := h2 hx
    rw [GlobalTheory.IdemSupport.mem_cP] at h3
    rw [Ideal.mem_comap, RingHom.coe_coe, hbar]
    exact h3
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have h1 := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h1
    have h2 : (l.M : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
    exact h2 h1
  have hfin : {Q : HeightOneSpectrum (𝓞 D.host.E) | l.Mb ≤ Q.asIdeal}.Finite :=
    (Ideal.finite_factors (I := l.Mb) (by rwa [Ideal.zero_eq_bot])).subset fun Q hQ => Ideal.dvd_iff_le.2 hQ
  refine (GlobalTheory.GridIdem.exists_isIdemSum hfin.toFinset ?_ ?_).imp fun e he => ⟨hfin.toFinset, he, fun PP => hfin.mem_toFinset⟩
  · intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    refine GlobalTheory.Hk3.SplitMatch.exists_isIdemAt fun h => key Q hQ fun x hx => ?_
    rw [GlobalTheory.IdemSupport.mem_cP]
    have h4 : Formalism.DivisionValues.cO D.host.E x ∈ (Formalism.DivisionValues.conjPl Q).asIdeal := Ideal.mem_map_of_mem _ (hQ hx)
    rw [h] at h4
    exact h4
  · intro Q hQ Q' hQ' hu
    rw [Set.Finite.mem_toFinset] at hQ hQ'
    rcases GlobalTheory.IdemSupport.eq_or_eq_cP hu with h | h
    · exact h
    · exact absurd (by rw [← h]; exact hQ) (key Q' hQ')

end GlobalTheory.SingleDatum
end

section
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelFourier

theorem charSum (M K : ℕ) (hM : M ≠ 0) (z : Fin K → ℂ) (hz : ∀ i, z i ^ M = 1) :
    ∑ c : Fin K → Fin M, ∏ i, z i ^ (c i : ℕ) = if ∀ i, z i = 1 then (M : ℂ) ^ K else 0 := by
  rw [← Fintype.prod_sum (fun i (j : Fin M) => z i ^ (j : ℕ))]
  have h1 : ∀ i, ∑ j : Fin M, z i ^ (j : ℕ) = if z i = 1 then (M : ℂ) else 0 := by
    intro i
    rw [Fin.sum_univ_eq_sum_range (fun j => z i ^ j) M]
    split_ifs with h
    · simp [h]
    · rw [geom_sum_eq h, hz i, sub_self, zero_div]
  simp only [h1]
  split_ifs with h
  · simp [h]
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem char_sum {A ι : Type} [AddCommMonoid A] (ψ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  refine Finset.induction_on s (by simp) fun a s ha ih => ?_
  rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

open GlobalTheory.LatFinMod GlobalTheory.LatVac in

theorem gens (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : ΛS.FG) (hT : ΛT.FG) :
    ∃ (K : ℕ) (g : Fin K → WO S T),
      (∀ i, g i ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧
      ∀ k : ℕ, 0 < k → ∀ w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ∃ n : Fin K → ℤ, ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          w = ∑ i, n i • g i + k • u := by
  obtain ⟨A, hA, hA1, hA2⟩ := exists_int_gen (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl _)
  obtain ⟨B, hB, hB1, hB2⟩ := exists_int_gen ΛS hS
  obtain ⟨C, hC, hC1, hC2⟩ := exists_int_gen ΛT hT
  let P : HeightOneSpectrum (𝓞 D.host.F) → Prop := fun _ => True
  let ε := idemAt D.host.F P
  have hε : ε ∈ intAf D.host.F := by
    intro v
    rw [evalV_idemAt]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hε0 : ∀ v, ¬ P v → evalV D.host.F v ε = 0 := fun v hv => by rw [evalV_idemAt, if_neg hv]
  let φ : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[ℤ] WO S T :=
    (AddMonoidHom.mk' (finTens ε) (finTens_add ε)).toIntLinearMap
  let G := φ '' ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C))
  have hG : G.Finite := ((hA.prod (hB.prod hC)).image _).image _
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) P
  have hGΛ : ∀ x ∈ G, x ∈ Λ := by
    rintro _ ⟨_, ⟨⟨a, s, t⟩, ⟨ha, hs, ht⟩, rfl⟩, rfl⟩
    exact AddSubgroup.subset_closure ⟨ε, hε, hε0, a, hA1 ha, s, hB1 hs, t, hC1 ht, rfl⟩
  obtain ⟨K, g, hg⟩ := hG.fin_embedding
  refine ⟨K, g, fun i => hGΛ _ (hg ▸ Set.mem_range_self i), fun k hk w hw => ?_⟩
  have key : ∀ w ∈ Λ, ∃ y ∈ Submodule.span ℤ G, ∃ u ∈ Λ, w = y + k • u := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F k hk).2 α hα
      have e : α = ε * α := by
        refine RestrictedProduct.ext _ _ fun v => ?_
        change evalV D.host.F v α = evalV D.host.F v (ε * α)
        rw [map_mul, evalV_idemAt]
        split_ifs with hv
        · rw [one_mul]
        · rw [h0 v hv, mul_zero]
      have hxa : algebraMap D.host.F D.host.E x * a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) :=
        Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
          (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ha
      refine ⟨φ (genMap S T (algebraMap D.host.F D.host.E x * a) s t),
        Submodule.apply_mem_span_image_of_mem_span φ
          (genMap_mem_span S T (hA2 _ hxa) (hB2 _ hs) (hC2 _ ht)),
        finTens (ε * β) (genMap S T a s t),
        AddSubgroup.subset_closure ⟨ε * β, fun v => ?_, fun v hv => ?_, a, ha, s, hs, t, ht, rfl⟩, ?_⟩
      · rw [map_mul]; exact mul_mem (hε v) (hβ v)
      · rw [map_mul, hε0 v hv, zero_mul]
      · rw [e, hx]
        exact Matrix.ext fun i j => pair_tmul_split ε β _ k a (t i) _
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add x x' _ _ h h' =>
      obtain ⟨y, hy, u, hu, rfl⟩ := h
      obtain ⟨y', hy', u', hu', rfl⟩ := h'
      exact ⟨y + y', add_mem hy hy', u + u', add_mem hu hu', add_nsmul_residue_add k y u y' u'⟩
    | neg x _ h =>
      obtain ⟨y, hy, u, hu, rfl⟩ := h
      exact ⟨-y, neg_mem hy, -u, neg_mem hu, neg_nsmul_residue k y u⟩
  obtain ⟨y, hy, u, hu, rfl⟩ := key w hw
  rw [← hg] at hy
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy
  exact ⟨n, u, hu, by rw [hn]⟩

theorem root_mem {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {M : ℕ} (hM : M ≠ 0) {O : Subring ℂ} (hz : zeta M ∈ O)
    {t y : WO S T} (ht : t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (hy : M • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    ψ (symplO S T t y) ^ M = 1 ∧ ψ (symplO S T t y) ∈ O := by
  have h1 : ψ (symplO S T t y) ^ M = 1 := by
    have e1 : symplO S T t (M • y) = M • symplO S T t y :=
      (AddMonoidHom.mk' (symplO S T t) (GlobalTheory.PlaceModel.symplO_add_right S T t)).map_nsmul M y
    rw [← AddChar.map_nsmul_eq_pow, ← e1]
    exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT ht hy
  refine ⟨h1, ?_⟩
  haveI : NeZero M := ⟨hM⟩
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp M hM).eq_pow_of_pow_eq_one h1
  rw [← hi]
  exact Subring.pow_mem _ hz i

set_option maxHeartbeats 4000000 in

theorem smul_mem_trSp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∃ K : ℕ, ∀ (M : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (O : Subring ℂ) (Φ φ : WO V W → ℂ), M ≠ 0 → Nat.Coprime M (GlobalTheory.Tow.badN D) → IsIdemSum e P → (∀ PP ∈ P, ((M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → zeta M ∈ O → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsLevelFn (cA D e) (latO V W ΛV ΛW fun _ => True) M Φ → (∀ x, Φ x ∈ O) → IsThetaAt ψ (symplO V W) (heisO ψ V W) (cA D e) (latO V W ΛV ΛW fun _ => True) 1 f₀ Φ φ → ((M : ℂ) ^ K) • φ ∈ trSp ψ V W ΛV ΛW f₀ e M O := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP
  obtain ⟨-, -, -, -, hSV, hSW, -, -, hvac⟩ := hP
  have hψ : IsStdChar D ψ (-1) := hvac.1
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ V W ΛV ΛW hψ hSV hSW).1
  set Λ := latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True with hΛ
  obtain ⟨K, g, hgΛ, hgen⟩ := gens D V W ΛV ΛW hSV.1.fg hSW.1.fg
  refine ⟨K, fun M e P O Φ φ hM _ he _ hz hlev hO hθ => ?_⟩
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  have hoe := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hoc := hoe.conj
  have hee : e * e = e := hoe.idem
  have hcc : cA D e * cA D e = cA D e := hoc.idem
  have half' : ∀ {a : AE D} {u : WO V W}, IsHalf a u ↔ a • u = u := fun {a u} =>
    (GlobalTheory.PlaceModel.isHalf_iff V W).trans (GlobalTheory.PlaceModel.mem_half V W)
  let r : AE D := algebraMap D.host.F (AE D) ((M : D.host.F)⁻¹)
  have hrk : r * (M : AE D) = 1 := by
    rw [← map_natCast (algebraMap D.host.F (AE D)) M, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hM), map_one]
  have hcr : cA D r = r := by
    have h1 : cA D r * (M : AE D) = 1 := by rw [← map_natCast (cA D) M, ← map_mul, hrk, map_one]
    calc cA D r = cA D r * ((M : AE D) * r) := by rw [mul_comm (M : AE D) r, hrk, mul_one]
      _ = r := by rw [← mul_assoc, h1, one_mul]
  have hnat : ∀ z : WO V W, M • z = (M : AE D) • z := fun z => (Nat.cast_smul_eq_nsmul (AE D) M z).symm
  have hkrz : ∀ z : WO V W, M • (r • z) = z := fun z => by rw [hnat, smul_smul, mul_comm, hrk, one_smul]
  let h : Fin K → WO V W := fun i => r • (e • g i)
  let y : (Fin K → Fin M) → WO V W := fun c => ∑ i, (c i : ℕ) • h i
  have heh : ∀ i, e • h i = h i := fun i => by
    simp only [h]; rw [smul_comm e r, smul_smul e e, hee]
  have hye : ∀ c, IsHalf e (y c) := fun c => half'.2 (by
    simp only [y]; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [smul_comm, heh])
  have hMh : ∀ i, M • h i = e • g i := fun i => hkrz _
  have heg : ∀ i, e • g i ∈ Λ := fun i => GlobalTheory.PlaceModelSum.idem_smul_latO hee (hgΛ i)
  have hMy : ∀ c, M • y c ∈ Λ := fun c => by
    simp only [y]; rw [Finset.smul_sum]
    exact sum_mem fun i _ => by rw [smul_comm, hMh]; exact AddSubgroup.nsmul_mem _ (heg i) _

  have hprod : ∀ t c, ψ (symplO V W t (y c)) = ∏ i, ψ (symplO V W t (h i)) ^ (c i : ℕ) := fun t c => by
    let F := AddMonoidHom.mk' (symplO V W t) (GlobalTheory.PlaceModel.symplO_add_right V W t)
    change ψ (F (y c)) = ∏ i, ψ (F (h i)) ^ (c i : ℕ)
    simp only [y, map_sum, map_nsmul, char_sum, AddChar.map_nsmul_eq_pow]
  have hroot : ∀ t ∈ Λ, ∀ i, ψ (symplO V W t (h i)) ^ M = 1 := fun t ht i =>
    (root_mem hψ hSV hSW hM (O := ⊤) (Subring.mem_top _) ht (by rw [hMh]; exact heg i)).1

  have hdualT : ∀ t ∈ Λ, IsHalf (cA D e) t → (∀ i, ψ (symplO V W t (h i)) = 1) →
      ∃ u ∈ Λ, IsHalf (cA D e) u ∧ t = M • u := by
    intro t ht hth hall
    have hx : r • t ∈ GlobalTheory.PlaceModel.half V W (cA D e) := by
      rw [GlobalTheory.PlaceModel.mem_half, smul_comm, half'.1 hth]
    have hmem := hoc.mem_of_dual hdual (r • t) hx (fun z hz => by
      obtain ⟨hzΛ, hzh⟩ := AddSubgroup.mem_inf.1 hz
      rw [GlobalTheory.LatVac.cA_cA, GlobalTheory.PlaceModel.mem_half] at hzh
      obtain ⟨n, u, hu, hzn⟩ := hgen M hMpos z hzΛ
      let ρ : WO V W →+ WO V W :=
        (DistribMulAction.toAddMonoidHom _ r).comp (DistribMulAction.toAddMonoidHom _ e)
      have hρ : r • z = ∑ i, n i • h i + e • u := by
        have e1 : r • z = ρ z := by
          simp only [ρ, AddMonoidHom.comp_apply, DistribMulAction.toAddMonoidHom_apply, hzh]
        rw [e1, hzn, map_add, map_sum, map_nsmul]
        simp only [map_zsmul]
        congr 1
        exact hkrz (e • u)
      rw [GlobalTheory.PlaceModel.symplO_smul, hcr, hρ]
      let F := AddMonoidHom.mk' (symplO V W t) (GlobalTheory.PlaceModel.symplO_add_right V W t)
      change ψ (F _) = 1
      rw [map_add, AddChar.map_add_eq_mul, map_sum, char_sum]
      simp only [map_zsmul, AddChar.map_zsmul_eq_zpow]
      change (∏ i, ψ (symplO V W t (h i)) ^ n i) * ψ (symplO V W t (e • u)) = 1
      rw [Finset.prod_eq_one fun i _ => by rw [hall i, _root_.one_zpow], one_mul]
      exact GlobalTheory.LatVac.char_sympl_eq_one hψ hSV hSW ht (GlobalTheory.PlaceModelSum.idem_smul_latO hee hu))
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hmem
    exact ⟨r • t, h1, (GlobalTheory.PlaceModel.isHalf_iff V W).2 h2, (hkrz t).symm⟩
  have hconv : ∀ u ∈ Λ, ∀ i, ψ (symplO V W (M • u) (h i)) = 1 := fun u hu i => by
    have a1 : symplO V W (M • u) (h i) = M • symplO V W u (h i) :=
      (AddMonoidHom.mk' (fun x => symplO V W x (h i)) fun x x' =>
        GlobalTheory.PlaceModel.symplO_add_left V W x x' _).map_nsmul M u
    have a2 : symplO V W u (M • h i) = M • symplO V W u (h i) :=
      (AddMonoidHom.mk' (symplO V W u) (GlobalTheory.PlaceModel.symplO_add_right V W u)).map_nsmul M (h i)
    rw [a1, ← a2, hMh]
    exact GlobalTheory.LatVac.char_sympl_eq_one hψ hSV hSW hu (heg i)

  have hA : ∀ t ∈ Λ, IsHalf (cA D e) t → ∑ c, ψ (symplO V W t (y c)) =
      if ∃ u ∈ Λ, IsHalf (cA D e) u ∧ t = M • u then (M : ℂ) ^ K else 0 := by
    intro t ht hth
    simp only [hprod t]
    rw [charSum M K hM _ (hroot t ht)]
    by_cases hc : ∃ u ∈ Λ, IsHalf (cA D e) u ∧ t = M • u
    · rw [if_pos hc, if_pos]
      obtain ⟨u, hu, -, rfl⟩ := hc
      exact hconv u hu
    · rw [if_neg hc, if_neg]
      exact fun hall => hc (hdualT t ht hth hall)

  obtain ⟨C, hCh, hC⟩ := GlobalTheory.BadOrth.finCosets D V W ΛV ΛW hSV hSW (cA D e) hcc M hMpos
  let L : AddSubgroup (WO V W) :=
    AddSubgroup.map (nsmulAddMonoidHom M) (Λ ⊓ GlobalTheory.PlaceModel.half V W (cA D e))
  have memL : ∀ x, x ∈ L ↔ ∃ u ∈ Λ, IsHalf (cA D e) u ∧ x = M • u := fun x => by
    constructor
    · intro hx
      obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.1 hx
      exact ⟨u, (AddSubgroup.mem_inf.1 hu).1, (GlobalTheory.PlaceModel.isHalf_iff V W).2 (AddSubgroup.mem_inf.1 hu).2, rfl⟩
    · rintro ⟨u, hu, hue, rfl⟩
      exact AddSubgroup.mem_map.2 ⟨u, AddSubgroup.mem_inf.2 ⟨hu, (GlobalTheory.PlaceModel.isHalf_iff V W).1 hue⟩, rfl⟩
  let mkL : WO V W → WO V W ⧸ L := QuotientAddGroup.mk
  have hmkL : ∀ a b, mkL a = mkL b ↔ a - b ∈ L := fun a b => by
    rw [QuotientAddGroup.eq, ← neg_mem_iff, neg_add, neg_neg, ← sub_eq_add_neg]
  let C' := C.filter (· ∈ Λ)
  let Q : Finset (WO V W ⧸ L) := C'.image mkL
  have hrepex : ∀ q ∈ Q, ∃ c ∈ C', mkL c = q := fun q hq => Finset.mem_image.1 hq
  let rep : WO V W ⧸ L → WO V W := fun q => if hq : q ∈ Q then (hrepex q hq).choose else 0
  have hrep : ∀ q ∈ Q, rep q ∈ Λ ∧ IsHalf (cA D e) (rep q) ∧ mkL (rep q) = q := fun q hq => by
    simp only [rep, dif_pos hq]
    obtain ⟨h1, h2⟩ := (hrepex q hq).choose_spec
    obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h1
    exact ⟨h4, hCh _ h3, h2⟩
  have hcover : ∀ t ∈ Λ, IsHalf (cA D e) t → mkL t ∈ Q := fun t ht hth => by
    obtain ⟨c, hc, u, hu, hue, htc⟩ := hC t hth (AddSubgroup.nsmul_mem _ ht M)
    have hcΛ : c ∈ Λ := by
      rw [show c = t - M • u by rw [htc]; abel]
      exact sub_mem ht (AddSubgroup.nsmul_mem _ hu M)
    refine Finset.mem_image.2 ⟨c, Finset.mem_filter.2 ⟨hc, hcΛ⟩, (hmkL c t).2 ?_⟩
    rw [htc, show c - (c + M • u) = M • (-u) by rw [smul_neg]; abel]
    exact AddSubgroup.mem_map.2 ⟨-u, AddSubgroup.mem_inf.2 ⟨neg_mem hu, neg_mem ((GlobalTheory.PlaceModel.isHalf_iff V W).1 hue)⟩, rfl⟩

  let a : (Fin K → Fin M) → ℂ := fun c =>
    ((M : ℂ) ^ K)⁻¹ * ∑ q ∈ Q, Φ (rep q) * ψ (symplO V W (-(rep q)) (y c))
  have hMK : ((M : ℂ) ^ K) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hM)
  have hΦ : ∀ t, Φ t = halfInd (cA D e) Λ t * ∑ c, a c * ψ (symplO V W t (y c)) := by
    intro t
    rw [halfInd]
    split_ifs with ht
    · rw [one_mul]
      have hsub : ∀ q c, ψ (symplO V W (t - rep q) (y c)) =
          ψ (symplO V W (-(rep q)) (y c)) * ψ (symplO V W t (y c)) := fun q c => by
        rw [sub_eq_add_neg, add_comm, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul]
      have e1 : ∑ c, a c * ψ (symplO V W t (y c)) =
          ((M : ℂ) ^ K)⁻¹ * ∑ q ∈ Q, Φ (rep q) * ∑ c, ψ (symplO V W (t - rep q) (y c)) := by
        simp only [a, hsub, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun c _ => by ring
      have e2 : ∀ q ∈ Q, ∑ c, ψ (symplO V W (t - rep q) (y c)) = if mkL t = q then (M : ℂ) ^ K else 0 :=
        fun q hq => by
          obtain ⟨hq1, hq2, hq3⟩ := hrep q hq
          rw [hA _ (sub_mem ht.1 hq1) (half'.2 (by rw [smul_sub, half'.1 ht.2, half'.1 hq2]))]
          refine if_congr ?_ rfl rfl
          rw [← memL, ← hmkL, hq3]
      rw [e1, Finset.sum_congr rfl fun q hq => by rw [e2 q hq, mul_ite, mul_zero], Finset.sum_ite_eq,
        if_pos (hcover t ht.1 ht.2)]
      obtain ⟨-, -, hr3⟩ := hrep (mkL t) (hcover t ht.1 ht.2)
      obtain ⟨w, hw, hwh, hwe⟩ := (memL _).1 ((hmkL _ _).1 hr3)
      have hΦr : Φ (rep (mkL t)) = Φ t := by
        rw [show rep (mkL t) = t + M • w by rw [← hwe]; abel]
        exact hlev.2 w hw hwh t
      rw [hΦr, mul_comm (Φ t), ← mul_assoc, inv_mul_cancel₀ hMK, one_mul]
    · rw [zero_mul]
      by_contra h0
      exact ht ⟨(hlev.1 t h0).1, (hlev.1 t h0).2⟩
  have hY : ∀ c, IsHalf (cA D (cA D e)) (y c) := fun c => by rw [GlobalTheory.LatVac.cA_cA]; exact hye c
  have hφ := GlobalTheory.DatumFourier.thetaAt_eq_sum y a hθ hY hΦ
  have hb : ∀ c, (∑ q ∈ Q, Φ (rep q) * ψ (symplO V W (-(rep q)) (y c))) ∈ O := fun c =>
    sum_mem fun q hq => mul_mem (hO _) (root_mem hψ hSV hSW hM hz (neg_mem (hrep q hq).1) (hMy c)).2
  rw [hφ, Finset.smul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  have e2 : ((M : ℂ) ^ K) • (a c • heisO ψ V W (y c) f₀) = (⟨_, hb c⟩ : O) • heisO ψ V W (y c) f₀ := by
    rw [smul_smul, Subring.smul_def]
    congr 1
    simp only [a]
    rw [← mul_assoc, mul_inv_cancel₀ hMK, one_mul]
  rw [e2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y c, hye c, hMy c, rfl⟩)

end GlobalTheory.LevelFourier

end
end

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_pair_uniform_level_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∃ K : ℕ, ∀ (M : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (O : Subring ℂ) (Φ φ : WO V W → ℂ), M ≠ 0 → Nat.Coprime M (GlobalTheory.Tow.badN D) → IsIdemSum e P → (∀ PP ∈ P, ((M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → zeta M ∈ O → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsLevelFn (cA D e) (latO V W ΛV ΛW fun _ => True) M Φ → (∀ x, Φ x ∈ O) → IsThetaAt ψ (symplO V W) (heisO ψ V W) (cA D e) (latO V W ΛV ΛW fun _ => True) 1 f₀ Φ φ → ((M : ℂ) ^ K) • φ ∈ trSp ψ V W ΛV ΛW f₀ e M O := by
  atlas_forward_decl GlobalTheory.LevelFourier.smul_mem_trSp
end

section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitSupportedClassScalar_mem_valuationRing : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (b l bad : ℕ), ChiData χW χ b → l.Prime → b ∣ bad → l ∣ bad → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → χ.ValuesIn (-1 / 2) σ → ∀ (h : GA D V) (Λ : GenLat D.host.E V.rank) (e' : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), bad ≠ 0 → IsIdemSum e' Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC V → SuppAt e' V h → IsDetAt e' V h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (GlobalTheory.ExportSeries.finPt V h)) → clsScal χW y Λ W.rank ∈ O := by
  first | exact @GlobalTheory.LevelSeries.clsScal_mem_valRing | exact GlobalTheory.LevelSeries.clsScal_mem_valRing | (intros; apply GlobalTheory.LevelSeries.clsScal_mem_valRing <;> assumption)
end

section
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem chiData_chrTh_base : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ChiData (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).2 (R.C.mu0 i * R.C.eta⁻¹) (D.host.g 0 * D.host.g 1) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ hLev _ _ _ _ _ i _
  have hxi : R.toLevCh.xi A.μ0 = 1 := MonoidHom.ext fun x => by
    have h := hLev.xi A.μ0
    rw [hLev.xi_base] at h
    exact GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one h x
  have e : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).2 = R.toLevCh.mu0 ((i : ℕ) + 1) * R.eta⁻¹ := by
    simp only [Lift.chrTh, LevCh.mu, Lift.tup, hxi, mul_one]
  rw [e]
  refine ⟨?_, fun Q hQ => ?_, fun Q hQ k => ?_⟩
  · have ha := hLev.mu0 i
    have hc := hLev.eta
    refine ⟨⟨ha.1.1.mul hc.1.1.inv, fun x => ?_⟩, fun P e he k x hx => ?_⟩
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ha.1.2, hc.1.2, inv_one, one_mul]
    · show ((R.toLevCh.mu0 ((i : ℕ) + 1) x * (R.eta x)⁻¹ : Circle) : ℂ) =
        (((R.C.mu0 i).locK P k * (R.C.eta.locK P k)⁻¹ : ℂˣ) : ℂ)
      rw [Circle.coe_mul, Circle.coe_inv, ha.2 P e he k x hx, hc.2 P e he k x hx, Units.val_mul,
        Units.val_inv_eq_inv_val]
  · intro x hx
    have hg : ∀ k, ¬ Formalism.L2.Host.OverP D.host (D.host.g k) Q := fun k hk => hQ (by
      rw [Nat.cast_mul]
      fin_cases k
      · exact Ideal.mul_mem_right _ _ hk
      · exact Ideal.mul_mem_left _ _ hk)
    rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, (R.C.isMu0 i).unr Q hg x hx, R.C.isEta.unr Q x hx,
      inv_one, one_mul]
  · have hcard : (Formalism.L2.Host.aboveF (L := D.host.E) D.host.F (Q.under (𝓞 D.host.F))).card ≠ 1 := by
      refine ne_of_gt (Finset.one_lt_card.2 ⟨Q, ?_, GlobalTheory.IdemSupport.cP Q, ?_, hQ.symm⟩)
      · rw [Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset]; rfl
      · rw [Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset]; exact GlobalTheory.IdemSupport.under_cP Q
    rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv, (R.C.isMu0 i).triv.1, R.C.isEta.res.1,
      Formalism.L2.Host.etaFin, if_neg hcard, inv_one, one_mul]

end GlobalTheory.LevelSeries

end
end

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_secondSplittingCharacter : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ChiData (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).2 (R.C.mu0 i * R.C.eta⁻¹) (D.host.g 0 * D.host.g 1) := by
  atlas_forward_decl GlobalTheory.LevelSeries.chiData_chrTh_base
end

section
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries.PinBase

variable {D : D7}

theorem exists_rat_of_unitary (V : HSp D) (hV : V.gram = 1) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (hb : bᴴ * b = 1) : ∃ β ∈ GQ V, Formalism.L2.Theta.mt V β = b.map (incA D) ∧ Formalism.L2.Theta.mt V β⁻¹ = bᴴ.map (incA D) := by
  let δ : GL (Fin V.rank) D.host.E := ⟨b, bᴴ, mul_eq_one_comm.1 hb, hb⟩
  have hδ : δ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
    change Formalism.UG.cT _ b * V.gram * b = V.gram
    rw [hV, Matrix.mul_one]
    exact hb
  have hA : Formalism.UG.bc (inclR (AF D.host.F)) δ ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    change Formalism.UG.cT _ (b.map (incA D)) * V.gram.map (incA D) * b.map (incA D) = V.gram.map (incA D)
    have e : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (b.map (incA D)) = bᴴ.map (incA D) := rfl
    rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hV, Matrix.mul_one, hb]
  exact ⟨⟨_, hA⟩, ⟨δ, hδ, rfl⟩, rfl, rfl⟩

theorem actO_mem_of_rat (V W : HSp D) (hV : V.gram = 1) (LV : Set (Fin V.rank → D.host.E)) (LW : Set (Fin W.rank → D.host.E))
    (γ : GA D V) (d : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hγ : Formalism.L2.Theta.mt V γ⁻¹ = dᴴ.map (incA D))
    (hd : ∀ s ∈ LV, d *ᵥ s ∈ LV) {u : WO V W} (hu : u ∈ latO V W LV LW fun _ => True) :
    actO V W γ 1 u ∈ latO V W LV LW fun _ => True := by
  have h1 : Formalism.L2.Theta.mt W 1 = 1 := rfl
  unfold actO
  rw [h1, Matrix.one_mul, hγ]
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, h0, a, ha, d *ᵥ s, hd s hs, t, ht, ?_⟩
    ext i j
    simp only [hV, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.one_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.mulVec, dotProduct, star_sum, star_mul',
      Finset.mul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1; ring
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

theorem realPt_mul (V W : HSp D) (X : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) :
    HMul.hMul (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W X : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (b.map (incA D)) =
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W (X * b) := by
  ext i j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

open scoped ComplexOrder in

theorem exists_phase {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hP : IsPair ψ θ V W χV χW om)
    {ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)}
    (h3 : IsSelfDualC V ΛV) (h4 : IsSelfDualC W ΛW) {s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (hs : ∀ τ, IsCartanInv (gramAt D W τ) (s τ)) {f : WO V W → ℂ}
    (hf : IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f)
    (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : bᴴ * b = 1) (h1 : ∀ x ∈ ΛV, b *ᵥ x ∈ ΛV)
    (h2 : ∀ x ∈ ΛV, bᴴ *ᵥ x ∈ ΛV) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ (g : GA D W) (X : Matrix (Fin W.rank) (Fin V.rank) D.host.E),
      om (1, g) f (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W (X * b)) = c * om (1, g) f (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W X) := by
  obtain ⟨β, hβ, e1, e2⟩ := exists_rat_of_unitary V hP.std b hb
  have hv := GlobalTheory.WeilVacMove.isVacO_om D ψ θ V W χV χW om hP.weil hP.inf (fun _ => 1) (fun _ => 1) s s _ _ _ _ β 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by
      have : compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 := by
        rw [show Formalism.L2.Theta.mt W 1 = 1 from rfl]
        exact Matrix.map_one _ (by simp) (by simp)
      rw [this, Matrix.one_mul, Matrix.mul_one])
    (fun u => ⟨fun hu => ⟨actO V W β⁻¹ 1 u, actO_mem_of_rat V W hP.std _ _ β⁻¹ bᴴ
        (by rw [inv_inv, Matrix.conjTranspose_conjTranspose, e1]) h2 hu, by
        have := GlobalTheory.WeilVacMove.actO_inv_actO β⁻¹ (1 : GA D W) u
        rw [inv_inv, inv_one] at this
        exact this.symm⟩,
      fun ⟨u₀, hu₀, e⟩ => e ▸ actO_mem_of_rat V W hP.std _ _ β b e2 h1 hu₀⟩) f hf
  have hg : ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun τ => by
    rw [GlobalTheory.AdTh.PhaseMap.gramAt_one hP.std]
    exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  obtain ⟨c, hc, hcf⟩ := GlobalTheory.VacUnique.vacUniqueO D ψ θ hf.1 hP.inf V W _ s hP.sigV hP.sigW hg hs ΛV ΛW h3 h4 f _ hf hv
  refine ⟨c, hc, fun g X => ?_⟩
  have h := GlobalTheory.RatSubst.om_rat_left_apply D ψ V W χV χW om hP.weil _ (hP.weil.om_pres (1, g) f hf.2.theta) β hβ
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W X)
  have hcomm : om (β, 1) (om (1, g) f) = om (1, g) (om (β, 1) f) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one,
      one_mul, mul_one]
  rw [hcomm, hcf, map_smul] at h
  unfold actO at h
  rw [inv_inv, show Formalism.L2.Theta.mt W 1 = 1 from rfl, Matrix.one_mul, e1, realPt_mul] at h
  exact h.symm

theorem mulVec_mem_of_basis {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (b : Matrix (Fin n) (Fin n) D.host.E)
    (hb : bᴴ * b = 1) (h : Λ = Formalism.L2.Pj.stdLat D.host.E n)
    (h' : Λ = Submodule.span (𝓞 D.host.E) (Set.range fun a i => b i a)) :
    (∀ x ∈ Λ, b *ᵥ x ∈ Λ) ∧ ∀ x ∈ Λ, bᴴ *ᵥ x ∈ Λ := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [h] at hx
    choose y hy using fun a => Submodule.mem_one.1 (hx a trivial)
    have e : b *ᵥ x = ∑ a, y a • fun i => b i a := by
      funext i
      simp [Matrix.mulVec, dotProduct, ← hy, Algebra.smul_def, mul_comm]
    rw [e, h']
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [h'] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [h]
      intro j _
      change (bᴴ * b) j a ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)
      rw [hb, Matrix.one_apply]
      split_ifs
      · exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · exact zero_mem _
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx

theorem frAt_of_atComp {W : HSp D} {S : D.what₂.Tau → Finset (ℚ × Bool)} (M : Formalism.IndefR.Mult.DSModel W S) {θ : InfFam D}
    (hθ : IsInfFam θ) {r : ℕ} (hr : W.rank = r) {Comp : Type} {X : Comp → Data D.host.E r}
    {dict : GA D W → Σ k, Frame (X k).Ψ r} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (h0 : IsModelBaseFrameFamily M hr x₀)
    {h γ : GA D W} (ha : AtComp θ W hr X dict x₀ h γ) : FrAt M θ hr dict γ h := by
  rintro ρ ⟨τ, hτ⟩ e
  obtain rfl : τ = tauE D ρ := e
  rw [← h0.mul, ← CcModel.realM_mt hθ W (γ * h) (tauE D ρ) ⟨ρ, rfl⟩ _ (hθ ρ)]
  exact congrFun ha.2.2 ⟨_, hτ⟩

theorem exists_theta_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp}
    {x : (U.X k).dom} (hσ : GoodEmb c σ) (hU : IsUnf U) (h1 : 1 ≤ r) (Wt : PullbackSections.UnfAt U k x) (Y : PullbackSections.UnitAt Wt)
    {bas : (Fin Wt.g ⊕ Fin Wt.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ} {idx : Fin Wt.g ≃ (U.X k).Ψ × Fin r} (hb : IsSympl (U.X k) bas)
    (hg : GenReads U k bas idx Wt.e x Y.θ) : ∃ v : Fin r → E, Y.θ (pv (U.X k) idx x.1 v) ≠ 0 := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hU' : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj U) := hU
  obtain ⟨W0⟩ := nonempty_uw hU'
  have hsd : SelfD (U.X k) (U.X k).Λ := (uw_lattice _ H Dw l Xo c σ _ _ hσ hU' h1 W0 k).2.1
  obtain ⟨A, hA⟩ := hg
  have hd := ((GlobalTheory.Dict.reads_existsUnique_theta E H Dw l Xo c r _ _ bas idx _ x.1 _ _ A hb x.2 hsd 1 _).2 Y.θ hA).1
  refine GlobalTheory.FrameEquiv.exists_apply_pv_ne_zero E r _ _ bas idx hb x.1 x.2 _ hd.continuous fun h0 => ?_
  have h9 := Y.c9
  simp [h0] at h9

set_option maxHeartbeats 1000000 in

theorem baseCc_of_framePin : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∃ ph : ℂ, ‖ph‖ = 1 ∧ BaseCc T R i hV ph := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hlev hgrp hfam hmod hthP hT i hS hV hpin
  have hC : GlobalTheory.Core5 R F := ⟨hlev, hgrp, hfam, hmod, hthP⟩
  have hj := inR i
  have hσ : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  have hU := hL.unf _ hj _ hσ
  have hθ : IsInfFam R.θ := hmod.inf
  obtain ⟨hP, hV0, h1, h2, h3, h4, h5⟩ := GlobalTheory.AdTh.RecPair.isPair_record_ofFive D G Pl0 T0 A _ R F hC i A.μ0 hS
  have hM := GlobalTheory.AdTh.models_at_record_ofFive D G Pl0 T0 A T R F κ v₀ hC hT i T.σ₀ rfl
  have hχ : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).1 = T.chiW ((i : ℕ) + 1) T.σ₀ := by
    rw [chiTie_of_chiR T R hT.alg hT.laws.pins.2.2.1 hT.chiR i]
    ext1 x
    change R.mu0 _ x * R.xi A.μ0 x = _
    rw [TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hC.lev.xi_base ▸ hC.lev.xi A.μ0) x, mul_one]
  have hcast : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) T.σ₀ = W),
      MuVal W (T.chiW ((i : ℕ) + 1) T.σ₀) (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) ∧ (∀ γ ∈ GQ W, ∀ h,
        castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) (γ * h) = castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) h) ∧
        ∀ h, castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) h ≠ 0 := by
    intro W hV
    subst hV
    have hu := hL.muUnit _ hj _ hσ
    exact ⟨hL.muVal _ hj _ hσ, fun γ hγ h => (hu.1 γ h).trans (by rw [hu.2.2.1 γ hγ, one_mul]; rfl),
      fun h => norm_ne_zero_iff.1 ((hu.2.1 _).trans_ne one_ne_zero)⟩
  obtain ⟨hmu, hmuQ, hmu0⟩ := hcast _ hV
  obtain ⟨-, -, -, -, -, -, hr1, hrt, -, -, hdom, -⟩ := hM (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) 1).1
  obtain ⟨cc, hcc⟩ := GlobalTheory.AdTh.CcEx.exists_ccIs_of_pair GlobalTheory.chartIndependence_unconditional hP (hχ ▸ hmu) hmuQ (rank_Wc i) hrt
    _ hσ hU hr1 hL.pins.2.1.2 hdom hV0 h1 h2 h3 h4 h5 _ _ (fun k => (hM k).1) (fun k => (hM k).2.1)
    (fun k => (hM k).2.2.1) (hthP.vP i A.μ0).1 (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀))
  have hres : res T (sg0 D A) = T.toCore.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T hT.alg hL.pins.2.2.1]
  have h0 : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.toCore.σ₀) :=
    hres ▸ hT.x0 i (sg0 D A) (base_embedding_good T R hT.alg hL.pins.2.2.1)
  have hΨ : ∀ k, ∀ τ ∈ ((T.U ((i : ℕ) + 1) T.σ₀).X k).Ψ, ∃ ρ, τ = tauE D ρ := fun k τ hτ =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hL.pins.1 τ (((hU.2.1 k).2 τ).1 hτ)
  obtain ⟨ph, b, hph, hb, hpin⟩ := hpin
  have hbb : bᴴ * b = 1 := by
    ext a a'
    have h := hb.1 a a'
    rw [hS.1] at h
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true] at h
    rw [Matrix.one_apply, ← h, Matrix.mul_apply]
    rfl
  obtain ⟨k1, k2⟩ := mulVec_mem_of_basis (R.ΛV i) b hbb (SetLike.coe_injective h5) (SetLike.coe_injective (h1.trans hb.2))
  obtain ⟨c, hc, hmove⟩ := exists_phase hP h3 h4 (GlobalTheory.FrameEquiv.isCartanInv_cart_model _) (hthP.vP i A.μ0).1 b hbb k1 k2
  refine ⟨c * ph, by rw [norm_mul, hc, hph, one_mul], fun k => ?_, fun h γ ha => ?_⟩
  · rw [norm_mul, norm_mul, hc, hph, hL.cUnit _ hj _ hσ k, one_mul, one_mul]
  suffices e : c * ph * T.cE ((i : ℕ) + 1) T.σ₀ (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).1 =
      cc (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).1 by
    beta_reduce
    rw [e]
    exact hcc.2 h γ ha
  obtain ⟨hx, Wt, ⟨Y⟩⟩ := GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.exists_witness T i T.σ₀ hV hL.toLawsM hσ h
  obtain ⟨bas, idx, hs, hi, hgr, hH⟩ := GlobalTheory.FrameConst.exists_genReads_of_unitAt hσ hU hr1 Wt Y
  obtain ⟨v, hv⟩ := exists_theta_ne_zero hσ hU hr1 Wt Y hs hgr
  let X' : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E := Matrix.of fun m _ => v (Fin.cast (rank_Wc i) m)
  have hX : X' * bᴴ * b = X' := by rw [Matrix.mul_assoc, hbb, Matrix.mul_one]
  have hpv : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt v = pv _ idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2 v :=
    funext fun j => (hi.1 _ v j).symm
  have p := hpin h γ ha.1 (frAt_of_atComp _ hθ (rank_Wc i) h0 ha) hx Wt Y (X' * bᴴ)
    (fun _ => pv _ idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2 v) fun a => by
      rw [← hpv]
      congr 1
      funext m
      exact (congrFun (congrFun hX (Fin.cast (rank_Wc i).symm m)) a).symm
  have key := hcc.2 h γ ha hx Wt.g bas idx Wt.e hs hi Y.θ hgr _ (GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) X')
  have hzz : AdTh.zOf R.θ (Vc D i) (Wc D i) (rank_Wc i) _ idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2
      (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X') =
      fun _ => pv _ idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2 v := by
    funext a j
    rw [pv, Function.comp_apply, ← perC_emb, AdTh.zOf]
    congr 1
    funext τ m
    rw [GlobalTheory.FrameConst.realM_realPt hθ _ _ _ (hΨ _ _ τ.2)]
    rfl
  rw [hzz, ← hX, hmove] at key
  rw [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.thetaAt_eq] at p
  simp only [hH] at p
  rw [neg_mul, Complex.exp_neg] at key
  have hprod : ∏ _a : Fin (Vc D i).rank, Y.θ (pv _ idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2 v) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => hv
  refine mul_right_cancel₀ (mul_ne_zero (hmu0 h) hprod) ?_
  have hE := mul_inv_cancel₀ (Complex.exp_ne_zero ((Real.pi / 2 : ℂ) * ∑ _a : Fin (Vc D i).rank,
    GlobalTheory.Dict.hx _ bas idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2
      (pv _ idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2 v) (pv _ idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2 v)))
  generalize cexp _ = Ex at p key hE
  generalize ∏ _a : Fin (Vc D i).rank, Y.θ _ = P at p key ⊢
  linear_combination (-c) * p + Ex * key + (cc _ * castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) h * P) * hE

end GlobalTheory.LevelSeries.PinBase

end
end

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coreConstants_eq_vacuumIdentity_up_to_phase : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∃ ph : ℂ, ‖ph‖ = 1 ∧ BaseCc T R i hV ph := by
  atlas_forward_decl GlobalTheory.LevelSeries.PinBase.baseCc_of_framePin
end

section
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries.SpanInt

variable {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}

theorem rd_add (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f g : Rul C.d.Xo₂ C.d.c₂) :
    C.rd a (f + g) = C.rd a f + C.rd a g := by
  simp only [Cover.rd, map_add, smul_add]

theorem rd_smul (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (x : C.d.c₂.F) (f : Rul C.d.Xo₂ C.d.c₂) :
    C.rd a (x • f) = C.σ₂ x • C.rd a f := by
  simp only [Cover.rd, LinearMap.map_smulₛₗ, map_smul]
  exact smul_comm _ _ _

theorem rd_zero (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) : C.rd a 0 = 0 := by
  simp only [Cover.rd, map_zero, smul_zero]

theorem vAdd_nonneg {k : Type} [Field k] [NumberField k] (la : HeightOneSpectrum (𝓞 k)) {x : k} (hx0 : x ≠ 0)
    (hx : la.valuation k x ≤ 1) : 0 ≤ vAdd la x := by
  unfold vAdd
  have h2 : (la.valuation k) x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr hx
  rw [WithZero.log_one] at h3
  omega

theorem cuspSec_add (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {f g : Rul C.d.Xo₂ C.d.c₂}
    (hf : f ∈ C.cuspSec a n) (hg : g ∈ C.cuspSec a n) : f + g ∈ C.cuspSec a n :=
  ⟨add_mem hf.1 hg.1, by rw [map_add]; exact add_mem hf.2 hg.2⟩

theorem cuspSec_smul (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : C.d.c₂.F)
    {f : Rul C.d.Xo₂ C.d.c₂} (hf : f ∈ C.cuspSec a n) : x • f ∈ C.cuspSec a n :=
  ⟨Submodule.smul_mem _ x hf.1, by rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hf.2⟩

theorem cuspSec_zero (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : (0 : Rul C.d.Xo₂ C.d.c₂) ∈ C.cuspSec a n :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem exists_of_mem_span_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    {φ : GA D (T.V j σ) → ℂ} (hφ : φ ∈ Submodule.span C.σ₂.range (C.ratForms a n)) :
    ∃ f ∈ C.cuspSec a n, C.rd a f = φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, cuspSec_zero C a n, rd_zero C a⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := hy
    exact ⟨f + g, cuspSec_add C a n hf hg, rd_add C a f g⟩
  | smul s x _ hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨s, y, rfl⟩ := s
    exact ⟨y • f, cuspSec_smul C a n y hf, by rw [rd_smul]; rfl⟩

theorem exists_of_mem_span_intForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) {φ : GA D (T.V j σ) → ℂ}
    (hφ : φ ∈ Submodule.span (locRing C.σ₂ la) (C.intForms a n {la})) :
    ∃ f ∈ C.cuspSec a n, (∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v f) ∧ C.rd a f = φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, ⟨hf, hv⟩, rfl⟩ := hx
    exact ⟨f, hf, hv la rfl, rfl⟩
  | zero =>
    refine ⟨0, cuspSec_zero C a n, fun v hv => ?_, rd_zero C a⟩
    rw [(isVal_valSet la v hv).zero]
    exact le_top
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, hvf, rfl⟩ := hx
    obtain ⟨g, hg, hvg, rfl⟩ := hy
    exact ⟨f + g, cuspSec_add C a n hf hg,
      fun v hv => (le_min (hvf v hv) (hvg v hv)).trans ((isVal_valSet la v hv).add _ _), rd_add C a f g⟩
  | smul s x _ hx =>
    obtain ⟨f, hf, hvf, rfl⟩ := hx
    obtain ⟨s, y, hy, rfl⟩ := s
    refine ⟨y • f, cuspSec_smul C a n y hf, fun v hv => ?_, by rw [rd_smul]; rfl⟩
    by_cases h0 : y = 0
    · rw [h0, zero_smul, (isVal_valSet la v hv).zero]
      exact le_top
    · rw [(isVal_valSet la v hv).smul y f h0]
      exact add_nonneg (by exact_mod_cast vAdd_nonneg la h0 hy) (hvf v hv)

theorem eq_of_rd_eq (D : D7) (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : Formalism.L2.Pj.InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (C : Cover T j σ) (hC : C.IsUnif) (hcc : CUnit C.cc₂) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (ha : Dom a n) {f g : Rul C.d.Xo₂ C.d.c₂} (hf : f ∈ sec C.d.Xo₂ C.d.c₂ a n) (hg : g ∈ sec C.d.Xo₂ C.d.c₂ a n)
    (h : C.rd a f = C.rd a g) : f = g := by
  by_contra hne
  have hli : LinearIndependent C.d.c₂.F (fun _ : Fin 1 => f - g) :=
    LinearIndependent.of_subsingleton 0 (sub_ne_zero.2 hne)
  have h2 := GlobalTheory.CoverIndep.cover_rd_linearIndependent D T hT j hj σ hσ C hC hcc a n ha 1 (fun _ => f - g)
    (fun _ => sub_mem hf hg) hli
  have h3 : C.rd a (f - g) = 0 := by
    have e := rd_add C a (f - g) g
    rw [sub_add_cancel, h] at e
    calc C.rd a (f - g) = (C.rd a (f - g) + C.rd a g) - C.rd a g := by abel
      _ = 0 := by rw [← e, sub_self]
  exact h2.ne_zero 0 h3

theorem mem_intForms_of_spans : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → CUnit C.cc₂ → ∀ (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom wa n → ∀ (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) (φ : GA D (T.V j σ) → ℂ), φ ∈ Submodule.span C.σ₂.range (C.ratForms wa n) → (∀ la ∈ S, φ ∈ Submodule.span (locRing C.σ₂ la) (C.intForms wa n {la})) → φ ∈ C.intForms wa n S := by
  intro D T hT j hj σ hσ C hC hcc wa n hn S φ hφ hS
  obtain ⟨f, hf, rfl⟩ := exists_of_mem_span_ratForms C wa n hφ
  refine ⟨f, ⟨hf, fun la hla => ?_⟩, rfl⟩
  obtain ⟨g, hg, hvg, hfg⟩ := exists_of_mem_span_intForms C wa n la (hS la hla)
  rw [eq_of_rd_eq D T hT j hj σ hσ C hC hcc wa n hn hf.1 hg.1 hfg.symm]
  exact hvg

end GlobalTheory.LevelSeries.SpanInt
end

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralForms_of_rational_and_local_spans : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → CUnit C.cc₂ → ∀ (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom wa n → ∀ (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) (φ : GA D (T.V j σ) → ℂ), φ ∈ Submodule.span C.σ₂.range (C.ratForms wa n) → (∀ la ∈ S, φ ∈ Submodule.span (locRing C.σ₂ la) (C.intForms wa n {la})) → φ ∈ C.intForms wa n S := by
  atlas_forward_decl GlobalTheory.LevelSeries.SpanInt.mem_intForms_of_spans
end

section
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.TwistInt

set_option maxHeartbeats 1000000 in

theorem mul_twist_mem_intForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ C : Cover T j T.σ₀, C.IsUnif → (∃ φ : D.host.K →+* C.d.c₂.F, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ C.d.l₂.M) → ∀ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTwist C.σ₂ C.d.pd xi → ∀ (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), ∀ φ ∈ C.intForms wa n S, (fun g => ((xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g)) : ℂˣ) : ℂ) * φ g) ∈ C.intForms wa n S := by
  intro D T hL j hj C hU hRay xi hxi wa n S φ hφ
  have hP : T.Q.Pins := hL.pins
  have hlev : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have hM3 : 3 ≤ C.d.l₂.M := C.d.l₂.three_le
  have hpd : 0 < C.d.pd := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hlev; omega

  have hsq : ∃ a : D.host.K, a ^ 2 = -(T.Q.H.d : D.host.K) := by
    refine ⟨⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩, ?_⟩
    rw [show T.Q.H.d = D.host.d from hP.1.1]
    apply Subtype.ext
    have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
    simpa using hb
  obtain ⟨φK, hφK⟩ := hRay
  have hW := (GlobalTheory.T.weberValues_mem_of_containsRayField D.host.E T.Q.H D.host.K C.d.c₂.F φK C.d.c₂.F.val.toRingHom (Formalism.L2.Pj.LPb.finrank_K D) hsq
    C.d.l₂.M hM3 hφK).1
  have hWc : GlobalTheory.FinalJoin.WeberIn T.Q.H C.d.c₂.F C.d.l₂.M := fun P hP' => by
    have hsub : ∀ z ∈ C.d.c₂.F.val.toRingHom.toRatAlgHom.fieldRange, z ∈ C.d.c₂.F := fun z hz' => by
      obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.1 hz'
      exact y.2
    obtain ⟨a1, a2⟩ := hW P hP'
    exact ⟨hsub _ a1, fun s hs => hsub _ (a2 s hs)⟩

  have hno : ∀ g : GA D (T.V j T.σ₀),
      GlobalTheory.FinalJoin.NormOne (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g)) := fun g => by
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (T.V j T.σ₀)).1 g
    rw [← GlobalTheory.NormOneTwist.finQuot_of_isDetRoot hx]
    exact GlobalTheory.NormOneTwist.normOne_finQuot x
  obtain ⟨m, hm, hexp⟩ := GlobalTheory.XiCounterexample.fin_of_rat_tame D C.d.pd hpd xi hxi.rat hxi.cond
  choose w hw using fun g => hxi.val _ (hno g)
  have hinj : ∀ g g', xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g)) =
      xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g')) → w g = w g' :=
    fun g g' h => C.σ₂.injective (by rw [hw, hw, h])
  have hleft : ∀ γ ∈ GQ (T.V j T.σ₀), xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) γ)) = 1 := by
    intro γ hγ
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (T.V j T.σ₀)).2.2.1 γ hγ
    rw [← GlobalTheory.NormOneTwist.finQuot_of_isDetRoot hx]
    exact hxi.rat _ _ (GlobalTheory.NormOneTwist.finQuot_incA x) (GlobalTheory.NormOneTwist.normOne_finQuot _)
  have hright : ∀ u : GA D (T.V j T.σ₀), GlobalTheory.Member.FinCong (T.V j T.σ₀) C.d.l₂.M u →
      xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) u)) = 1 := by
    intro u hu
    obtain ⟨k1, -, k3, k4, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D (T.V j T.σ₀)
    obtain ⟨w', hw', e⟩ := GlobalTheory.CharRead.det_cong_one D.host.F (GlobalTheory.Member.latC (T.V j T.σ₀)) k3 k4 C.d.l₂.M (by omega)
      (finHom (T.V j T.σ₀) u).1 (by rw [← k1]; exact hu)
    refine hxi.cond _ (hno u) ⟨T.Q.l.M • w', AddSubgroup.nsmul_mem _ (GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers D ▸ hw') _, ?_⟩
    rw [smul_smul, mul_comm, ← hlev]
    exact e
  have key := (GlobalTheory.CoverComp.forms_mul_comp D T hL j hj T.σ₀ rfl C hU C.d.l₂.M (by omega) dvd_rfl (Or.inl hWc) w
    (fun h h' hh => hinj _ _ (by rw [hh]))
    (fun γ hγ h => hinj _ _ (by rw [map_mul, map_mul, map_mul, hleft γ hγ, one_mul]))
    (fun u _ hu2 h => hinj _ _ (by rw [map_mul, map_mul, map_mul, hright u hu2, mul_one])) wa n).2 S ?_ φ hφ
  · simpa only [hw] using key
  · intro la _ h
    have hpow : w h ^ m = 1 := C.σ₂.injective (by
      rw [map_pow, hw, map_one, ← Units.val_pow_eq_pow_val, hexp _ (hno h), Units.val_one])
    have hint : IsIntegral ℤ (w h) := IsIntegral.of_pow hm (by rw [hpow]; exact isIntegral_one)
    have := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := C.d.c₂.F) la (⟨w h, hint⟩ : 𝓞 C.d.c₂.F)
    exact this

end GlobalTheory.TwistInt
end

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistDeterminant_mul_integralForms_rayClassCover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ C : Cover T j T.σ₀, C.IsUnif → (∃ φ : D.host.K →+* C.d.c₂.F, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ C.d.l₂.M) → ∀ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTwist C.σ₂ C.d.pd xi → ∀ (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), ∀ φ ∈ C.intForms wa n S, (fun g => ((xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g)) : ℂˣ) : ℂ) * φ g) ∈ C.intForms wa n S := by
  atlas_forward_decl GlobalTheory.TwistInt.mul_twist_mem_intForms
end

section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

section Ring

variable {k : Type} [Field k] [NumberField k] {σ : k →+* ℂ} {la : HeightOneSpectrum (𝓞 k)} {O : Subring ℂ} {l : ℕ}

theorem val_le_of_integral (hl : ((l : ℕ) : 𝓞 k) ∈ la.asIdeal) {m : ℕ} (hm : Nat.Coprime m l) {x : k}
    (hx : IsIntegral ℤ ((m : k) * x)) : la.valuation k x ≤ 1 := by
  have h1 : la.valuation k ((m : k) * x) ≤ 1 := la.valuation_le_one (K := k) (⟨_, hx⟩ : 𝓞 k)
  rwa [map_mul, GlobalTheory.ScalarUnit.val_natCast la hl hm, one_mul] at h1

theorem mem_of_integral (hl : ((l : ℕ) : 𝓞 k) ∈ la.asIdeal) (hO : ValRing σ la O) {m : ℕ} (hm : Nat.Coprime m l) {z : ℂ}
    (hz : ∃ x, σ x = z) (hi : IsIntegral ℤ ((m : ℂ) * z)) : z ∈ O := by
  obtain ⟨x, rfl⟩ := hz
  refine hO x (val_le_of_integral hl hm ?_)
  rw [← isIntegral_algHom_iff σ.toIntAlgHom σ.injective]
  simpa using hi

theorem inv_mem_of_coprime (hl : ((l : ℕ) : 𝓞 k) ∈ la.asIdeal) (hO : ValRing σ la O) {m : ℕ} (hm : Nat.Coprime m l) :
    (m : ℂ)⁻¹ ∈ O := by
  have := hO (m : k)⁻¹ (by rw [map_inv₀, GlobalTheory.ScalarUnit.val_natCast la hl hm, inv_one])
  simpa using this

end Ring

theorem zeta_mem_range {k : IntermediateField ℚ ℂ} {M : ℕ} (hM : M ≠ 0) (h : zeta M ∈ k) (σ : k →+* ℂ) :
    ∃ x, σ x = zeta M := by
  have h0 : IsPrimitiveRoot (zeta M) M := Complex.isPrimitiveRoot_exp M hM
  have h1 : IsPrimitiveRoot (⟨zeta M, h⟩ : k) M :=
    IsPrimitiveRoot.of_map_of_injective (f := k.val.toRingHom) h0 Subtype.val_injective
  have h2 := h1.map_of_injective σ.injective
  haveI : NeZero M := ⟨hM⟩
  obtain ⟨j, -, hj⟩ := h2.eq_pow_of_pow_eq_one h0.pow_eq_one
  exact ⟨⟨zeta M, h⟩ ^ j, by rw [map_pow, hj]⟩

theorem bddAll_scale {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {la : HeightOneSpectrum (𝓞 c.F)} {κ n : ℤ} {f : Rul Xo c}
    (h : GlobalTheory.GoodPts.BddAll Xo c la (κ : c.F) f) (hd : κ ∣ n) : GlobalTheory.GoodPts.BddAll Xo c la 1 ((n : c.F) • f) := by
  obtain ⟨j, rfl⟩ := hd
  intro T io e ho y hy
  have := mul_mem (intCast_mem (algebraMap T.V T.Fr).range j) (h T io e ho y hy)
  rw [map_one, one_mul, evI_smul, Int.cast_mul, map_mul, map_intCast io j, mul_comm (io _), mul_assoc]
  exact this

theorem exists_denom {X ι : Type} [AddCommGroup X] [Module ℂ X] (J : X →ₗ[ℂ] MvPolynomial ι ℂ) (Lat : Submodule ℤ X)
    (hL : Lat.FG) (l : ℕ) (hl : l.Prime) : ∃ c : ℕ, ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ)
      (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O →
      (∀ v ∈ Lat, ∀ mo, ∃ x, σ x = (J v).coeff mo) → ∀ v ∈ Lat, ∀ mo, ((l : ℂ) ^ c • J v).coeff mo ∈ O := by
  have one : ∀ z : ℂ, ∃ c : ℕ, IsAlgebraic ℤ z → ∃ m : ℕ, Nat.Coprime m l ∧ IsIntegral ℤ ((m : ℂ) * ((l : ℂ) ^ c * z)) := by
    intro z
    by_cases hz : IsAlgebraic ℤ z
    · obtain ⟨y, hy0, hy⟩ := hz.exists_integral_multiple
      obtain ⟨c, m, hm, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hy0) l hl.ne_one
      refine ⟨c, fun _ => ⟨m, ((Nat.Prime.coprime_iff_not_dvd hl).2 hm).symm, ?_⟩⟩
      have e2 : (m : ℂ) * ((l : ℂ) ^ c * z) = ((y.natAbs : ℕ) : ℂ) * z := by rw [e]; push_cast; ring
      rw [e2]
      rw [zsmul_eq_mul] at hy
      have e3 : ((y.natAbs : ℕ) : ℂ) = ((y.sign : ℤ) : ℂ) * (y : ℂ) := by
        rw [← Int.cast_mul, Int.sign_mul_self_eq_natAbs, Int.cast_natCast]
      rw [e3, mul_assoc]
      exact (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := y.sign)).mul hy
    · exact ⟨0, fun h => absurd h hz⟩
  choose cz hcz using one
  obtain ⟨S, rfl⟩ := hL
  refine ⟨S.sup fun v => (J v).support.sup fun mo => cz ((J v).coeff mo), fun k _ _ σ la O hla hO hσ v hv => ?_⟩
  generalize hc : (S.sup fun v => (J v).support.sup fun mo => cz ((J v).coeff mo)) = c
  induction hv using Submodule.span_induction with
  | mem v hv =>
    intro mo
    by_cases hmo : mo ∈ (J v).support
    · have hle : cz ((J v).coeff mo) ≤ c := hc ▸ (Finset.le_sup (f := fun mo => cz ((J v).coeff mo)) hmo).trans
        (Finset.le_sup (f := fun v => (J v).support.sup fun mo => cz ((J v).coeff mo)) hv)
      obtain ⟨x, hx⟩ := hσ v (Submodule.subset_span hv) mo
      have halg : IsAlgebraic ℤ ((J v).coeff mo) := by
        rw [← hx]
        exact ((IsFractionRing.isAlgebraic_iff ℤ ℚ k).2 (Algebra.IsAlgebraic.isAlgebraic x)).algHom σ.toIntAlgHom
      obtain ⟨m, hm, hi⟩ := hcz _ halg
      have h1 := mem_of_integral hla hO hm ⟨(l : k) ^ cz ((J v).coeff mo) * x, by rw [map_mul, map_pow, map_natCast, hx]⟩ hi
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hle
      rw [MvPolynomial.coeff_smul, smul_eq_mul, pow_add, mul_assoc]
      exact mul_mem (pow_mem (natCast_mem O l) _) h1
    · rw [MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.1 hmo, smul_zero]; exact zero_mem _
  | zero => intro mo; simp
  | add x y _ _ hx hy => intro mo; rw [map_add, smul_add, MvPolynomial.coeff_add]; exact add_mem (hx mo) (hy mo)
  | smul n x _ hx =>
    intro mo
    rw [map_zsmul, smul_comm, MvPolynomial.coeff_smul]
    exact zsmul_mem (hx mo) n

set_option maxHeartbeats 2000000 in

theorem series_bound {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)} {sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    {f₀ : WO V W → ℂ} (hP : VacPair ψ θ V W χV χW om ΛV ΛW sW f₀) {r : ℕ} (hr : W.rank = r) (hodd : Odd r)
    {χ : Formalism.L2.Host.HChar D.host.E} {M₀ : ℕ} (hχ : ChiData χW χ M₀) (hM₀ : M₀ ≠ 0)
    {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    {lt : LtN Dw V.rank ≃ FVar D W.rank V.rank} {wa : (D.host.E →+* ℂ) × ℕ → ℕ} (hpq : W.rank = Dw.p + Dw.q)
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hB : ∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) Dw.p)
    (hlt : IsLetters Dw lt) (hDom : Dom wa V.rank) (hLast : LastPos Dw wa) {l : ℕ} (hl : l.Prime) {s : GA D V} (hs : s ∈ GfC V) :
    ∃ c : ℕ, ∀ (l₂ : Geo.Tor.Level H) (pd : ℕ) (Xo : Moduli Dw l₂) (c₂ : Coeff l₂) (σ : c₂.F →+* ℂ) (U : Unf Xo c₂ σ r)
      (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E))
      (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (mu : GA D W → ℂ) (cc : U.Comp → ℂ),
      l₂.M = M₀ * pd → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime l₂.M (GlobalTheory.Tow.badN D) → l₂.A = 1 → l₂.GoodAt l →
      (∀ τ, relab c₂ σ τ = τ) → GoodEmb c₂ σ → IsDict U W hr dict ι x₀ → FrameTie U W hr x₀ sW BW →
      CcIs θ V W hr U dict mu x₀ om f₀ cc → χ.ValuesIn (-1 / 2) σ →
      ∀ (la : HeightOneSpectrum (𝓞 c₂.F)) (O : Subring ℂ), ((l : ℕ) : 𝓞 c₂.F) ∈ la.asIdeal → ValRing σ la O →
      ∀ (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (Φ φ : WO V W → ℂ), IsIdemSum e P →
        (∀ PP ∈ P, ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) →
        GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsLevelFn (cA D e) (latO V W ΛV ΛW fun _ => True) l₂.M Φ → (∀ x, Φ x ∈ O) →
        IsThetaAt ψ (symplO V W) (heisO ψ V W) (cA D e) (latO V W ΛV ΛW fun _ => True) 1 f₀ Φ φ →
      ∀ Q ∈ HHa Dw.mult V.rank ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)), (∀ mo, Q.coeff mo ∈ O) →
        ∃ (m : ℕ) (β : Fin m → ℂ) (f : Fin m → Rul Xo c₂), (∀ k, β k ∈ O ∧ f k ∈ sec Xo c₂ wa V.rank ∧
          rdU U (f k) ∈ Formalism.L2.Pj.holSub0 U.X (laU U wa V.rank) ∧ GlobalTheory.GoodPts.BddAll Xo c₂ la 1 (f k)) ∧
          ∀ g : GA D W, (l : ℂ) ^ c * thetaKO om s g (stdF ψ θ V W sW BW φ (MvPolynomial.rename lt Q)) =
            ∑ k, β k * ((lieFac Dw (xiR D) wa : ℂ) * (cc (dict g).1 * mu g * rdU U (f k) (dict g).1 (dict g).2)) := by
  subst hr
  obtain ⟨K, hK⟩ := GlobalTheory.T.vacuum_pair_uniform_level_bound D ψ θ V W χV χW om ΛV ΛW sW f₀ hP
  obtain ⟨Z, cf, hZ, hflip⟩ := GlobalTheory.T.exists_centralFlip_thetaTranslate_halfLevel D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l hχ hl hM₀
  choose cm hcm using fun z : Z => GlobalTheory.T.exists_levelSeries_translate_boundedDenominator D ψ θ V W χV χW om ΛV ΛW sW f₀ hP l hl (s * z) (mul_mem hs (hZ z z.2))
  obtain ⟨ca, hca⟩ := GlobalTheory.T.real_rational_point_acts_harmonic_substitution D ψ θ V W χV χW om ΛV ΛW sW f₀ hP H Dw BW lt wa hpq hΨ hB hlt l (Finset.univ.sup cm)
  obtain ⟨c₃, hc₃⟩ := GlobalTheory.ConstBound.const_dvd _ H Dw V.rank (degA Dw wa) M₀ l hl hM₀
  obtain ⟨v, M₁, hM₁, eM⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM₀ l hl.ne_one
  refine ⟨v * K + cf + ca + c₃, fun l₂ pd Xo c₂ σ U dict ι x₀ mu cc hM hc1 hc2 hbadN hA hgood hrel hσ hD hF hcc hval la O hla hO
    e P Φ φ he hPM hΦ hΦO hth Q hQ hQO => ?_⟩
  have hM0 : l₂.M ≠ 0 := by have := l₂.three_le; omega
  have hconj : ConjIn D σ := fun τ a => ⟨embF c₂ τ a, RingHom.congr_fun (hrel τ) a⟩
  have hz : zeta l₂.M ∈ O := by
    have h1 := c₂.zeta_mem
    rw [Geo.Tor.Level.M', hA, Nat.lcm_one_right] at h1
    refine mem_of_integral hla hO (Nat.coprime_one_left l) (zeta_mem_range hM0 h1 σ) ?_
    rw [Nat.cast_one, one_mul]
    exact (Complex.isPrimitiveRoot_exp _ hM0).isIntegral (Nat.pos_of_ne_zero hM0)
  have hn : Nat.Coprime (M₁ * pd) l := Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd hl).2 hM₁).symm hc2
  have hn0 : ((M₁ * pd : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun h => hl.one_lt.ne' (by simpa [h] using hn)
  have h4 : ((l : ℂ) ^ (v * K)) • φ ∈ trSp ψ V W ΛV ΛW f₀ e l₂.M O := by
    have h1 := Submodule.smul_mem _ (⟨_, pow_mem (inv_mem_of_coprime hla hO hn) K⟩ : O)
      (hK l₂.M e P O Φ φ hM0 hbadN he hPM hz hΦ hΦO hth)
    convert h1 using 1
    change _ = (((M₁ * pd : ℕ) : ℂ)⁻¹ ^ K) • ((l₂.M : ℂ) ^ K • φ)
    rw [smul_smul, hM, eM, mul_assoc, Nat.cast_mul (l ^ v), mul_pow, inv_pow, mul_left_comm, inv_mul_cancel₀ (pow_ne_zero _ hn0),
      mul_one, Nat.cast_pow, pow_mul]
  obtain ⟨e₂, he₂⟩ := GlobalTheory.SingleDatum.exists_isHalfIdem D H l₂
  obtain ⟨z₂, hz₂, z₁, hz₁, hone, hfl⟩ := hflip H l₂ pd hM hc1 hc2 hbadN c₂.F σ la O hla hO hconj hval hz e e₂ P he hPM he₂
  obtain ⟨f', hf', hser₁⟩ := hfl _ h4
  have hbad0 : 2 * l * l₂.M ≠ 0 := Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero hl.ne_zero) hM0
  have b1 : l ∣ 2 * l * l₂.M := (dvd_mul_left l 2).mul_right _
  have b2 : l₂.M ∣ 2 * l * l₂.M := dvd_mul_left _ _
  obtain ⟨γ, h, a, γ', hγ, hrat, ha, hγa, hh, ⟨m, hm, hden⟩, hser₂⟩ := hcm ⟨z₂, hz₂⟩ z₁ hz₁ hone l₂.M _ hM0 hbad0 b1
  have hent : ∀ (τ : D.host.E →+* ℂ) (x : D.host.E), IsIntegral ℤ (((m * l ^ cm ⟨z₂, hz₂⟩ : ℕ) : D.host.E) * x) →
      (l : ℂ) ^ Finset.univ.sup cm * τ x ∈ O := fun τ x hx => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := cm) (Finset.mem_univ ⟨z₂, hz₂⟩))
    rw [hd, pow_add, mul_assoc]
    refine mul_mem (pow_mem (natCast_mem O l) _) (mem_of_integral hla hO hm ?_ ?_)
    · obtain ⟨y, hy⟩ := hconj τ x
      exact ⟨(l : c₂.F) ^ cm ⟨z₂, hz₂⟩ * y, by rw [map_mul, map_pow, map_natCast, hy]⟩
    · have := hx.map τ.toIntAlgHom
      simpa [mul_assoc] using this
  obtain ⟨Q', hQ', hQ'O, harch⟩ := hca γ a γ' O hγ hrat ha hγa (fun τ x y => ⟨hent τ _ (hden x y).1, hent τ _ (hden x y).2⟩) Q hQ hQO
  obtain ⟨u, hu, rfl⟩ := GlobalTheory.T.exists_levelPointsTranslateMean_of_integral_combination D ψ θ V W χV χW om ΛV ΛW sW f₀ hP H Dw ι hD.2.1 l₂ e₂ he₂ hbadN O f' hf'
  obtain ⟨Λ, n, hΛ, hun, hT, hnl, hN⟩ := GlobalTheory.SingleDatum.exists_conjLat_levOK D V hP.1.std (hP.2.2.1.symm.trans hP.2.2.2.2.2.2.1)
    (2 * l * l₂.M) l₂.M l l₂.odd ((dvd_mul_right 2 l).mul_right _) b2 b1 h hh
  obtain ⟨hhf, e', Ps, he', hPs, hsupp⟩ := hh
  obtain ⟨y, hy⟩ := GlobalTheory.PtId.exists_isDetAt he' V h
  have hep := GlobalTheory.T.splitSupportedClassScalar_mem_valuationRing D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l _ hχ hl ((hM ▸ dvd_mul_right _ _ : M₀ ∣ l₂.M).trans b2) b1
    c₂.F σ la O hla hO hval h Λ e' Ps y hbad0 he' hPs hhf hsupp hy hΛ
  obtain ⟨m', β, f, hf, hsum⟩ := GlobalTheory.T.exists_forms_theta_short_series_identity D ψ θ V W χV χW om ΛV ΛW sW f₀ hP H Dw l₂ Xo c₂ _ σ hrel hσ U hA hodd rfl dict ι x₀ BW mu cc
    hD hF hcc e₂ he₂ _ _ h Λ e' Ps y b2 he' hPs hhf hsupp hy hΛ hun hT hN lt wa hlt hDom hLast la l hl hla hgood O hO u hu Q' hQ' hQ'O
  obtain ⟨u', hu', hdvd⟩ := hc₃ l₂ pd n Λ hM ((Nat.Prime.coprime_iff_not_dvd hl).1 hc2.symm) hnl hN
  have hu0 : (u' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun h => hl.one_lt.ne' (by simpa [h] using hu')
  refine ⟨m', fun k => (-1) ^ degA Dw wa * clsScal χW y Λ W.rank * β k * (u' : ℂ)⁻¹,
    fun k => (((l ^ c₃ * u' : ℕ) : ℤ) : c₂.F) • f k, fun k => ⟨?_, Submodule.smul_mem _ _ (hf k).2.1, ?_, ?_⟩, fun g => ?_⟩
  · exact mul_mem (mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) hep) (hf k).1) (inv_mem_of_coprime hla hO hu')
  · rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (hf k).2.2.1
  · exact bddAll_scale (by have := (hf k).2.2.2; push_cast at this ⊢; exact this) hdvd
  · have e1 := hser₁ BW (MvPolynomial.rename lt Q) s g
    have e2 := hser₂ e₂ O _ hf' BW (MvPolynomial.rename lt Q) g
    have e3 := harch l₂.M e₂ O hM0 _ hf'
    have e4 := hsum g
    rw [← e3] at e4
    rw [GlobalTheory.FiniteFock.pureTensorO_smul] at e1
    replace e2 := e1.trans e2
    simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul] at e2 e4 ⊢
    have e5 : ∀ k, (-1) ^ degA Dw wa * clsScal χW y Λ W.rank * β k * (u' : ℂ)⁻¹ * ((lieFac Dw (xiR D) wa : ℂ) *
        (cc (dict g).1 * mu g * rdU U ((((l ^ c₃ * u' : ℕ) : ℤ) : c₂.F) • f k) (dict g).1 (dict g).2)) =
        (l : ℂ) ^ c₃ * ((-1) ^ degA Dw wa * clsScal χW y Λ W.rank) * (β k * ((lieFac Dw (xiR D) wa : ℂ) *
        (cc (dict g).1 * mu g * rdU U (f k) (dict g).1 (dict g).2))) := fun k => by
      rw [map_smulₛₗ, map_intCast]
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl fun k _ => e5 k, ← Finset.mul_sum, mul_assoc, ← e4, ← e2]
    ring

theorem exists_place_over (k : Type) [Field k] [NumberField k] {l : ℕ} (hl : l.Prime) :
    ∃ la : HeightOneSpectrum (𝓞 k), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal := by
  have h1 : Ideal.span {((l : ℕ) : 𝓞 k)} ≠ ⊤ := fun h => by
    have h2 := Ideal.absNorm_span_natCast (S := 𝓞 k) l
    rw [h, Ideal.absNorm_top] at h2
    exact hl.one_lt.ne' ((pow_eq_one_iff_of_nonneg (Nat.zero_le _) Module.finrank_pos.ne').1 h2.symm)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h1
  have h3 : ((l : ℕ) : 𝓞 k) ∈ m := hle (Ideal.mem_span_singleton_self _)
  exact ⟨⟨m, hm.isPrime, fun h => by rw [h, Ideal.mem_bot] at h3; exact Nat.cast_ne_zero.2 hl.ne_zero h3⟩, h3⟩

theorem goodAt_of_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {l₁ l₂ : Geo.Tor.Level H}
    {pd p : ℕ} (hp : p.Prime) (hM : l₂.M = l₁.M * pd) (hc : Nat.Coprime pd p) (h : l₁.GoodAt p) : l₂.GoodAt p := by
  have h1 : l₁.M ≠ 0 := by have := l₁.three_le; omega
  have h2 : pd ≠ 0 := by rintro rfl; have := l₂.three_le; omega
  unfold Geo.Tor.Level.GoodAt at h ⊢
  rw [hM, Nat.factorization_mul h1 h2, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hc.symm), add_zero]
  exact h.trans (Nat.div_le_div_right (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h2)))

theorem castDict_symm {D : D7} {Y : Type} {V W : HSp D} (h : V = W) (F : GA D W → Y) : castDict h (castDict h.symm F) = F := by
  subst h; rfl

theorem castDict_twist {D : D7} {V W : HSp D} (h : V = W) (xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ) (F : GA D V → ℂ) (g : GA D W) :
    castDict h (fun g => ((xi (Matrix.GeneralLinearGroup.det (finHom V g)) : ℂˣ) : ℂ) * F g) g =
      ((xi (Matrix.GeneralLinearGroup.det (finHom W g)) : ℂˣ) : ℂ) * castDict h F g := by
  subst h; rfl

theorem eq_of_castDict {D : D7} {Y : Type} {V W : HSp D} (h : V = W) {F F' : GA D V → Y}
    (e : ∀ g, castDict h F g = castDict h F' g) : F = F' := by
  subst h; exact funext e

set_option maxHeartbeats 2000000 in

theorem serIntAt_record : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerIntAt T R i (κ i) hV u c0 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd hV hFP u hu c0 hc0
  have hj : Formalism.L2.Pj.InR D ((i : ℕ) + 1) := inR i
  have h5 : GlobalTheory.Core5 R F := ⟨hLev, hG, hFam, hMod, hTh⟩
  obtain ⟨hPr, q1, q2, q3, q4, q5, q6⟩ := GlobalTheory.AdTh.RecPair.isPair_record_ofFive D G Pl0 T0 A _ R F h5 i A.μ0 hstd
  obtain ⟨-, -, f3, -, f5⟩ := GlobalTheory.AdTh.PhaseMapFree.vec_fock_of_clauses D G Pl0 T0 A _ R hMod hTh i A.μ0 hstd
  have hvac := (hTh.vP i A.μ0).1
  have hP : VacPair R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i A.μ0) (R.ΛV i) (R.ΛW i) (cart (R.MW i (sg0 D A))) (R.vacP i) :=
    ⟨hPr, q1, q2, q3, q4, q5, q6, f3, hvac⟩
  obtain ⟨-, -, -, -, hrpq, -, -, -, -, -, hDom, hn, hLast⟩ := GlobalTheory.AdTh.models_at_record_ofFive D G Pl0 T0 A T R F κ v₀ h5 hTie i
    T.σ₀ rfl (T.dict _ T.σ₀ 1).1
  obtain ⟨-, -, hΨ, -, -⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hL.pins _ hj (κ i)
  have hodd : Odd D.R.r := by
    have := D.R.m_add_three_le_k
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hpq := (rank_Wc i).trans hrpq
  have hB : ∀ τ, IsONBasis (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) (onb (R.MW i (sg0 D A)) τ)
      (T.Q.Dw ((i : ℕ) + 1)).p := fun τ => by
    rw [(hL.pins.2.2.2 _ hj).1, ← show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
    exact f5 τ
  have hlt := GlobalTheory.FockLetters.isLetters_letterEquiv (n := (Vc D i).rank) (T.Q.Dw ((i : ℕ) + 1)) hΨ hpq
  generalize GlobalTheory.FockLetters.letterEquiv (n := (Vc D i).rank) (T.Q.Dw ((i : ℕ) + 1)) hΨ hpq = lt at hlt
  have hχ := GlobalTheory.T.referenceTuple_secondSplittingCharacter D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hL.pins.2.1.1
  rw [← hMg] at hχ
  have hM₀ : T.Q.l.M ≠ 0 := by have := T.Q.l.three_le; omega
  have hMb : Nat.Coprime T.Q.l.M (GlobalTheory.Tow.badN D) := by
    have : ∀ k, Nat.Coprime (D.host.g k) (GlobalTheory.Tow.badN D) := fun k =>
      ((D.host.level_coprimeS _ (D.host.g_level k)).mul_right (ReciprocityTheory.ChartRestriction.G.PullbackSections.g_coprime_ram D k _ (by simp))).mul_right
        (D.host.ccK_coprime _ (by simp [D.host.g_level k])).symm
    rw [hMg]
    exact (this 0).mul_left (this 1)
  obtain ⟨ph, hph, hbase⟩ := GlobalTheory.T.coreConstants_eq_vacuumIdentity_up_to_phase D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd hV hFP
  obtain ⟨ka, hka, J, hJH, hJk, hJ⟩ := GlobalTheory.T.harmonicMap_extremalVector_eq_phase_smul_letters D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd u hu c0 hc0 lt hlt
  have hph0 : ph ≠ 0 := fun h => by simp [h] at hph
  have hka0 : ka ≠ 0 := fun h => by simp [h] at hka
  refine ⟨(ka * ph)⁻¹, by rw [norm_inv, norm_mul, hka, hph]; norm_num, fun l hl s hs Lat hLat => ?_⟩
  obtain ⟨c₁, hc₁⟩ := exists_denom J Lat hLat l hl
  obtain ⟨c₂, hc₂⟩ := series_bound hP (rank_Wc i) hodd hχ hM₀ hpq hΨ hB hlt hDom hLast hl hs
  refine ⟨c₂ + c₁, fun C hC hpin hbig S hS xi hxi Φ f hf hΦ v hv => ?_⟩
  obtain ⟨hU, -, hcl, hcb⟩ := hC
  obtain ⟨hval, hcoef, hray⟩ := hbig
  obtain ⟨P, e, he, hPM, hfn, hth⟩ := hf
  obtain ⟨hD, hF, hrel, hσ⟩ := GlobalTheory.T.uniformisedCover_isDictionary_frameCompatible D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd hV C hU
  have hcc := GlobalTheory.T.vacuumIdentityConstants_cover_of_dominantPins D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd hV ph hph hbase C hU hpin
  have hM₂ : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have hgood : C.d.l₂.GoodAt l := goodAt_of_dvd hl hM₂ hcl
    (Formalism.L2.Pj.goodAt_of_two_primes hMg (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne l hl)
  have hθf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f :=
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hPr.weil.std hPr.inf hth hvac.2.theta
  have hfld : ∀ x ∈ T.Q.c.F, x ∈ C.σ₂.fieldRange := fun x hx => ⟨C.inc ⟨x, hx⟩, RingHom.congr_fun hU.2.2.1 ⟨x, hx⟩⟩
  have hJσ : ∀ w ∈ Lat, ∀ mo, ∃ x, C.σ₂ x = (J w).coeff mo := fun w hw mo =>
    hJk C.σ₂.fieldRange hfld w (fun m => hcoef w hw m) mo
  let Fn : GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ := castDict hV.symm fun g =>
    (l : ℂ) ^ (c₂ + c₁) * ((ka * ph)⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.series R i u s f (c0 v) g)
  have key : ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (O : Subring ℂ), ((l : ℕ) : 𝓞 C.d.c₂.F) ∈ la.asIdeal →
      ValRing C.σ₂ la O → (∀ x, Φ x ∈ O) → Fn ∈ Submodule.span O (C.intForms (wtA (κ i)) (κ i).n {la}) := by
    intro la O hla hO hΦO
    obtain ⟨m, β, fs, hfs, hsum⟩ := hc₂ C.d.l₂ C.d.pd C.d.Xo₂ C.d.c₂ C.σ₂ C.U₂ _ _ _ _ _ hM₂ hU.1.2.2.1 hcl
      (hM₂ ▸ hMb.mul_left hcb) hU.2.1 hgood hrel hσ hD hF hcc hval la O hla hO e P Φ f he hPM hfn hΦO hth
      ((l : ℂ) ^ c₁ • J v) (GlobalTheory.PtId.mem_HHa_of_span _ _ _ _ _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (hJH v))))
      (hc₁ _ C.σ₂ la O hla hO hJσ v hv)
    have e1 : Fn = ∑ k, β k • C.rd (wtA (κ i)) (fs k) := by
      refine eq_of_castDict hV fun g => ?_
      rw [castDict_symm]
      have e2 := hsum g
      have e3 : castDict hV (∑ k, β k • C.rd (wtA (κ i)) (fs k)) g = ∑ k, β k * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
          (C.cc₂ (castDict hV C.dict₂ g).1 * castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) g *
            rdU C.U₂ (fs k) (castDict hV C.dict₂ g).1 (castDict hV C.dict₂ g).2)) := by
        unfold castDict
        rw [Finset.sum_apply]
        rfl
      rw [e3, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.series, hJ f hθf v]
      simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul] at e2 ⊢
      have e4 : ∑ k, β k * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
          (ph * C.cc₂ (castDict hV C.dict₂ g).1 * castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) g *
            rdU C.U₂ (fs k) (castDict hV C.dict₂ g).1 (castDict hV C.dict₂ g).2)) = ph *
          ∑ k, β k * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
          (C.cc₂ (castDict hV C.dict₂ g).1 * castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) g *
            rdU C.U₂ (fs k) (castDict hV C.dict₂ g).1 (castDict hV C.dict₂ g).2)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e4] at e2
      refine mul_left_cancel₀ hph0 ?_
      rw [← e2]
      field_simp
      ring
    rw [e1]
    refine sum_mem fun k _ => Submodule.smul_mem _ (⟨β k, (hfs k).1⟩ : O) (Submodule.subset_span ⟨fs k, ⟨?_, ?_⟩, rfl⟩)
    · rw [hn]; exact ⟨(hfs k).2.1, (hfs k).2.2.1⟩
    · rintro _ rfl
      exact (GlobalTheory.T.integral_values_algebraic_points_iff_value_nonneg _ _ _ _ _ _ _ _).1 (hfs k).2.2.2
  have hint : Fn ∈ C.intForms (wtA (κ i)) (κ i).n S := by
    refine GlobalTheory.T.mem_integralForms_of_rational_and_local_spans D T hL _ hj T.σ₀ T.toCore.good_σ₀ C hU (hpin _ (dom_wtA (κ i))).1 _ _ (dom_wtA (κ i)) S Fn ?_ fun la hla => ?_
    · obtain ⟨la, hla⟩ := exists_place_over C.d.c₂.F hl
      exact Submodule.span_mono (C.intForms_subset _ _ _)
        (key la _ hla (valRing_range _ _) fun x => let ⟨a, ha, _⟩ := hΦ x; ⟨a, ha⟩)
    · exact key la _ (hS la hla) (valRing_locRing _ _) fun x => let ⟨a, ha, hb⟩ := hΦ x; ⟨a, hb la hla, ha⟩
  refine ⟨_, GlobalTheory.T.twistDeterminant_mul_integralForms_rayClassCover D T hL _ hj C hU hray xi hxi _ _ S Fn hint, fun g => ?_⟩
  rw [castDict_twist, castDict_symm]
  ring

end GlobalTheory.LevelSeries

end
end
