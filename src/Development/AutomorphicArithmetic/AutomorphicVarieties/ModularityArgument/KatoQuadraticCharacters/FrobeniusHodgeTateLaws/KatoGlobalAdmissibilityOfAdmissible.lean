import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.HtLawCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.DistributionApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.InOfIntIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryMod
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.DetIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.LawMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ThickFrames
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.IndSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SerVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMuModelMeasureOfEigenfunctional
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SumUnits
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsModularFunctionTowerAlgebraicCoefficientsStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.AdmissibleFunctionalOfProjection
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.FormPLamSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.FinSuppCompLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SgDOneMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.CgAppr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuadAlt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSetStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerBAdmissibleHeckeCommuteStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.CgpTrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.LamEig2
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinaryEisensteinEigenfunctionalExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeProjectorNewformGaloisImageStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShapeStatement

section
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.jEx :
    UpperTheory.V.Z.Kato.Joint.JEx := by
  intro l _ Ω _ _ _ A hA
  obtain ⟨v, hv, hl⟩ := hA
  have hAl : A.valuation ((l : ℕ) : Ω) < 1 := by
    have := (hv ((l : ℕ) : NumberField.RingOfIntegers ℚ)).2 hl
    simpa using this
  exact ⟨(ValuationSubring.mem_nonunits_iff _).2 hAl, Formalism.BasicNotions.Examples₂.LB.exists_emb A hAl⟩
end

section
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.coefUb :
    UpperTheory.V.Z.Kato.Joint.CoefUb := by
  intro l _ c c' F hF
  obtain ⟨d, h1, h2⟩ := (UpperTheory.V.HV.coefSup l).1 c c'
  obtain ⟨d', h3, h4⟩ := (UpperTheory.V.Th.Nm.inOf d).1 {x // x ∈ F} (fun x => x.1) (fun x => hF x.1 x.2)
  exact ⟨d', h1.trans h3, h2.trans h3, fun x hx => h4 ⟨x, hx⟩⟩
end

section
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.mono :
    UpperTheory.V.Z.Kato.Joint.Mono := by
  intro l _ Ω _ _ c c' h
  refine ⟨?_, ?_, ?_⟩
  · rintro W y S' ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun s i j => h (h1 s i j), h2, fun s i => h (h3 s i), h4, fun n hn w hw hd ψ hk hs => ?_⟩
    obtain ⟨Y, P, u, b, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h5 n hn w hw hd ψ hk hs
    refine ⟨Y, P, u, b, a1, fun s x i => h (a2 s x i), h a3, a4, fun i => h (a5 i), a6, a7, a8, fun q hq hl => ?_⟩
    obtain ⟨B, hB, t, ht, ht'⟩ := a9 q hq hl
    exact ⟨B, hB, t, fun x i => h (ht x i), ht'⟩
  · rintro A ν Z ⟨h1, h2, h3⟩
    exact ⟨h1, fun r => ⟨fun s x => h ((h2 r).1 s x), (h2 r).2⟩, h3⟩
  · rintro A Z j m₀ c₀ Rhs ⟨ζ, hζ, H⟩
    refine ⟨ζ, hζ, fun m hm => ?_⟩
    obtain ⟨ι, inst, P, o, ⟨p1, p2, p3, p4, p5⟩, hc⟩ := H m hm
    exact ⟨ι, inst, P, o, ⟨p1, p2, fun i => h (p3 i), p4, p5⟩, hc⟩
end

section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open UpperTheory.V.Z.Kato.Joint

private theorem apply_eq_pow_cycMod_of_pow_eq_one (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (s : G ℚ Ω) (ζ : Ω) (hζ : ζ ^ l = 1) :
    s ζ = ζ ^ ((cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).1 inferInstance
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : Nat.Prime l).ne_zero⟩
  exact cyclotomicCharacter.spec l (n := 1) (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ
    (by rwa [pow_one])

private theorem cyc1_surjective (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (u : (ZMod l)ˣ) : ∃ s : G ℚ Ω, cyc1 l s = u := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).1 inferInstance
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : Nat.Prime l).ne_zero⟩
  haveI : NeZero l := ⟨(Fact.out : Nat.Prime l).ne_zero⟩
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  set K := IntermediateField.adjoin ℚ ({ζ} : Set Ω) with hK
  haveI : IsCyclotomicExtension {l} ℚ K := by
    convert hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
    · rfl
    · exact Subsingleton.elim _ _
  haveI : NumberField K := IsCyclotomicExtension.numberField {l} ℚ K
  haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq (fun x => by simp)
  let σ := (IsCyclotomicExtension.Rat.galEquivZMod l K).symm u
  let ζK : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hζK : ζK ^ l = 1 := Subtype.ext (by simpa using hζ.pow_eq_one)
  refine ⟨σ.liftNormal Ω, ?_⟩
  have h1 : (σ.liftNormal Ω) ζ = ζ ^ (u : ZMod l).val := by
    have h2 := σ.liftNormal_commutes Ω ζK
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq l K σ hζK,
      show IsCyclotomicExtension.Rat.galEquivZMod l K σ = u from MulEquiv.apply_symm_apply _ u] at h2
    simpa [ζK] using h2
  have h3 := apply_eq_pow_cycMod_of_pow_eq_one l Ω (σ.liftNormal Ω) ζ hζ.pow_eq_one
  rw [h1] at h3
  have hc : (cycMod ℚ Ω l 1 (σ.liftNormal Ω) : ZMod (l ^ 1)).val < l := by
    simpa [pow_one] using ZMod.val_lt (cycMod ℚ Ω l 1 (σ.liftNormal Ω) : ZMod (l ^ 1))
  have h4 := hζ.pow_inj (ZMod.val_lt (u : ZMod l)) hc h3
  unfold cyc1
  rw [← h4, ZMod.natCast_zmod_val]

theorem UpperTheory.V.Z.Kato.Joint.psiEx :
    UpperTheory.V.Z.Kato.Joint.PsiEx := by
  intro l _ Ω _ _ _ ι χ hχ
  have key : ∀ s t : G ℚ Ω, cyc1 l s = cyc1 l t → χ s = χ t := by
    intro s t hst
    have hv : (cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val = (cycMod ℚ Ω l 1 t : ZMod (l ^ 1)).val := by
      have h1 := congrArg ZMod.val hst
      unfold cyc1 at h1
      have hs : (cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val < l := by
        simpa [pow_one] using ZMod.val_lt (cycMod ℚ Ω l 1 s : ZMod (l ^ 1))
      have ht : (cycMod ℚ Ω l 1 t : ZMod (l ^ 1)).val < l := by
        simpa [pow_one] using ZMod.val_lt (cycMod ℚ Ω l 1 t : ZMod (l ^ 1))
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht] at h1
      exact h1
    have hfix : ∀ ζ : Ω, ζ ^ l = 1 → (t⁻¹ * s) ζ = ζ := by
      intro ζ hζ
      rw [AlgEquiv.mul_apply, apply_eq_pow_cycMod_of_pow_eq_one l Ω s ζ hζ, hv, ← apply_eq_pow_cycMod_of_pow_eq_one l Ω t ζ hζ]
      exact t.symm_apply_apply ζ
    have h1 := hχ (t⁻¹ * s) hfix
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  have hd : l ∣ l ^ 1 := by rw [pow_one]
  have hcast : ∀ s : G ℚ Ω, cyc1 l s = ZMod.cast (cycMod ℚ Ω l 1 s : ZMod (l ^ 1)) := by
    intro s
    unfold cyc1
    rw [ZMod.cast_eq_val]
  have hone : cyc1 l (1 : G ℚ Ω) = 1 := by
    rw [hcast, map_one, Units.val_one, ZMod.cast_one hd]
  have hmul : ∀ s t : G ℚ Ω, cyc1 l (s * t) = cyc1 l s * cyc1 l t := by
    intro s t
    rw [hcast, hcast, hcast, map_mul, Units.val_mul, ZMod.cast_mul hd]
  let sec : (ZMod l)ˣ → G ℚ Ω := fun u => (cyc1_surjective l Ω u).choose
  have hsec : ∀ u, cyc1 l (sec u) = u := fun u => (cyc1_surjective l Ω u).choose_spec
  let f : (ZMod l)ˣ →* ℂˣ :=
    { toFun := fun u => Units.map ι.toMonoidHom (χ (sec u))
      map_one' := by
        rw [key (sec 1) 1 (by rw [hsec, hone, Units.val_one]), map_one, map_one]
      map_mul' := by
        intro u v
        rw [key (sec (u * v)) (sec u * sec v) (by rw [hsec, hmul, hsec, hsec, Units.val_mul]),
          map_mul, map_mul] }
  refine ⟨MulChar.ofUnitHom f, fun s => ?_⟩
  let w : (ZMod l)ˣ := Units.map (ZMod.castHom hd (ZMod l)).toMonoidHom (cycMod ℚ Ω l 1 s)
  have hw : (w : ZMod l) = cyc1 l s := by
    rw [hcast]
    rfl
  rw [← hw, MulChar.ofUnitHom_coe]
  show (χ s : Formalism.ConjugateSelfDual.Qbar l) = ι.symm (ι (χ (sec w) : Formalism.ConjugateSelfDual.Qbar l))
  rw [RingEquiv.symm_apply_apply, key s (sec w) (by rw [hsec, hw])]
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open UpperTheory.V.Z.Kato.Joint

private theorem frobU_normV {p : ℕ} (hp : p.Prime) {v : Pl} (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : normV v = p := by
  have hN : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hspan : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_singleton]
    have h1 : ((p : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
    rw [h1, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
    simp
  have hle : Ideal.span {((p : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hv
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [hspan] at hd
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h1
  · exact absurd (Ideal.absNorm_eq_one_iff.1 h1) v.isPrime.ne_top
  · rw [hN, h1]

theorem UpperTheory.V.Z.Kato.Joint.frobU :
    UpperTheory.V.Z.Kato.Joint.FrobU := by
  intro l hl Ω _ _ _ e S A W hW
  refine ⟨?_, fun s hs => ?_, fun s => ?_⟩
  · obtain ⟨v, hA, hv⟩ := hW.atL
    obtain ⟨σ, hσ⟩ := exists_isFrob (F := ℚ) hA
    rw [frobU_normV hl.out hv] at hσ
    exact ⟨σ, mem_Dec.2 hσ.1, hσ⟩
  · obtain ⟨c, hc⟩ := hW.int
    have hm : mat W s * mat W s⁻¹ = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    have h11 : mat W s 1 1 * mat W s⁻¹ 1 1 = 1 := by
      have h := congrFun (congrFun hm 1) 1
      rw [Matrix.mul_apply, Fin.sum_univ_two, hW.upper s hs, zero_mul, zero_add, Matrix.one_apply_eq] at h
      exact h
    have ha := GlobalTheory.Ord2.CupCob.norm_le_one_of_mem c (hc s 1 1)
    have hb := GlobalTheory.Ord2.CupCob.norm_le_one_of_mem c (hc s⁻¹ 1 1)
    have hn : ‖mat W s 1 1‖ * ‖mat W s⁻¹ 1 1‖ = 1 := by rw [← norm_mul, h11, norm_one]
    refine le_antisymm ha ?_
    calc (1 : ℝ) = ‖mat W s 1 1‖ * ‖mat W s⁻¹ 1 1‖ := hn.symm
      _ ≤ ‖mat W s 1 1‖ := mul_le_of_le_one_right (norm_nonneg _) hb
  · have h : eps l s = algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := rfl
    rw [h, norm_algebraMap']
    exact PadicInt.norm_units _
end

section
open UpperTheory.V.Z.Kato.Joint

private theorem norm_le_of_pow {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (z : ℂ) (n : ℕ) (hn : n ≠ 0)
    (h : z ^ n = 1) : ‖ι.symm z‖ ≤ 1 := by
  have h1 : ‖ι.symm z‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h, map_one, norm_one]
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h1).le

private theorem hat_std {N : ℕ} [NeZero N] (φ : ZMod N → ℂ) (d : ℤ) :
    GlobalTheory.EisM.hat φ d = ∑ y : ZMod N, φ y * ZMod.stdAddChar (y * (d : ZMod N)) := by
  unfold GlobalTheory.EisM.hat
  refine Finset.sum_nbij' (fun i => (i : ZMod N)) (fun y => y.val) (fun _ _ => Finset.mem_univ _)
    (fun y _ => Finset.mem_range.mpr (ZMod.val_lt y)) (fun i hi => ZMod.val_cast_of_lt (Finset.mem_range.mp hi))
    (fun y _ => ZMod.natCast_zmod_val y) (fun i _ => ?_)
  have h : ((i : ZMod N)) * (d : ZMod N) = (((i : ℤ) * d : ℤ) : ZMod N) := by push_cast; rfl
  rw [h, ZMod.stdAddChar_coe]
  push_cast
  rfl

private theorem norm_two' {l : ℕ} [hl : Fact l.Prime] (h : l ≠ 2) : ‖(2 : PadicAlgCl l)‖ = 1 := by
  have h1 : (2 : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) ((2 : ℕ) : ℚ_[l]) := by
    rw [map_natCast]; rfl
  rw [h1, norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes hl.out Nat.prime_two).mpr h)

theorem UpperTheory.V.Z.Kato.Joint.hatW :
    UpperTheory.V.Z.Kato.Joint.HatW := by
  intro l _ ι N _ θ hl
  refine ⟨?_, fun d => ?_, fun d => ?_⟩
  · by_contra hc
    push Not at hc
    have h0 : ZMod.dft (fun y : ZMod N => θ y) = 0 := by
      funext k
      have := hc (-k)
      rw [hat_std] at this
      rw [ZMod.dft_apply, Pi.zero_apply, ← this]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp [mul_comm]
    have h1 := congrFun ((LinearEquiv.map_eq_zero_iff _).mp h0) 1
    simp at h1
  · have h2 : ι.symm 2 = 2 := map_ofNat _ 2
    rw [map_div₀, norm_div, h2, norm_two' hl, div_one, hat_std, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun y _ => ?_
    rw [map_mul, norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) ?_
    · by_cases hy : IsUnit y
      · obtain ⟨u, rfl⟩ := hy
        refine norm_le_of_pow ι _ (Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_
        rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
      · rw [MulChar.map_nonunit _ hy]; simp
    · refine norm_le_of_pow ι _ N (NeZero.ne N) ?_
      rw [← AddChar.map_nsmul_eq_pow]
      simp
  · rw [hat_std, hat_std]
    simp
end

section
open UpperTheory.V.Z.Kato.Joint

private lemma smNz_unit {l : ℕ} [Fact l.Prime] {n : ℕ} (h : ¬ l ∣ n) : IsUnit (n : ZMod l) := by
  rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
  exact h

private lemma smNz_norm {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) {n : ℕ} (h : ¬ l ∣ n) :
    ‖χ (n : ZMod l)‖ = 1 := by
  have hu := smNz_unit (l := l) h
  have := χ.unit_norm_eq_one hu.unit
  rwa [IsUnit.unit_spec] at this

theorem UpperTheory.V.Z.Kato.Joint.smNz :
    UpperTheory.V.Z.Kato.Joint.SmNz := by
  intro l _ ι e N c d ψ a b hN hN0 hc0 hd0 hc hd ha hce hdb
  have hp : l.Prime := Fact.out
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> simp [smT, hp.dvd_mul, hN, hc, hd]
  · simp only [Fin.sum_univ_four, smB, smT, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_mul,
      map_neg, map_pow, map_zpow₀, map_natCast, RingEquiv.apply_symm_apply, Nat.cast_mul,
      MulChar.inv_apply_eq_inv', mul_pow]
    have hC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    have hD : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    have hψN : ψ (N : ZMod l) ≠ 0 := by
      intro h0
      have := smNz_norm ψ hN
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hψc : ψ (c : ZMod l) ≠ 0 := by
      intro h0
      have := smNz_norm ψ hc
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hCe : (c : ℂ) ^ e ≠ 0 := pow_ne_zero _ hC
    have hw : (c : ℂ) ^ ((3 : ℤ) - ((2 * e + 1 : ℕ) : ℤ)) * (c : ℂ) ^ e = (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ := by
      rw [← zpow_natCast (c : ℂ) e, ← zpow_add₀ hC, ← zpow_natCast (c : ℂ) 2, ← zpow_neg,
        ← zpow_add₀ hC]
      congr 1
      push_cast
      ring
    set w := (c : ℂ) ^ ((3 : ℤ) - ((2 * e + 1 : ℕ) : ℤ)) with hwdef
    have hfac : (c : ℂ) ^ 2 * (d : ℂ) ^ 2 * (ψ (N : ZMod l))⁻¹ * (N : ℂ) ^ e +
        -(w * a * (d : ℂ) ^ 2) * (ψ (N : ZMod l) * ψ (c : ZMod l))⁻¹ * ((N : ℂ) ^ e * (c : ℂ) ^ e) +
        -((c : ℂ) ^ 2 * ((d : ℂ) * b)) * (ψ (N : ZMod l) * ψ (d : ZMod l))⁻¹ * ((N : ℂ) ^ e * (d : ℂ) ^ e) +
        w * a * ((d : ℂ) * b) * (ψ (N : ZMod l) * ψ (c : ZMod l) * ψ (d : ZMod l))⁻¹ *
          ((N : ℂ) ^ e * (c : ℂ) ^ e * (d : ℂ) ^ e) =
        (N : ℂ) ^ e * (ψ (N : ZMod l))⁻¹ *
          ((c : ℂ) ^ 2 - w * (c : ℂ) ^ e * a * (ψ (c : ZMod l))⁻¹) *
          ((d : ℂ) ^ 2 - (d : ℂ) * b * (d : ℂ) ^ e * (ψ (d : ZMod l))⁻¹) := by
      ring
    rw [hfac, hw]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hNc) (inv_ne_zero hψN)) ?_) ?_
    · have h1 : (c : ℂ) ^ 2 - (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ * a * (ψ (c : ZMod l))⁻¹ =
          (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ * ((c : ℂ) ^ e - a * (ψ (c : ZMod l))⁻¹) := by
        field_simp
      rw [h1]
      refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hC) (inv_ne_zero hCe)) ?_
      rw [sub_ne_zero]
      apply hce
      rw [norm_mul, norm_inv, ha, smNz_norm ψ hc]
      norm_num
    · intro h0
      apply hdb
      rw [zpow_neg_one, pow_succ]
      linear_combination h0
end

section
open UpperTheory.V.Z.Kato.Joint
open scoped Matrix MatrixGroups

theorem UpperTheory.V.Z.Kato.Joint.gmEx :
    UpperTheory.V.Z.Kato.Joint.GmEx := by
  intro l _ N h
  have hN : (N : ZMod l) * (N : ZMod l)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one N h.symm
  let m : (ZMod l)ˣ → ℤ := fun r => (((-(r : ZMod l)) * (N : ZMod l)⁻¹).val : ℤ)
  have hm : ∀ r : (ZMod l)ˣ, (N : ZMod l) * ((m r : ℤ) : ZMod l) = -(r : ZMod l) := by
    intro r
    simp only [m, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [mul_left_comm, hN, mul_one]
  refine ⟨fun r => ⟨!![1, 0; (N : ℤ) * m r, 1], by simp [Matrix.det_fin_two]⟩, fun r => ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (CongruenceSubgroup.Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩ <;> simp
  · simp
  · simp [hm r]
  · refine ⟨-1, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hm r]
end

section
open UpperTheory.V.Z.Kato.Joint
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

private theorem cg_mul_left {l : ℕ} [Fact l.Prime] {n : ℕ} {a b a' b' : Qbar l} (x : Qbar l) (hx : ‖x‖ ≤ 1)
    (h : Cg n a b) (ha : a' = x * a) (hb : b' = x * b) : Cg n a' b' := by
  unfold Cg at h ⊢
  rw [ha, hb, ← mul_sub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans h

theorem UpperTheory.V.Z.Kato.Joint.explSmul :
    UpperTheory.V.Z.Kato.Joint.ExplSmul := by
  intro l _ Ω _ _ ι e A c Z j s u w α B cc n β t m ⟨κ, v, m₀, c₀, hκ, hv, ζ, hζ, H⟩
  have hl1 : ‖((l : ℕ) : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) l
  have hx : ‖((l : ℕ) : Qbar l) ^ m‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hl1
  have hl0 : ((l : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  refine ⟨(l : Qbar l) ^ m * κ, v, m₀, c₀, mul_ne_zero (pow_ne_zero _ hl0) hκ, hv, ζ, hζ, fun k hk => ?_⟩
  obtain ⟨I, inst, P, o, ⟨p1, p2, p3, p4, q1, q2, q3, q4, q5⟩, hc⟩ := H k hk
  refine ⟨I, inst, P, fun i => (l : Qbar l) ^ m * o i,
    ⟨p1, p2, fun i => c.O.mul_mem (c.O.pow_mem (natCast_mem c.O l) m) (p3 i), p4, q1, q2, q3, fun i => ?_,
      fun s hs h1 h2 => ?_⟩, fun ψ hψ => ?_⟩
  · rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) (q4 i)
  · obtain ⟨kk, a1, a2⟩ := q5 s hs h1 h2
    refine ⟨kk, a1, cg_mul_left _ hx a2 rfl ?_⟩
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
  · refine cg_mul_left _ hx (hc ψ hψ) ?_ ?_
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      unfold htv
      rw [mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
    · beta_reduce
      split_ifs
      · ring
      · rw [mul_zero]
end

section
open UpperTheory.V.Z.Kato.Joint GlobalTheory.EisM

theorem UpperTheory.V.Z.Kato.Joint.avgMF :
    UpperTheory.V.Z.Kato.Joint.AvgMF := by
  intro k l N m θ χ f t α B c hp hk hodd hN hlN hm hχ hf hα hE
  haveI : NeZero N := ⟨hN.ne'⟩
  have hsq : ∀ ν : DirichletCharacter ℂ N, ν (-1) * ν (-1) = 1 := fun ν => by rw [← map_mul]; simp
  have hform : ∀ ν : DirichletCharacter ℂ N, ν (-1) = -θ (-1) → MF k (N * l) (ch (θ⁻¹ * ν)) (frm l N m k θ ν f) :=
    fun ν hν => (GlobalTheory.iterU_level_val_stable k N l m (θ⁻¹ * ν) (fun _ => 0) α B c _ (by omega) hp hα
      (GlobalTheory.T.isModularFormCoeffSeq_eisensteinProduct_parity k N l m (θ⁻¹ * ν) θ ν f hk hodd hN hp hm hlN rfl hν hf)).1
  have hsign : (θ * χ) (-1) = -θ (-1) := by
    rw [MulChar.coeToFun_mul, Pi.mul_apply, hχ]; ring
  have hmain := hform (θ * χ) hsign
  rw [inv_mul_cancel_left] at hmain
  refine ⟨hmain, ?_⟩
  have hφ : (N.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hN).ne'
  have htw : tw2 N (θ (-1)) =
      fun y => ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - θ (-1) * ν (-1))) * ch ν y := by
    funext y
    rw [GlobalTheory.T.tw2_eq_inv_totient_mul_sum_characters N (θ (-1)) hN y, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  have hmes : mesMu k l (hat θ) (tw2 N (θ (-1))) α B c m f =
      ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - θ (-1) * ν (-1))) *
        ((α ^ m)⁻¹ * lam B c (frm l N m k θ ν f)) := by
    unfold mesMu
    rw [htw, funext (measMu_zm_sum k l (hat θ) Finset.univ _ _ _), measMu_val_sum]
    rfl
  rw [hmes, Finset.sum_eq_single_of_mem (θ * χ) (Finset.mem_univ _)]
  · have h2 : (1 : ℂ) - θ (-1) * (θ * χ) (-1) = 2 := by
      rw [hsign]; linear_combination hsq θ
    rw [h2]
    field_simp
  · intro ν _ hne
    have h0 : (ν (-1) - θ (-1)) * (ν (-1) + θ (-1)) = 0 := by linear_combination hsq ν - hsq θ
    rcases mul_eq_zero.1 h0 with h | h
    · rw [sub_eq_zero.1 h, hsq θ]; ring
    · have hne' : θ⁻¹ * ν ≠ χ := fun h' => hne (by rw [← h', mul_inv_cancel_left])
      rw [hE.kill _ _ hne' (hform ν (eq_neg_of_add_eq_zero_left h))]
      ring
end

section
open UpperTheory.V.Z.Kato.Joint Topology Filter

private theorem mem_fixingSubgroup_of_fixes_finite_set (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E] :
    ∃ T : Finset Ω, ∀ g : Ω ≃ₐ[K] Ω, (∀ x ∈ T, g x = x) → g ∈ E.fixingSubgroup := by
  have h1 : (Subalgebra.toSubmodule E.toSubalgebra).FG :=
    Module.Finite.iff_fg.1 (inferInstanceAs (Module.Finite K E))
  obtain ⟨t, ht⟩ := h1
  refine ⟨t, fun g hg => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hle : Algebra.adjoin K (t : Set Ω) ≤ AlgHom.equalizer (g : Ω →ₐ[K] Ω) (AlgHom.id K Ω) :=
    Algebra.adjoin_le (fun y hy => by
      rw [SetLike.mem_coe, AlgHom.mem_equalizer]
      simpa using hg y hy)
  have hx1 : x ∈ Submodule.span K (t : Set Ω) := by
    rw [ht]
    exact hx
  have hx2 : x ∈ Algebra.adjoin K (t : Set Ω) := Algebra.span_le_adjoin K _ hx1
  have hx3 := hle hx2
  rw [AlgHom.mem_equalizer] at hx3
  simpa using hx3

private theorem uniform_continuity_galois_group (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] {X : Type} [NormedAddCommGroup X]
    (f : (Ω ≃ₐ[K] Ω) → X) (hf : Continuous f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[K] Ω, (∀ x ∈ E0, s' x = x) → ‖f (s * s') - f s‖ < δ := by
  classical
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have key : ∀ s : Ω ≃ₐ[K] Ω, ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ g ∈ E.fixingSubgroup, ‖f (s * g) - f s‖ < δ / 2 := by
    intro s
    have hc : Continuous fun g : Ω ≃ₐ[K] Ω => ‖f (s * g) - f s‖ :=
      ((hf.comp (continuous_const.mul continuous_id)).sub continuous_const).norm
    have hA : {g : Ω ≃ₐ[K] Ω | ‖f (s * g) - f s‖ < δ / 2} ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω) :=
      IsOpen.mem_nhds (isOpen_lt hc continuous_const) (by simp [hδ2])
    obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 hA
    exact ⟨E, hE, fun g hg => hsub hg⟩
  choose E hEf hE using key
  let U : (Ω ≃ₐ[K] Ω) → Set (Ω ≃ₐ[K] Ω) := fun i => {h | i⁻¹ * h ∈ (E i).fixingSubgroup}
  have hUo : ∀ i, IsOpen (U i) := by
    intro i
    haveI := hEf i
    exact (IntermediateField.fixingSubgroup_isOpen (E i)).preimage (continuous_const.mul continuous_id)
  have hUc : Set.univ ⊆ ⋃ i, U i := by
    intro h _
    refine Set.mem_iUnion.2 ⟨h, ?_⟩
    show h⁻¹ * h ∈ (E h).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U hUo hUc
  have hT : ∀ i, ∃ T : Finset Ω, ∀ g : Ω ≃ₐ[K] Ω, (∀ x ∈ T, g x = x) → g ∈ (E i).fixingSubgroup := by
    intro i
    haveI := hEf i
    exact mem_fixingSubgroup_of_fixes_finite_set K Ω (E i)
  choose T hT using hT
  refine ⟨S.biUnion T, fun s s' hs' => ?_⟩
  obtain ⟨i, hiS, hi⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ s))
  have hi' : i⁻¹ * s ∈ (E i).fixingSubgroup := hi
  have hs'i : s' ∈ (E i).fixingSubgroup :=
    hT i s' (fun x hx => hs' x (Finset.mem_biUnion.2 ⟨i, hiS, hx⟩))
  have h1 := hE i _ (mul_mem hi' hs'i)
  have h2 := hE i _ hi'
  rw [← mul_assoc, mul_inv_cancel_left] at h1
  rw [mul_inv_cancel_left] at h2
  have h3 : f (s * s') - f s = (f (s * s') - f i) - (f s - f i) := by abel
  rw [h3]
  have := norm_sub_le (f (s * s') - f i) (f s - f i)
  linarith

theorem UpperTheory.V.Z.Kato.Joint.unif :
    UpperTheory.V.Z.Kato.Joint.Unif := by
  intro l _ Ω _ _ _ f hf δ hδ
  haveI : IsGalois ℚ Ω := inferInstance
  exact uniform_continuity_galois_group ℚ Ω f hf δ hδ
end

section
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.towerEx :
    UpperTheory.V.Z.Kato.Joint.TowerEx := by
  intro Ω _ _ _ ε
  obtain ⟨T, -⟩ := GlobalTheory.T.exists_modular_function_tower_algebraic_coefficients Ω ε
  exact ⟨T⟩
end

section
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.rhoFrob :
    UpperTheory.V.Z.Kato.Joint.RhoFrob := by
  intro l _ Ω _ _ _ ι e S A W g χ hN _ hatt ρ hρ
  have h : ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Formalism.ConjugateSelfDual.Qbar l)) = _ := fun s =>
    (hρ s).trans (GlobalTheory.RhoAdm.untw_val' e W χ s).symm
  refine ⟨?_, fun V hV => GlobalTheory.RhoAdm.untw_irr e W χ hN.irr V fun s v hv => ?_⟩
  · obtain ⟨S0, hS0⟩ := GlobalTheory.RhoAdm.frob_trace_det ι e W g χ hatt
    refine ⟨S0, fun q hq hqS s hs => ?_⟩
    rw [h s]
    exact hS0 q hq hqS s hs
  · rw [← h s]
    exact hV s v hv
end

section
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.chiStab :
    UpperTheory.V.Z.Kato.Joint.ChiStab := by
  intro l hp Ω _ _ _ ε X N w χ hl hlN hN hw T b hT hb
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hlN).symm
  obtain ⟨φ, h1, h2⟩ := X.j_hol
  refine ⟨GlobalTheory.T.hecke_letter_preserves_basis_set ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T hT b hb.1, fun d hd => ?_⟩
  have h := GlobalTheory.T.modularTowerB_admissibleHecke_commute ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T (GlobalTheory.KZ.Letter.D d) hT hd b hb.1
  change X.op N l T (X.diam N l d b) = X.diam N l d (X.op N l T b) at h
  rw [← h, hb.2 d hd, map_smul]
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open UpperTheory.V.Z.Kato.Joint
open scoped Pointwise

private theorem aqBd_place {q : ℕ} (hq : q.Prime) : ∃ w : Pl, ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
  have hn : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 ℚ)}) = q := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  have hne : Ideal.span {((q : ℕ) : 𝓞 ℚ)} ≠ ⊤ := fun h => by
    rw [h, Ideal.absNorm_top] at hn
    exact hq.one_lt.ne hn
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : ((q : ℕ) : 𝓞 ℚ) ∈ M := (Ideal.span_singleton_le_iff_mem M).1 hle
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hmem⟩
  rw [h, Ideal.mem_bot] at hmem
  exact hq.ne_zero (Nat.cast_eq_zero.1 hmem)

private theorem aqBd_frob (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {q : ℕ} (hq : q.Prime) :
    ∃ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s := by
  obtain ⟨w, hw⟩ := aqBd_place hq
  obtain ⟨V, hV⟩ := exists_isPlaceOver (F := ℚ) Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob (F := ℚ) hV
  rw [GlobalTheory.RhoAdm.normV_ratPrime hq w hw] at hσ
  refine ⟨σ, V, ?_, fun x hx => ⟨?_, hσ.2 x ((V.valuation_le_one_iff x).2 hx)⟩⟩
  · rw [ValuationSubring.mem_nonunits_iff]
    simpa using (hV _).2 hw
  · have h : σ • V = V := MulAction.mem_stabilizer_iff.1 hσ.1
    rw [← h]
    exact ValuationSubring.smul_mem_pointwise_smul σ x V hx

theorem UpperTheory.V.Z.Kato.Joint.aqBd :
    UpperTheory.V.Z.Kato.Joint.AqBd := by
  intro l _ Ω _ _ _ ι e S A W g χ hN hχ hatt
  obtain ⟨S0, hS0⟩ := GlobalTheory.RhoAdm.frob_trace_det ι e W g χ hatt
  have hc := (Continuous.matrix_trace
    (Units.continuous_val.comp (GlobalTheory.RhoAdm.untw_cont e W χ hN.cont hχ))).norm
  haveI : CompactSpace (Ω ≃ₐ[ℚ] Ω) := inferInstance
  obtain ⟨C, hC⟩ := (isCompact_range hc).bddAbove
  obtain ⟨k, hk⟩ := GlobalTheory.KummerEisensteinGalois.exists_le_l_pow l (max C (∑ q ∈ S0, ‖ι.symm (g.a q)‖))
  refine ⟨k, fun q hq => le_trans ?_ hk⟩
  by_cases hqS : q ∈ S0
  · exact le_max_of_le_right
      (Finset.single_le_sum (f := fun q => ‖ι.symm (g.a q)‖) (fun _ _ => norm_nonneg _) hqS)
  · obtain ⟨s, hs⟩ := aqBd_frob Ω hq
    rw [← (hS0 q hq hqS s hs).1]
    exact le_max_of_le_left (hC ⟨s, rfl⟩)
end

section
namespace UpperTheory.V.Z.Kato.Joint

theorem kato_global_admissibility_of_admissible (hA : AdmTop) : AdmFR := by
  have hK : NewformPartOfTowerModule := fun {Ω} _ _ _ ε X => GlobalTheory.T.heckeProjector_newform_galoisImage ε X
  have hR : AdmRho := GlobalTheory.T.untwisted_representation_ordinary_triangular_shape
  exact admissibleFunctional_of_projection hA hK hR jEx rhoFrob unif LocFacts₂ finP coefUb thLin thOp chiStab thP lamEig2 chiQuad aqBd

end UpperTheory.V.Z.Kato.Joint
end
