import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleShapeAndEpsilonAtEveryLocalisation
import Development.AutomorphicArithmetic.CyclotomicBounds.ImageMemOfGens
import BuildAid.ForwardExisting
import Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostCompletionLeMaxUnramifiedPadic
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankKsEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowAndBlockExponentOfEmbeddings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankLeOfSubsetClosureRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFinrankKs
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBlochKatoConditionOfWachModules
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalConditionAllLocalizations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocDegPosAndSumLe

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.PrimesQD

open Formalism.FrobeniusOrbits Formalism.MainNotions.EmbeddingTypeJumps
open scoped Pointwise

theorem liesOver_span {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E p) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  constructor
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hle : Ideal.span {(p : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 E)) v.asIdeal := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa [placesOver] using hv
  exact hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) hle

theorem ramIdx_eq_two (D : D7) {l : ℕ} (hl : l.Prime) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hv : v ∈ placesOver D.host.E l) (g : D.R.GG) (hg : g ≠ 1)
    (hin : ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E, σ ∈ ineG D v ↔
      (D.host.galE σ = 1 ∨ D.host.galE σ = g)) :
    v.asIdeal.ramificationIdx ℤ = 2 := by
  have hgal := D.host.hostE_isGalois
  have : IsGaloisGroup Gal(D.host.E/ℚ) ℤ (𝓞 D.host.E) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ D.host.E
  have := liesOver_span hl hv
  have := v.isPrime
  have : Fact l.Prime := ⟨hl⟩
  have hp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible).isPrime
  have hIn : Nat.card (v.asIdeal.inertia Gal(D.host.E/ℚ)) = 2 := by
    have e1 : (v.asIdeal.inertia Gal(D.host.E/ℚ)) ≃ (({1, g} : Set (D.R.GG))) :=
      Equiv.subtypeEquiv (D.host.gal).toEquiv (fun σ => by
        rw [show σ ∈ v.asIdeal.inertia Gal(D.host.E/ℚ) ↔ σ ∈ ineG D v from Iff.rfl, hin σ]
        simp [Formalism.HC.HostRaw.galE])
    rw [Nat.card_congr e1, Nat.card_coe_set_eq, Set.ncard_pair hg.symm]
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v.asIdeal Gal(D.host.E/ℚ),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(D.host.E/ℚ)) (Ideal.span {(l : ℤ)}) v.asIdeal, hIn]

theorem bE_sq (D : D7) : (D.host.sqd) ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq

theorem neg_mem_iff (D : D7) (φ : D.host.E →+* ℂ) :
    (-φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ)) ↔
      ¬ φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) := by
  set z := φ (D.host.sqd)
  set s : ℂ := (Real.sqrt D.host.d : ℂ)
  have hd0 : (0 : ℝ) < Real.sqrt D.host.d :=
    Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hs : s ^ 2 = (D.host.d : ℂ) := by
    simp only [s, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hz : z ^ 2 = -(D.host.d : ℂ) := by
    simp only [z, ← map_pow, bE_sq, map_neg, map_natCast]
  have hs0 : Complex.I * s ≠ 0 := mul_ne_zero Complex.I_ne_zero
    (by simpa [s] using hd0.ne')
  have hfac : (z - Complex.I * s) * (z + Complex.I * s) = 0 := by
    have : (z - Complex.I * s) * (z + Complex.I * s) = z ^ 2 - Complex.I ^ 2 * s ^ 2 := by ring
    rw [this, hz, hs, Complex.I_sq]; ring
  constructor
  · intro h1 h2
    apply hs0
    have : (2 : ℂ) * (Complex.I * s) = 0 := by linear_combination -(h1 + h2)
    simpa using this
  · intro h
    rcases mul_eq_zero.1 hfac with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) h
    · linear_combination -h1

theorem ramification_two_and_conjugation_at_q_and_d : ∀ D : D7, EmbeddingTypeJumps.Conclusion1 D := by
  intro D
  have hH := D.host.hyp
  obtain ⟨hq, hd, hq8, hd16, -⟩ := hH
  intro l hl
  have hl' : l = D.host.q ∨ l = D.host.d := by simpa using hl
  have hlp : l.Prime := by rcases hl' with rfl | rfl <;> assumption
  refine ⟨by rcases hl' with rfl | rfl <;> omega, ?_⟩
  intro v hv
  have hlo := liesOver_span hlp hv
  have := v.isPrime
  have hmemI : ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E, σ ∈ ineG D v ↔ ∀ x : 𝓞 D.host.E, σ • x - x ∈ v.asIdeal :=
    fun σ => AddSubgroup.mem_inertia
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rcases hl' with rfl | rfl
    · obtain ⟨g, hg, hin⟩ := UpperTheory.Small.inertia_q D.host
      exact ramIdx_eq_two D hlp v hv g hg fun σ => (hmemI σ).trans (hin v.asIdeal σ)
    · refine ramIdx_eq_two D hlp v hv D.R.iod (fun h => ?_)
        fun σ => (hmemI σ).trans (D.host.der.inertia_d v.asIdeal σ)
      have h' := congrArg (fun g : D.R.GG => g.1.2) h
      exact absurd (show (-1 : ℤˣ) = 1 from h') (by decide)
  ·
    intro h
    refine D.host.der.decompConj l hlp ?_ v.asIdeal (MulAction.mem_stabilizer_iff.mpr h)
    rcases hl' with rfl | rfl
    · exact (dvd_mul_left _ _).mul_right _
    · exact dvd_mul_left _ _
  ·
    rintro rfl σ hσ φ
    have hb : σ (D.host.sqd) = D.host.sqd :=
      (D.host.galE_mem_Psi_iff σ).1 (D.host.der.decomp_typeI _ hlp (dvd_mul_left _ _) v.asIdeal σ hσ)
    simp only [InPhi, Formalism.HC.HostRaw.cmType, Set.mem_setOf_eq, RingHom.coe_comp, Function.comp_apply]
    rw [show ((σ : D.host.E →+* D.host.E) (D.host.sqd)) = D.host.sqd from hb]
  ·
    rintro rfl σ hσ hσ1 φ
    have h2 := (D.host.der.inertia_d v.asIdeal σ).1 ((hmemI σ).1 hσ)
    have hg : D.host.galE σ = D.R.iod := h2.resolve_left fun h => hσ1 ((D.host.galE_eq_one_iff σ).1 h)
    have hb : σ (D.host.sqd) = -D.host.sqd := by
      rw [D.host.galE_bE σ, hg, show D.R.iod.1.2 = -1 from rfl]
      simp
    simp only [InPhi, Formalism.HC.HostRaw.cmType, Set.mem_setOf_eq, RingHom.coe_comp, Function.comp_apply]
    rw [show ((σ : D.host.E →+* D.host.E) (D.host.sqd)) = -D.host.sqd from hb,
      map_neg]
    exact neg_mem_iff D φ

end GlobalTheory.PrimesQD
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aux_statement : ∀ D : D7, EmbeddingTypeJumps.Conclusion1 D := by
  atlas_forward_decl GlobalTheory.PrimesQD.ramification_two_and_conjugation_at_q_and_d
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.HubLoc

open Formalism.FrobeniusOrbits

section Gen

variable {l : ℕ} [Fact l.Prime] {R : Ranks} (H : Host R) (J : H.E →+* Om l)

theorem kw_eq_sup_of_gens (Kw : FinExt l) (hE : ∀ x : H.E, J x ∈ Kw.1)
    (hdense : (Kw.1 : Set (Om l)) ⊆ closure (Set.range J)) (g₁ g₂ g₃ : H.E)
    (hgen : ∀ M : IntermediateField ℚ_[l] (Om l), J g₁ ∈ M → J g₂ ∈ M → J g₃ ∈ M → ∀ x : H.E, J x ∈ M) :
    Kw.1 = IntermediateField.adjoin ℚ_[l] ({J g₁, J g₂} : Set (Om l)) ⊔
      IntermediateField.adjoin ℚ_[l] {J g₃} := by
  set M := IntermediateField.adjoin ℚ_[l] ({J g₁, J g₂} : Set (Om l)) with hM
  set N := M ⊔ IntermediateField.adjoin ℚ_[l] {J g₃} with hN
  have hfM : FiniteDimensional ℚ_[l] ↥M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral (R := ℚ_[l]) x
  have hfy : FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {J g₃}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) _)
  have hfN : FiniteDimensional ℚ_[l] ↥N := IntermediateField.finiteDimensional_sup _ _
  have hcl : IsClosed ((N : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional N.toSubalgebra.toSubmodule
  have h1 : J g₁ ∈ N := le_sup_left (a := M) (IntermediateField.subset_adjoin _ _ (by simp))
  have h2 : J g₂ ∈ N := le_sup_left (a := M) (IntermediateField.subset_adjoin _ _ (by simp))
  have h3 : J g₃ ∈ N := le_sup_right (a := M) (IntermediateField.mem_adjoin_simple_self _ _)
  apply le_antisymm
  · intro x hx
    refine closure_minimal ?_ hcl (hdense hx)
    rintro _ ⟨z, rfl⟩
    exact hgen N h1 h2 h3 z
  · refine sup_le ?_ ?_
    · rw [hM, IntermediateField.adjoin_le_iff]
      rintro _ (rfl | rfl)
      exacts [hE g₁, hE g₂]
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact hE g₃

theorem sq_aE_image : (J (H.sqq)) ^ 2 = -(H.q : Om l) := by
  rw [← map_pow, H.sqq_sq]; simp

theorem sq_bE_image : (J (H.sqd)) ^ 2 = -(H.d : Om l) := by
  rw [← map_pow, H.sqd_sq]; simp

theorem kw_eq_sup_sqrt (Kw : FinExt l) (hE : ∀ x : H.E, J x ∈ Kw.1)
    (hdense : (Kw.1 : Set (Om l)) ⊆ closure (Set.range J)) (hl : l = H.q ∨ l = H.d) :
    ∃ M : IntermediateField ℚ_[l] (Om l), M ≤ MaximalUnramifiedExtension l ∧ ∃ y : Om l, y ^ 2 = -(l : Om l) ∧
      Kw.1 = M ⊔ IntermediateField.adjoin ℚ_[l] {y} := by
  have hh := H.hyp
  have hq2 : H.q % 4 = 3 := by have := hh.2.2.1; omega
  have hd2 : H.d % 4 = 3 := by have := hh.2.2.2.1; omega
  have hqd : H.q ≠ H.d := by have := hh.2.2.1; have := hh.2.2.2.1; omega
  have hlS : ¬ l ∣ H.QS := UpperTheory.Small.not_dvd_QS H Fact.out (UpperTheory.Small.not_mem_of_qd H hl)
  have hθ := theta_mem_Kur H J
  rcases hl with rfl | rfl
  · refine ⟨_, ?_, _, sq_aE_image H J, kw_eq_sup_of_gens H J Kw hE hdense (thL H H.q) (H.sqd)
      (H.sqq) fun M m1 m2 m3 x => image_le H J hlS M m1 m3 m2 x⟩
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (rfl | rfl)
    · exact hθ
    · exact sqrtKur_holds _ H.d hh.2.1 hd2 hqd.symm _ (sq_bE_image H J)
  · refine ⟨_, ?_, _, sq_bE_image H J, kw_eq_sup_of_gens H J Kw hE hdense (thL H H.d) (H.sqq)
      (H.sqd) fun M m1 m2 m3 x => image_le H J hlS M m1 m2 m3 x⟩
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (rfl | rfl)
    · exact hθ
    · exact sqrtKur_holds _ H.q hh.1 hq2 hqd _ (sq_aE_image H J)

end Gen

theorem kw_eq_unram_sup_sqrt : ∀ (D : D7) (i : D.nd.Loc), (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    ∃ M : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)), M ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
      ∃ y : Om (D.nd.l i), y ^ 2 = -(D.nd.l i : Om (D.nd.l i)) ∧
        (D.nbr i w hw).Kw.1 = M ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y} := by
  intro D i hl w hw
  exact kw_eq_sup_sqrt D.host ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) (D.nbr i w hw).Kw
    (D.nbr i w hw).j_E (D.nbr i w hw).j_dense hl

end GlobalTheory.HubLoc
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_over_q_or_d_eq_unramified_sup_sqrt : ∀ (D : D7) (i : D.nd.Loc), (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), ∃ M : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)), M ≤ MaximalUnramifiedExtension (D.nd.l i) ∧ ∃ y : Om (D.nd.l i), y ^ 2 = -(D.nd.l i : Om (D.nd.l i)) ∧ (D.nbr i w hw).Kw.1 = M ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y} := by
  atlas_forward_decl GlobalTheory.HubLoc.kw_eq_unram_sup_sqrt
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory

theorem sqrt_neg_l_mem_adjoin_roots_of_unity :
    ∀ (l : ℕ) [Fact l.Prime], l % 4 = 3 → ∀ y : Om l, y ^ 2 = -(l : Om l) →
      y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} := by
  intro l _ h4 y hy
  set K := IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} with hK
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hchar : ringChar (ZMod l) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hm1 : quadraticChar (ZMod l) (-1) = -1 := by
    rw [quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]
  set χ := (quadraticChar (ZMod l)).ringHomComp (Int.castRingHom (Om l)) with hχdef
  have hχm1 : χ (-1) = -1 := by
    simp [χ, MulChar.ringHomComp_apply, hm1]
  have h2 : (2 : Om l) ≠ 0 := two_ne_zero
  have hχ1 : χ ≠ 1 := by
    intro h
    rw [h, MulChar.one_apply (isUnit_one.neg)] at hχm1
    apply h2; linear_combination hχm1
  have hq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod l)).comp _
  have hψ := AddChar.zmodChar_primitive_of_primitive_root l hζ
  have hsq := gaussSum_sq hχ1 hq hψ
  rw [hχm1, ZMod.card] at hsq
  set g := gaussSum χ (AddChar.zmodChar l hζ.pow_eq_one) with hg

  have hgK : g ∈ K := by
    rw [hg, gaussSum]
    refine sum_mem fun a _ => mul_mem ?_ ?_
    · rw [hχdef, MulChar.ringHomComp_apply]
      exact intCast_mem K _
    · rw [AddChar.zmodChar_apply]
      refine pow_mem (IntermediateField.subset_adjoin _ _ ?_) _
      show ζ ^ (l ^ 1) = 1
      rw [pow_one]; exact hζ.pow_eq_one

  have hyg : (y - g) * (y + g) = 0 := by
    linear_combination hy - hsq
  rcases mul_eq_zero.1 hyg with h | h
  · rw [sub_eq_zero.1 h]; exact hgK
  · rw [eq_neg_of_add_eq_zero_left h]; exact neg_mem hgK

end GlobalTheory
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqrt_neg_prime_mem_padic_cyclotomic : ∀ (l : ℕ) [Fact l.Prime], l % 4 = 3 → ∀ y : Om l, y ^ 2 = -(l : Om l) → y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} := by
  atlas_forward_decl GlobalTheory.sqrt_neg_l_mem_adjoin_roots_of_unity
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory

theorem sqrt_neg_l_not_mem_Kur : ∀ (l : ℕ) [Fact l.Prime] (y : Om l), y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l := by
  intro l _ y hy hK
  have hl1 : (1 : ℝ) < (l : ℝ) := Formalism.MainNotions.N.PreambleDegrees.Loc.one_lt_l
  have hl0 : (0 : ℝ) < l := by linarith
  have hn : ‖y‖ ^ 2 = (l : ℝ)⁻¹ := by
    rw [← norm_pow, hy, norm_neg]
    exact Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hn
    have : (l : ℝ)⁻¹ ≠ 0 := inv_ne_zero hl0.ne'
    exact this (by rw [← hn]; norm_num)
  obtain ⟨k, hk⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow hK hy0
  rw [hk, ← zpow_natCast, ← zpow_mul, ← zpow_neg_one] at hn
  have h := zpow_right_injective₀ hl0 hl1.ne' hn
  omega

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqrt_neg_prime_not_mem_max_unramified : ∀ (l : ℕ) [Fact l.Prime] (y : Om l), y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l := by
  atlas_forward_decl GlobalTheory.sqrt_neg_l_not_mem_Kur
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.SqrtNegL

open Polynomial

theorem natDegree_minpoly_sqrt (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (y : Om l)
    (hF : F ≤ MaximalUnramifiedExtension l) (hy : y ^ 2 = -(l : Om l)) (hyK : y ∉ MaximalUnramifiedExtension l) :
    (minpoly F y).natDegree = 2 := by
  have hint : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  have hmon : (X ^ 2 + C ((l : ℕ) : F)).Monic :=
    (monic_X_pow 2).add_of_left (degree_C_le.trans_lt (by simp))
  have hdeg : (X ^ 2 + C ((l : ℕ) : F)).natDegree = 2 := by
    rw [natDegree_add_eq_left_of_natDegree_lt] <;> simp
  have hev : aeval y (X ^ 2 + C ((l : ℕ) : F)) = 0 := by
    simp [hy]
  have h1 : (minpoly F y).natDegree ≤ 2 :=
    hdeg ▸ natDegree_le_natDegree (minpoly.min F y hmon hev)
  have h2 : 0 < (minpoly F y).natDegree := minpoly.natDegree_pos hint
  have h3 : (minpoly F y).natDegree ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ := minpoly.natDegree_eq_one_iff.mp h
    apply hyK
    rw [← ha]
    exact hF a.2
  omega

theorem structure_sqrt_neg : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : FinExt l) (M : IntermediateField ℚ_[l] (Om l)) (y : Om l), M ≤ MaximalUnramifiedExtension l → y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l → y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} → K.1 = M ⊔ IntermediateField.adjoin ℚ_[l] {y} → K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y} ∧ K.1 ≤ Ks K 1 ∧ Module.finrank ↥(K0 K) ↥K.1 = 2 ∧ Module.finrank ℚ_[l] ↥(Ks K 1) = (l - 1) / 2 * Module.finrank ℚ_[l] ↥K.1 := by
  intro l _ hl2 K M y hM hy hyK hyz hK
  have hyK1 : y ∈ K.1 := hK ▸ (le_sup_right : IntermediateField.adjoin ℚ_[l] {y} ≤ _)
      (IntermediateField.mem_adjoin_simple_self _ _)
  have hMK0 : M ≤ K0 K := le_inf (hK ▸ le_sup_left) hM
  have hA : IntermediateField.adjoin ℚ_[l] {y} ≤ K.1 :=
    (IntermediateField.adjoin_simple_le_iff).2 hyK1
  have e1 : K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y} :=
    le_antisymm (hK.le.trans (sup_le_sup_right hMK0 _)) (sup_le inf_le_left hA)
  have e2 : K.1 ≤ Ks K 1 := by
    rw [e1]
    exact sup_le_sup_left ((IntermediateField.adjoin_simple_le_iff).2 hyz) _
  have hd := natDegree_minpoly_sqrt l (K0 K) y inf_le_right hy hyK
  have hf : Module.finrank ℚ_[l] ↥K.1 = Module.finrank ℚ_[l] ↥(K0 K) * 2 := by
    rw [← hd, ← GlobalTheory.HubLoc.finrank_sup_adjoin, ← e1]
  have hpos := GlobalTheory.HubLoc.finrank_maxUnramifiedSubfield_padicFinExt_pos K
  have := K.2
  have htow := Module.finrank_mul_finrank ℚ_[l] ↥(K0 K) ↥K.1
  have e3 : Module.finrank ↥(K0 K) ↥K.1 = 2 := by
    rw [hf] at htow
    exact Nat.eq_of_mul_eq_mul_left hpos htow
  refine ⟨e1, e2, e3, ?_⟩
  rw [GlobalTheory.HubLoc.finrank_Ks_eq l K 1 one_pos, hf]
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two hl2
  have hev : 2 ∣ l - 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  obtain ⟨k, hk⟩ := hev
  rw [hk]
  rw [Nat.sub_self, pow_zero, one_mul]
  rw [Nat.mul_div_cancel_left k two_pos]
  ring

end GlobalTheory.SqrtNegL
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structure_unramified_adjoin_sqrt_neg_prime : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : FinExt l) (M : IntermediateField ℚ_[l] (Om l)) (y : Om l), M ≤ MaximalUnramifiedExtension l → y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l → y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} → K.1 = M ⊔ IntermediateField.adjoin ℚ_[l] {y} → K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y} ∧ K.1 ≤ Ks K 1 ∧ Module.finrank ↥(K0 K) ↥K.1 = 2 ∧ Module.finrank ℚ_[l] ↥(Ks K 1) = (l - 1) / 2 * Module.finrank ℚ_[l] ↥K.1 := by
  atlas_forward_decl GlobalTheory.SqrtNegL.structure_sqrt_neg
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.LocalFieldsQD

theorem main : ∀ D : D7, EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D := by
  intro D
  refine ⟨fun i hi w hw => ?_, GlobalTheory.T.aux_statement D⟩
  obtain ⟨M, hM, y, hy, hK⟩ := GlobalTheory.T.completion_over_q_or_d_eq_unramified_sup_sqrt D i hi w hw
  obtain ⟨-, -, hq8, hd16, -⟩ := D.host.hyp
  have h4 : D.nd.l i % 4 = 3 := by rcases hi with h | h <;> rw [h] <;> omega
  have h2 : D.nd.l i ≠ 2 := by omega
  obtain ⟨e1, e2, e3, e4⟩ := GlobalTheory.T.structure_unramified_adjoin_sqrt_neg_prime (D.nd.l i) h2 (D.nbr i w hw).Kw M y hM hy
    (GlobalTheory.T.sqrt_neg_prime_not_mem_max_unramified _ y hy) (GlobalTheory.T.sqrt_neg_prime_mem_padic_cyclotomic _ h4 y hy) hK
  exact ⟨⟨y, hy, e1⟩, e2, e3, e4⟩

end GlobalTheory.LocalFieldsQD
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fields_at_auxiliary_primes : ∀ D : D7, EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D := by
  atlas_forward_decl GlobalTheory.LocalFieldsQD.main
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.RowBoundB

open Module

theorem good_one {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {s : ℕ} (hl : l ≠ 2) (h : Good K s LL)
    (hK : K.1 ≤ Ks K 1) : Good K 1 LL := by
  obtain ⟨hs, -, -, hτ⟩ := h
  refine ⟨le_rfl, fun h2 => absurd h2 hl, hK, fun τ x => ?_⟩
  have hle : Ks K 1 ≤ Ks K s := by
    refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _
    intro y hy
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
    simp only [Set.mem_setOf_eq] at hy ⊢
    rw [pow_add, pow_mul, hy, one_pow]
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := ℚ_[l]) (L := ↥(Ks K 1))
    (M := Om l) (E := Om l) τ
  have := hτ (φ.comp (Ks K s).val) ⟨x.1, hle x.2⟩
  rw [← hφ]
  exact this

theorem jump_windows (η Sc b : ℝ) (t : ℕ) (hη : 0 < η) (hS : 0 < Sc) (ht : 1 ≤ (t : ℝ))
    (hpar : Sc + η + t + 2 ≤ b) (s : ℤ) (Jc Jl : Finset ℤ)
    (h1 : η + t + 1 < (s : ℝ)) (h2 : (s : ℝ) ≤ b + η + t + 1)
    (hl : ∀ a ∈ Jl, ((-η + ((t : ℝ) - 1) / 2 ≤ (a : ℝ) ∧ a ≤ -2) ∨
            ((t : ℤ) + 1 ≤ a ∧ (a : ℝ) ≤ η + ((t : ℝ) - 1) / 2)))
    (hc : (∀ a ∈ Jc, s ≤ a ∧ (a : ℝ) ≤ s + Sc) ∨ (∀ a ∈ Jc, -((s : ℝ) + Sc) ≤ a ∧ a ≤ -s)) :
    ∃ (up : Bool) (bτ : ℕ), ⌊η⌋₊ + t < bτ ∧
      (∀ a : ℤ, (-a - 1 ∈ Jc ∨ -a - 1 ∈ Jl ∨ (0 ≤ -a - 1 ∧ -a - 1 < t)) →
        a ∈ ElementDenominator.deep up bτ ⌊Sc⌋₊ ∪ Set.Icc (-((⌊η⌋₊ + t : ℕ) : ℤ)) ((⌊η⌋₊ + t : ℕ) : ℤ) ∧
        a ∈ Set.Icc (-((⌊2 * b⌋₊ : ℕ) : ℤ)) ((⌊2 * b⌋₊ : ℕ) : ℤ)) ∧
      ∀ a ∈ Finset.Icc (-((⌊η⌋₊ + t : ℕ) : ℤ)) ((⌊η⌋₊ + t : ℕ) : ℤ), -a - 1 ∉ Jc := by
  have key : ∀ (x : ℝ) (n : ℤ), 0 ≤ x → (n : ℝ) ≤ x → n ≤ ((⌊x⌋₊ : ℕ) : ℤ) := by
    intro x n hx hn
    rw [Int.natCast_floor_eq_floor hx]
    exact Int.le_floor.2 hn
  have e1 : ((⌊η⌋₊ : ℕ) : ℝ) ≤ η := Nat.floor_le hη.le
  have e2 : ((⌊Sc⌋₊ : ℕ) : ℝ) ≤ Sc := Nat.floor_le hS.le
  have ht' : (1 : ℤ) ≤ t := by exact_mod_cast ht
  have hs1 : ((⌊η⌋₊ : ℕ) : ℤ) + t + 1 < s := by
    have : (((⌊η⌋₊ : ℕ) : ℤ) : ℝ) + ((t : ℤ) : ℝ) + 1 < (s : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hb : s + 1 + ((⌊Sc⌋₊ : ℕ) : ℤ) ≤ ((⌊2 * b⌋₊ : ℕ) : ℤ) := by
    apply key _ _ (by linarith)
    push_cast; linarith
  have hlow : ∀ a : ℤ, -a - 1 ∈ Jl → -(((⌊η⌋₊ : ℕ) : ℤ) + t) ≤ a ∧ a ≤ ((⌊η⌋₊ : ℕ) : ℤ) + t := by
    intro a ha
    rcases hl _ ha with ⟨p, q⟩ | ⟨p, q⟩
    · have : a ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by
        apply key _ _ hη.le
        push_cast at p; linarith
      omega
    · have : -a - t ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by
        apply key _ _ hη.le
        push_cast at q ⊢; linarith
      omega
  rcases hc with hc | hc
  · have hc' : ∀ a : ℤ, -a - 1 ∈ Jc → s ≤ -a - 1 ∧ -a - 1 - s ≤ ((⌊Sc⌋₊ : ℕ) : ℤ) := by
      intro a ha
      obtain ⟨p, q⟩ := hc _ ha
      refine ⟨p, key _ _ hS.le ?_⟩
      push_cast at q ⊢; linarith
    refine ⟨false, (s + 1).toNat, by omega, fun a ha => ?_, fun a ha hj => ?_⟩
    · simp only [ElementDenominator.deep, Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc]
      rcases ha with ha | ha | ha
      · have := hc' a ha
        omega
      · have := hlow a ha
        omega
      · omega
    · have := hc' a hj
      rw [Finset.mem_Icc] at ha
      omega
  · have hc' : ∀ a : ℤ, -a - 1 ∈ Jc → -a - 1 ≤ -s ∧ a + 1 - s ≤ ((⌊Sc⌋₊ : ℕ) : ℤ) := by
      intro a ha
      obtain ⟨p, q⟩ := hc _ ha
      refine ⟨q, key _ _ hS.le ?_⟩
      push_cast at p ⊢; linarith
    refine ⟨true, (s - 1).toNat, by omega, fun a ha => ?_, fun a ha hj => ?_⟩
    · simp only [ElementDenominator.deep, if_true, Set.mem_union, Set.mem_Icc]
      rcases ha with ha | ha | ha
      · have := hc' a ha
        omega
      · have := hlow a ha
        omega
      · omega
    · have := hc' a hj
      rw [Finset.mem_Icc] at ha
      omega

theorem sum_le_card (I Jl : Finset ℤ) (f : ℤ → ℤ) (h1 : ∀ a ∈ I, f a ≤ 1)
    (h0 : ∀ a ∈ I, -a - 1 ∉ Jl → f a = 0) : ∑ a ∈ I, f a ≤ Jl.card := by
  classical
  have e : ∑ a ∈ I, f a ≤ ∑ a ∈ I, (if -a - 1 ∈ Jl then (1 : ℤ) else 0) := by
    refine Finset.sum_le_sum fun a ha => ?_
    split_ifs with h
    · exact h1 a ha
    · exact (h0 a ha h).le
  refine e.trans ?_
  rw [Finset.sum_boole]
  have : (I.filter fun a => -a - 1 ∈ Jl).card ≤ Jl.card := by
    refine Finset.card_le_card_of_injOn (fun a => -a - 1) (fun a ha => (Finset.mem_filter.1 ha).2) ?_
    intro a _ b _ hab
    simp only at hab
    omega
  exact_mod_cast this

theorem boundA_le (CA η Sc b : ℝ) (l n r t m f : ℕ) (hl : 2 ≤ l) (hη : 0 < η) (hS : 0 < Sc) (hb : 1 ≤ b)
    (hf : f = n * 2) :
    ElementDenominator.boundA CA l n 2 r ⌊Sc⌋₊ (⌊η⌋₊ + t) m ⌊2 * b⌋₊ ≤
      max CA 0 * (((f : ℕ) + 1 : ℝ) * (r : ℝ) * (4 * b / (l : ℝ) + 2 * Sc + 2 * Real.logb (l : ℝ) (2 * b) + 1 + η + (t : ℝ)) + 3 * ((f : ℕ) : ℝ) * (m : ℝ) * (2 * b + 1)) := by
  have e1 : ((⌊η⌋₊ : ℕ) : ℝ) ≤ η := Nat.floor_le hη.le
  have e2 : ((⌊Sc⌋₊ : ℕ) : ℝ) ≤ Sc := Nat.floor_le hS.le
  have e3 : ((⌊2 * b⌋₊ : ℕ) : ℝ) ≤ 2 * b := Nat.floor_le (by linarith)
  have e4 : (1 : ℝ) ≤ ((⌊2 * b⌋₊ : ℕ) : ℝ) := by
    have : 1 ≤ ⌊2 * b⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast this
  have hl' : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have e5 : 0 ≤ Real.logb (l : ℝ) ((⌊2 * b⌋₊ : ℕ) : ℝ) := Real.logb_nonneg hl' e4
  have e6 : Real.logb (l : ℝ) ((⌊2 * b⌋₊ : ℕ) : ℝ) ≤ Real.logb (l : ℝ) (2 * b) :=
    Real.logb_le_logb_of_le hl' (by linarith) e3
  have e7 : 2 * ((⌊2 * b⌋₊ : ℕ) : ℝ) / (l : ℝ) ≤ 4 * b / (l : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hQ : ElementDenominator.boundA CA l n 2 r ⌊Sc⌋₊ (⌊η⌋₊ + t) m ⌊2 * b⌋₊ =
      CA * (((f : ℕ) + 1 : ℝ) * (r : ℝ) * (2 * ((⌊2 * b⌋₊ : ℕ) : ℝ) / (l : ℝ) + 2 * ((⌊Sc⌋₊ : ℕ) : ℝ) +
        2 * Real.logb (l : ℝ) ((⌊2 * b⌋₊ : ℕ) : ℝ) + 1 + ((⌊η⌋₊ : ℕ) : ℝ) + (t : ℝ)) +
        3 * ((f : ℕ) : ℝ) * (m : ℝ) * (((⌊2 * b⌋₊ : ℕ) : ℝ) + 1)) := by
    simp only [ElementDenominator.boundA, hf]
    push_cast
    ring
  rw [hQ]
  refine (mul_le_mul_of_nonneg_right (le_max_left CA 0) (by positivity)).trans ?_
  gcongr

theorem rowAt_of_thmA {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (CA : ℝ)
    (hT : ElementDenominator.thmA P K LL CA) (he : finrank ↥(K0 K) ↥K.1 = 2) {ι : Type} {k r : ℕ}
    (Ms : ι → ↥(GK K) → Matrix (Fin k) (Fin k) ↥LL.1) (M2 : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1)
    (S η m h : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) (q : ℚ)
    (h1 : ∀ (V1 : Type) [AddCommGroup V1] [Module ↥LL.1 V1] [Module ℚ_[l] V1]
          [IsScalarTower ℚ_[l] ↥LL.1 V1] [FiniteDimensional ↥LL.1 V1]
          (ρ1 : Representation ↥LL.1 ↥(GK K) V1), IsSubOfSums ρ1 Ms → IsCrys (P.PD K) ρ1 ∧
          ∀ τ a, IsJumpV (P.PD K) ρ1 τ a →
            a ∈ ElementDenominator.deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η ∧ a ∈ Set.Icc (-(h : ℤ)) h)
    (h2 : IsCrys (P.PD K) (matRep M2)) (hb : ∀ τ, η < b τ)
    (hsum : ∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) (matRep M2) τ a ≤ m)
    (hq : ElementDenominator.boundA CA l (finrank ℚ_[l] ↥(K0 K)) 2 r S η m h ≤ q) :
    RowAt (P.PD K) (O := ↥(OL LL)) Ms ⇑M2 q := by
  intro V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 T2 hc2 hmat V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 T1 hc1 hsub F hFo
  obtain ⟨c1, c2⟩ := h1 V1 ρ1 hsub
  obtain ⟨e, heg, -⟩ := hmat
  have he' : ∀ g v, e (ρ2 g v) = matRep M2 g (e v) := by
    intro g v
    rw [heg]
    simp [matRep, Matrix.toLinAlgEquiv'_apply]
  have hr : finrank ↥LL.1 V2 = r := by simpa using e.finrank_eq
  have hs2 : ∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) ρ2 τ a ≤ m := by
    intro τ
    simp only [GlobalTheory.HTW.Rec.multV_eq_of_equiv _ e he']
    exact hsum τ
  obtain ⟨mm, k, hm, hk, hle⟩ := hT { V := V1, ρ := ρ1, cont := hc1, L := T1 }
    { V := V2, ρ := ρ2, cont := hc2, L := T2 } F r S η m h up b c1
    (GlobalTheory.HTW.Rec.isCrys_of_equiv _ e he' h2) hFo hr
    (fun τ a ha => (c2 τ a ha).1) hb hs2 (fun τ a ha => (c2 τ a ha).2) (Or.inl he)
  refine ⟨mm, k, hm, hk, ?_⟩
  rw [he] at hle
  have h3 := hle.trans (mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg k))
  exact_mod_cast h3

theorem row_bound : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA : ℝ), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∀ dc : TruncatedSeriesCountingIdentities.Decl D i, ∃ lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ, TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (r i) (ρ i) π dc lenRow ∧ ∀ w ∈ dc.row, (lenRow w : ℝ) ≤ max CA 0 * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * (4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ)) + 3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * (2 * large₂.sc.b + 1)) + 1 := by
  intro D r ρ large₂ ep CA h0 h1 hA hJ hF _ _ hLit hPar i hi π hπ dc
  refine ⟨fun w => ((⌈max CA 0 * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * (4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ)) + 3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * (2 * large₂.sc.b + 1))⌉ : ℤ) : ℚ), ?_, fun w _ => ?_⟩
  swap
  · rw [Rat.cast_intCast]
    exact (Int.ceil_lt_add_one _).le
  intro w hw _ C hC
  have hl4 : D.nd.l i % 4 = 3 := (h1 (D.nd.l i) (by simpa using hi.1.1)).1
  have hl2 : D.nd.l i ≠ 2 := by omega
  obtain ⟨-, hK1, he, -⟩ := h0 i hi.1.1 w hw
  have hG : Good (D.nbr i w hw).Kw 1 C.LL := hC.good_one hl2 hK1
  have hdeg : locDeg D.host.E w = finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) * 2 := by
    have h := ((hLit i hi).2.2.1 w hw).2.2
    unfold Br.DegW at h
    rw [← h, ← he]
    exact (Module.finrank_mul_finrank _ _ _).symm
  have hT := hA (D.nd.l i) hl2 _ _ hG
  have hη := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have ht := large₂.t_win.1
  have hb : 1 ≤ large₂.sc.b := by unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hPar; linarith
  choose s Jc Jl j1 j2 _ j4 j5 j6 _ _ j9 using hJ i hi w hw C
  choose up bτ w1 w2 w3 using fun τ => jump_windows large₂.etaSz large₂.Sc large₂.sc.b D.R.t hη hS ht hPar (s τ) (Jc τ) (Jl τ)
    (j1 τ) (j2 τ) (fun a ha => (j5 τ a ha).1) (j6 τ)
  obtain ⟨f1, f2⟩ := hF i hi w hw C
  obtain ⟨g1, g2⟩ := f2 π hπ
  have hbd := boundA_le CA large₂.etaSz large₂.Sc large₂.sc.b (D.nd.l i) _ D.R.r D.R.t D.R.m _ (by omega) hη hS hb hdeg
  refine rowAt_of_thmA (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL CA hT he _ _
    ⌊large₂.Sc⌋₊ (⌊large₂.etaSz⌋₊ + D.R.t) D.R.m ⌊2 * large₂.sc.b⌋₊ up bτ _ ?_ g1 w1 ?_ ?_
  · intro V1 _ _ _ _ _ ρ1 hsub
    obtain ⟨c1, c2⟩ := f1 V1 ρ1 hsub
    refine ⟨c1, fun τ a ha => ?_⟩
    obtain ⟨x, hx⟩ := c2 τ a ha
    exact w2 τ a ((j9 τ x _).1 hx)
  · intro τ
    rw [← j4 τ]
    apply sum_le_card
    · intro a _
      by_cases hh : (IsJumpV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) π))) τ (-a - 1) ∧
                ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ)))
      · exact ((g2 τ a).1 hh).le
      · exact ((g2 τ a).2 hh).le.trans zero_le_one
    · intro a ha hn
      refine (g2 τ a).2 ?_
      rintro ⟨p, q⟩
      rcases (j9 τ π _).1 p with h | h | h
      · exact w3 τ a ha h
      · exact hn h
      · exact q h
  · rw [Rat.cast_intCast]
    exact hbd.trans (Int.le_ceil _)

end GlobalTheory.RowBoundB
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowPlaces_satisfy_rowHypothesis_at_q_and_d : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA : ℝ), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∀ dc : TruncatedSeriesCountingIdentities.Decl D i, ∃ lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ, TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (r i) (ρ i) π dc lenRow ∧ ∀ w ∈ dc.row, (lenRow w : ℝ) ≤ max CA 0 * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * (4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ)) + 3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * (2 * large₂.sc.b + 1)) + 1 := by
  atlas_forward_decl GlobalTheory.RowBoundB.row_bound
end

section
section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.TBLocalW

theorem tb_of_localW : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ),
    LocalSituation.Conclusion4 D HW F →
    (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (h : Good (D.nbr i w hw).Kw 1 C.LL),
      EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL h)
        ((F (D.nd.l i)).E (D.nbr i w hw).Kw 1 C.LL h).tie) →
    TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → JointConditionTameBound D HW F i r π M0 h0 cB → TruncatedSeriesCountingIdentities.admTB i r π cB := by
  intro D HW F i r π M0 h0 cB hP hW hF hJ
  obtain ⟨hl2, hJw⟩ := hJ
  intro w hw C hG
  obtain ⟨hIn, hKs, hJC⟩ := hJw w hw
  have hs : Good (D.nbr i w hw).Kw 1 C.LL := hG.good_one hl2 hKs
  have hP1 := hP (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hs
  have hTB := hP1.1
  have hTBe := hP1.2
  have hWs := hW w hw C hs
  have hFa := hF w hw C
  refine ⟨?_, ?_⟩
  · intro Vy _ _ _ _ _ _ _ _ _ _ _ ρy Ly hcy hcrys hjmp p hp hint e₀ he₀ hpe e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat φ hφ
    have hE := GlobalTheory.TBLocal.eps_lat (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) Le.T e hMat
    let Yt : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
      { V := Vy, ρ := ρy, cont := hcy, L := Ly }
    let Y := kerY Yt p e₀ hpe hp hint he₀
    let VeL : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
      { V := Ve, ρ := ρe, cont := hce, L := Le }
    have hcjY := cj_sub hFa (GRep.ofLat Yt) (LinearMap.ker p) (ker_stable Yt p hp) ⟨hcrys, hjmp⟩
    have hJY := hJC C hs Y hcjY.1 hcjY.2
    have hWY := hWs Y M0 h0 hcjY.1 hJY.1
    have hJYt := hJC C hs Yt hcrys hjmp
    have hCt := (hWs Yt M0 h0 hcrys hJYt.1).1
    haveI : IsTopologicalRing (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).LL :=
      inferInstanceAs (IsTopologicalRing ↥C.LL.1)
    haveI : IsDomain (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).O :=
      inferInstanceAs (IsDomain ↥(OL C.LL))
    haveI : IsPrincipalIdealRing (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).O :=
      inferInstanceAs (IsPrincipalIdealRing ↥(OL C.LL))
    exact GlobalTheory.TBLocal.tb_part1 (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs)
      Yt p e₀ hpe hp hint he₀ Subtype.val_injective _ hTB e M0 h0 cB VeL hE.1 hE.2 hCt hWY (hJY.2 e he) φ hφ
  · intro e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat
    have hE := GlobalTheory.TBLocal.eps_lat (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) Le.T e hMat
    let VeL : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
      { V := Ve, ρ := ρe, cont := hce, L := Le }
    have hT := hTBe e VeL hE.1 hE.2
    exact GlobalTheory.TBLocal.tbe_clauses (Br.PD D.loc D.nbr i w hw) Le _ _ hIn e cB hT.2.1 hT.2.2 (hT.1 cB)

end GlobalTheory.TBLocalW
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCondition_of_local_theorem_hypW : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ), LocalSituation.Conclusion4 D HW F → (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (h : Good (D.nbr i w hw).Kw 1 C.LL), EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL h) ((F (D.nd.l i)).E (D.nbr i w hw).Kw 1 C.LL h).tie) → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → JointConditionTameBound D HW F i r π M0 h0 cB → TruncatedSeriesCountingIdentities.admTB i r π cB := by
  atlas_forward_decl GlobalTheory.TBLocalW.tb_of_localW
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TheoremBTB

theorem localTB : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ), LocalSituation.Conclusion4 D HW F → (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (h : Good (D.nbr i w hw).Kw 1 C.LL), EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL h) ((F (D.nd.l i)).E (D.nbr i w hw).Kw 1 C.LL h).tie) → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → JointConditionTameBound D HW F i r π M0 h0 cB → TruncatedSeriesCountingIdentities.admTB i r π cB := GlobalTheory.T.localCondition_of_local_theorem_hypW

theorem l_ge_three (D : D7) (i : D.nd.Loc) (hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) : 3 ≤ D.nd.l i := by
  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have htr : 1 ≤ D.R.t * D.R.r := Nat.mul_pos ht1 hr1
  rcases hl with h | h <;> rw [h]
  · have := D.host.qd_big.1; nlinarith
  · have := D.host.qd_big.2; nlinarith

theorem jointCond_at_qd (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool)
    (h0 : EmbeddingTypeJumps.Conclusion0 D) (hJump : EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂) (hPar : EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂) (i : D.nd.Loc) (hQ : EmbeddingTypeJumps.AtQD i)
    (π : D.nd.X i) :
    JointConditionTameBound D HW F i (r i) π ⌊2 * large₂.sc.b⌋₊ ⌊2 * large₂.sc.b⌋₊
      (GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV)) := by
  have hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d := hQ.1.1
  have hl3 := l_ge_three D i hl
  refine ⟨by omega, fun w hw => ?_⟩
  obtain ⟨-, hK1, -, hdegK⟩ := h0 i hl w hw
  refine ⟨GlobalTheory.BridgeInertia.inertEq D i w hw, hK1, fun C hs Y hc hY => ?_⟩
  have hs1 : (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).W.s = 1 :=
    (HW (D.nd.l i)).W_s _ 1 _ hs
  have hell : LocalSituation.ell (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) = D.nd.l i :=
    (D.loc (D.nd.l i)).PD_p _
  haveI : CharZero (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).Qp :=
    inferInstanceAs (CharZero ℚ_[D.nd.l i])
  haveI : FiniteDimensional (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).Qp
      (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).K := (D.nbr i w hw).Kw.2
  have hcard : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 :=
    GlobalTheory.HubLoc.card_emb _ _ fun τ x => C.le ((D.nbr i w hw).LL_split τ x)
  have hdeg := GlobalTheory.bridge_finrank_le D i w hw
  obtain ⟨hv1, -⟩ := GlobalTheory.HubLoc.padicValNat_finrank_Ks (D.nd.l i) (D.nbr i w hw).Kw
  have hK0 : Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 ≠ 0 := Module.finrank_pos.ne'
  have hgK : LocalSituation.gK (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) = 0 := by
    unfold LocalSituation.gK
    rw [hs1, hell]
    show padicValNat (D.nd.l i) (Module.finrank ℚ_[D.nd.l i] ↥(Ks (D.nbr i w hw).Kw 1)) -
      padicValNat (D.nd.l i) (Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1) = 0
    have hpos : (D.nd.l i - 1) / 2 ≠ 0 := by omega
    have hv : padicValNat (D.nd.l i) ((D.nd.l i - 1) / 2) = 0 :=
      padicValNat.eq_zero_of_not_dvd fun h => by
        have := Nat.le_of_dvd (by omega) h
        omega
    rw [hdegK, padicValNat.mul hpos hK0, hv, zero_add, Nat.sub_self]
  have hvd : ∀ m : ℕ, 0 < m → LocalSituation.vdegMs (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) m = m - 1 := by
    intro m hm
    unfold LocalSituation.vdegMs
    rw [hs1, hell]
    exact hv1 m hm
  have hb := hPar
  unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hb
  have hη := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
  have hfl : ∀ z : ℤ, (z : ℝ) ≤ 2 * large₂.sc.b → z ≤ (⌊2 * large₂.sc.b⌋₊ : ℤ) := by
    intro z hz
    rcases le_or_gt z 0 with h | h
    · exact h.trans (Int.natCast_nonneg _)
    · have h2 : ((z.toNat : ℕ) : ℝ) ≤ 2 * large₂.sc.b := by
        rw [show ((z.toNat : ℕ) : ℝ) = (z : ℝ) by exact_mod_cast Int.toNat_of_nonneg h.le]; exact hz
      have := Nat.le_floor h2
      omega
  have ht : D.R.t ≤ ⌊2 * large₂.sc.b⌋₊ := by
    have := hfl (D.R.t : ℤ) (by push_cast; linarith)
    omega
  have key := GlobalTheory.HubLoc.window_and_cTB_of_jumps_at_embeddings
    (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) Y ⌊2 * large₂.sc.b⌋₊ D.R.nV (4 * D.R.n) D.R.t
    hs1 hcard hdeg hgK (hvd _ (by unfold LocalSituation.mN; omega)) ht (fun τ => by
      obtain ⟨s, Jc, Jl, hs1', hs2', hJc, hJl, hlow, hcl, -, -, hiff⟩ := hJump i hQ w hw C τ
      classical
      refine ⟨Jc ∪ Jl ∪ Finset.Ico (0 : ℤ) D.R.t, ?_, ?_, fun a ha => ?_⟩
      · calc (Jc ∪ Jl ∪ Finset.Ico (0 : ℤ) D.R.t).card ≤ (Jc ∪ Jl).card + (Finset.Ico (0 : ℤ) D.R.t).card :=
              Finset.card_union_le _ _
          _ ≤ Jc.card + Jl.card + (Finset.Ico (0 : ℤ) D.R.t).card := by
              have := Finset.card_union_le Jc Jl; omega
          _ = D.R.nV := by
              rw [hJc, hJl, Int.card_Ico]
              unfold Ranks.nV Ranks.r
              have := D.R.m_add_three_le_k
              simp only [sub_zero, Int.toNat_natCast]
              omega
      · intro u hu
        simp only [Finset.mem_union, Finset.mem_Ico] at hu
        rcases hu with (hu | hu) | hu
        · rcases hcl with hc' | hc'
          · obtain ⟨a1, a2⟩ := hc' u hu
            have hs0 : (0 : ℝ) < s := by linarith
            constructor
            · have : (0 : ℤ) < s := by exact_mod_cast hs0
              omega
            · exact hfl (u + 1) (by push_cast; linarith)
          · obtain ⟨a1, a2⟩ := hc' u hu
            have hs0 : (0 : ℝ) < s := by linarith
            constructor
            · have := hfl (-u) (by push_cast; linarith)
              omega
            · have : (0 : ℤ) < s := by exact_mod_cast hs0
              omega
        · obtain ⟨hb', -, -, -⟩ := hlow u hu
          rcases hb' with ⟨a1, a2⟩ | ⟨a1, a2⟩
          · constructor
            · have := hfl (-u) (by push_cast; linarith)
              omega
            · omega
          · constructor
            · omega
            · exact hfl (u + 1) (by push_cast; linarith)
        · constructor
          · omega
          · omega
      · have := (hiff π a).1 (hY τ a ha)
        simp only [Finset.mem_union, Finset.mem_Ico]
        tauto)
  refine ⟨key.1, fun e he => (key.2 e he).trans (le_of_eq ?_)⟩
  rw [hell]

theorem cBnum_le (l t n r : ℕ) (b : ℝ) (hl : 3 ≤ l) (ht : 1 ≤ t) (hn : 1 ≤ n) (hr : 1 ≤ r) (hb : 1 < b)
    (hL : 1 < Real.log b) :
    (GlobalTheory.HubLoc.cBnum l ⌊2 * b⌋₊ t (4 * n * (r + t)) : ℝ) ≤
      60 * (t : ℝ) * ((2 * n : ℕ) : ℝ) * ((r : ℝ) + (t : ℝ)) * Real.log b := by
  set L := Real.log b with hLdef
  set lam := Nat.log l (2 * ⌊2 * b⌋₊) with hlam
  have hfl2 : 2 ≤ ⌊2 * b⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hpow : l ^ lam ≤ 2 * ⌊2 * b⌋₊ := Nat.pow_log_le_self l (by omega)
  have h3pow : 3 ^ lam ≤ l ^ lam := Nat.pow_le_pow_left hl lam
  have hfb : ((⌊2 * b⌋₊ : ℕ) : ℝ) ≤ 2 * b := Nat.floor_le (by linarith)
  have h3R : (3 : ℝ) ^ lam ≤ 4 * b := by
    have : ((3 ^ lam : ℕ) : ℝ) ≤ ((2 * ⌊2 * b⌋₊ : ℕ) : ℝ) := by exact_mod_cast h3pow.trans hpow
    push_cast at this
    linarith
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  have hlamL : (lam : ℝ) ≤ 4 * L := by
    have h1 : Real.log ((3 : ℝ) ^ lam) ≤ Real.log (4 * b) := Real.log_le_log (by positivity) h3R
    rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : (lam : ℝ) ≤ (lam : ℝ) * Real.log 3 := by
      have : (0 : ℝ) ≤ lam := by positivity
      nlinarith
    linarith
  unfold GlobalTheory.HubLoc.cBnum
  rw [← hlam]
  push_cast
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlam0 : (0 : ℝ) ≤ lam := by positivity
  set P : ℝ := (t : ℝ) * (2 * n) * (r + t) with hP
  have hP1 : 1 ≤ P := by
    have : (1 : ℝ) ≤ (2 * n) * (r + t) := by nlinarith
    nlinarith
  have hA : 3 + (lam : ℝ) + 3 ≤ 10 * P * L := by nlinarith
  have hB : 4 * (t : ℝ) + 3 * t ≤ 7 * P * L := by
    have : (t : ℝ) ≤ P := by
      have : (1 : ℝ) ≤ (2 * n) * (r + t) := by nlinarith
      nlinarith
    nlinarith
  have hC : (t : ℝ) * (4 * n * (r + t) * (4 + 2 * lam)) ≤ 24 * P * L := by
    have h4 : (4 : ℝ) + 2 * lam ≤ 12 * L := by linarith
    have hq : (0 : ℝ) ≤ (t : ℝ) * (4 * n * (r + t)) := by positivity
    calc (t : ℝ) * (4 * n * (r + t) * (4 + 2 * lam)) = ((t : ℝ) * (4 * n * (r + t))) * (4 + 2 * lam) := by ring
      _ ≤ ((t : ℝ) * (4 * n * (r + t))) * (12 * L) := mul_le_mul_of_nonneg_left h4 hq
      _ = 24 * P * L := by rw [hP]; ring
  have hPL : 0 ≤ P * L := by positivity
  nlinarith

theorem main : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∃ cB : ℕ, TruncatedSeriesCountingIdentities.admTB i (r i) π cB ∧ (cB : ℝ) ≤ 60 * (D.R.t : ℝ) * (D.R.f : ℝ) * ((D.R.r : ℝ) + (D.R.t : ℝ)) * Real.log large₂.sc.b := by
  intro D HW F r ρ large₂ ep h0 _h1 hW hTB hJump _hFon _hG2 _hSet hLit hPar i hQ π _hπ
  have hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d := hQ.1.1
  refine ⟨GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV), ?_, ?_⟩
  · exact localTB D HW F i (r i) π _ _ _ hTB (fun w hw C h => hW i hQ w hw C h) (hLit i hQ).2.2.2.1
      (jointCond_at_qd D HW F r large₂ ep h0 hJump hPar i hQ π)
  · have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
    have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
    have hn1 : 1 ≤ D.R.n := by unfold Ranks.n; exact Nat.succ_le_of_lt (by positivity)
    have hL0 : 0 < large₂.sc.L := by unfold Scale.L; exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
    have hb1 : 1 < large₂.sc.b := by unfold Scale.b; have := Real.add_one_lt_exp (ne_of_gt hL0); linarith
    have hLb : 1 < Real.log large₂.sc.b := by
      unfold Scale.b; rw [Real.log_exp]; unfold Scale.L
      exact Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
    have key := cBnum_le (D.nd.l i) D.R.t D.R.n D.R.r large₂.sc.b (l_ge_three D i hl) ht1 hn1 hr1 hb1 hLb
    have hnV : D.R.nV = D.R.r + D.R.t := rfl
    have hf : D.R.f = 2 * D.R.n := rfl
    rw [hnV, hf]
    exact key

end GlobalTheory.TheoremBTB
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockBound_qd_places_uniformConst : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∃ cB : ℕ, TruncatedSeriesCountingIdentities.admTB i (r i) π cB ∧ (cB : ℝ) ≤ 60 * (D.R.t : ℝ) * (D.R.f : ℝ) * ((D.R.r : ℝ) + (D.R.t : ℝ)) * Real.log large₂.sc.b := by
  atlas_forward_decl GlobalTheory.TheoremBTB.main
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.BKAtQD

theorem admBK_embeddingTypeJumps : ∀ (D : D7), EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.LiteratureHypotheses (D := D) →
    ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.admBK i := by
  intro D hBK hLit i hi w hw C
  obtain ⟨-, hTD, -⟩ := hLit i hi
  exact ⟨(hTD w hw C).1, (hTD w hw C).2,
    fun _ => TruncatedSeriesCountingIdentities.bkBAt_of_core _ _ _ (hBK _ _).2.2.2.1 (GlobalTheory.AdmBK.litGoodO_all _ _)⟩

end GlobalTheory.BKAtQD
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoHypothesis_globalStep_at_qd : ∀ (D : D7), EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.admBK i := by
  atlas_forward_decl GlobalTheory.BKAtQD.admBK_embeddingTypeJumps
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CycDegRam

open Formalism Formalism.BasicNotions NumberField IsDedekindDomain Polynomial UniqueFactorizationMonoid

theorem sub_one_le_two_mul_finrank (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime)
    (hram : ∀ v ∈ placesOver E l, v.asIdeal.ramificationIdx ℤ = 2) :
    l - 1 ≤ 2 * Module.finrank E (CyclotomicField l E) := by
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : NeZero l := ⟨hl.ne_zero⟩
  set L := CyclotomicField l E
  set k := Module.finrank E L with hk
  have hkpos : 0 < k := Module.finrank_pos
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta l E L) l := IsCyclotomicExtension.zeta_spec l E L
  let z : 𝓞 L := ⟨IsCyclotomicExtension.zeta l E L, hζ.isIntegral hl.pos⟩
  have hz : IsPrimitiveRoot z l :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L) hζ RingOfIntegers.coe_injective
  have hprod : ∏ μ ∈ primitiveRoots l (𝓞 L), (1 - μ) = (l : 𝓞 L) := by
    have h := Polynomial.eval_one_cyclotomic_prime (R := 𝓞 L) (p := l)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz, Polynomial.eval_prod] at h
    simpa using h
  have hassoc : ∀ μ ∈ primitiveRoots l (𝓞 L), Associated (1 - z) (1 - μ) := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ l := (mem_primitiveRoots hl.pos).1 hμ
    obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨b, -, hb⟩ := hμ'.eq_pow_of_pow_eq_one hz.pow_eq_one
    refine associated_of_dvd_dvd ?_ ?_
    · rw [← ha]; simpa using sub_dvd_pow_sub_pow (1 : 𝓞 L) z a
    · rw [← hb]; simpa using sub_dvd_pow_sub_pow (1 : 𝓞 L) μ b
  have hA : Associated ((1 - z) ^ (l - 1)) (l : 𝓞 L) := by
    rw [← hprod]
    have := Associated.prod (primitiveRoots l (𝓞 L)) (fun _ => 1 - z) (fun μ => 1 - μ) hassoc
    rwa [Finset.prod_const, hz.card_primitiveRoots, Nat.totient_prime hl] at this
  set n : 𝓞 E := RingOfIntegers.norm E (1 - z)
  have hB : Associated (n ^ (l - 1)) ((l : 𝓞 E) ^ k) := by
    have := hA.map (RingOfIntegers.norm E)
    rw [map_pow] at this
    have hl' : (l : 𝓞 L) = algebraMap (𝓞 E) (𝓞 L) (l : 𝓞 E) := (map_natCast _ _).symm
    rwa [hl', RingOfIntegers.norm_algebraMap] at this
  have hI : (Ideal.span {n}) ^ (l - 1) = (Ideal.span {(l : 𝓞 E)}) ^ k := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.2 hB

  have hmaxZ : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hinj : Function.Injective (algebraMap ℤ (𝓞 E)) := (algebraMap ℤ (𝓞 E)).injective_int
  have hker : RingHom.ker (algebraMap ℤ (𝓞 E)) ≤ Ideal.span {(l : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (Ideal.span {(l : ℤ)}) hker
  have hlZ : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    have h1 : (l : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) (⊥ : Ideal (𝓞 E)) := by
      rw [hQ]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, Ideal.mem_bot, map_natCast] at h1
    exact hl.ne_zero (by exact_mod_cast h1)
  let v : HeightOneSpectrum (𝓞 E) := ⟨Q, hQmax.isPrime, hQ0⟩
  have hv : v ∈ placesOver E l := by
    show (l : 𝓞 E) ∈ Q
    have h1 : (l : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) Q := by
      rw [hQ]; exact Ideal.mem_span_singleton_self _
    rwa [Ideal.mem_comap, map_natCast] at h1
  have hram2 : Q.ramificationIdx ℤ = 2 := hram v hv
  haveI : Q.LiesOver (Ideal.span {(l : ℤ)}) := ⟨hQ.symm⟩
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) = Ideal.span {(l : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hne : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.ne_zero
  have hc := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    (Ideal.span {(l : ℤ)}) Q (by rw [hmap]; exact hne)
  rw [hram2, hmap] at hc
  have h1 := congrArg (fun I => Multiset.count Q (normalizedFactors I)) hI
  simp only [normalizedFactors_pow, Multiset.count_nsmul] at h1
  rw [← hc] at h1
  rcases Nat.eq_zero_or_pos (Multiset.count Q (normalizedFactors (Ideal.span {n}))) with h0 | hpos
  · rw [h0] at h1; omega
  · calc l - 1 ≤ (l - 1) * Multiset.count Q (normalizedFactors (Ideal.span {n})) :=
          Nat.le_mul_of_pos_right _ hpos
      _ = 2 * k := by rw [h1, mul_comm]

end GlobalTheory.CycDegRam

namespace GlobalTheory.CycDegRam

theorem tr_lt_finrank_cyclotomic : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc,
    (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) →
    D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E) := by
  intro D h1 i hi
  have hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ) := by
    rcases hi with h | h <;> simp [h]
  have hprime : (D.nd.l i).Prime := by
    rcases hi with h | h <;> rw [h]
    · exact D.host.hyp.1
    · exact D.host.hyp.2.1
  have hbig : 4 * D.R.t * D.R.r + 1 < D.nd.l i := by
    rcases hi with h | h <;> rw [h]
    · exact D.host.qd_big.1
    · exact D.host.qd_big.2
  have key := sub_one_le_two_mul_finrank D.host.E (D.nd.l i) hprime
    (fun v hv => ((h1 _ hmem).2 v hv).1)
  have h4 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r) := by ring
  omega

example : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E) := tr_lt_finrank_cyclotomic

end GlobalTheory.CycDegRam
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_lt_finrank_cyclotomic_at_q_and_d : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E) := by
  atlas_forward_decl GlobalTheory.CycDegRam.tr_lt_finrank_cyclotomic
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.Proof.TypePrimesQD

theorem not_split_of_ram_two (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime)
    (hram : ∀ v ∈ placesOver E l, v.asIdeal.ramificationIdx ℤ = 2)
    (hsplit : (placesOver E l).ncard = Module.finrank ℚ E) : False := by
  classical
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hfin : (placesOver E l).Finite := Set.finite_of_ncard_pos (by omega)
  obtain ⟨hdpos, hsum⟩ := GlobalTheory.Proof.LocDegPos.locDeg_pos_and_sum_le E l hl
  have hle := hsum hfin.toFinset (fun v hv => hfin.mem_toFinset.1 hv)
  have hge : ∑ v ∈ hfin.toFinset, 2 ≤ ∑ v ∈ hfin.toFinset, Formalism.MainNotions.N.locDeg E v := by
    refine Finset.sum_le_sum fun v hv => ?_
    have h2 := hram v (hfin.mem_toFinset.1 hv)
    have hp := hdpos v
    unfold Formalism.MainNotions.N.locDeg at hp ⊢
    rw [h2] at hp ⊢
    omega
  rw [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin, hsplit] at hge
  omega

theorem qd_ne_typePrimes : ∀ (D : D7), Formalism.MainNotions.EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc,
    (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1 := by
  intro D h1 i hl
  have key : ∀ k : Fin 2, D.nd.l i ≠ D.host.g k := by
    intro k hk
    have hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ) := by
      rcases hl with h | h <;> simp [h]
    have hram := (h1 _ hmem).2
    rw [hk] at hram
    exact not_split_of_ram_two D.host.E (D.host.g k) (D.host.g_prime k)
      (fun v hv => (hram v hv).1) (D.nd.g_split k)
  exact ⟨key 0, key 1⟩

end GlobalTheory.Proof.TypePrimesQD
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theoremB_ramifiedPrimes_ne_typePrimes : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1 := by
  atlas_forward_decl GlobalTheory.Proof.TypePrimesQD.qd_ne_typePrimes
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.Proof.QDDeg

theorem locDeg_sum_le_and_ge : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.E)), (∀ w ∈ s, w ∈ placesOver D.host.E (D.nd.l i)) → (∑ w ∈ s, locDeg D.host.E w) ≤ 2 * D.R.f ∧ 2 * s.card ≤ ∑ w ∈ s, locDeg D.host.E w := by
  intro D h1 i hi s hs
  have hl : (D.nd.l i).Prime := by
    rcases hi with h | h <;> rw [h]
    · exact D.host.hyp.1
    · exact D.host.hyp.2.1
  have hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ) := by
    rcases hi with h | h <;> simp [h]
  obtain ⟨hpos, hsum⟩ := GlobalTheory.Proof.LocDegPos.locDeg_pos_and_sum_le D.host.E (D.nd.l i) hl
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  refine ⟨(hsum s hs).trans hfr.le, ?_⟩
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun w hw => ?_
  have he : w.asIdeal.ramificationIdx ℤ = 2 := ((h1 _ hmem).2 w (hs w hw)).1
  have hp := hpos w
  unfold Formalism.MainNotions.N.locDeg at hp ⊢
  rw [he] at hp ⊢
  omega

end GlobalTheory.Proof.QDDeg
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theoremB_localDegree_sum_bounds : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.E)), (∀ w ∈ s, w ∈ placesOver D.host.E (D.nd.l i)) → (∑ w ∈ s, locDeg D.host.E w) ≤ 2 * D.R.f ∧ 2 * s.card ≤ ∑ w ∈ s, locDeg D.host.E w := by
  atlas_forward_decl GlobalTheory.Proof.QDDeg.locDeg_sum_le_and_ge
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory

theorem closing_numerical_inequality :
    ∀ (CA C b l S η Rw Tb Vd : ℝ) (f r t m p : ℕ), 13 * max CA 0 ≤ C → 260 * f ^ 2 * t ^ 2 * (r + t) ≤ p → 1 ≤ t → 1 ≤ f → m ≤ r → 3 ≤ l → 0 ≤ S → 0 ≤ η → 0 < b → 1 < Real.log b → Rw ≤ max CA 0 * (3 * (f : ℝ) * r * (4 * b / l + 2 * S + 2 * Real.logb l (2 * b) + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1)) + f → Tb ≤ 240 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * Real.log b → Vd ≤ 4 * ((r : ℝ) + t) * t → Rw + Tb + Vd ≤ C * f * (r * (b / l + S + t + η + Real.log b) + m * b) + (p : ℝ) * Real.log b := by
  intro CA C b l S η Rw Tb Vd f r t m p hC hp ht hf hm hl hS hη hb hL hRw hTb hVd
  have hK : 0 ≤ max CA 0 := le_max_right _ _
  have hpR : (260 : ℝ) * (f : ℝ) ^ 2 * (t : ℝ) ^ 2 * ((r : ℝ) + t) ≤ (p : ℝ) := by exact_mod_cast hp
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hmR : (m : ℝ) ≤ r := by exact_mod_cast hm
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hl0 : 0 < l := by linarith

  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogl : 1 ≤ Real.log l := by
    have := Real.log_le_log (by norm_num) hl
    linarith
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith

  have hlam : Real.logb l (2 * b) ≤ 2 * Real.log b := by
    rw [Real.logb, div_le_iff₀ (by linarith), Real.log_mul (by norm_num) hb.ne']
    nlinarith
  set L := Real.log b with hLdef
  set lam := Real.logb l (2 * b) with hlamdef
  have hx : 0 ≤ b / l := div_nonneg hb.le hl0.le
  set x := b / l with hxdef
  have h4x : 4 * b / l = 4 * x := by rw [hxdef]; ring
  rw [h4x] at hRw

  have hinner : 3 * (r : ℝ) * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (m : ℝ) * (2 * b + 1)
      ≤ 13 * ((r : ℝ) * (x + S + t + η + L) + m * b) := by
    nlinarith [mul_nonneg hr0 hx, mul_nonneg hr0 hS, mul_nonneg hr0 (sub_nonneg.2 htR),
      mul_nonneg hr0 hη, mul_nonneg hr0 (sub_nonneg.2 hlam), mul_nonneg hr0 (by linarith : (0:ℝ) ≤ L),
      mul_nonneg hm0 hb.le]
  have hB : 0 ≤ (r : ℝ) * (x + S + t + η + L) + m * b := by
    have : 0 ≤ x + S + t + η + L := by linarith
    exact add_nonneg (mul_nonneg hr0 this) (mul_nonneg hm0 hb.le)
  have hf0 : (0 : ℝ) ≤ f := by linarith
  have hmain : max CA 0 * (3 * (f : ℝ) * r * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1))
      ≤ C * f * ((r : ℝ) * (x + S + t + η + L) + m * b) := by
    have e : 3 * (f : ℝ) * r * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1)
        = f * (3 * (r : ℝ) * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (m : ℝ) * (2 * b + 1)) := by ring
    rw [e]
    calc max CA 0 * (f * (3 * (r : ℝ) * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (m : ℝ) * (2 * b + 1)))
        ≤ max CA 0 * (f * (13 * ((r : ℝ) * (x + S + t + η + L) + m * b))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hf0) hK
      _ = (13 * max CA 0) * (f * ((r : ℝ) * (x + S + t + η + L) + m * b)) := by ring
      _ ≤ C * (f * ((r : ℝ) * (x + S + t + η + L) + m * b)) :=
          mul_le_mul_of_nonneg_right hC (mul_nonneg hf0 hB)
      _ = C * f * ((r : ℝ) * (x + S + t + η + L) + m * b) := by ring

  set Q : ℝ := (f : ℝ) ^ 2 * (t : ℝ) ^ 2 * ((r : ℝ) + t) with hQ
  have hQe : Q = (f : ℝ) ^ 2 * ((t : ℝ) ^ 2 * ((r : ℝ) + t)) := by rw [hQ]; ring
  have ht2 : (1 : ℝ) ≤ (t : ℝ) ^ 2 := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (t : ℝ) * t := mul_le_mul htR htR zero_le_one (by linarith)
      _ = (t : ℝ) ^ 2 := by ring
  have hf2 : (f : ℝ) ≤ (f : ℝ) ^ 2 := by
    calc (f : ℝ) = f * 1 := by ring
      _ ≤ (f : ℝ) * f := mul_le_mul_of_nonneg_left hfR hf0
      _ = (f : ℝ) ^ 2 := by ring
  have hrt : (1 : ℝ) ≤ (r : ℝ) + t := by linarith
  have hT1 : (1 : ℝ) ≤ (t : ℝ) ^ 2 * ((r : ℝ) + t) := one_le_mul_of_one_le_of_one_le ht2 hrt
  have hfQ : (f : ℝ) ≤ Q := by
    rw [hQe]
    exact hf2.trans (le_mul_of_one_le_right (sq_nonneg _) hT1)
  have hVQ : 4 * ((r : ℝ) + t) * t ≤ 4 * Q := by
    have h1 : ((r : ℝ) + t) * t ≤ (t : ℝ) ^ 2 * ((r : ℝ) + t) := by
      have : ((r : ℝ) + t) * t = ((r : ℝ) + t) * t * 1 := by ring
      calc ((r : ℝ) + t) * t ≤ ((r : ℝ) + t) * (t * t) :=
            mul_le_mul_of_nonneg_left (by
              calc (t : ℝ) = t * 1 := by ring
                _ ≤ (t : ℝ) * t := mul_le_mul_of_nonneg_left htR (by linarith)) (by linarith)
        _ = (t : ℝ) ^ 2 * ((r : ℝ) + t) := by ring
    have hf1 : (1 : ℝ) ≤ (f : ℝ) ^ 2 := hfR.trans hf2
    have h2 : (t : ℝ) ^ 2 * ((r : ℝ) + t) ≤ Q := by
      rw [hQe]; exact le_mul_of_one_le_left (by linarith) hf1
    linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hQL : Q ≤ Q * L := le_mul_of_one_le_right hQ0 hL.le
  have hTbQ : Tb ≤ 240 * Q * L := by
    have : 240 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * L = 240 * Q * L := by rw [hQ]; ring
    linarith
  have hpL : 260 * Q * L ≤ (p : ℝ) * L := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have : 260 * Q = (260 : ℝ) * (f : ℝ) ^ 2 * (t : ℝ) ^ 2 * ((r : ℝ) + t) := by rw [hQ]; ring
    linarith
  have hQL0 : 0 ≤ Q * L := mul_nonneg hQ0 (by linarith)
  linarith

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closing_numerical_inequality_theoremB : ∀ (CA C b l S η Rw Tb Vd : ℝ) (f r t m p : ℕ), 13 * max CA 0 ≤ C → 260 * f ^ 2 * t ^ 2 * (r + t) ≤ p → 1 ≤ t → 1 ≤ f → m ≤ r → 3 ≤ l → 0 ≤ S → 0 ≤ η → 0 < b → 1 < Real.log b → Rw ≤ max CA 0 * (3 * (f : ℝ) * r * (4 * b / l + 2 * S + 2 * Real.logb l (2 * b) + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1)) + f → Tb ≤ 240 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * Real.log b → Vd ≤ 4 * ((r : ℝ) + t) * t → Rw + Tb + Vd ≤ C * f * (r * (b / l + S + t + η + Real.log b) + m * b) + (p : ℝ) * Real.log b := by
  atlas_forward_decl GlobalTheory.closing_numerical_inequality
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TheoremB

theorem placesOver_finite (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem declNoColumns : ∀ (D : D7) (i : D.nd.Loc), (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, dc.col = ∅ := by
  intro D i _
  have hf := placesOver_finite D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero
  exact ⟨⟨hf.toFinset, ∅, Finset.disjoint_empty_right _, fun v => by simp⟩, rfl⟩

theorem localDelta_le_cuspTwistDepth : ∀ (D : D7) (i : D.nd.Loc), (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.vdel i ≤ (D.R.t : ℚ) := by
  intro D i hl
  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have htr : D.R.t ≤ D.R.t * D.R.r := Nat.le_mul_of_pos_right _ hr1
  have h4 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r) := by ring
  have hlt : D.R.t < D.nd.l i := by
    rcases hl with h | h <;> rw [h]
    · have := D.host.qd_big.1; rw [h4] at this; omega
    · have := D.host.qd_big.2; rw [h4] at this; omega
  have hl2 : D.nd.l i ≠ 2 := by have := D.R.rank_add_five_le; omega
  unfold NData.vdel
  rw [UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i (UpperTheory.Small.not_mem_of_qd D.host hl)]
  have hk : ∀ k ∈ Finset.Ioo 0 D.R.t, ((1 : ℕ) : ℚ) + (padicValNat (D.nd.l i) k : ℚ) = 1 := by
    intro k hk
    rw [Finset.mem_Ioo] at hk
    rw [padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hk.1 (by omega))]
    simp
  rw [Finset.sum_congr rfl hk]
  simp

theorem rowBound : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA : ℝ), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∀ dc : TruncatedSeriesCountingIdentities.Decl D i, ∃ lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ, TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (r i) (ρ i) π dc lenRow ∧ ∀ w ∈ dc.row, (lenRow w : ℝ) ≤ max CA 0 * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * (4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ)) + 3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * (2 * large₂.sc.b + 1)) + 1 := GlobalTheory.T.rowPlaces_satisfy_rowHypothesis_at_q_and_d

theorem tbConst : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∃ cB : ℕ, TruncatedSeriesCountingIdentities.admTB i (r i) π cB ∧ (cB : ℝ) ≤ 60 * (D.R.t : ℝ) * (D.R.f : ℝ) * ((D.R.r : ℝ) + (D.R.t : ℝ)) * Real.log large₂.sc.b := GlobalTheory.T.blockBound_qd_places_uniformConst

theorem bkAt : ∀ (D : D7), EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.admBK i := GlobalTheory.T.blochKatoHypothesis_globalStep_at_qd

theorem cycDegree_gt : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E) := GlobalTheory.T.mul_lt_finrank_cyclotomic_at_q_and_d

theorem ne_typePrimes : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1 := GlobalTheory.T.theoremB_ramifiedPrimes_ne_typePrimes

theorem degBounds : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.E)), (∀ w ∈ s, w ∈ placesOver D.host.E (D.nd.l i)) → (∑ w ∈ s, locDeg D.host.E w) ≤ 2 * D.R.f ∧ 2 * s.card ≤ ∑ w ∈ s, locDeg D.host.E w := GlobalTheory.T.theoremB_localDegree_sum_bounds

theorem closingIneq : ∀ (CA C b l S η Rw Tb Vd : ℝ) (f r t m p : ℕ), 13 * max CA 0 ≤ C → 260 * f ^ 2 * t ^ 2 * (r + t) ≤ p → 1 ≤ t → 1 ≤ f → m ≤ r → 3 ≤ l → 0 ≤ S → 0 ≤ η → 0 < b → 1 < Real.log b → Rw ≤ max CA 0 * (3 * (f : ℝ) * r * (4 * b / l + 2 * S + 2 * Real.logb l (2 * b) + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1)) + f → Tb ≤ 240 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * Real.log b → Vd ≤ 4 * ((r : ℝ) + t) * t → Rw + Tb + Vd ≤ C * f * (r * (b / l + S + t + η + Real.log b) + m * b) + (p : ℝ) * Real.log b := GlobalTheory.T.closing_numerical_inequality_theoremB

theorem theoremB_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 13 * max CA 0 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp := by
  intro D HW F r ρ large₂ ep CA C Qp hC hP hW hA hN5 hG1 hG2 hG3 hG4 hG5 hG6 hSet hTB hBK hKill hJump hFon hLit hPar
  obtain ⟨h0, h1⟩ := GlobalTheory.T.local_fields_at_auxiliary_primes D
  intro i hl tw hbig π hπ hsF hsha
  have hQ : EmbeddingTypeJumps.AtQD i := ⟨⟨hl, tw⟩, ⟨π, (D.Zgood_tie i π).1 hπ⟩⟩
  obtain ⟨dc, hcol⟩ := declNoColumns D i hl
  obtain ⟨lenRow, hROW, hRowB⟩ := rowBound D r ρ large₂ ep CA h0 h1 hA hJump hFon hG2 hSet hLit hPar i hQ π hπ dc
  obtain ⟨cB, hTBi, hcB⟩ := tbConst D HW F r ρ large₂ ep h0 h1 hW hTB hJump hFon hG2 hSet hLit hPar i hQ π hπ
  have hAdm : TruncatedSeriesCountingIdentities.admitted i (r i) (ρ i) π dc lenRow (fun _ => 0) cB := by
    refine ⟨hG1 i hQ, hG2 i hQ π hπ, hG3 i hQ π hπ, hG4 i hQ, hG5 i hQ, (hLit i hQ).1, hG6 i hQ,
      bkAt D hBK hLit i hQ, hTBi, hROW, ?_, (hSet i hQ π hπ).1, (hSet i hQ π hπ).2.1,
      (hSet i hQ π hπ).2.2.1, (hSet i hQ π hπ).2.2.2, (hLit i hQ).2.2.1, (GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main D i).1,
      (hLit i hQ).2.2.2.1, (hLit i hQ).2.2.2.2.1, (hLit i hQ).2.2.2.2.2⟩
    intro w hw hwc
    simp [hcol] at hwc
  obtain ⟨hg0, hg1⟩ := ne_typePrimes D h1 i hl
  have key := hN5 i π dc lenRow (fun _ => 0) cB hAdm hg0 hg1 (LargeLevelLemmas.zgoodSubsetZ i hπ) hsF hsha
  have hlw : ∀ w ∈ dc.row, TruncatedSeriesCountingIdentities.lenW i (ρ i) π dc lenRow (fun _ => 0) w = lenRow w := by
    intro w _
    unfold TruncatedSeriesCountingIdentities.lenW
    rw [dif_neg (by simp [hcol])]
  rw [hcol] at key
  simp only [Finset.union_empty] at key
  rw [Finset.sum_congr rfl hlw] at key
  simp only [Finset.card_empty, Nat.cast_zero, zero_add, mul_one, mul_zero, zero_mul, add_zero] at key
  have keyR := (Rat.cast_le (K := ℝ)).2 key
  push_cast at keyR
  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hmr : D.R.m ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; omega
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hf1 : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hl3 : 3 ≤ D.nd.l i := by
    have htr : 1 ≤ D.R.t * D.R.r := Nat.mul_pos ht1 hr1
    rcases hl with h | h <;> rw [h]
    · have := D.host.qd_big.1; nlinarith
    · have := D.host.qd_big.2; nlinarith
  have hnV : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
  have hL0 : 0 < large₂.sc.L := by unfold Scale.L; exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hb1 : 1 < large₂.sc.b := by unfold Scale.b; have := Real.add_one_lt_exp (ne_of_gt hL0); linarith
  have hb0 : 0 < large₂.sc.b := by linarith
  have hLb : 1 < Real.log large₂.sc.b := by
    unfold Scale.b; rw [Real.log_exp]; unfold Scale.L
    exact Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hrowP : ∀ w ∈ dc.row, w ∈ placesOver D.host.E (D.nd.l i) := fun w hw => (dc.cover w).1 (Or.inl hw)
  obtain ⟨hSD, hSC⟩ := degBounds D h1 i hl dc.row hrowP
  have hSDr : ((∑ w ∈ dc.row, locDeg D.host.E w : ℕ) : ℝ) ≤ 2 * D.R.f := by exact_mod_cast hSD
  have hSCr : 2 * (dc.row.card : ℝ) ≤ ((∑ w ∈ dc.row, locDeg D.host.E w : ℕ) : ℝ) := by exact_mod_cast hSC
  set SD : ℝ := ((∑ w ∈ dc.row, locDeg D.host.E w : ℕ) : ℝ) with hSDdef
  set K := max CA 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  set X := 4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ) with hX
  have hl3r : (3 : ℝ) ≤ D.nd.l i := by exact_mod_cast hl3
  have hX0 : 0 ≤ X := by
    have : 0 ≤ Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) := Real.logb_nonneg (by linarith) (by linarith)
    have := large₂.Sc_pos; have := large₂.etaSz_pos
    have : 0 ≤ 4 * large₂.sc.b / (D.nd.l i : ℝ) := by positivity
    positivity
  set Y := 2 * large₂.sc.b + 1 with hY
  have hY0 : 0 ≤ Y := by positivity
  have hRw : (∑ w ∈ dc.row, (lenRow w : ℝ)) ≤
      K * (3 * (D.R.f : ℝ) * D.R.r * X + 6 * (D.R.f : ℝ) * D.R.m * Y) + D.R.f := by
    have hcard : (dc.row.card : ℝ) ≤ D.R.f := by linarith
    have hsum : (∑ w ∈ dc.row, (K * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * X +
        3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * Y) + 1)) =
        (K * D.R.r * X + 3 * K * D.R.m * Y) * SD + dc.row.card * (K * D.R.r * X + 1) := by
      have : ∀ w ∈ dc.row, K * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * X +
          3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * Y) + 1 =
          (K * D.R.r * X + 3 * K * D.R.m * Y) * ((locDeg D.host.E w : ℕ) : ℝ) + (K * D.R.r * X + 1) := by
        intro w _; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hSDdef]
      push_cast; ring
    have e1 : (K * D.R.r * X + 3 * K * D.R.m * Y) * SD ≤ (K * D.R.r * X + 3 * K * D.R.m * Y) * (2 * D.R.f) :=
      mul_le_mul_of_nonneg_left hSDr (by positivity)
    have e2 : (dc.row.card : ℝ) * (K * D.R.r * X + 1) ≤ D.R.f * (K * D.R.r * X + 1) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    calc (∑ w ∈ dc.row, (lenRow w : ℝ)) ≤ ∑ w ∈ dc.row, (K * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * X +
          3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * Y) + 1) := Finset.sum_le_sum hRowB
      _ = (K * D.R.r * X + 3 * K * D.R.m * Y) * SD + dc.row.card * (K * D.R.r * X + 1) := hsum
      _ ≤ (K * D.R.r * X + 3 * K * D.R.m * Y) * (2 * D.R.f) + D.R.f * (K * D.R.r * X + 1) := add_le_add e1 e2
      _ = K * (3 * (D.R.f : ℝ) * D.R.r * X + 6 * (D.R.f : ℝ) * D.R.m * Y) + D.R.f := by ring
  have hTb : (D.R.t : ℝ) * ∑ w ∈ dc.row, (((locDeg D.host.E w : ℕ) : ℝ) + 2) * (cB : ℝ) ≤
      240 * (D.R.t : ℝ) ^ 2 * (D.R.f : ℝ) ^ 2 * ((D.R.r : ℝ) + D.R.t) * Real.log large₂.sc.b := by
    have hs : ∑ w ∈ dc.row, (((locDeg D.host.E w : ℕ) : ℝ) + 2) * (cB : ℝ) = (SD + 2 * dc.row.card) * cB := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hSDdef]
      push_cast; ring
    rw [hs]
    have h4 : SD + 2 * (dc.row.card : ℝ) ≤ 4 * D.R.f := by linarith
    have hc0 : (0 : ℝ) ≤ cB := by positivity
    have hS0 : (0 : ℝ) ≤ SD + 2 * (dc.row.card : ℝ) := by positivity
    calc (D.R.t : ℝ) * ((SD + 2 * dc.row.card) * cB) ≤ (D.R.t : ℝ) * ((4 * D.R.f) *
          (60 * (D.R.t : ℝ) * (D.R.f : ℝ) * ((D.R.r : ℝ) + (D.R.t : ℝ)) * Real.log large₂.sc.b)) := by
          gcongr
      _ = 240 * (D.R.t : ℝ) ^ 2 * (D.R.f : ℝ) ^ 2 * ((D.R.r : ℝ) + D.R.t) * Real.log large₂.sc.b := by ring
  have hVd : 4 * (D.R.nV : ℝ) * ((D.nd.vdel i : ℚ) : ℝ) ≤ 4 * ((D.R.r : ℝ) + D.R.t) * D.R.t := by
    rw [hnV]
    have h1' : ((D.nd.vdel i : ℚ) : ℝ) ≤ D.R.t := by exact_mod_cast localDelta_le_cuspTwistDepth D i hl
    have : (0 : ℝ) ≤ D.R.r + D.R.t := by positivity
    nlinarith
  have hK2 := (hKill i hl tw (Or.inr (cycDegree_gt D h1 i hl)) π hπ).2
  simp only [EmbeddingTypeJumps.vZeta] at hK2
  push_cast at hK2
  have har := closingIneq CA C large₂.sc.b (D.nd.l i) large₂.Sc large₂.etaSz (∑ w ∈ dc.row, (lenRow w : ℝ))
    ((D.R.t : ℝ) * ∑ w ∈ dc.row, (((locDeg D.host.E w : ℕ) : ℝ) + 2) * (cB : ℝ))
    (4 * (D.R.nV : ℝ) * ((D.nd.vdel i : ℚ) : ℝ)) D.R.f D.R.r D.R.t D.R.m (EmbeddingTypeJumps.polyVal Qp D.R.f D.R.r D.R.t)
    hC (hP _ _ _) ht1 hf1 hmr hl3r large₂.Sc_pos.le large₂.etaSz_pos.le hb0 hLb hRw hTb hVd
  unfold EmbeddingTypeJumps.bndB
  push_cast
  linarith [keyR, hK2, har]

end GlobalTheory.TheoremB
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theoremB_of_admittedHypotheses : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 13 * max CA 0 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp := by
  atlas_forward_decl GlobalTheory.TheoremB.theoremB_of_admitted
end
