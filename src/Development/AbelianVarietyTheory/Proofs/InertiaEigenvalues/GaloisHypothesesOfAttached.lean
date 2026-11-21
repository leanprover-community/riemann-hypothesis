import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Eps0UnramFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobDualOfAttached
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkFrobOfAttached
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeOfAttached
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsGoodOfAttached
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PureOfAttached
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfAttached
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAndResidualTrivComplexConj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateNegativeJumpCountOfGoodHodgeJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepresentationHomFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsJumpVOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaElementActsByScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexReadingLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvAwayOfPure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeOfConjDualCharpoly

section
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem firstAdmissibilityAt_of_parts : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HodgeL bkP i s → (∀ v, NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v) → NegCount bkP i s → IsotypicValuationAtRing bkP i s := by
  intro D bkP i s h1 h2 h3 h4
  exact ⟨h1, h2, fun v => (h3 v).1, fun v => (h3 v).2, h4⟩

end GlobalTheory.TripleGal
end

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypicValuationAtRing_of_unrRho_hodgeL_noInv_negCount : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HodgeL bkP i s → (∀ v, NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v) → NegCount bkP i s → IsotypicValuationAtRing bkP i s := by
  atlas_forward_decl GlobalTheory.TripleGal.firstAdmissibilityAt_of_parts
end

section
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.AdmFrobTriple

theorem not_mem_placesOver_of_ne (E : Type) [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ≠ q) {v : HeightOneSpectrum (𝓞 E)} (h1 : v ∈ placesOver E p) : v ∉ placesOver E q := by
  intro h2
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 h)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 E))
  have h1' : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := h1
  have h2' : ((q : ℕ) : 𝓞 E) ∈ v.asIdeal := h2
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1') (Ideal.mul_mem_left _ _ h2')

theorem continuous_algebraMap_padicInt {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O] (I : Ideal O) (hI : IsAdic I) (hO : (l : O) ∈ I) :
    Continuous (algebraMap ℤ_[l] O) := by
  refine continuous_of_continuousAt_zero (algebraMap ℤ_[l] O) ?_
  rw [ContinuousAt, map_zero, hI.hasBasis_nhds_zero.tendsto_right_iff]
  intro n _
  have hl : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[l]) hl] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hO n)

theorem sum_coeff_charpolyRev {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    ∑ k ∈ Finset.range (n + 1), M.charpolyRev.coeff k = (1 - M).det := by
  have hdeg : M.charpolyRev.natDegree < n + 1 := by
    rw [← Matrix.reverse_charpoly]
    have := Polynomial.reverse_natDegree_le M.charpoly
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
    omega
  have h1 := Polynomial.eval_eq_sum_range' hdeg (1 : R)
  simp only [one_pow, mul_one] at h1
  rw [← h1, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, RingHom.mapMatrix_apply]
  split_ifs <;> simp

variable {D : D7}

theorem l_mem (i : D.ntw.Tw) : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i) := by
  intro h
  have h2 := h.map (algebraMap (D.ntw.O0 i) (D.ntw.O i))
  rw [map_natCast] at h2
  exact D.ntw.O_l i h2

theorem continuous_twistCyclotomicCharacter (i : D.ntw.Tw) :
    Continuous fun g : Gen.GE D.nd => ((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) :=
  (continuous_algebraMap_padicInt _ (D.ntw.twistBaseCoefficientRing_isAdic i) (l_mem i)).comp
    (Units.continuous_val.comp (continuous_cycZ D.host.E D.nd.Om (D.ntw.l i)))

theorem pD_not (i : D.ntw.Tw) (v) (hv : v ∈ D.ntw.pD i) :
    v ∉ placesOver D.host.E (D.ntw.l i) ∧ ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
  have h2 : v ∈ (D.ntw.pD i : Set _) := hv
  rw [D.ntw.pD_eq] at h2
  have hl := (D.ntw.lPrime i).out
  split_ifs at h2 with h
  · refine ⟨not_mem_placesOver_of_ne _ D.host.pde'_prime hl ?_ h2, fun k =>
      not_mem_placesOver_of_ne _ D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h2⟩
    rw [h]; exact D.host.pde_ne.symm
  · exact ⟨not_mem_placesOver_of_ne _ D.host.pde_prime hl (Ne.symm h) h2, fun k =>
      not_mem_placesOver_of_ne _ D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h2⟩

end GlobalTheory.AdmFrobTriple

namespace GlobalTheory.AdmFrobTriple

theorem eta_smul {D : D7} (i : D.ntw.Tw) (s : D.ntw.Sig i) (σ : Gen.GE D.nd) :
    ((((eps0 D.ntw i) ^ D.R.t * (chiS i s)⁻¹) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) •
      ((D.ntw.rhoS i s σ : GL (Fin D.R.r) (D.ntw.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) =
    (((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t) • Tmat i s σ := by
  simp only [Tmat, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
    Units.val_pow_eq_pow_val, mul_smul]

theorem adm8At_of_hkFrob : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HkFrob i s →
    characterTwistExists D.ntw D.nexp i s := by
  intro D i s hU hH _
  refine ⟨(eps0 D.ntw i) ^ D.R.t * (chiS i s)⁻¹, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous fun g : Gen.GE D.nd => (((chiS i s g)⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) := by
      simp_rw [← map_inv]
      exact (D.ntw.twistCharacterFamily_continuous i _ _).comp continuous_inv
    have he : (fun g : Gen.GE D.nd => ((((eps0 D.ntw i) ^ D.R.t * (chiS i s)⁻¹) g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) =
        fun g => ((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t *
          (((chiS i s g)⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) := by
      funext g
      simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
        Units.val_pow_eq_pow_val]
    rw [he]
    exact ((continuous_twistCyclotomicCharacter i).pow _).mul hc
  · intro P hP _ A hA σ hσ
    have hPl : P ∉ placesOver D.host.E (D.ntw.l i) := fun h => hP (D.ntw.twistExcludedPlaces_contains_residueChar i h)
    have hPg : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k h => hP (D.ntw.placesOver_subset_exceptional i k h)
    have hPd : P ∉ D.ntw.pD i := fun h => hP (D.ntw.primes_subset_exceptional i h)
    have h1 : D.ntw.rhoS i s σ = 1 := hU P hPl hPg A hA σ hσ
    have h2 : chiS i s σ = 1 := D.ntw.twistCharacterFamily_unramified i _ _ P hPl hPg hPd A hA σ hσ
    have h3 : eps0 D.ntw i σ = 1 := (GlobalTheory.TripleGal.eps0_unram_frob D i P hPl A hA).1 σ hσ
    simp [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, h1, h2, h3]
  · intro v hv A hA
    obtain ⟨hl, hg⟩ := pD_not i v hv
    have h1 : ∀ σ ∈ Ine (F := D.host.E) A, D.ntw.rhoS i s σ = 1 := fun σ hσ => hU v hl hg A hA σ hσ
    have h3 : ∀ σ ∈ Ine (F := D.host.E) A, eps0 D.ntw i σ = 1 := (GlobalTheory.TripleGal.eps0_unram_frob D i v hl A hA).1
    have h2 := D.ntw.twistCharacterFamily_at_auxiliaryPlaces i (D.ntw.jS i s) (D.ntw.side i s) v hv A hA
    cases hb : D.ntw.side i s
    · left
      intro σ hσ
      have h2' : chiS i s σ = (D.ntw.delta i σ)⁻¹ := by
        have := h2 σ hσ; rw [hb] at this; simpa [chiS, hb] using this
      simp [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, h1 σ hσ, h2', h3 σ hσ]
    · right
      intro σ hσ
      have h2' : chiS i s σ = D.ntw.delta i σ := by
        have := h2 σ hσ; rw [hb] at this; simpa [chiS, hb] using this
      simp [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, h1 σ hσ, h2', h3 σ hσ]
  · intro P hP hs σ hσ
    rw [eta_smul, ← sum_coeff_charpolyRev, map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    exact hH P hP hs σ hσ k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

end GlobalTheory.AdmFrobTriple
end
end

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterTwistExists_of_unrRho_of_hkFrob : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HkFrob i s → characterTwistExists D.ntw D.nexp i s := by
  atlas_forward_decl GlobalTheory.AdmFrobTriple.adm8At_of_hkFrob
end

section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobDual_of_attached : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), TripleAtt D.naut bkP i s → FrobDual i s := by
  first | exact @GlobalTheory.TripleFrobDual.frobDual_of_tripleAtt | exact GlobalTheory.TripleFrobDual.frobDual_of_tripleAtt | (intros; apply GlobalTheory.TripleFrobDual.frobDual_of_tripleAtt <;> assumption)
end

section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hkFrob_of_attached : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), TripleAtt D.naut bkP i s → HkFrob i s := by
  first | exact @GlobalTheory.TripleGal.HkFrobProof.hkFrob_of_tripleAtt | exact GlobalTheory.TripleGal.HkFrobProof.hkFrob_of_tripleAtt | (intros; apply GlobalTheory.TripleGal.HkFrobProof.hkFrob_of_tripleAtt <;> assumption)
end

section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_of_attached : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), TripleAtt D.naut bkP i s → HodgeL bkP i s := by
  first | exact @GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt | exact GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt | (intros; apply GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt <;> assumption)
end

section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jumps_good_of_attached : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), TripleAtt D.naut bkP i s → ∃ ι J, JumpsAre bkP i s ι J ∧ GoodJ D J := by
  first | exact @GlobalTheory.TripleGal.Jumps.exists_jumpsAre_goodJ | exact GlobalTheory.TripleGal.Jumps.exists_jumpsAre_goodJ | (intros; apply GlobalTheory.TripleGal.Jumps.exists_jumpsAre_goodJ <;> assumption)
end

section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_of_attached : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), TripleAtt D.naut bkP i s → ∃ ι, Pure i s ι := by
  first | exact @GlobalTheory.TripleGal.pure_of_tripleAtt | exact GlobalTheory.TripleGal.pure_of_tripleAtt | (intros; apply GlobalTheory.TripleGal.pure_of_tripleAtt <;> assumption)
end

section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_of_attached : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), TripleAtt D.naut bkP i s → UnrRho i s := by
  first | exact @GlobalTheory.TripleUnramified.unrRho_of_tripleAtt | exact GlobalTheory.TripleUnramified.unrRho_of_tripleAtt | (intros; apply GlobalTheory.TripleUnramified.unrRho_of_tripleAtt <;> assumption)
end

section
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.CharDualDense

theorem t2_O0 {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) :
    T2Space (X.O0 i) :=
  (IsAdic.isHausdorff_iff (X.twistBaseCoefficientRing_isAdic i)).1 inferInstance

theorem finite_S0_conj {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) :
    ((X.S0 i : Set (PlE D.host)) ∪ {P | ∃ P' ∈ X.S0 i, IsConjPl D.host P P'}).Finite := by
  refine (X.S0 i).finite_toSet.union ?_
  refine ((X.S0 i).finite_toSet.biUnion (t := fun P' => {P | IsConjPl D.host P' P}) fun P' _ => ?_).subset ?_
  · exact (show ({P | IsConjPl D.host P' P} : Set (PlE D.host)).Subsingleton from
      fun a ha b hb => GlobalTheory.TwistDet.isConjPl_unique ha hb).finite
  · rintro P ⟨P', hP', hc⟩
    exact Set.mem_biUnion (x := P') hP' (GlobalTheory.TwistDet.isConjPl_symm hc)

theorem charDual_of_frobDual : ∀ (D : D7), GlobalTheory.TypeLeaf.FrobDense D → ∀ (i : D.ntw.Tw) (s : D.ntw.Sig i),
    FrobDual i s → CharDual i s := by
  intro D hF i s hFD g g' hg'
  haveI := t2_O0 D.ntw i
  have e : g' = GlobalTheory.TwistDet.cConj D.ntw g := by
    ext x
    rw [hg', GlobalTheory.TwistDet.cConj_apply]
  subst e
  refine GlobalTheory.TypeLeaf.charpoly_eq_of_dense (Gen.GE D.nd) (D.ntw.O0 i) D.R.r
    (fun g => Tdual i s (GlobalTheory.TwistDet.cConj D.ntw g))
    (fun g => ((((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t) • Tmat i s g)) _
    (hF _ (finite_S0_conj D.ntw i))
    ((GlobalTheory.PrimeToInertia.continuous_Tdual i s).comp (GlobalTheory.ResConjTriv.continuous_cConj D.ntw)) ?_ ?_ g
  · have h1 : Continuous fun g : Gen.GE D.nd => ((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) :=
      (GlobalTheory.PrimeToInertia.continuous_algebraMap_padicInt _ (D.ntw.twistBaseCoefficientRing_isAdic i) (GlobalTheory.PrimeToInertia.l_mem i)).comp
        (Units.continuous_val.comp (continuous_cycZ D.host.E D.nd.Om (D.ntw.l i)))
    exact (h1.pow _).smul (GlobalTheory.PrimeToInertia.continuous_Tmat i s)
  · rintro σ ⟨w, hwT, hsp, B, hB, hσ⟩
    refine hFD w (fun h => hwT (Or.inl h)) hsp (fun P' hc h => hwT (Or.inr ⟨P', h, hc⟩)) B hB σ _ hσ
      (GlobalTheory.TwistDet.cConj_apply D.ntw σ)

end GlobalTheory.CharDualDense

end
end

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjDualCharpoly_of_splitFrobenius_dense : ∀ (D : D7), GlobalTheory.TypeLeaf.FrobDense D → ∀ (i : D.ntw.Tw) (s : D.ntw.Sig i), FrobDual i s → CharDual i s := by
  atlas_forward_decl GlobalTheory.CharDualDense.charDual_of_frobDual
end

section
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.NoLocalInvariants

section General

variable {R : Type} [CommRing R] [IsDomain R] {n : Type} [Fintype n] [DecidableEq n]

theorem eq_zero_of_fixed {M : Matrix n n R} (h : (M - 1).det ≠ 0)
    {x : n → FractionRing R} (hx : (M.map (algebraMap R (FractionRing R))).mulVec x = x) : x = 0 := by
  have h1 : ((M - 1).map (algebraMap R (FractionRing R))).mulVec x = 0 := by
    have e : (M - 1).map (algebraMap R (FractionRing R)) =
        M.map (algebraMap R (FractionRing R)) - 1 := by
      ext a b
      simp [Matrix.sub_apply, Matrix.one_apply, apply_ite (algebraMap R (FractionRing R))]
    rw [e, Matrix.sub_mulVec, hx, Matrix.one_mulVec, sub_self]
  have h2 : ((M - 1).map (algebraMap R (FractionRing R))).det ≠ 0 := by
    have e : ((M - 1).map (algebraMap R (FractionRing R))).det =
        algebraMap R (FractionRing R) (M - 1).det := by
      simpa using ((algebraMap R (FractionRing R)).map_det (M - 1)).symm
    rw [e]
    exact fun h0 => h ((IsFractionRing.injective R (FractionRing R)) (by simpa using h0))
  exact Matrix.eq_zero_of_mulVec_eq_zero h2 h1

theorem det_inv_transpose_sub_one_ne_zero {M : Matrix n n R} (hu : IsUnit M.det)
    (h : (M - 1).det ≠ 0) : ((M⁻¹).transpose - 1).det ≠ 0 := by
  have e : (M⁻¹).transpose - 1 = (M⁻¹ - 1).transpose := by simp
  rw [e, Matrix.det_transpose]
  intro h0
  have h1 : (M⁻¹ - 1) * M = -(M - 1) := by
    rw [sub_mul, Matrix.nonsing_inv_mul _ hu, one_mul]
    abel
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_neg] at h2
  have h3 : ((-1 : R) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ (by simp)
  exact h (by simpa [h3] using h2.symm)

omit [IsDomain R] in

theorem det_scaled_sub_one_ne_zero [IsLocalRing R] (P : Matrix n n R) (c : Rˣ)
    (h : (P.map (IsLocalRing.residue R) - (IsLocalRing.residue R (c : R)) • (1 : Matrix n n _)).det ≠ 0) :
    ((((c⁻¹ : Rˣ) : R) • P) - 1).det ≠ 0 := by
  intro h0
  have e1 : P - (c : R) • (1 : Matrix n n R) = (c : R) • ((((c⁻¹ : Rˣ) : R) • P) - 1) := by
    rw [smul_sub, smul_smul, Units.mul_inv, one_smul]
  have e2 : (P - (c : R) • (1 : Matrix n n R)).det = 0 := by
    rw [e1, Matrix.det_smul, h0, mul_zero]
  apply h
  have e3 : P.map (IsLocalRing.residue R) - (IsLocalRing.residue R (c : R)) • (1 : Matrix n n _) =
      (P - (c : R) • (1 : Matrix n n R)).map (IsLocalRing.residue R) := by
    ext a b
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, apply_ite (IsLocalRing.residue R)]
  rw [e3]
  have := (IsLocalRing.residue R).map_det (P - (c : R) • (1 : Matrix n n R))
  rw [e2, map_zero] at this
  simpa using this.symm

end General

theorem noInv_of_adm2At : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), ValuationStabilityAtRing D.ntw i s → ∀ k, D.host.g k ≠ D.ntw.l i → ∀ v ∈ placesOver D.host.E (D.host.g k), NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  intro D i s h k hk v hv
  have hvl : v ∉ placesOver D.host.E (D.ntw.l i) := by
    intro hl
    have hlp : (D.ntw.l i).Prime := Fact.out
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2
      ((Nat.coprime_primes (D.host.g_prime k) hlp).2 hk)
    have h1 : (1 : 𝓞 D.host.E) ∈ v.asIdeal := by
      have e : (1 : 𝓞 D.host.E) = (a : 𝓞 D.host.E) * ((D.host.g k : ℕ) : 𝓞 D.host.E) +
          (b : 𝓞 D.host.E) * ((D.ntw.l i : ℕ) : 𝓞 D.host.E) := by
        have h2 := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
        push_cast at h2
        exact h2.symm
      rw [e]
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hl)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have key : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) A v →
      ∃ σ ∈ Ine (F := D.host.E) A, (Tmat i s σ - 1).det ≠ 0 := by
    intro A hA
    obtain ⟨-, σ, hσ, hdet⟩ := h.2 k hk v hv A hA
    exact ⟨σ, hσ, det_scaled_sub_one_ne_zero _ _ hdet⟩
  constructor
  · intro A hA x hx
    obtain ⟨σ, hσ, hd⟩ := key A hA
    exact eq_zero_of_fixed hd (hx σ (Ine_le_Dec A hσ))
  · intro A hA x hx
    obtain ⟨σ, hσ, hd⟩ := key A hA
    have he := (GlobalTheory.TripleGal.eps0_unram_frob D i v hvl A hA).1 σ hσ
    have hu : IsUnit (Tmat i s σ).det := by
      rw [← Tgl_coe]
      exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
    have hT : Tdual i s σ = ((Tmat i s σ)⁻¹).transpose := by
      simp [Tdual, he]
    have := hx σ (Ine_le_Dec A hσ)
    rw [hT] at this
    exact eq_zero_of_fixed (det_inv_transpose_sub_one_ne_zero hu hd) this

end GlobalTheory.NoLocalInvariants
end
end

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noInv_at_type_primes : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), ValuationStabilityAtRing D.ntw i s → ∀ k, D.host.g k ≠ D.ntw.l i → ∀ v ∈ placesOver D.host.E (D.host.g k), NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  atlas_forward_decl GlobalTheory.NoLocalInvariants.noInv_of_adm2At
end

section
section
noncomputable section

namespace GlobalTheory.InvJump

section Generic

open Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem eq_zero_of_mem_Fil_one (c : K) (h : algebraMap K BdR c ∈ PD.Fil 1) : c = 0 := by
  by_contra hc
  have h1 : (1 : BdR) ∈ PD.Fil 1 := by
    have := (PD.Fil 1).smul_mem c⁻¹ h
    rwa [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc, map_one] at this
  exact PD.not_mem_filtration_two (by simpa using PD.Fil_mul 1 1 _ _ h1 PD.mem_filtration_one)

theorem isJumpV_zero_of_invariant [CharZero Qp] (ρ : Representation LL G V) (x : V) (hx : x ≠ 0)
    (hinv : ∀ g, ρ g x = x) (τ : K →ₐ[Qp] LL) : IsJumpV PD ρ τ 0 := by
  classical
  haveI := PD.finK
  let b := Module.finBasis Qp K
  let b' := b.traceDual
  let y : V ⊗[Qp] BdR := ∑ i, (τ (b' i) • x) ⊗ₜ[Qp] algebraMap K BdR (b i)
  have e1 : ∀ z : K, z = ∑ j, Algebra.trace Qp K (z * b' j) • b j := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    conv_rhs => rw [← b.sum_repr z, Finset.sum_mul, map_sum]
    simp only [b', smul_mul_assoc, map_smul, Module.Basis.trace_mul_traceDual]
    simp
  have e2 : ∀ z : K, z = ∑ j, Algebra.trace Qp K (z * b j) • b' j := by
    intro z
    conv_lhs => rw [← b'.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    conv_rhs => rw [← b'.sum_repr z]
    simp [b', Finset.sum_mul, Module.Basis.trace_traceDual_mul]
  have h0 : y ∈ FildR PD ρ τ 0 := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      simp [y, actVdR, map_sum, hinv]
    · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero, LinearMap.smul_apply]
      intro c
      have l : mulVdR (LL := LL) (V := V) c y =
          ∑ i, ∑ j, Algebra.trace Qp K (c * b i * b' j) •
            ((τ (b' i) • x) ⊗ₜ[Qp] algebraMap K BdR (b j)) := by
        simp only [y, map_sum, mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
          LinearMap.mulLeft_apply, ← map_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [e1 (c * b i), map_sum, tmul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← tmul_smul, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
      have r : τ c • y =
          ∑ j, ∑ i, Algebra.trace Qp K (c * b' j * b i) •
            ((τ (b' i) • x) ⊗ₜ[Qp] algebraMap K BdR (b j)) := by
        simp only [y, Finset.smul_sum, smul_tmul', smul_smul, ← map_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        conv_lhs => rw [e2 (c * b' j), map_sum, Finset.sum_smul, sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_assoc]
      rw [l, r, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_right_comm]
    · refine Submodule.sum_mem _ fun i _ => ⟨(τ (b' i) • x) ⊗ₜ ⟨algebraMap K BdR (b i), ?_⟩, rfl⟩
      rw [Algebra.algebraMap_eq_smul_one]
      exact (PD.Fil 0).smul_mem _ PD.one_mem
  intro h
  rw [← h] at h0
  obtain ⟨w, hw⟩ := h0.2
  obtain ⟨φ, hφ⟩ : ∃ φ : LL →ₗ[Qp] Qp, φ 1 = 1 := by
    obtain ⟨φ, hφ⟩ := (Algebra.linearMap Qp LL).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.2 (algebraMap Qp LL).injective)
    exact ⟨φ, by simpa using LinearMap.congr_fun hφ 1⟩
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[LL] LL, f x = 1 := Module.Projective.exists_dual_eq_one LL hx
  let m : V ⊗[Qp] BdR →ₗ[Qp] BdR :=
    (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ (φ ∘ₗ f.restrictScalars Qp).rTensor BdR
  have hm : ∀ w, m (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      ((PD.Fil (0 + 1)).restrictScalars Qp).subtype w) ∈ (PD.Fil (0 + 1)).restrictScalars Qp := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simpa [m] using ((PD.Fil (0 + 1)).restrictScalars Qp).smul_mem (φ (f v)) c.2
    | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  have h1 := hm w
  rw [hw] at h1
  have h2 : m y = algebraMap K BdR (∑ i, φ (τ (b' i)) • b i) := by
    simp only [y, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [m, hf, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  rw [h2] at h1
  have h3 := eq_zero_of_mem_Fil_one PD _ (by rw [zero_add] at h1; exact h1)
  have h4 : ∀ i, φ (τ (b' i)) = 0 := Fintype.linearIndependent_iff.1 b.linearIndependent _ h3
  have h5 : φ ∘ₗ τ.toLinearMap = 0 := b'.ext fun i => by simpa using h4 i
  have := LinearMap.congr_fun h5 1
  simp [hφ] at this

end Generic

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

open scoped Pointwise in

theorem noInv_of_noJump : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tmat i s) v := by
  intro D bkP i s hJ v hv A hA x hx
  by_contra hx0
  obtain ⟨k, hk⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) (D.nd.plOm.2 v) hA
  let Bw := bkP.br i v hv
  have inj : Function.Injective Bw.toLL := Subtype.val_injective.comp Bw.eO.injective
  let ψ : FractionRing (D.ntw.O0 i) →+* ↥Bw.LL.1 := IsFractionRing.lift inj
  have hψ : ∀ a, ψ (algebraMap _ _ a) = Bw.toLL a := fun a => IsFractionRing.lift_algebraMap inj a
  let M : Gen.GE D.nd → Matrix (Fin D.R.r) (Fin D.R.r) ↥Bw.LL.1 := fun g => (Tmat i s g).map Bw.toLL
  have hM : ∀ g g', M (g * g') = M g * M g' := fun g g' => by
    simp only [M, ← Tgl_coe, map_mul, Units.val_mul, Matrix.map_mul]
  have hM1 : M 1 = 1 := by
    simp only [M, ← Tgl_coe, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let z : Fin D.R.r → ↥Bw.LL.1 := fun a => ψ (x a)
  have hz : ∀ g ∈ Dec (F := D.host.E) A, (M g).mulVec z = z := fun g hg => by
    funext a
    have := congrArg ψ (congrFun (hx g hg) a)
    simpa [Matrix.mulVec, dotProduct, map_sum, hψ, M, z] using this
  have hz0 : (M k⁻¹).mulVec z ≠ 0 := fun h => hx0 (by
    have h1 := congrArg (M k).mulVec h
    rw [Matrix.mulVec_mulVec, ← hM, mul_inv_cancel, hM1, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
    funext a
    exact ψ.injective (by simpa [z] using congrFun h1 a))
  let τ : EmbV bkP i v hv := Bw.Kw.1.val.codRestrict Bw.LL.1.toSubalgebra (Bw.LL_split Bw.Kw.1.val)
  have hj := isJumpV_zero_of_invariant (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) _ hz0 (fun g => by
    have hg : k * (Bw.e.symm g : Gen.GE D.nd) * k⁻¹ ∈ Dec (F := D.host.E) A := by
      have h : (Bw.e.symm g : Gen.GE D.nd) • D.nd.plOm.1 v = D.nd.plOm.1 v := (Bw.e.symm g).2
      show (k * (Bw.e.symm g : Gen.GE D.nd) * k⁻¹) • A = A
      rw [← hk, mul_smul, inv_smul_smul, mul_smul, h]
    have e : repV bkP i v hv (Tgl i s) g ((M k⁻¹).mulVec z) =
        (M (Bw.e.symm g : Gen.GE D.nd)).mulVec ((M k⁻¹).mulVec z) := by
      simp only [M, ← Tgl_coe]
      rfl
    rw [e]
    conv_rhs => rw [← hz _ hg]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hM, ← hM, ← mul_assoc, ← mul_assoc,
      inv_mul_cancel, one_mul]) τ
  have := hJ v hv τ 0 hj
  omega

end GlobalTheory.InvJump

end
end

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noDecompositionInvariants_aboveL_of_noHodgeJump : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tmat i s) v := by
  atlas_forward_decl GlobalTheory.InvJump.noInv_of_noJump
end

section
section
noncomputable section

namespace GlobalTheory.TateDualInv

section Bridge

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
open ReciprocityTheory.Gal (cycZ)

variable {l : ℕ} [Fact l.Prime]

theorem isJumpV_zero_of_invariant (P : LocPrime l) (K LL : FinExt l) {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (x : V) (hx : x ≠ 0)
    (h : ∀ g, ρ g x = x) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : IsJumpV (P.PD K) ρ τ 0 := by
  have := LL.2
  refine GlobalTheory.HTW.isJumpV_of_injective (P.PD K) (Representation.trivial ↥LL.1 ↥(GK K) ↥LL.1) ρ
    (LinearMap.toSpanSingleton ↥LL.1 V x) (LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton _ hx))
    (fun g v => by simp [h]) τ 0 fun h0 => ?_
  have h1 := GlobalTheory.CrysExt.finrank_fildR_trivial (P.PD K) (LL := ↥LL.1) τ 0
  have h2 := GlobalTheory.CrysExt.finrank_fildR_trivial (P.PD K) (LL := ↥LL.1) τ (0 + 1)
  rw [h0, h1] at h2
  simp at h2

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) (P : LocPrime l)

theorem cycLL_eq (g : ↥(GK Bw.Kw)) :
    ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 g : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) =
      Bw.toLL (algebraMap ℤ_[l] O ((cycZ E Ω l (Bw.e.symm g : ↥Gw) : ℤ_[l]ˣ) : ℤ_[l])) := by
  change algebraMap ℚ_[l] ↥Bw.LL.1 (((P.PD Bw.Kw).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
  rw [P.PD_χ, ← GlobalTheory.BlockJumps.cycZ_eq_chi Bw P g]
  exact (congrArg Subtype.val (Bw.eO_alg _)).symm

theorem dot_dual {O L : Type} [CommRing O] [CommRing L] (φ : O →+* L) {m : ℕ} (A : GL (Fin m) O) (ε : O)
    (x y : Fin m → L) :
    ((A : Matrix (Fin m) (Fin m) O).map φ).mulVec x ⬝ᵥ
      ((ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ).mulVec y = φ ε * (x ⬝ᵥ y) := by
  have h1 : (ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ =
      φ ε • (((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ).transpose := by
    ext a b
    simp
  have h2 : ((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ * (A : Matrix (Fin m) (Fin m) O).map φ = 1 := by
    rw [← Matrix.map_mul, ← Matrix.coe_units_inv, Units.inv_mul, Matrix.map_one _ φ.map_zero φ.map_one]
  rw [h1, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

omit [IsAlgClosed Ω] in
theorem rep_apply {m : ℕ} (r : ↥Gw →* GL (Fin m) O) (g : ↥(GK Bw.Kw)) (x : Fin m → ↥Bw.LL.1) :
    Bw.rep r g x = (((r (Bw.e.symm g) : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x := rfl

omit [IsAlgClosed Ω] in
theorem card_emb : Nat.card (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1) = Module.finrank ℚ_[l] ↥Bw.Kw.1 := by
  have : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  rw [← AlgHom.card ℚ_[l] ↥Bw.Kw.1 (Loc.Om l), ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun τ => Bw.LL.1.val.comp τ
      invFun := fun τ => τ.codRestrict Bw.LL.1.toSubalgebra (Bw.LL_split τ)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem dot_bijective {L : Type} [Field L] (m : ℕ) :
    Function.Bijective (dotProductBilin L L : (Fin m → L) →ₗ[L] (Fin m → L) →ₗ[L] L) := by
  have hi : Function.Injective (dotProductBilin L L : (Fin m → L) →ₗ[L] (Fin m → L) →ₗ[L] L) := by
    intro x y h
    funext i
    simpa using LinearMap.congr_fun h (Pi.single i 1)
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hi⟩

theorem local_noInv (AI : LocAinf l P) (T : LocTied l P AI) {m : ℕ} (r r' : ↥Gw →* GL (Fin m) O)
    (hd : ∀ g, ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O) =
      algebraMap ℤ_[l] O ((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l]) •
        ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)⁻¹.transpose)
    (hdR : Bw.IsdRW P r) (hj : ∀ τ, ¬ IsJumpV (P.PD Bw.Kw) (Bw.rep r) τ (-1))
    (x : Fin m → ↥Bw.LL.1) (hx : ∀ g, Bw.rep r' g x = x) : x = 0 := by
  by_contra h0
  have : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  have hc := card_emb Bw
  obtain ⟨⟨τ⟩, -⟩ := Nat.card_pos_iff.1 (hc ▸ Module.finrank_pos (R := ℚ_[l]) (M := ↥Bw.Kw.1))
  have hJ := isJumpV_zero_of_invariant P Bw.Kw Bw.LL (Bw.rep r') x h0 hx τ
  have hm := (GlobalTheory.DRDual.twisted_dual_deRham l P AI T Bw.Kw Bw.LL _ (Bw.rep r) _ (Bw.rep r')
    (dotProductBilin _ _) 1 (dot_bijective m) (fun g x y => by
      rw [zpow_one, cycLL_eq, rep_apply, rep_apply, hd]
      exact dot_dual _ _ _ _ _) (by simpa [IsDR, LocBridge.IsdRW] using hdR)).2 τ (-1) hc
  have h1 : multV (P.PD Bw.Kw) (Bw.rep r) τ (-1) = 0 := by
    unfold multV
    rw [not_not.1 (hj τ), sub_self]
  rw [h1, show -(-1 : ℤ) - 1 = 0 by norm_num] at hm
  apply hJ
  have hfin := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T Bw.Kw Bw.LL _ (Bw.rep r')).1
  have hle : FildR (P.PD Bw.Kw) (Bw.rep r') τ 0 ≤ DdR (P.PD Bw.Kw) (Bw.rep r') := le_trans inf_le_left inf_le_left
  have := Submodule.finiteDimensional_of_le hle
  refine Submodule.eq_of_le_of_finrank_eq (inf_le_inf_left _ ?_) ?_
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => exact ⟨v ⊗ₜ[ℚ_[l]] ⟨b.1, (P.PD Bw.Kw).Fil_anti 0 b.2⟩, rfl⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · unfold multV at hm
    omega

end Bridge

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

section Global

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

def dualHom (i : X.Tw) (s : X.Sig i) : Gen.GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) where
  toFun := Tdual i s
  map_one' := by simp [Tdual, ← Tgl_coe]
  map_mul' g h := by
    simp only [Tdual, ← Tgl_coe, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul, smul_mul_smul_comm]

end Global

open scoped Pointwise in

theorem noInv_tateDual : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) → HodgeL bkP i s → NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tdual i s) v := by
  rintro D bkP i s ⟨AI, ⟨T⟩⟩ hH hJ v hv A hA x hx
  let φ := algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))
  let M : Gen.GE D.nd → Matrix (Fin D.R.r) (Fin D.R.r) (FractionRing (D.ntw.O0 i)) := fun g => (Tdual i s g).map φ
  have hmul : ∀ g h, M (g * h) = M g * M h := fun g h => by
    simp only [M, ← Matrix.map_mul]
    exact congrArg (fun Y => Matrix.map Y φ) ((dualHom i s).map_mul g h)
  have hone : M 1 = 1 := by
    have : Tdual i s 1 = 1 := (dualHom i s).map_one
    simp only [M, this, Matrix.map_one _ φ.map_zero φ.map_one]
  obtain ⟨k, hk⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) hA (D.nd.plOm.2 v)
  have hy : ∀ g ∈ DecV D.nd v, (M g).mulVec ((M k).mulVec x) = (M k).mulVec x := by
    intro g hg
    have h1 : k⁻¹ * g * k ∈ Dec (F := D.host.E) A := by
      have hg' : g • D.nd.plOm.1 v = D.nd.plOm.1 v := hg
      change (k⁻¹ * g * k) • A = A
      rw [mul_smul, mul_smul, hk, hg', ← hk, inv_smul_smul]
    have h2 : (M (k⁻¹ * g * k)).mulVec x = x := hx _ h1
    conv_rhs => rw [← h2]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hmul, ← hmul]
    congr 2
    group
  have : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  let Bw := bkP.br i v hv
  have hz := local_noInv Bw (D.loc (D.ntw.l i)) AI T ((Tgl i s).comp (DecV D.nd v).subtype)
    ((dualHom i s).toHomUnits.comp (DecV D.nd v).subtype)
    (fun g => by
      change Tdual i s g = _ • (((Tgl i s g : GL (Fin D.R.r) (D.ntw.O0 i)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)))⁻¹.transpose
      rw [Tgl_coe]
      rfl)
    (hH v hv _ (Set.mem_insert_of_mem _ rfl)).1
    (fun τ h => by
      have := hJ v hv τ (-1) h
      omega)
    (fun a => Br.toLLK Bw ((M k).mulVec x a)) (fun g => by
      rw [rep_apply]
      funext a
      have h3 := congrArg (Br.toLLK Bw) (congrFun (hy _ (Bw.e.symm g).2) a)
      rw [← h3, RingHom.map_mulVec]
      congr 1
      ext b c
      exact congrArg Subtype.val (Br.toLLK_alg Bw _).symm)
  have h4 : (M k).mulVec x = 0 := funext fun a => (Br.toLLK Bw).injective (by
    rw [Pi.zero_apply, map_zero]; exact congrFun hz a)
  have h5 := congrArg (M k⁻¹).mulVec h4
  rwa [Matrix.mulVec_mulVec, ← hmul, inv_mul_cancel, hone, Matrix.one_mulVec, Matrix.mulVec_zero] at h5

end GlobalTheory.TateDualInv

end
end

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noInv_tateDual_of_hodge_of_noJump : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) → HodgeL bkP i s → NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tdual i s) v := by
  atlas_forward_decl GlobalTheory.TateDualInv.noInv_tateDual
end

section
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.ScalarInvariants

theorem eq_zero_of_scalar {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (d : O) (hd : d ≠ 1)
    (x : Fin n → FractionRing O)
    (h : ((d • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O (FractionRing O))).mulVec x = x) : x = 0 := by
  have e : (d • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O (FractionRing O)) =
      algebraMap O (FractionRing O) d • (1 : Matrix (Fin n) (Fin n) (FractionRing O)) := by
    ext a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [e, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  have h1 : algebraMap O (FractionRing O) d - 1 ≠ 0 := fun h0 =>
    hd (IsFractionRing.injective O (FractionRing O) (by rw [map_one]; exact sub_eq_zero.1 h0))
  have h2 : (algebraMap O (FractionRing O) d - 1) • x = 0 := by rw [sub_smul, h, one_smul, sub_self]
  exact (smul_eq_zero.1 h2).resolve_left h1

theorem inv_unit_smul_one {O : Type} [CommRing O] {n : ℕ} (d : Oˣ) :
    ((d : O) • (1 : Matrix (Fin n) (Fin n) O))⁻¹ = ((d⁻¹ : Oˣ) : O) • (1 : Matrix (Fin n) (Fin n) O) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, Units.inv_mul, one_smul]

theorem noInv_pD : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → ∀ v ∈ D.ntw.pD i,
    NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  intro D i s h v hv
  have hlp : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  have hv' : v ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← D.ntw.pD_eq i]; exact hv
  have hp : (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    exacts [D.host.pde'_prime, D.host.pde_prime]
  have hl : v ∉ placesOver D.host.E (D.ntw.l i) := by
    refine GlobalTheory.TwSys.TameScalar.not_mem_placesOver hp hlp ?_ hv'
    split_ifs with hh
    · rw [hh]; exact D.host.pde_ne.symm
    · exact fun e => hh e.symm
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k => by
    refine GlobalTheory.TwSys.TameScalar.not_mem_placesOver hp (D.host.g_prime k) ?_ hv'
    split_ifs
    exacts [(D.host.pde_ne_g k).2, (D.host.pde_ne_g k).1]
  have key : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ z ∈ Dec (F := D.host.E) A,
      ∃ d : (D.ntw.O0 i)ˣ, d ≠ 1 ∧
        Tmat i s z = (d : D.ntw.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) ∧ eps0 D.ntw i z = 1 := by
    intro A hA
    have h15 := D.ntw.delta_15 i v hv A hA
    obtain ⟨z, hzA, hz⟩ : ∃ z ∈ Ine (F := D.host.E) A, D.ntw.delta i z ≠ 1 := by
      by_contra hc
      push Not at hc
      have hb : (Ine (F := D.host.E) A).map (D.ntw.delta i) = ⊥ :=
        (Subgroup.map_eq_bot_iff _).2 fun z hz => hc z hz
      rw [hb, Subgroup.card_bot] at h15
      exact absurd h15 (by norm_num)
    have h1 : D.ntw.rhoS i s z = 1 := h v hl hg A hA z hzA
    have h2 : chiS i s z = if D.ntw.side i s then D.ntw.delta i z else (D.ntw.delta i z)⁻¹ :=
      D.ntw.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA z hzA
    refine ⟨z, Ine_le_Dec A hzA, (chiS i s z)⁻¹, ?_, ?_, ?_⟩
    · rw [h2]
      split_ifs
      · exact inv_ne_one.2 hz
      · rw [inv_inv]; exact hz
    · rw [Tmat, h1, Units.val_one]
    · have h4 : cycZ D.host.E D.nd.Om (D.ntw.l i) z = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.1 fun n => ?_)
        rw [ReciprocityTheory.Gal.cycZ_toZModPow_eq hl hA (q := 1) (fun x hx => by simpa using hzA.2 x hx) n]
        simp
      simp [eps0, h4]
  refine ⟨fun A hA x hx => ?_, fun A hA x hx => ?_⟩
  · obtain ⟨z, hz, d, hd, hT, -⟩ := key A hA
    have e := hx z hz
    rw [hT] at e
    exact eq_zero_of_scalar _ (fun h0 => hd (Units.ext h0)) x e
  · obtain ⟨z, hz, d, hd, hT, he⟩ := key A hA
    have e := hx z hz
    rw [Tdual, hT, he, inv_unit_smul_one, Units.val_one, one_smul, Matrix.transpose_smul, Matrix.transpose_one] at e
    exact eq_zero_of_scalar _ (fun h0 => inv_ne_one.2 hd (Units.ext h0)) x e

end GlobalTheory.TripleGal.ScalarInvariants
end

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noDecompositionInvariants_auxiliaryPrime : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → ∀ v ∈ D.ntw.pD i, NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  atlas_forward_decl GlobalTheory.TripleGal.ScalarInvariants.noInv_pD
end

section
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NoJumpMult

open Module TensorProduct

section Gen
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem filV_anti (a : ℤ) : Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) (a + 1) ≤ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a := by
  have h := PD.Fil_anti a
  unfold Formalism.WeaklyAdmissibleFiltrations.FilV
  have : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil (a + 1)).restrictScalars Qp).subtype =
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype).comp
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
          (Submodule.inclusion (show (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp from h))) := by
    ext x y; rfl
  rw [this]
  exact LinearMap.range_comp_le_range _ _

theorem fildR_anti (τ : K →ₐ[Qp] LL) (a : ℤ) : Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ (a + 1) ≤ Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a :=
  inf_le_inf_left _ (filV_anti PD a)

theorem fildR_le (τ : K →ₐ[Qp] LL) (a : ℤ) : Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a ≤ Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ :=
  inf_le_left.trans inf_le_left

theorem multV_ne_zero (τ : K →ₐ[Qp] LL) (a : ℤ) (hpos : 0 < finrank LL ↥(Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ))
    (hj : Formalism.WeaklyAdmissibleFiltrations.IsJumpV PD ρ τ a) : Formalism.WeaklyAdmissibleFiltrations.multV PD ρ τ a ≠ 0 := by
  have : FiniteDimensional LL ↥(Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) := Module.finite_of_finrank_pos hpos
  have : FiniteDimensional LL ↥(Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a) := Submodule.finiteDimensional_of_le (fildR_le PD ρ τ a)
  have hlt : Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ (a + 1) < Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a := lt_of_le_of_ne (fildR_anti PD ρ τ a) hj
  have := Submodule.finrank_lt_finrank_of_lt hlt
  unfold Formalism.WeaklyAdmissibleFiltrations.multV
  omega
end Gen

end GlobalTheory.NoJumpMult

namespace GlobalTheory.NoJumpMult

theorem r_pos (D : D7) : 0 < D.R.r := by
  have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
  unfold Formalism.BasicNotions.Ranks.r; omega

theorem noJump_of_jumps : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (J : (D.host.E →+* ℂ) → Multiset ℤ), HodgeL bkP i s → JumpsAre bkP i s ι J → GoodJ D J → NoJump bkP i s := by
  intro D bkP i s ι J hH hJ hG v hv τ a ha
  obtain ⟨τc, hτc, -⟩ := GlobalTheory.ReadEmbEx.exists_readEmb D bkP i ι v hv τ
  have hdR := (hH v hv (Tgl i s) (Set.mem_insert_of_mem _ rfl)).1
  have hK : 0 < Module.finrank ℚ_[D.ntw.l i] ↥(bkP.br i v hv).Kw.1 := by
    have := (bkP.br i v hv).Kw.2
    exact Module.finrank_pos
  have hpos : 0 < Module.finrank ↥(bkP.br i v hv).LL.1
      ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (PDv bkP i v hv) (repV bkP i v hv (Tgl i s))) := by
    have : Module.finrank ↥(bkP.br i v hv).LL.1
      ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (PDv bkP i v hv) (repV bkP i v hv (Tgl i s))) =
        Module.finrank ℚ_[D.ntw.l i] ↥(bkP.br i v hv).Kw.1 * D.R.r := hdR
    rw [this]; exact Nat.mul_pos hK (r_pos D)
  have hm := multV_ne_zero _ _ τ a hpos ha
  rw [hJ v hv τ τc hτc a] at hm
  have hmem : a ∈ J τc := by
    by_contra hn
    exact hm (by simp [Multiset.count_eq_zero.mpr hn])
  exact (hG τc).2.2 a hmem

end GlobalTheory.NoJumpMult
end

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noHodgeJump_of_goodJumpMultiset : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (J : (D.host.E →+* ℂ) → Multiset ℤ), HodgeL bkP i s → JumpsAre bkP i s ι J → GoodJ D J → NoJump bkP i s := by
  atlas_forward_decl GlobalTheory.NoJumpMult.noJump_of_jumps
end

section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noInv_away_of_pure : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (ι : FractionRing (D.ntw.O0 i) →+* ℂ), Pure i s ι → ∀ v, v ∉ placesOver D.host.E (D.ntw.l i) → v ∉ Spl (X := D.ntw) i → NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  first | exact @GlobalTheory.PurityInvariants.noInv_of_pure | exact GlobalTheory.PurityInvariants.noInv_of_pure | (intros; apply GlobalTheory.PurityInvariants.noInv_of_pure <;> assumption)
end

section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem noInv_all_places (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i)
    (hT : ∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) (h2 : ValuationStabilityAtRing D.ntw i s)
    (hA : TripleAtt D.naut bkP i s) (hJ : NoJump bkP i s) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  by_cases hl : v ∈ placesOver D.host.E (D.ntw.l i)
  · exact ⟨GlobalTheory.T.noDecompositionInvariants_aboveL_of_noHodgeJump D bkP i s hJ v hl, GlobalTheory.T.noInv_tateDual_of_hodge_of_noJump D bkP i s hT (GlobalTheory.T.hodge_of_attached D bkP i s hA) hJ v hl⟩
  by_cases hS : v ∈ Spl (X := D.ntw) i
  · rcases hS.1 with hg | hp
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hg
      exact GlobalTheory.T.noInv_at_type_primes D i s h2 k (fun e => hl (e ▸ hk)) v hk
    · exact GlobalTheory.T.noDecompositionInvariants_auxiliaryPrime D i s (GlobalTheory.T.unramified_of_attached D bkP i s hA) v (Finset.mem_coe.1 hp)
  · obtain ⟨ι, hι⟩ := GlobalTheory.T.pure_of_attached D bkP i s hA
    exact GlobalTheory.T.noInv_away_of_pure D i s ι hι v hl hS

theorem galois_hypotheses_of_attached : ∀ (D : D7) (bkP : BlochKatoReduction.BK D), GlobalTheory.TypeLeaf.FrobDense D → (∀ i, D.ntw.NonzeroIndexPlace i → (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI))) → BlochKatoReduction.adm2 D → (∀ i, D.ntw.NonzeroIndexPlace i → ∀ s, TripleAtt D.naut bkP i s) → BlochKatoReduction.adm1 bkP ∧ BlochKatoReduction.adm8 D ∧ ∀ i, D.ntw.NonzeroIndexPlace i → True ∧ ∀ s : D.ntw.Sig i, SelfDual i s ∧ NoJump bkP i s := by
  intro D bkP hF hT h2 hA
  have hJ : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ s, NoJump bkP i s := fun i hi s => by
    obtain ⟨ι, J, h, h'⟩ := GlobalTheory.T.jumps_good_of_attached D bkP i s (hA i hi s)
    exact GlobalTheory.T.noHodgeJump_of_goodJumpMultiset D bkP i s ι J (GlobalTheory.T.hodge_of_attached D bkP i s (hA i hi s)) h h'
  refine ⟨fun i hi s => ?_, fun i hi s => ?_, fun i hi => ⟨trivial, fun s => ⟨?_, hJ i hi s⟩⟩⟩
  · obtain ⟨ι, J, h, h'⟩ := GlobalTheory.T.jumps_good_of_attached D bkP i s (hA i hi s)
    exact GlobalTheory.T.isotypicValuationAtRing_of_unrRho_hodgeL_noInv_negCount D bkP i s (GlobalTheory.T.unramified_of_attached D bkP i s (hA i hi s)) (GlobalTheory.T.hodge_of_attached D bkP i s (hA i hi s))
      (noInv_all_places D bkP i s (hT i hi) (h2 i hi s) (hA i hi s) (hJ i hi s))
      (GlobalTheory.T.conjugateNegativeJumpCount_of_goodHodgeJumps D bkP i s ι J (GlobalTheory.T.hodge_of_attached D bkP i s (hA i hi s)) h h')
  · exact GlobalTheory.T.characterTwistExists_of_unrRho_of_hkFrob D i s (GlobalTheory.T.unramified_of_attached D bkP i s (hA i hi s)) (GlobalTheory.T.hkFrob_of_attached D bkP i s (hA i hi s))
  · exact GlobalTheory.T.selfDual_lattice_of_conjDualCharpoly D i s (h2 i hi s) (GlobalTheory.T.conjDualCharpoly_of_splitFrobenius_dense D hF i s (GlobalTheory.T.frobDual_of_attached D bkP i s (hA i hi s)))

end GlobalTheory.TripleGal
end
