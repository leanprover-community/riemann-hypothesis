import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLtOneIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceNondegenerateOfIsSSRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntSubMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeneralAdmissibleOfIrreducibilityStmt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHypothesesOfAttached
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCSDOfIsEtaT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyTrivialEverywhere

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicHodgeProperties_conj_invariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r r' : ↥Gw →* GL (Fin a) (Om l)) (A : GL (Fin a) (Om l)), (∀ g, r' g = A * r g * A⁻¹) → (IsdRAt P Bw r → IsdRAt P Bw r') ∧ (IsCrysAt P Bw r → IsCrysAt P Bw r') ∧ (IsPotCrysAt P Bw r → IsPotCrysAt P Bw r') ∧ ∀ (τ : E →+* Om l) (J : Multiset ℤ), IsJumpsAt P Bw r τ J → IsJumpsAt P Bw r' τ J := by
  first | exact @GlobalTheory.ConjLocal.local_conj | exact GlobalTheory.ConjLocal.local_conj | (intros; apply GlobalTheory.ConjLocal.local_conj <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf

noncomputable section

namespace GlobalTheory.TripleLocal

open GlobalTheory.RowTie (WDTie)

theorem frobConj_natCast_notMem (E : Type) [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime] :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  have h0 : (Ideal.span {((l : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hl.out.ne_zero
  rw [Filter.eventually_cofinite]
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simpa [Ideal.dvd_span_singleton] using hw

theorem conj_of_frobMatch : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), FrobDense D → ∀ (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : D.naut.CG a) (s : ℝ) (r r' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)),
    IsAttachedAway D T ι π s r → Continuous (fun g => (r' g : Matrix (Fin a) (Fin a) (Qbar l))) → IsSSRep r' →
    FrobMatch D π ι.toRingHom r' (s + (1 - (a : ℝ)) / 2) → ∃ A : GL (Fin a) (Qbar l), ∀ g, r' g = A * r g * A⁻¹ := by
  intro D T hD l _ ι a π s r r' h hc' hss' hm
  have hall := (hm.and (D.naut.locG_unr_ae π)).and (frobConj_natCast_notMem D.host.E l)
  have htr : ∀ g, ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace =
      ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
    intro g
    refine congrFun (Continuous.ext_on (hD _ (Filter.eventually_cofinite.1 hall))
      (h.cont.matrix_trace) (hc'.matrix_trace) ?_) g
    rintro σ ⟨w, hw, -, B, hB, hσ⟩
    obtain ⟨⟨h1, hu⟩, hl⟩ := not_not.1 hw
    have e1 := (h.frob hl hu).2 B σ hB hσ
    have e2 := h1 B σ hB hσ
    have e : ((r σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
        ((r' σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly :=
      Polynomial.map_injective ι.toRingHom ι.injective (e1.trans e2.symm)
    show Matrix.trace _ = Matrix.trace _
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      simp [Matrix.trace]
    · haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
      rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, e]
  exact GlobalTheory.TraceConj.conj_of_trace_eq _ _ a r r' h.ss hss' htr

end GlobalTheory.TripleLocal

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_of_frobenius_match : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), FrobDense D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : D.naut.CG a) (s : ℝ) (r r' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), IsAttachedAway D T ι π s r → Continuous (fun g => (r' g : Matrix (Fin a) (Fin a) (Qbar l))) → IsSSRep r' → FrobMatch D π ι.toRingHom r' (s + (1 - (a : ℝ)) / 2) → ∃ A : GL (Fin a) (Qbar l), ∀ g, r' g = A * r g * A⁻¹ := by
  first | exact @GlobalTheory.TripleLocal.conj_of_frobMatch | exact GlobalTheory.TripleLocal.conj_of_frobMatch | (intros; apply GlobalTheory.TripleLocal.conj_of_frobMatch <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleGal
open GlobalTheory.TypeLeaf (FrobDense)

theorem exists_aut {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O]
    (φ ψ : O →+* Qbar l) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hφ' : ∀ z : ℤ_[l], φ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (hψ' : ∀ z : ℤ_[l], ψ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ γ : Qbar l ≃+* Qbar l, ∀ x, γ (φ x) = ψ x := by
  have halg : Algebra.IsAlgebraic ℤ_[l] (Qbar l) :=
    haveI := IsLocalization.isAlgebraic (R := ℤ_[l]) ℚ_[l] (nonZeroDivisors ℤ_[l])
    Algebra.IsAlgebraic.trans ℤ_[l] ℚ_[l] (Qbar l)
  have key : ∀ (f : O →+* Qbar l) (hf : Function.Injective f),
      (∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) →
      letI := f.toAlgebra
      haveI : Module.IsTorsionFree O (Qbar l) := Module.isTorsionFree_iff_algebraMap_injective.2 hf
      IsAlgClosure O (Qbar l) := fun f hf hf' => by
    letI := f.toAlgebra
    haveI : Module.IsTorsionFree O (Qbar l) := Module.isTorsionFree_iff_algebraMap_injective.2 hf
    haveI : IsScalarTower ℤ_[l] O (Qbar l) := IsScalarTower.of_algebraMap_eq fun z => (hf' z).symm
    have hi : Function.Injective (algebraMap ℤ_[l] O) := fun x y h => by
      have := (hf' x).symm.trans ((congrArg f h).trans (hf' y))
      exact Subtype.ext ((algebraMap ℚ_[l] (Qbar l)).injective this)
    exact ⟨inferInstance, Algebra.IsAlgebraic.extendScalars hi⟩
  let e := @IsAlgClosure.equiv O _ _ (Qbar l) (Qbar l) _ _ ψ.toAlgebra
    (@Module.isTorsionFree_iff_algebraMap_injective _ _ _ _ ψ.toAlgebra _ _ |>.2 hψ) (key ψ hψ hψ') φ.toAlgebra
    (@Module.isTorsionFree_iff_algebraMap_injective _ _ _ _ φ.toAlgebra _ _ |>.2 hφ) (key φ hφ hφ')
  exact ⟨@AlgEquiv.toRingEquiv O _ _ _ _ _ φ.toAlgebra ψ.toAlgebra e,
    fun x => @AlgEquiv.commutes O _ _ _ _ _ φ.toAlgebra ψ.toAlgebra e x⟩

variable {D : D7} {T : WDTie D.nd D.naut} {i : D.ntw.Tw} {j : FractionRing (D.ntw.O0 i) →+* ℂ}
  {ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.ntw.O0 i)} {π : D.naut.CG D.R.r} {s : ℝ}

theorem exists_conj (hF : FrobDense D) (hG : GalHodge D T) (hc : D.naut.csd π) (hr : RegAlgShift D.naut π s)
    (hρ : Continuous fun g => (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)))
    (hM : FrobMatch D π (rd i j) ρ (s + (1 - (D.R.r : ℝ)) / 2))
    {φ : D.ntw.O0 i →+* Qbar (D.ntw.l i)} {ι : Qbar (D.ntw.l i) ≃+* ℂ} (hφ : Continuous φ)
    (hι : ∀ x, ι (φ x) = rd i j x) (hs : IsSSRep (mapRep φ ρ)) :
    ∃ r A, IsAttachedHodge D T ι π s r ∧ ∀ g, mapRep φ ρ g = A * r g * A⁻¹ := by
  obtain ⟨r, h⟩ := hG _ ι π s hc hr
  have e : ι.toRingHom.comp φ = rd i j := RingHom.ext hι
  obtain ⟨A, hA⟩ := GlobalTheory.T.conj_of_frobenius_match D T hF _ ι _ π s r (mapRep φ ρ) h.toIsAttachedAway (hρ.matrix_map hφ) hs
    (hM.mono fun w hw B σ hB hσ => by
      rw [← hw B σ hB hσ, ← e, ← Polynomial.map_map, ← Matrix.charpoly_map _ φ]
      rfl)
  exact ⟨r, A, h, hA⟩

def brEmb (i : D.ntw.Tw) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) : D.ntw.O0 i →+* Qbar (D.ntw.l i) :=
  (algebraMap ↥(D.ntwbr i v hv).LL.1 (Om (D.ntw.l i))).comp (D.ntwbr i v hv).toLL

theorem isModel_brEmb (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) :
    IsModel (D.ntwbr i v hv) (resDec D.nd.plOm.1 (mapRep (brEmb i v hv) ρ) v) (D.ntwbr i v hv).LL
      (mapRep (D.ntwbr i v hv).toLL (ρ.comp (DecV D.nd v).subtype)) :=
  ⟨le_rfl, by ext g a b; rfl⟩

theorem exists_conj_br (hF : FrobDense D) (hG : GalHodge D T) (hc : D.naut.csd π) (hr : RegAlgShift D.naut π s)
    (hρ : Continuous fun g => (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)))
    (hM : FrobMatch D π (rd i j) ρ (s + (1 - (D.R.r : ℝ)) / 2))
    {φ : D.ntw.O0 i →+* Qbar (D.ntw.l i)} {ι : Qbar (D.ntw.l i) ≃+* ℂ}
    (hφ : ∀ z : ℤ_[D.ntw.l i], φ (algebraMap _ _ z) = algebraMap ℚ_[D.ntw.l i] _ (z : ℚ_[D.ntw.l i]))
    (hι : ∀ x, ι (φ x) = rd i j x) (hs : IsSSRep (mapRep φ ρ))
    (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) :
    ∃ (ι' : Qbar (D.ntw.l i) ≃+* ℂ) (r : _) (A : GL (Fin D.R.r) (Qbar (D.ntw.l i))),
      (∀ x, ι' (brEmb i v hv x) = rd i j x) ∧ IsAttachedHodge D T ι' π s r ∧
      ∀ g, resDec D.nd.plOm.1 (mapRep (brEmb i v hv) ρ) v g = A * resDec D.nd.plOm.1 r v g * A⁻¹ := by
  have hj : Function.Injective (rd i j) := j.injective.comp (IsFractionRing.injective _ _)
  have h1 : Function.Injective φ := fun x y h => hj (by rw [← hι, ← hι, h])
  have h2 : Function.Injective (brEmb i v hv) :=
    (algebraMap ↥(D.ntwbr i v hv).LL.1 (Om (D.ntw.l i))).injective.comp (GlobalTheory.EmbInj.toLL_inj _)
  obtain ⟨γ, hγ⟩ := exists_aut φ (brEmb i v hv) h1 h2 hφ fun z =>
    congrArg (fun y : ↥(OL (D.ntwbr i v hv).LL) => ((y : ↥(D.ntwbr i v hv).LL.1) : Om (D.ntw.l i)))
      ((D.ntwbr i v hv).eO_alg z)
  have h3 : ∀ x, (γ.symm.trans ι) (brEmb i v hv x) = rd i j x := fun x => by
    rw [← hγ, RingEquiv.trans_apply, γ.symm_apply_apply, hι]
  have h4 : mapRep (brEmb i v hv) ρ = mapRep γ.toRingHom (mapRep φ ρ) := by
    ext g a b
    exact (hγ _).symm
  obtain ⟨r, A, h, hA⟩ := exists_conj hF hG hc hr hρ hM (φ := brEmb i v hv)
    (continuous_subtype_val.comp (continuous_subtype_val.comp (D.ntwbr i v hv).eO_cont)) h3
    (h4 ▸ GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ _ _ _ hs)
  exact ⟨_, r, A, h3, h, fun g => hA g⟩

theorem att_of_frobMatch (hF : FrobDense D) (hG : GalHodge D T) (hc : D.naut.csd π) (hr : RegAlgShift D.naut π s)
    (hρ : Continuous fun g => (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)))
    (hM : FrobMatch D π (rd i j) ρ (s + (1 - (D.R.r : ℝ)) / 2))
    {φ : D.ntw.O0 i →+* Qbar (D.ntw.l i)} {ι : Qbar (D.ntw.l i) ≃+* ℂ} (hφc : Continuous φ)
    (hφ : ∀ z : ℤ_[D.ntw.l i], φ (algebraMap _ _ z) = algebraMap ℚ_[D.ntw.l i] _ (z : ℚ_[D.ntw.l i]))
    (hι : ∀ x, ι (φ x) = rd i j x) (hs : IsSSRep (mapRep φ ρ)) :
    Att D.naut (bk0 D) i j ρ π (s + (1 - (D.R.r : ℝ)) / 2) := by
  have hj : Function.Injective (rd i j) := j.injective.comp (IsFractionRing.injective _ _)
  have h1 : Function.Injective φ := fun x y h => hj (by rw [← hι, ← hι, h])
  obtain ⟨r, A, h, hA⟩ := exists_conj hF hG hc hr hρ hM hφc hι hs
  refine ⟨fun w hw hu σ hσ => ?_, fun w hw hu B σ hB hσ => ?_, fun w hw => h.temp w hw, fun v hv => ?_,
    fun v hv τ τc hτ a => ?_⟩
  · have h2 := hA σ
    rw [(h.toIsAttachedAway.frob hw hu).1 σ hσ, mul_one, mul_inv_cancel] at h2
    refine Units.ext (Matrix.map_injective h1 ?_)
    exact (congrArg Units.val h2).trans (Matrix.map_one φ (map_zero φ) (map_one φ)).symm
  · rw [← (h.toIsAttachedAway.frob hw hu).2 B σ hB hσ, ← (RingHom.ext hι : ι.toRingHom.comp φ = rd i j),
      ← Polynomial.map_map, ← Matrix.charpoly_map _ φ]
    have h2 : ((mapRep φ ρ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i))).charpoly =
        ((r σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i))).charpoly := by
      rw [hA, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact congrArg (Polynomial.map ι.toRingHom) h2
  · obtain ⟨ι', r', A', -, h', hA'⟩ := exists_conj_br hF hG hc hr hρ hM hφ hι hs v hv
    obtain ⟨a1, a2, a3⟩ := h'.above v hv _ (D.ntwbr i v hv) (D.ntwbr_ind i v hv)
    obtain ⟨b1, b2, b3, -⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant _ (D.loc _) _ _ _ _ (D.ntwbr i v hv) _ _ _ A' hA'
    exact ⟨((isModel_brEmb v hv).isdRAt_iff _).1 (b1 a1.deRham),
      fun hu => ((isModel_brEmb v hv).isCrysAt_iff _).1 (b2 (a2 hu)),
      fun hu => ((isModel_brEmb v hv).isPotCrysAt_iff _).1 (b3 (a3 hu))⟩
  · obtain ⟨ι', r', A', hι', h', hA'⟩ := exists_conj_br hF hG hc hr hρ hM hφ hι hs v hv
    obtain ⟨a1, -, -⟩ := h'.above v hv _ (D.ntwbr i v hv) (D.ntwbr_ind i v hv)
    obtain ⟨-, -, -, b4⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant _ (D.loc _) _ _ _ _ (D.ntwbr i v hv) _ _ _ A' hA'
    let c : D.host.E →+* ↥(D.ntwbr i v hv).Kw.1 :=
      ((D.ntwbr i v hv).j.comp (algebraMap D.host.E D.nd.Om)).codRestrict (D.ntwbr i v hv).Kw.1 (D.ntwbr i v hv).j_E
    let τ₀ : D.host.E →+* Qbar (D.ntw.l i) :=
      (algebraMap ↥(D.ntwbr i v hv).LL.1 (Om (D.ntw.l i))).comp ((AlgHom.toRingHom τ).comp c)
    have hi : IsInduced (D.ntwbr i v hv) τ₀ τ := fun _ => rfl
    have e : ι'.toRingHom.comp τ₀ = τc := by
      ext x
      obtain ⟨n, d, hd, hnd⟩ := GlobalTheory.EmbInj.exists_frac (D.ntwbr i v hv) (τ (c x))
      have h3 := (map_mul (ι'.toRingHom.comp (algebraMap ↥(D.ntwbr i v hv).LL.1 (Om (D.ntw.l i)))) _ _).symm.trans
        (congrArg _ hnd)
      have h4 : rd i j d * ι' (τ₀ x) = rd i j n := by rw [← hι', ← hι']; exact h3
      exact mul_left_cancel₀ ((map_ne_zero_iff _ hj).2 hd) (h4.trans (hτ x n d ⟨hd, hnd⟩).symm)
    obtain ⟨J, hJ, hJ'⟩ := a1.jumps τ₀ _ τ hi
    refine ((b4 τ₀ J hJ').count_eq _ (isModel_brEmb v hv) hi a).symm.trans ?_
    rw [e] at hJ
    rw [← Multiset.count_map_eq_count' (fun n : ℤ => (n : ℂ)) J Int.cast_injective, hJ]
    congr 2
    refine Multiset.map_congr rfl fun z _ => ?_
    push_cast
    ring

end GlobalTheory.TripleLocal

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monodromy_trivial_everywhere : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), FrobDense D → GalHodge D T → ∀ (σ : D.what₂.FT) (π : D.naut.CG D.R.r), D.nd.goodRow σ → D.naut.csd π → D.naut.ralg π → (∀ w, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → D.naut.unr (D.naut.locG π w)) → (∀ k v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v))) → ∀ w, D.naut.mono0 (D.naut.locG π w) := by
  first | exact @GlobalTheory.GoodRowMono.mono0_all | exact GlobalTheory.GoodRowMono.mono0_all | (intros; apply GlobalTheory.GoodRowMono.mono0_all <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)

theorem b_mono {R : Ranks} (P : HCParam R) : Monotone P.b := by
  obtain ⟨n, hn⟩ : ∃ n, R.m = n + 1 := ⟨R.m - 1, by have := R.two_le_m; omega⟩
  have ht : (0 : ℚ) ≤ R.t := by positivity
  intro a c hac
  induction' hc : c.1 - a.1 with d ih generalizing c
  · rw [show a = c from Fin.ext (by have : a.1 ≤ c.1 := hac; omega)]
  · let c' : Fin R.m := ⟨c.1 - 1, by omega⟩
    have h1 := ih (c := c') (show a.1 ≤ c.1 - 1 by omega) (show c.1 - 1 - a.1 = d by omega)
    have h2 := P.gap_be c'
    have h3 := P.gap_eb c' (show c.1 - 1 + 1 < R.m by omega)
    rw [show (⟨c'.1 + 1, _⟩ : Fin R.m) = c from Fin.ext (show c.1 - 1 + 1 = c.1 by omega)] at h3
    linarith

theorem u_last_le {R : Ranks} (P : HCParam R) (h : 0 < R.k) (a : Fin R.k) : P.u ⟨R.k - 1, by omega⟩ ≤ P.u a := by
  induction' hd : R.k - 1 - a.1 with d ih generalizing a
  · rw [show a = ⟨R.k - 1, by omega⟩ from Fin.ext (by have := a.2; simp only; omega)]
  · have h1 := ih ⟨a.1 + 1, by omega⟩ (show R.k - 1 - (a.1 + 1) = d by omega)
    have h2 := P.u_gt_v ⟨a.1, by omega⟩
    have h3 := P.v_gt_u ⟨a.1, by omega⟩
    exact h1.trans (h3.trans h2).le

theorem gap_rowPar {R : Ranks} (P : HCParam R) (j : Fin R.m) {y : ℚ} (hy : y ∈ rowPar P) :
    ((R.t : ℚ) + 3) / 2 ≤ y + P.e j ∨ y + P.e j ≤ -(((R.t : ℚ) + 3) / 2) := by
  have hk := R.m_add_three_le_k
  have h0 := P.gap_be j
  rcases Multiset.mem_add.1 hy with h | h
  · obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 h
    have h1 := P.v_gt_u a
    have h2 := u_last_le P (by omega) ⟨a.1 + 1, by omega⟩
    have h3 := P.u_last_gt (by omega) j.pos
    have h4 := b_mono P (show (⟨0, j.pos⟩ : Fin R.m) ≤ j from Nat.zero_le _)
    left
    linarith
  · obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 h
    rcases le_or_gt a j with h1 | h1
    · have := b_mono P h1
      left
      linarith
    · have h2 := P.gap_eb j (by have : j.1 < a.1 := h1; omega)
      have h3 := b_mono P (show (⟨j.1 + 1, by have : j.1 < a.1 := h1; omega⟩ : Fin R.m) ≤ a from h1)
      right
      linarith

section Twist

variable {D : D7} {C₀ : CharFrame D} (S : CharSide D C₀) {n : ℕ} (π : D.naut.CG n) {ξ : HChar D.host.E} (hξ : ξ.IsUnitary)

def twBy : D.naut.CG n := D.naut.tw π (S.e1.symm ⟨ξ, hξ⟩)

theorem rankOneCuspidal_unitaryChar_equiv_apply_symm : (S.e1 (S.e1.symm ⟨ξ, hξ⟩)).1 = ξ := by rw [S.e1.apply_symm_apply]

variable {π}

theorem twBy_unr {w : PlE D.host} (h : D.naut.unr (D.naut.locG π w)) (h' : ξ.UnrAt w) :
    D.naut.unr (D.naut.locG (twBy S π hξ) w) ∧ D.naut.frobEig (D.naut.locG (twBy S π hξ) w) =
      (D.naut.frobEig (D.naut.locG π w)).map (· * ((ξ.val w : ℂˣ) : ℂ)⁻¹) := by
  have h1 : (S.e1 (S.e1.symm ⟨ξ, hξ⟩)).1.UnrAt w := by rwa [rankOneCuspidal_unitaryChar_equiv_apply_symm]
  have h2 := (S.unr_iff _ w).2 h1
  have h3 := S.frob _ w h1
  rw [rankOneCuspidal_unitaryChar_equiv_apply_symm, Units.val_inv_eq_inv_val] at h3
  rw [twBy, D.naut.locG_tw]
  exact ⟨D.naut.unr_char _ _ (D.naut.locG_dim _ _) h h2, D.naut.frobEig_char _ _ _ h h2 (D.naut.locG_dim _ _) h3⟩

theorem twBy_mono {w : PlE D.host} (h : D.naut.mono0 (D.naut.locG π w)) : D.naut.mono0 (D.naut.locG (twBy S π hξ) w) := by
  rw [twBy, D.naut.locG_tw, D.naut.monomial_char_iff _ _ (D.naut.locG_dim _ _)]
  exact h

theorem twBy_csd (h : D.naut.csd π) (h' : IsCSD D.host ξ) : D.naut.csd (twBy S π hξ) :=
  D.naut.csd_tw _ _ ((S.csd _).2 (by rwa [rankOneCuspidal_unitaryChar_equiv_apply_symm])) h

theorem twBy_inf {a : D.R.Psi → ℚ} (h : ξ.HasInfQ (embPsi D.host) a) (τ : D.what₂.Tau) :
    D.naut.infG (twBy S π hξ) (embOver D τ false) =
      (D.naut.infG π (embOver D τ false)).map (· + (a (D.eTau τ) : ℂ)) ∧
    D.naut.infG (twBy S π hξ) (embOver D τ true) =
      (D.naut.infG π (embOver D τ true)).map (· + -(a (D.eTau τ) : ℂ)) := by
  obtain ⟨h1, h2⟩ := S.infG (S.e1.symm ⟨ξ, hξ⟩) a (by rwa [rankOneCuspidal_unitaryChar_equiv_apply_symm]) (D.eTau τ)
  refine ⟨D.naut.infG_tw _ _ _ _ h1, D.naut.infG_tw _ _ _ _ ?_⟩
  rw [← h2]
  exact congrArg _ (RingHom.ext (embOver_true_apply D τ))

theorem twBy_regAlg (hr : D.naut.ralg π) {a : D.R.Psi → ℚ} (h : ξ.HasInfQ (embPsi D.host) a) {s : ℝ}
    (hs : ∀ g, (∃ m : ℤ, (a g : ℂ) + s = m) ∧ ∃ m : ℤ, -(a g : ℂ) + s = m) : RegAlgShift D.naut (twBy S π hξ) s := by
  intro φ
  obtain ⟨h1, h2⟩ := (D.naut.ralg_def π).1 hr φ
  obtain ⟨c, m, hc, hm⟩ : ∃ (c : ℂ) (m : ℤ),
      D.naut.infG (twBy S π hξ) φ = (D.naut.infG π φ).map (· + c) ∧ c + s = m := by
    obtain ⟨τ, b, rfl⟩ := exists_embOver D φ
    obtain ⟨⟨m, hm⟩, m', hm'⟩ := hs (D.eTau τ)
    cases b
    exacts [⟨_, m, (twBy_inf S hξ h τ).1, hm⟩, ⟨_, m', (twBy_inf S hξ h τ).2, hm'⟩]
  rw [hc]
  refine ⟨h1.map (add_left_injective c), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := h2 y hy
  exact ⟨k + m, by push_cast; rw [← hm]; ring⟩

end Twist

section Chars

variable {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m)

theorem isDelta_delAt : IsDelta (H := D.host) (if l = D.host.pde then D.host.pde' else D.host.pde) (C.delAt l) := by
  unfold CharFrame.delAt
  split_ifs
  exacts [C.isDel', C.isDel]

theorem mu_unitary : (muBase C l j)⁻¹.IsUnitary := ((C.isMu0 j).unitary.mul (isDelta_delAt C l).unitary).inv

theorem isCSD_inv {χ : HChar D.host.E} (h : IsCSD D.host χ) : IsCSD D.host χ⁻¹ :=
  ⟨fun w w' hw k => congrArg (·⁻¹) (h.1 w w' hw k), fun k => congrArg (·⁻¹) (h.2 k)⟩

theorem isCSD_mul {χ χ' : HChar D.host.E} (h : IsCSD D.host χ) (h' : IsCSD D.host χ') : IsCSD D.host (χ * χ') :=
  ⟨fun w w' hw k => (congrArg₂ (· * ·) (h.1 w w' hw k) (h'.1 w w' hw k)).trans (mul_inv _ _).symm,
    fun k => (congrArg₂ (· * ·) (h.2 k) (h'.2 k)).trans (mul_inv _ _).symm⟩

theorem mu_csd : IsCSD D.host (muBase C l j)⁻¹ :=
  isCSD_inv (isCSD_mul (GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ (C.isMu0 j).triv) (GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ (isDelta_delAt C l).triv))

theorem mu_inf : (muBase C l j)⁻¹.HasInfQ (embPsi D.host) (eExp D j) := by
  have h1 : ∀ k, (C.delAt l).inf k = 1 := fun k => Units.ext <| by
    have := GlobalTheory.GalChar.del_alg (hframe C) l k fun φ => by
      have h2 := congrArg φ (GlobalTheory.JumpDictionaryFoundation.sqrt_sq D.host)
      have h3 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
      rw [map_pow, map_neg, map_natCast] at h2
      nlinarith [sq_nonneg (φ D.host.sqrtMinusD)]
    exact this.trans (by simp)
  have h2 := GlobalTheory.HalfIntChars.hasInfQ_inv ((C.isMu0 j).inf.mul_triv h1)
  rwa [show (-fun τ => -eExp D j τ) = eExp D j from funext fun _ => neg_neg _] at h2

theorem eta_inf : C.eta⁻¹.HasInfQ (embPsi D.host) (fun _ => -(1 / 2)) :=
  GlobalTheory.HalfIntChars.hasInfQ_inv (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, C.isEta.inf⟩

theorem mu_unr {i : D.ntw.Tw} {w : PlE D.host} (hg : ∀ k, w ∉ placesOver D.host.E (D.host.g k)) (hp : w ∉ D.ntw.pD i) :
    (muBase C (D.ntw.l i) j).UnrAt w :=
  ((C.isMu0 j).unr w hg).mul ((isDelta_delAt C _).unr w fun h => hp (by
    rw [← Finset.mem_coe, D.ntw.pD_eq]; exact h))

end Chars

theorem isSSRep_of_smul {Γ K : Type} [Group Γ] [Field K] {n : ℕ} {ρ ρ' : Γ →* GL (Fin n) K} (c : Γ → K) (hc : ∀ g, c g ≠ 0)
    (h : ∀ g, (ρ' g : Matrix (Fin n) (Fin n) K) = c g • (ρ g : Matrix (Fin n) (Fin n) K)) (hs : IsSSRep ρ) : IsSSRep ρ' := by
  have key : ∀ W, IsInv ρ' W ↔ IsInv ρ W := fun W => forall_congr' fun g => forall₂_congr fun v _ => by
    rw [h, Matrix.smul_mulVec, W.smul_mem_iff (hc g)]
  exact fun W hW => (hs W ((key W).1 hW)).imp fun W' h' => ⟨(key W').2 h'.1, h'.2⟩

section Triple

variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}

theorem cpow_add_real (P : PlE D.host) (a b : ℝ) : ((normV P : ℕ) : ℂ) ^ ((a + b : ℝ) : ℂ) =
    ((normV P : ℕ) : ℂ) ^ (a : ℂ) * ((normV P : ℕ) : ℂ) ^ (b : ℂ) := by
  rw [Complex.ofReal_add, Complex.cpow_add _ _ (normV_ne_zero P)]

theorem cpow_ne_zero' (P : PlE D.host) (a : ℂ) : ((normV P : ℕ) : ℂ) ^ a ≠ 0 := by
  simp [normV_ne_zero P]

theorem frobMatch_rho (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) (h : IsTripleWith C art ρ s σ π r ν w red) :
    FrobMatch D (twBy S π C.isEta.unitary.inv) (rd i (ρ.ι.toRingHom.comp ρ.κ)) (D.ntw.rhoS i s)
      (-((D.R.t : ℝ) / 2) + (1 - (D.R.r : ℝ)) / 2) := by
  filter_upwards [(D.ntw.S0 i).finite_toSet.compl_mem_cofinite] with P hP B g hB hg
  obtain ⟨h1, h2⟩ := twBy_unr S C.isEta.unitary.inv (h.unr_of_notMem hP) (C.isEta.unr P).inv
  refine (h.charpoly_frob ha (fun hl => hP (D.ntw.twistExcludedPlaces_contains_residueChar i hl)) (fun k hk => hP (D.ntw.placesOver_subset_exceptional i k hk)) hB hg).trans ?_
  rw [D.naut.frobEig_tw _ _ h1, h2, Multiset.map_map, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply]
  rw [shiftChar_val, cpow_add_real, Complex.ofReal_neg, Complex.cpow_neg, HChar.val_inv, Units.val_inv_eq_inv_val]
  congr 2
  rw [mul_inv]
  ring

theorem frobMatch_T (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) (hχ : IsChars C art ρ) (h : IsTripleWith C art ρ s σ π r ν w red) :
    FrobMatch D (twBy S π (mu_unitary C (D.ntw.l i) (jIdx s))) (rd i (ρ.ι.toRingHom.comp ρ.κ)) (Tgl i s)
      (((D.R.r : ℝ) / 2 + -((D.R.t : ℝ) / 2)) + (1 - (D.R.r : ℝ)) / 2) := by
  filter_upwards [(D.ntw.S0 i).finite_toSet.compl_mem_cofinite] with P hP B g hB hg
  have hl : P ∉ placesOver D.host.E (D.ntw.l i) := fun hl => hP (D.ntw.twistExcludedPlaces_contains_residueChar i hl)
  have hk : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k hk => hP (D.ntw.placesOver_subset_exceptional i k hk)
  have hμ := mu_unr C (jIdx s) hk fun hp => hP (D.ntw.primes_subset_exceptional i hp)
  obtain ⟨h1, h2⟩ := twBy_unr S (mu_unitary C (D.ntw.l i) (jIdx s)) (h.unr_of_notMem hP) hμ.inv
  obtain ⟨n, hn⟩ := hχ.chiS
  have h3 := hn.frob ha (Or.inl hl) (fun x hx => by
    rw [blockChar, GlobalTheory.GalChar.block_loc (C.isEta.unr P) hx]; exact hμ x hx) hB hg
  have h4 := h.charpoly_frob ha hl hk hB hg
  rw [← Matrix.charpoly_map] at h4
  have h5 : (Tmat i s g).map ρ.toC = (((blockChar C (D.ntw.l i) (jIdx s)).val P : ℂˣ) : ℂ) •
      ((D.ntw.rhoS i s g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)).map ρ.toC := by
    ext x y
    simp only [Tmat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_units_inv]
    rw [ρ.toC_apply ((chiS i s g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i), h3, inv_inv]
  have h6 := charpoly_smul_of_prod _ (((D.naut.frobEig (D.naut.locG π P)).map fun a =>
    a * ((normV P : ℕ) : ℂ) ^ (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) * (((shiftChar C).val P : ℂˣ) : ℂ)⁻¹))
    (((blockChar C (D.ntw.l i) (jIdx s)).val P : ℂˣ) : ℂ) (by rw [h4, Multiset.map_map]; rfl)
  rw [← h5, Matrix.charpoly_map] at h6
  rw [Tgl_coe]
  refine h6.trans ?_
  rw [D.naut.frobEig_tw _ _ h1, h2, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply]
  rw [shiftChar_val, blockChar_val, cpow_add_real, cpow_add_real, Complex.ofReal_neg, Complex.cpow_neg, HChar.val_inv,
    Units.val_inv_eq_inv_val]
  congr 2
  have := (C.eta.val P).ne_zero
  have := cpow_ne_zero' P (((D.R.t : ℝ) / 2 : ℝ) : ℂ)
  field_simp

theorem hkSat (h : IsTripleWith C art ρ s σ π r ν w red) :
    HkSat D.naut i s (ρ.ι.toRingHom.comp ρ.κ) (twBy S π (mu_unitary C (D.ntw.l i) (jIdx s))) := by
  intro P hP hs k hk
  obtain ⟨x, h1, h2⟩ := h.hecke k P hk hs hP
  refine ⟨x, h1.symm, h2.trans ?_⟩
  have hμ := mu_unr C (jIdx s) (fun k hk => hP (D.ntw.placesOver_subset_exceptional i k hk)) fun hp => hP (D.ntw.primes_subset_exceptional i hp)
  rw [(twBy_unr S (mu_unitary C (D.ntw.l i) (jIdx s)) (h.unr_of_notMem hP) hμ.inv).2, heckeVal, satake, Multiset.map_map]
  have e1 : ((k : ℂ) * ((D.R.r : ℂ) - k)) / 2 = ((k * (D.R.r - k) / 2 : ℕ) : ℂ) := by
    have := congrArg (Nat.cast : ℕ → ℂ) (two_mul_half D.R hk)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk] at this
    rw [← this]
    push_cast
    ring
  have e2 : -((D.R.r : ℂ) + D.R.t) / 2 = -((D.R.nV / 2 : ℕ) : ℂ) := by
    have := congrArg (Nat.cast : ℕ → ℂ) (two_mul_nV_half D.R)
    rw [Nat.cast_mul, Nat.cast_add] at this
    rw [← this]
    push_cast
    ring
  rw [e1, e2, Complex.cpow_neg, Complex.cpow_natCast, Complex.cpow_natCast]
  congr 2
  refine Multiset.map_congr rfl fun a _ => ?_
  simp [mul_comm]

theorem rowFacts (h : IsParam σ π) (hm : ∀ v, D.naut.mono0 (D.naut.locG π v)) (j : Fin D.R.m) :
    RowFacts D.naut i (twBy S π C.isEta.unitary.inv) (twBy S π (mu_unitary C (D.ntw.l i) j)) := by
  have hinf : ∀ τ, D.naut.infG (twBy S π (mu_unitary C (D.ntw.l i) j)) (embOver D τ false) =
      (rowPar (D.hc τ)).map (fun y => ((y + (D.hc τ).e j : ℚ) : ℂ)) ∧
      D.naut.infG (twBy S π (mu_unitary C (D.ntw.l i) j)) (embOver D τ true) =
      (rowPar (D.hc τ)).map (fun y => -((y + (D.hc τ).e j : ℚ) : ℂ)) := fun τ => by
    obtain ⟨h1, h2⟩ := twBy_inf S (π := π) (mu_unitary C (D.ntw.l i) j) (mu_inf C _ j) τ
    rw [h1, h2, (h.inf τ).1, (h.inf τ).2, Multiset.map_map, Multiset.map_map, eExp, D.eTau.symm_apply_apply]
    refine ⟨Multiset.map_congr rfl fun y _ => ?_, Multiset.map_congr rfl fun y _ => ?_⟩ <;>
      simp only [Function.comp_apply] <;> push_cast <;> ring
  refine ⟨fun v hv => (twBy_unr S _ (h.unr v hv) (C.isEta.unr v).inv).1, fun v => twBy_mono S _ (hm v),
    fun v hv hp => (twBy_unr S _ (h.unr v hv) (mu_unr C j hv hp).inv).1, fun v => twBy_mono S _ (hm v),
    twBy_csd S _ h.csd (mu_csd C _ j), (regAlgShift_zero _ _).1 (twBy_regAlg S _ h.ralg (mu_inf C _ j) fun g => ?_),
    fun φ => ?_, fun φ z hz a ha => ?_⟩
  · obtain ⟨z, hz⟩ := eExp_int j g
    exact ⟨⟨z, by simp [hz]⟩, -z, by simp [hz]⟩
  · obtain ⟨τ, b, rfl⟩ := exists_embOver D φ
    have e1 : (embOver D τ false).comp (cj D) = embOver D τ true := RingHom.ext fun _ => rfl
    have e2 : (embOver D τ true).comp (cj D) = embOver D τ false := RingHom.ext fun x => by
      rw [RingHom.comp_apply, embOver_true_apply, ← RingHom.comp_apply, ← RingHom.comp_apply, RingHom.comp_assoc, e1,
        RingHom.comp_apply, embOver_true_apply, Complex.conj_conj]
    cases b
    · rw [e1, (hinf τ).1, (hinf τ).2, Multiset.map_map]
      rfl
    · rw [e2, (hinf τ).1, (hinf τ).2, Multiset.map_map]
      exact Multiset.map_congr rfl fun _ _ => (neg_neg _).symm
  · obtain ⟨τ, b, rfl⟩ := exists_embOver D φ
    obtain ⟨y, hy, hz'⟩ : ∃ y : ℚ, (((D.R.t : ℚ) + 3) / 2 ≤ y ∨ y ≤ -(((D.R.t : ℚ) + 3) / 2)) ∧ z = y := by
      cases b
      · rw [(hinf τ).1] at hz
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
        exact ⟨_, gap_rowPar _ j hy, rfl⟩
      · rw [(hinf τ).2] at hz
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
        exact ⟨-(y + (D.hc τ).e j), (gap_rowPar _ j hy).symm.imp (fun _ => by linarith) fun _ => by linarith,
          (Rat.cast_neg _).symm⟩
    have h1 : (a : ℚ) = -y + ((D.R.t : ℚ) - 1) / 2 := by
      apply Rat.cast_injective (α := ℂ)
      push_cast
      rw [ha, hz']
    refine hy.imp (fun h2 => ?_) fun h2 => ?_
    · exact_mod_cast (show (a : ℚ) < -1 by linarith)
    · exact_mod_cast (show (D.R.t : ℚ) < a by linarith)

theorem tripleAtt_of_isTripleWith (hF : FrobDense D) (hG : GalHodge D T) (ha : GlobalTheory.HeckeGal.IsGlobalArtin art)
    (hχ : IsChars C art ρ) (h : IsTripleWith C art ρ s σ π r ν w red) (S : CharSide D C₀) :
    TripleAtt D.naut (bk0 D) i s := by
  have hR := rowFacts (C := C) (i := i) S h.param
    (GlobalTheory.T.monodromy_trivial_everywhere D T hF hG σ π h.good h.param.csd h.param.ralg h.param.unr h.param.lab) (jIdx s)
  have hφ := (GlobalTheory.GalChar.isEmbedding_toQ (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg).continuous
  have hne : ∀ u : (D.ntw.O0 i)ˣ, GlobalTheory.GalChar.toQ ρ.κ u ≠ 0 := fun u => (u.isUnit.map _).ne_zero
  have s1 : IsSSRep (mapRep (GlobalTheory.GalChar.toQ ρ.κ) (D.ntw.rhoS i s)) := isSSRep_of_smul _ (fun g => hne (ν g)) h.rho h.gal.2.1
  have s2 : IsSSRep (mapRep (GlobalTheory.GalChar.toQ ρ.κ) (Tgl i s)) :=
    isSSRep_of_smul _ (fun g => hne (chiS i s g)⁻¹) (fun g => by
      change ((Tgl i s g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)).map _ = _
      rw [Tgl_coe]
      ext x y
      exact map_mul (GlobalTheory.GalChar.toQ ρ.κ) _ _) s1
  have c2 : Continuous fun g => (Tgl i s g : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) := by
    simp only [Tgl_coe, Tmat]
    exact (Units.continuous_coe_inv.comp (GlobalTheory.GalChar.continuous_units _ (D.ntw.twistCharacterFamily_continuous i _ _))).smul (D.ntw.rhoS_cont i s)
  obtain ⟨c, hc⟩ := GlobalTheory.GalChar.odd_r D.R
  obtain ⟨d, hd⟩ := D.R.t_odd
  have a1 := att_of_frobMatch hF hG (twBy_csd S _ h.param.csd (isCSD_inv (GlobalTheory.EtaSelfDual.isCSD_of_isEtaT _ _ _ C.isEta)))
    (twBy_regAlg S _ h.param.ralg (eta_inf C) fun g =>
      ⟨⟨-d - 1, by rw [hd]; push_cast; ring⟩, -d, by rw [hd]; push_cast; ring⟩)
    (D.ntw.rhoS_cont i s) (frobMatch_rho S ha h) hφ ρ.κ_alg (fun _ => rfl) s1
  have a2 := att_of_frobMatch hF hG hR.csd
    (twBy_regAlg S _ h.param.ralg (mu_inf C _ (jIdx s)) fun g => by
      obtain ⟨z, hz⟩ := eExp_int (jIdx s) g
      exact ⟨⟨z + c - d, by rw [hz, hc, hd]; push_cast; ring⟩, -z + c - d, by rw [hz, hc, hd]; push_cast; ring⟩)
    c2 (frobMatch_T S ha hχ h) hφ ρ.κ_alg (fun _ => rfl) s2
  refine ⟨_, _, _, ?_, ?_, hR, hkSat S h⟩
  · convert a1 using 1
    ring
  · convert a2 using 1
    ring

end Triple

theorem tripleAtt_of_isTriple {D : D7} {T : WDTie D.nd D.naut} {C₀ : CharFrame D} (S : CharSide D C₀) (hF : FrobDense D)
    (hG : GalHodge D T) (h : IsTriple D) (i : D.ntw.Tw) (hi : D.ntw.NonzeroIndexPlace i) (s : D.ntw.Sig i) :
    TripleAtt D.naut (bk0 D) i s := by
  obtain ⟨C, art, h⟩ := h
  obtain ⟨ρ, h1, σ, π, r, ν, w, red, h2⟩ := h.triple hi s
  exact tripleAtt_of_isTripleWith hF hG h.artin h1 h2 S

theorem galois_hypotheses_of_isTriple {D : D7} {T : WDTie D.nd D.naut} {C₀ : CharFrame D} (S : CharSide D C₀)
    (hF : FrobDense D) (hG : GalHodge D T) (h2 : BlochKatoReduction.adm2 D) (h : IsTriple D) :
    BlochKatoReduction.adm1 (bk0 D) ∧ BlochKatoReduction.adm8 D ∧
      ∀ i, D.ntw.NonzeroIndexPlace i → True ∧ ∀ s : D.ntw.Sig i, SelfDual i s ∧ NoJump (bk0 D) i s :=
  galois_hypotheses_of_attached D (bk0 D) hF (fun _ _ => ⟨_, ⟨D.locT _⟩⟩) h2 (tripleAtt_of_isTriple S hF hG h)


end GlobalTheory.TripleLocal

end
end
