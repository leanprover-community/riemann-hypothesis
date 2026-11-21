import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharZeroEigenformSurvivingCompositionFacto
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDataOfCongruentHeckeSystem
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPol
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowDivRowWeight
import Formalism.PieriBlockIdeals.PieriColumnMinors.RealLocalDeltaNabla
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingAdmissibleFacts
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

section
section
open IsLocalRing

namespace GlobalTheory.ZJ

theorem exists_algEquiv_lift_residue (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l))
    (φ : kb l ≃+* kb l)
    (hφ : ∀ x : OO l, (x : PadicAlgCl l) ∈ L → φ (residue (OO l) x) = residue (OO l) x) :
    ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ x y : OO l,
      residue (OO l) y = φ (residue (OO l) x) → ‖g (x : PadicAlgCl l) - y‖ < 1 := by
  classical
  haveI : IsAlgClosure L (PadicAlgCl l) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) L⟩
  haveI : IsGalois L (PadicAlgCl l) := {}
  have hmem : ∀ (g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l) {x : PadicAlgCl l}, x ∈ OO l → g x ∈ OO l :=
    fun g _ hx => algEquiv_mem_OO (g.restrictScalars ℚ_[l]) hx
  letI : MulSemiringAction (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (OO l) :=
    { smul := fun g x => ⟨g x, hmem g x.2⟩
      one_smul := fun _ => Subtype.ext rfl
      mul_smul := fun _ _ _ => Subtype.ext rfl
      smul_zero := fun g => Subtype.ext (map_zero g)
      smul_add := fun g _ _ => Subtype.ext (map_add g _ _)
      smul_one := fun g => Subtype.ext (map_one g)
      smul_mul := fun g _ _ => Subtype.ext (map_mul g _ _) }
  have hsmul : ∀ (g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (x : OO l),
      ((g • x : OO l) : PadicAlgCl l) = g x := fun _ _ => rfl
  let A : Subring (OO l) := L.toSubalgebra.toSubring.comap (OO l).subtype
  have hA : ∀ a : A, (((a : OO l) : PadicAlgCl l)) ∈ L := fun a => a.2
  haveI : SMulCommClass (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) A (OO l) := ⟨fun g a b => by
    apply Subtype.ext
    change g (((a : OO l) : PadicAlgCl l) * b) = ((a : OO l) : PadicAlgCl l) * g b
    rw [map_mul]
    congr 1
    exact g.commutes (⟨_, hA a⟩ : L)⟩
  letI : TopologicalSpace (OO l) := ⊥
  haveI : DiscreteTopology (OO l) := ⟨rfl⟩
  haveI : ContinuousSMul (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (OO l) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := L) (x : PadicAlgCl l)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  haveI : Algebra.IsInvariant A (OO l) (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) (b : PadicAlgCl l)).2
      fun g => congrArg Subtype.val (hb g)
    have hbL : (b : PadicAlgCl l) ∈ L := hk ▸ k.2
    exact ⟨⟨b, hbL⟩, rfl⟩
  set Q := maximalIdeal (OO l) with hQ
  let φ' : ((OO l) ⧸ Q) ≃ₐ[A ⧸ Q.under A] ((OO l) ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := (φ : ((OO l) ⧸ Q) ≃+* ((OO l) ⧸ Q))) (by
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact hφ (a : OO l) (hA a))
  obtain ⟨⟨σ, hσQ⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (Q.under A) Q φ'
  refine ⟨σ, fun x y hxy => ?_⟩
  have h1 : Ideal.Quotient.mk Q (σ • x) = φ (residue (OO l) x) :=
    DFunLike.congr_fun hσ (Ideal.Quotient.mk Q x)
  have h2 : residue (OO l) (σ • x - y) = 0 := by
    rw [map_sub, hxy]
    exact sub_eq_zero.2 h1
  have h3 : ¬ IsUnit (σ • x - y) := by
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h2
    exact h2
  have h4 := (GlobalTheory.ZH.not_isUnit_OO_iff _).1 h3
  simpa [hsmul] using h4

end GlobalTheory.ZJ
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algEquiv_lift_residue_padicAlgCl : ∀ (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l)) (φ : GlobalTheory.ZJ.kb l ≃+* GlobalTheory.ZJ.kb l), (∀ x : GlobalTheory.ZJ.OO l, (x : PadicAlgCl l) ∈ L → φ (IsLocalRing.residue (GlobalTheory.ZJ.OO l) x) = IsLocalRing.residue (GlobalTheory.ZJ.OO l) x) → ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ x y : GlobalTheory.ZJ.OO l, IsLocalRing.residue (GlobalTheory.ZJ.OO l) y = φ (IsLocalRing.residue (GlobalTheory.ZJ.OO l) x) → ‖g (x : PadicAlgCl l) - y‖ < 1 := by
  atlas_forward_decl GlobalTheory.ZJ.exists_algEquiv_lift_residue
end

section
section
namespace GlobalTheory

def FieldCopy (k : Type) : Type := k

instance FieldCopy.instField (k : Type) [h : Field k] : Field (FieldCopy k) := h

instance FieldCopy.instIsAlgClosed (k : Type) [Field k] [h : IsAlgClosed k] :
    IsAlgClosed (FieldCopy k) := h

theorem exists_ringEquiv_extending_of_ker_le :
    ∀ (k : Type) [Field k] [IsAlgClosed k], (∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) →
      ∀ (R : Subring k) (J : Type) (α β : J → k),
        (∀ p : MvPolynomial J R, MvPolynomial.aeval α p = 0 → MvPolynomial.aeval β p = 0) →
        ∃ φ : k ≃+* k, (∀ r ∈ R, φ r = r) ∧ ∀ j, φ (α j) = β j := by
  intro k _ _ hroot R J α β hker
  let eα : MvPolynomial J R →ₐ[R] k := MvPolynomial.aeval α
  let eβ : MvPolynomial J R →ₐ[R] k := MvPolynomial.aeval β
  let S : Subalgebra R k := eα.range
  have hle : ∀ p ∈ RingHom.ker eα.rangeRestrict, eβ p = 0 := by
    intro p hp
    rw [RingHom.mem_ker] at hp
    apply hker
    have := congrArg Subtype.val hp
    simpa using this
  let ψ0 : S →ₐ[R] k := (Ideal.Quotient.liftₐ (RingHom.ker eα.rangeRestrict) eβ hle).comp
    (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective eα)).symm.toAlgHom
  have hψ0 : ∀ p, ψ0 (eα.rangeRestrict p) = eβ p := by
    intro p
    have h1 : (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective eα)).symm
        (eα.rangeRestrict p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    simp only [ψ0, AlgHom.comp_apply]
    erw [h1]
    rfl
  let ψ : S →+* FieldCopy k := ψ0.toRingHom
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    by_contra hne
    have hne' : (s : k) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨n, hn, hsn⟩ := hroot _ hne'
    have hsn' : s ^ n = 1 := Subtype.ext (by simpa using hsn)
    have : ψ s ^ n = 1 := by rw [← map_pow, hsn', map_one]
    rw [hs, zero_pow (by omega)] at this
    exact zero_ne_one this
  letI : Algebra S (FieldCopy k) := ψ.toAlgebra
  haveI : Module.IsTorsionFree S (FieldCopy k) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · left
      exact hψinj (h.trans (map_zero ψ).symm)
    · exact Or.inr h
  haveI : Algebra.IsIntegral S k := by
    constructor
    intro x
    by_cases hx : x = 0
    · rw [hx]; exact isIntegral_zero
    · obtain ⟨n, hn, hxn⟩ := hroot x hx
      refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
      simp [hxn]
  let θ' : k →ₐ[S] FieldCopy k := IsAlgClosed.lift
  let θ : k →+* k := θ'.toRingHom
  have hθS : ∀ s : S, θ (s : k) = ψ0 s := by
    intro s
    have := θ'.commutes s
    exact this
  have hθinj : Function.Injective θ := θ.injective
  have hθsurj : Function.Surjective θ := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, by rw [hy, map_zero]⟩
    obtain ⟨n, hn, hyn⟩ := hroot y hy
    let T := Polynomial.nthRootsFinset n (1 : k)
    have hmem : ∀ x : k, x ∈ T ↔ x ^ n = 1 := fun x => Polynomial.mem_nthRootsFinset (by omega) 1
    let f : T → T := fun t => ⟨θ t, (hmem _).2 (by rw [← map_pow, (hmem _).1 t.2, map_one])⟩
    have hf : Function.Injective f := by
      intro a b hab
      exact Subtype.ext (hθinj (congrArg Subtype.val hab))
    obtain ⟨t, ht⟩ := Finite.injective_iff_surjective.1 hf ⟨y, (hmem y).2 hyn⟩
    exact ⟨t, congrArg Subtype.val ht⟩
  refine ⟨RingEquiv.ofBijective θ ⟨hθinj, hθsurj⟩, ?_, ?_⟩
  · intro r hr
    have hrS : (r : k) ∈ S := ⟨MvPolynomial.C ⟨r, hr⟩, by simp [eα]; rfl⟩
    show θ r = r
    have h2 : (⟨r, hrS⟩ : S) = eα.rangeRestrict (MvPolynomial.C ⟨r, hr⟩) :=
      Subtype.ext (by simp [eα]; rfl)
    rw [show r = ((⟨r, hrS⟩ : S) : k) from rfl, hθS, h2, hψ0]
    simp [eβ]
  · intro j
    show θ (α j) = β j
    have h2 : (⟨α j, ⟨MvPolynomial.X j, by simp [eα]⟩⟩ : S) = eα.rangeRestrict (MvPolynomial.X j) :=
      Subtype.ext (by simp [eα])
    rw [show α j = ((⟨α j, ⟨MvPolynomial.X j, by simp [eα]⟩⟩ : S) : k) from rfl, hθS, h2, hψ0]
    simp [eβ]

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringEquiv_extending_of_ker_le' : ∀ (k : Type) [Field k] [IsAlgClosed k], (∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) → ∀ (R : Subring k) (J : Type) (α β : J → k), (∀ p : MvPolynomial J R, MvPolynomial.aeval α p = 0 → MvPolynomial.aeval β p = 0) → ∃ φ : k ≃+* k, (∀ r ∈ R, φ r = r) ∧ ∀ j, φ (α j) = β j := by
  atlas_forward_decl GlobalTheory.exists_ringEquiv_extending_of_ker_le
end

section
section
namespace GlobalTheory.ResidueLift

open IsLocalRing

theorem res_eq_zero_iff {l : ℕ} [Fact l.Prime] (x : GlobalTheory.ZJ.OO l) :
    residue (GlobalTheory.ZJ.OO l) x = 0 ↔ ‖(x : PadicAlgCl l)‖ < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, GlobalTheory.ZH.not_isUnit_OO_iff]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] L] (J : Type) (a b : J → PadicAlgCl l), (∀ j, ‖a j‖ ≤ 1) → (∀ j, ‖b j‖ ≤ 1) → (∀ p : MvPolynomial J (PadicAlgCl l), (∀ n, p.coeff n ∈ L ∧ ‖p.coeff n‖ ≤ 1) → (‖MvPolynomial.eval a p‖ < 1 ↔ ‖MvPolynomial.eval b p‖ < 1)) → ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ j, ‖g (a j) - b j‖ < 1 := by
  intro l _ L _ J a b ha hb hab
  let K := PadicAlgCl l
  let O := GlobalTheory.ZJ.OO l
  let a' : J → O := fun j => ⟨a j, (GlobalTheory.ZH.mem_OO_iff _).2 (ha j)⟩
  let b' : J → O := fun j => ⟨b j, (GlobalTheory.ZH.mem_OO_iff _).2 (hb j)⟩
  let As : Subring O := L.toSubalgebra.toSubring.comap O.subtype
  let f : As →+* GlobalTheory.ZJ.kb l := (residue O).comp As.subtype
  let R := f.range
  have key : ∀ (c : J → O) (q : MvPolynomial J As),
      MvPolynomial.aeval (fun j => residue O (c j)) (MvPolynomial.map f.rangeRestrict q) = 0 ↔
      ‖MvPolynomial.eval (fun j => (c j : K)) (MvPolynomial.map (O.subtype.comp As.subtype) q)‖ < 1 := by
    intro c q
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval_map]
    have h1 : MvPolynomial.eval₂ ((algebraMap R (GlobalTheory.ZJ.kb l)).comp f.rangeRestrict) (fun j => residue O (c j)) q
        = residue O (MvPolynomial.eval₂ As.subtype c q) := by
      rw [MvPolynomial.eval₂_comp_left]; rfl
    have h2 : MvPolynomial.eval₂ (O.subtype.comp As.subtype) (fun j => (c j : K)) q
        = ((MvPolynomial.eval₂ As.subtype c q : O) : K) :=
      (MvPolynomial.eval₂_comp_left O.subtype As.subtype c q).symm
    rw [h1, h2, res_eq_zero_iff]
  have hII : ∀ p : MvPolynomial J R, MvPolynomial.aeval (fun j => residue O (a' j)) p = 0 →
      MvPolynomial.aeval (fun j => residue O (b' j)) p = 0 := by
    intro p hp
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective f.rangeRestrict f.rangeRestrict_surjective p
    rw [key] at hp ⊢
    refine (hab _ fun n => ?_).1 hp
    rw [MvPolynomial.coeff_map]
    exact ⟨(MvPolynomial.coeff n q).2, (GlobalTheory.ZH.mem_OO_iff _).1 (((MvPolynomial.coeff n q : As) : O).2)⟩
  haveI := GlobalTheory.ZJ.isAlgClosed_kb (p := l)
  obtain ⟨φ, hφR, hφ⟩ := GlobalTheory.T.exists_ringEquiv_extending_of_ker_le' _ GlobalTheory.ZJ.exists_pow_eq_one_kb R J _ _ hII
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_algEquiv_lift_residue_padicAlgCl l L φ fun x hx => hφR _ ⟨⟨x, hx⟩, rfl⟩
  exact ⟨g, fun j => hg (a' j) (b' j) (hφ j).symm⟩

end GlobalTheory.ResidueLift
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_lift_residue_congruence_padic : ∀ (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] L] (J : Type) (a b : J → PadicAlgCl l), (∀ j, ‖a j‖ ≤ 1) → (∀ j, ‖b j‖ ≤ 1) → (∀ p : MvPolynomial J (PadicAlgCl l), (∀ n, p.coeff n ∈ L ∧ ‖p.coeff n‖ ≤ 1) → (‖MvPolynomial.eval a p‖ < 1 ↔ ‖MvPolynomial.eval b p‖ < 1)) → ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ j, ‖g (a j) - b j‖ < 1 := by
  atlas_forward_decl GlobalTheory.ResidueLift.main
end

section
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semilinear_action_dualWeylTensor : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (mu : ι → ℕ → ℕ) (g : R ≃+* R), ∃ Φ : NablaT R N mu →+ NablaT R N mu, Function.Injective Φ ∧ (∀ (c : R) x, Φ (c • x) = g c • Φ x) ∧ ∀ (h : ι → GL (Fin N) R), (∀ τ a b, g ((h τ : Matrix (Fin N) (Fin N) R) a b) = (h τ : Matrix (Fin N) (Fin N) R) a b) → ∀ x, Φ (grp R N mu h x) = grp R N mu h (Φ x) := by
  first | exact @GlobalTheory.semilinear_transport | exact GlobalTheory.semilinear_transport | (intros; apply GlobalTheory.semilinear_transport <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpFrame.Conj

theorem isEig_map {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N)
    (mu : ι → ℕ → ℕ) (g : PadicAlgCl l ≃+* PadicAlgCl l) (hg : ∀ x, g (F.emb x) = F.emb x)
    (θ : F.I → PadicAlgCl l) (h : F.IsEig mu θ) : F.IsEig mu (fun i => g (θ i)) := by
  obtain ⟨f, hf0, ⟨hΓ, hK⟩, hH⟩ := h
  obtain ⟨Φ, hinj, hsm, hgrp⟩ := GlobalTheory.T.exists_semilinear_action_dualWeylTensor (PadicAlgCl l) ι N mu g
  refine ⟨fun x => Φ (f x), ?_, ⟨fun γ hγ x => by simp only [hΓ γ hγ x], fun κ x => ?_⟩, fun i x => ?_⟩
  · intro h0
    apply hf0
    funext x
    have := congrFun h0 x
    exact hinj (by simpa using this)
  · have hfix : ∀ τ a b, g ((Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) : Matrix (Fin N) (Fin N) (PadicAlgCl l)) a b) =
        (Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) : Matrix (Fin N) (Fin N) (PadicAlgCl l)) a b := by
      intro τ a b
      simp [hg]
    rw [← hgrp _ hfix, ← hg (F.chi κ : F.O), ← hsm, hK κ x]
  · have := hH i x
    simp only
    rw [← hg (F.cst i), ← map_sum, ← hsm, this, hsm]

theorem exists_eig_congr : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ), F.Ok → ∀ (θ θ0 : F.I → PadicAlgCl l) (m : Ideal F.T), F.IsEig lam θ → F.Over θ m → F.Over θ0 m → ∃ θ', F.IsEig lam θ' ∧ (∀ i, ‖θ' i‖ ≤ 1) ∧ ∀ i, ‖θ' i - θ0 i‖ < 1 := by
  intro l _ ι _ _ N F lam hOk θ θ0 m hE hθ hθ0
  obtain ⟨_, L, hfin, hrange⟩ := hOk.ring
  have hmemL : ∀ x, F.emb x ∈ L := fun x => by
    have : F.emb x ∈ Set.range F.emb := ⟨x, rfl⟩
    rw [hrange] at this
    exact this.1
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_lift_residue_congruence_padic l L F.I θ θ0 hθ.1 hθ0.1 (by
    intro p hp
    have hmem : p ∈ Set.range (MvPolynomial.map F.emb) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hc
      rw [hrange]
      exact hp n
    obtain ⟨q, rfl⟩ := hmem
    rw [MvPolynomial.eval_map, MvPolynomial.eval_map, ← hθ.2 q, hθ0.2 q])
  have hn : ∀ x, ‖g x‖ = ‖x‖ := fun x => (spectralNorm_eq_of_equiv (g.restrictScalars ℚ_[l]) x).symm
  refine ⟨fun i => g (θ i), isEig_map F lam g.toRingEquiv (fun x => g.commutes ⟨F.emb x, hmemL x⟩) θ hE,
    fun i => (hn _).trans_le (hθ.1 i), hg⟩

end GlobalTheory.ExpFrame.Conj
end

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisConj_eigenSystem_congruent : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ), F.Ok → ∀ (θ θ0 : F.I → PadicAlgCl l) (m : Ideal F.T), F.IsEig lam θ → F.Over θ m → F.Over θ0 m → ∃ θ', F.IsEig lam θ' ∧ (∀ i, ‖θ' i‖ ≤ 1) ∧ ∀ i, ‖θ' i - θ0 i‖ < 1 := by
  atlas_forward_decl GlobalTheory.ExpFrame.Conj.exists_eig_congr
end

section
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockData_of_congruent_heckeSystem : GlobalTheory.Published.ChebotarevDegreeOne → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (P : Par) (W : Wts ι) (F : Frame l ι P.Nr) (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (mu : ι → ℕ → ℕ) (θ θ0 : F.I → PadicAlgCl l), (∀ τ, Antitone (res P.Nr (mu τ))) → F.IsEig mu θ → F.IsEig W.lam θ0 → Bk θ0 → (∀ i, ‖θ i - θ0 i‖ < 1) → BlockFor Ω inc P W mu := by
  first | exact @GlobalTheory.ExpFrame.CongrBlock.blockFor_of_congr | exact GlobalTheory.ExpFrame.CongrBlock.blockFor_of_congr | (intros; apply GlobalTheory.ExpFrame.CongrBlock.blockFor_of_congr <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.PolarFormula

theorem weight_rowW_le_colSum {N : ℕ} (d : Fin N × Fin N →₀ ℕ) (c : Fin N) :
    Finsupp.weight (rowW N N) d c ≤ ∑ s, Finsupp.weight (colW N N) d s := by
  classical
  have h2 : ∑ c', Finsupp.weight (rowW N N) d c' = ∑ s, Finsupp.weight (colW N N) d s := by
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add, Pi.add_apply, Finset.sum_add_distrib, hf, hg]
    | single v k => simp [Finsupp.weight_apply, rowW, colW, Finsupp.sum_single_index, Pi.single_apply]
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)).trans h2.le

theorem sum_rowComp {O : Type} [CommRing O] {N : ℕ} (ν : Fin N → ℕ) (M : ℕ) (hM : ∑ s, ν s ≤ M)
    (f : MvPolynomial (Fin N × Fin N) O) (hf : IsWeightedHomogeneous (colW N N) f ν) :
    ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
      weightedHomogeneousComponent (rowW N N) w f = f := by
  classical
  ext d
  rw [coeff_sum]
  simp_rw [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    rw [Fintype.mem_piFinset]
    intro c
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have e := hf (Ne.symm hne)
    calc _ ≤ _ := weight_rowW_le_colSum d c
      _ = ∑ s, ν s := by rw [e]
      _ ≤ M := hM

theorem comp_of_rowZ {O : Type} [CommRing O] {N : ℕ} (H : Fin N → ℤ) (h : MvPolynomial (Fin N × Fin N) O)
    (hh : IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) h H) (w : Fin N → ℕ) :
    weightedHomogeneousComponent (rowW N N) w h = if (fun c => (w c : ℤ)) = H then h else 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  by_cases hd : coeff d h = 0
  · split_ifs <;> simp [hd]
  · have e := hh hd
    have key : Finsupp.weight (rowW N N) d = w ↔ (fun c => (w c : ℤ)) = H := by
      rw [← e]
      constructor
      · intro hw; funext c; rw [GlobalTheory.LvT.KerLat.weight_rowZ, hw]
      · intro hw; funext c
        have := congrFun hw c
        rw [GlobalTheory.LvT.KerLat.weight_rowZ] at this
        exact_mod_cast this.symm
    by_cases hw : (fun c => (w c : ℤ)) = H
    · rw [if_pos (key.mpr hw), if_pos hw]
    · rw [if_neg (mt key.mp hw), if_neg hw, coeff_zero]

theorem eq_zero_of_rowZ_neg {O : Type} [CommRing O] {N : ℕ} (H : Fin N → ℤ) (h : MvPolynomial (Fin N × Fin N) O)
    (hh : IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) h H) (c : Fin N) (hc : H c < 0) : h = 0 := by
  ext d
  rw [coeff_zero]
  by_contra hd
  have e := congrFun (hh hd) c
  rw [GlobalTheory.LvT.KerLat.weight_rowZ] at e
  omega

theorem rowZ_of_rowW {O : Type} [CommRing O] {N : ℕ} (w : Fin N → ℕ) (h : MvPolynomial (Fin N × Fin N) O)
    (hh : IsWeightedHomogeneous (rowW N N) h w) :
    IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) h (fun c => (w c : ℤ)) := by
  intro d hd
  funext c
  rw [GlobalTheory.LvT.KerLat.weight_rowZ, hh hd]

theorem rowAct_transvection {O : Type} [CommRing O] {N : ℕ} (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) O) :
    rowAct O (n := N) (Matrix.transvection b a (1 : O)) f = (rowGen O a b f).eval 1 := by
  have e : (rowAct O (n := N) (Matrix.transvection b a (1 : O))).toRingHom =
      (Polynomial.evalRingHom (1 : MvPolynomial (Fin N × Fin N) O)).comp (rowGen O a b).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [rowAct, rowGen]
    · intro v
      simp [rowAct, rowGen, Matrix.transvection, Matrix.one_apply, Matrix.single_apply, Finset.sum_add_distrib,
        add_mul, ite_and]
      by_cases hv : v.1 = b
      · simp [hv]
      · simp [hv, Ne.symm hv]
  exact congrArg (fun φ : MvPolynomial (Fin N × Fin N) O →+* MvPolynomial (Fin N × Fin N) O => φ f) e

end GlobalTheory.PolarFormula

namespace GlobalTheory.PolarFormula

theorem comp_rowAct_transvection {O : Type} [CommRing O] {N : ℕ} (a b : Fin N) (hab : a ≠ b) (w : Fin N → ℕ)
    (h : MvPolynomial (Fin N × Fin N) O) (hh : IsWeightedHomogeneous (rowW N N) h w) :
    weightedHomogeneousComponent (rowW N N) (w + Pi.single a 1 - Pi.single b 1)
      (rowAct O (n := N) (Matrix.transvection b a (1 : O)) h) = rowDiv O a b 1 h := by
  classical
  have hZ := rowZ_of_rowW w h hh
  rw [rowAct_transvection, Polynomial.eval_eq_sum_range' (n := (rowGen O a b h).natDegree + 2) (by omega)]
  simp only [one_pow, mul_one, map_sum]
  have hk : ∀ k ∈ Finset.range ((rowGen O a b h).natDegree + 2),
      weightedHomogeneousComponent (rowW N N) (w + Pi.single a 1 - Pi.single b 1) ((rowGen O a b h).coeff k) =
        if k = 1 then rowDiv O a b 1 h else 0 := by
    intro k _
    have hs := GlobalTheory.LvT.KerLat.rowDiv_shift O _ a b k h hZ
    change weightedHomogeneousComponent _ _ (rowDiv O a b k h) = _
    rw [comp_of_rowZ _ _ hs]
    by_cases hk1 : k = 1
    · subst hk1
      by_cases hb : 1 ≤ w b
      · rw [if_pos, if_pos rfl]
        funext c
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply]
        by_cases hca : c = a
        · subst hca; simp [hab]
        · by_cases hcb : c = b
          · subst hcb; simp [hca]; omega
          · simp [hca, hcb]
      · have h0 : rowDiv O a b 1 h = 0 :=
          eq_zero_of_rowZ_neg _ _ hs b (by simp [Pi.single_apply, Ne.symm hab]; omega)
        simp [h0]
    · rw [if_neg hk1, if_neg]
      intro he
      have := congrFun he a
      simp [Pi.single_apply, hab] at this
      omega
  rw [Finset.sum_congr rfl hk, Finset.sum_ite_eq', if_pos (by simp)]

end GlobalTheory.PolarFormula

namespace GlobalTheory.PolarFormula

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink

theorem polar_formula : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι) (M : ℕ) (a b : Fin N), ∃ F : FreeAlgebra O (Letter O N ι), ∀ (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)), (∀ σ, Antitone (res N (lam σ))) → (∀ σ w, IsProj O N lam σ w (P σ w)) → ∑ c : Fin N, lam τ c ≤ M → ∀ x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ)), ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)), (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O a b 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧ evalE O N lam P F (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y) := by
  intro O _ N ι _ _ τ M a b
  by_cases hab : a = b
  · subst hab
    refine ⟨∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
      (w a : O) • FreeAlgebra.ι O (Sum.inr (τ, w)), ?_⟩
    intro lam P _ hP hM x
    refine ⟨⟨rowDiv O a a 1 (x τ), Formalism.GradedWeylDivisibility.rowDivStable O N N _ a a 1 _ (x τ).2⟩, rfl, ?_⟩
    have hcol := ((rowdiv_mem_dualWeyl_iff O N N _ _).mp (x τ).2).1
    let cmp : (Fin N → ℕ) → dualWeyl O N N (res N (lam τ)) := fun w =>
      ⟨weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O),
        Formalism.GradedWeylDivisibility.dualWeylRowGraded O N N _ w _ (x τ).2⟩
    have hPx : ∀ w, P τ w (PiTensorProduct.tprod O x) =
        PiTensorProduct.tprod O (Function.update x τ (cmp w)) :=
      fun w => hP τ w x (cmp w) rfl
    simp only [evalE, map_sum, map_smul, FreeAlgebra.lift_ι_apply, Sum.elim_inr, LinearMap.sum_apply,
      Finset.sum_apply, LinearMap.smul_apply, hPx]
    simp_rw [← MultilinearMap.map_update_smul]
    rw [← MultilinearMap.map_update_sum]
    congr 2
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    conv_rhs => rw [← sum_rowComp _ M hM _ hcol]
    rw [show rowDiv O a a 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) =
        rowDivL O a a 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) from rfl, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [rowDivL_apply, (GlobalTheory.ValCmp.rowDiv_rowWeight O N N w _
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)).2 a 1, Nat.choose_one_right,
      Nat.cast_smul_eq_nsmul]
  · let gt : GL (Fin N) O := ⟨Matrix.transvection b a (-1), Matrix.transvection b a 1,
        by rw [Matrix.transvection_mul_transvection_same b a (Ne.symm hab)]; simp,
        by rw [Matrix.transvection_mul_transvection_same b a (Ne.symm hab)]; simp⟩
    let g : ι → GL (Fin N) O := Pi.mulSingle τ gt
    refine ⟨∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
      FreeAlgebra.ι O (Sum.inr (τ, w + Pi.single a 1 - Pi.single b 1)) * FreeAlgebra.ι O (Sum.inl g) *
        FreeAlgebra.ι O (Sum.inr (τ, w)), ?_⟩
    intro lam P _ hP hM x
    refine ⟨⟨rowDiv O a b 1 (x τ), Formalism.GradedWeylDivisibility.rowDivStable O N N _ a b 1 _ (x τ).2⟩, rfl, ?_⟩
    have hcol := ((rowdiv_mem_dualWeyl_iff O N N _ _).mp (x τ).2).1
    let cmp : (Fin N → ℕ) → dualWeyl O N N (res N (lam τ)) → dualWeyl O N N (res N (lam τ)) := fun w v =>
      ⟨weightedHomogeneousComponent (rowW N N) w (v : MvPolynomial (Fin N × Fin N) O),
        Formalism.GradedWeylDivisibility.dualWeylRowGraded O N N _ w _ v.2⟩
    have hPz : ∀ w (z : ∀ σ, dualWeyl O N N (res N (lam σ))), P τ w (PiTensorProduct.tprod O z) =
        PiTensorProduct.tprod O (Function.update z τ (cmp w (z τ))) :=
      fun w z => hP τ w z (cmp w (z τ)) rfl
    have hg : ∀ z : ∀ σ, dualWeyl O N N (res N (lam σ)), grp O N lam g (PiTensorProduct.tprod O z) =
        PiTensorProduct.tprod O (Function.update z τ (Formalism.UG.dualWeylRep O N N _ gt (z τ))) := by
      intro z
      unfold grp
      rw [(Formalism.CohomologicalDescent.RealLocalDeltaNabla.nabla_rep_tensor_product O ι (fun _ => N) (fun _ => N) (fun σ => res N (lam σ)) g z).1]
      congr 1
      funext σ
      by_cases hσ : σ = τ
      · subst hσ; simp [g]
      · simp [g, hσ, Pi.mulSingle_eq_of_ne hσ]
    simp only [evalE, map_sum, map_mul, FreeAlgebra.lift_ι_apply, Sum.elim_inr, Sum.elim_inl, LinearMap.sum_apply,
      Finset.sum_apply, Module.End.mul_apply, hPz, hg, Function.update_self, Function.update_idem]
    rw [← MultilinearMap.map_update_sum]
    congr 2
    apply Subtype.ext
    simp only [Submodule.coe_sum]
    conv_rhs => rw [← sum_rowComp _ M hM _ hcol]
    rw [show rowDiv O a b 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) =
        rowDivL O a b 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) from rfl, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [rowDivL_apply]
    exact comp_rowAct_transvection a b hab w _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)

end GlobalTheory.PolarFormula
end
end

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisationOperator_formula_groupAndProjectors : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι) (M : ℕ) (a b : Fin N), ∃ F : FreeAlgebra O (Letter O N ι), ∀ (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)), (∀ σ, Antitone (res N (lam σ))) → (∀ σ w, IsProj O N lam σ w (P σ w)) → ∑ c : Fin N, lam τ c ≤ M → ∀ x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ)), ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)), (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O a b 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧ evalE O N lam P F (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y) := by
  atlas_forward_decl GlobalTheory.PolarFormula.polar_formula
end

section
section
open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink

noncomputable section

namespace GlobalTheory.CapelliCoeffs

open Polynomial

def entry (O : Type) [CommRing O] (N : ℕ) (α : Equiv.Perm (Fin N)) (k : Fin N) :
    Polynomial (FreeAlgebra O (Fin N × Fin N)) :=
  C (FreeAlgebra.ι O (α k, k)) + if α k = k then X - C (((k : ℕ) : FreeAlgebra O (Fin N × Fin N))) else 0

def capPoly (O : Type) [CommRing O] (N : ℕ) : Polynomial (FreeAlgebra O (Fin N × Fin N)) :=
  ∑ α : Equiv.Perm (Fin N), (((Equiv.Perm.sign α : ℤˣ) : ℤ) : Polynomial (FreeAlgebra O (Fin N × Fin N))) *
    (List.ofFn (entry O N α)).prod

theorem ofFn_intertwine {R S M M' : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module S M'] (ψ : M →+ M') : ∀ {m : ℕ} (g : Fin m → Module.End R M)
    (g' : Fin m → Module.End S M'), (∀ k x, ψ (g k x) = g' k (ψ x)) →
    ∀ x, ψ ((List.ofFn g).prod x) = (List.ofFn g').prod (ψ x)
  | 0, g, g', _, x => by simp
  | m + 1, g, g', h, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, h 0, ofFn_intertwine ψ (fun k => g k.succ) (fun k => g' k.succ) (fun k => h k.succ)]

theorem capDet_intertwine {R S M M' : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module S M'] {n : ℕ} (ψ : M →+ M') (E : Fin n → Fin n → Module.End R M)
    (E' : Fin n → Fin n → Module.End S M') (h : ∀ i j x, ψ (E i j x) = E' i j (ψ x)) (u : ℤ) (x : M) :
    ψ (Formalism.BranchingDeterminantCap.capDet E u x) = Formalism.BranchingDeterminantCap.capDet E' u (ψ x) := by
  unfold Formalism.BranchingDeterminantCap.capDet Formalism.BranchingDeterminantCap.bmPi Formalism.BranchingDeterminantCap.bmM
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 1
  refine ofFn_intertwine ψ _ _ (fun k y => ?_) x
  simp only [Formalism.BranchingDeterminantCap.bmF, LinearMap.sub_apply, map_sub, h]
  split_ifs
  · simp [Module.End.intCast_apply, map_zsmul]
  · simp

theorem capDet_dualWeyl_domain (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ)
    (hν : Antitone ν) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν) (u : ℤ) :
    Formalism.BranchingDeterminantCap.capDet (fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1) u f =
      ((∏ j : Fin N, (u + ((j : ℕ) : ℤ) - (ν j : ℤ)) : ℤ) : O) • f := by
  let K := FractionRing O
  let φ : O →+* K := algebraMap O K
  have hφ : Function.Injective φ := IsFractionRing.injective O K
  have hg := Formalism.GradedWeylDivisibility.dualWeylMap O K φ N N ν f hf
  have h1 := GlobalTheory.BrCompare.capDet_dualWeyl (K := K) hν u hg
  have e : (fun i j => GlobalTheory.Mem.Gelf.rowE K N N i j) = fun a b => Formalism.GradedWeylDivisibility.rowDivL K a b 1 := by
    funext a b
    exact LinearMap.ext fun P => (GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv K N N a b P).1
  rw [e] at h1
  have h2 := capDet_intertwine (MvPolynomial.map φ).toAddMonoidHom (fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1)
    (fun a b => Formalism.GradedWeylDivisibility.rowDivL K a b 1) (fun i j x => (Formalism.GradedWeylDivisibility.lclosedeq_rowDiv_map φ i j 1 x).symm) u f
  apply MvPolynomial.map_injective φ hφ
  have h3 := h2.trans h1
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at h3
  rw [h3, Int.cast_smul_eq_zsmul K, Int.cast_smul_eq_zsmul O, map_zsmul]

theorem eval_capPoly (O : Type) [CommRing O] (N : ℕ) {M : Type} [AddCommGroup M] [Module O M]
    (Φ : FreeAlgebra O (Fin N × Fin N) →ₐ[O] Module.End O M) (v : ℤ) (L : ℕ)
    (hL : (capPoly O N).natDegree < L) :
    ∑ i ∈ Finset.range L, (v ^ i) • Φ ((capPoly O N).coeff i) =
      ((-1 : ℤ) ^ N) • Formalism.BranchingDeterminantCap.capDet (fun a b => Φ (FreeAlgebra.ι O (a, b))) (-v) := by
  have hc : ∀ a : Module.End O M, Commute ((RingHom.id _) a) (v : Module.End O M) :=
    fun a => (Int.cast_commute v a).symm
  let ev := Polynomial.eval₂RingHom' (RingHom.id (Module.End O M)) (v : Module.End O M) hc
  let Ψ := Polynomial.mapRingHom (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M)
  have key : ev (Ψ (capPoly O N)) = ∑ i ∈ Finset.range L, (v ^ i) • Φ ((capPoly O N).coeff i) := by
    show eval₂ (RingHom.id _) (v : Module.End O M) (map (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M)
      (capPoly O N)) = _
    rw [eval₂_eq_sum_range' _ (lt_of_le_of_lt natDegree_map_le hL)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_map, RingHom.id_apply, ← Int.cast_pow, zsmul_eq_mul']
    rfl
  rw [← key]
  unfold capPoly Formalism.BranchingDeterminantCap.capDet Formalism.BranchingDeterminantCap.bmPi Formalism.BranchingDeterminantCap.bmM
  simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hev : ∀ p, ev p = p.eval₂ (RingHom.id _) (v : Module.End O M) := fun _ => rfl
  have hΨ : ∀ p, Ψ p = p.map (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M) := fun _ => rfl
  have e : (List.ofFn fun k => ev (Ψ (entry O N α k))) =
      (List.ofFn fun k => Formalism.BranchingDeterminantCap.bmF (fun a b => Φ (FreeAlgebra.ι O (a, b))) (-v) k (α k) (id k)).map Neg.neg := by
    rw [List.map_ofFn]
    congr 1
    funext k
    rw [hev, hΨ]
    simp only [Function.comp_apply, entry, Formalism.BranchingDeterminantCap.bmF, id]
    split_ifs
    · simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval₂_add,
        Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.id_apply, map_natCast, RingHom.coe_coe, Polynomial.map_natCast,
        Polynomial.eval₂_natCast]
      push_cast
      abel
    · simp
  rw [show (⇑ev ∘ ⇑Ψ ∘ entry O N α) = fun k => ev (Ψ (entry O N α k)) from rfl, e, List.prod_map_neg, List.length_ofFn, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  exact (Int.cast_commute _ _).left_comm _

theorem coeff_eq_of_int (P : Type) [CommRing P] [IsDomain P] [CharZero P] (L : ℕ) (a b : ℕ → P)
    (h : ∀ v : ℤ, ∑ i ∈ Finset.range L, (v : P) ^ i * a i = ∑ i ∈ Finset.range L, (v : P) ^ i * b i) :
    ∀ i < L, a i = b i := by
  intro i hi
  let Q : Polynomial P := ∑ j ∈ Finset.range L, monomial j (a j - b j)
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (Int.cast_injective (α := P)))
    rintro _ ⟨v, rfl⟩
    have hv := h v
    simp only [Set.mem_setOf_eq, IsRoot, Q, eval_finset_sum, eval_monomial]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hv
    rw [← hv]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have := congrArg (fun q : Polynomial P => q.coeff i) hQ
  simp only [Q, finset_sum_coeff, coeff_monomial, coeff_zero] at this
  rw [Finset.sum_eq_single i (fun j _ hj => if_neg hj) (fun h' => absurd (Finset.mem_range.2 hi) h'), if_pos rfl] at this
  exact sub_eq_zero.1 this

end GlobalTheory.CapelliCoeffs

namespace GlobalTheory.CapelliCoeffs

open Polynomial

theorem capelli_coeff_dualWeyl : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ),
    ∃ F : ℕ → FreeAlgebra O (Fin N × Fin N), ∀ ν : Fin N → ℕ, Antitone ν →
      ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν, ∀ k : ℕ,
        evalPol O N (F k) f = (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((ν a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • f := by
  intro O _ _ _ N
  refine ⟨fun k => (capPoly O N).coeff k, fun ν hν f hf k => ?_⟩
  set p : Polynomial ℤ := ∏ a : Fin N, (X + C (((ν a : ℤ) - (a : ℕ) : ℤ))) with hpdef
  set L := (capPoly O N).natDegree + N + 1 with hLdef
  have hp : p.natDegree ≤ N := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ => (natDegree_X_add_C (((ν a : ℤ) - (a : ℕ) : ℤ))).le).trans ?_
    simp
  have hE : (fun a b => evalPol O N (FreeAlgebra.ι O (a, b))) = fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1 := by
    funext a b
    simp [evalPol]
  by_cases hk : k < L
  · refine coeff_eq_of_int (MvPolynomial (Fin N × Fin N) O) L
      (fun i => evalPol O N ((capPoly O N).coeff i) f) (fun i => ((p.coeff i : ℤ) : O) • f) (fun v => ?_) k hk
    have hA := eval_capPoly O N (evalPol O N) v L (by omega)
    rw [hE] at hA
    have hB := capDet_dualWeyl_domain O N ν hν f hf (-v)
    have e1 : ∑ i ∈ Finset.range L, ((v : MvPolynomial (Fin N × Fin N) O)) ^ i * evalPol O N ((capPoly O N).coeff i) f =
        (∑ i ∈ Finset.range L, (v ^ i) • evalPol O N ((capPoly O N).coeff i)) f := by
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.smul_apply, ← Int.cast_pow, ← zsmul_eq_mul]
    have e2 : ∑ i ∈ Finset.range L, ((v : MvPolynomial (Fin N × Fin N) O)) ^ i * (((p.coeff i : ℤ) : O) • f) =
        (p.eval v) • f := by
      rw [eval_eq_sum_range' (n := L) (by omega), Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Int.cast_pow, ← zsmul_eq_mul, Int.cast_smul_eq_zsmul, smul_smul, mul_comm]
    have e3 : p.eval v = (-1 : ℤ) ^ N * ∏ j : Fin N, (-v + ((j : ℕ) : ℤ) - (ν j : ℤ)) := by
      rw [hpdef, eval_prod]
      have : ((-1 : ℤ) ^ N) = ∏ _j : Fin N, (-1 : ℤ) := by simp
      rw [this, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [eval_add, eval_X, eval_C]
      ring
    rw [e1, e2, hA, LinearMap.smul_apply, hB, e3, Int.cast_smul_eq_zsmul, smul_smul]
  · have h1 : (capPoly O N).coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have h2 : p.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    show evalPol O N ((capPoly O N).coeff k) f = _
    rw [h1, h2, map_zero]
    simp

end GlobalTheory.CapelliCoeffs
end
end

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliCoeff_dualWeyl_eq_coeff_prod : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ), ∃ F : ℕ → FreeAlgebra O (Fin N × Fin N), ∀ ν : Fin N → ℕ, Antitone ν → ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν, ∀ k : ℕ, evalPol O N (F k) f = (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((ν a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • f := by
  atlas_forward_decl GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl
end

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CapelliLink

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD

theorem pure_step {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] (τ : ι)
    (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam))
    (Fab : Fin N × Fin N → FreeAlgebra O (Letter O N ι))
    (hF : ∀ (p : Fin N × Fin N) (x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ))),
      ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)),
        (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O p.1 p.2 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧
        evalE O N lam P (Fab p) (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y))
    (Φ : FreeAlgebra O (Fin N × Fin N)) :
    ∀ x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ)), ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)),
      (y : MvPolynomial (Fin N × Fin N) O) = evalPol O N Φ (x τ : MvPolynomial (Fin N × Fin N) O) ∧
      evalE O N lam P (FreeAlgebra.lift O Fab Φ) (PiTensorProduct.tprod O x) =
        PiTensorProduct.tprod O (Function.update x τ y) := by
  induction Φ using FreeAlgebra.induction with
  | grade0 r =>
    intro x
    refine ⟨r • x τ, ?_, ?_⟩
    · rw [AlgHom.commutes, Module.algebraMap_end_apply]; rfl
    · rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, MultilinearMap.map_update_smul,
        Function.update_eq_self]
  | grade1 p =>
    intro x
    obtain ⟨y, hy, he⟩ := hF p x
    refine ⟨y, ?_, ?_⟩
    · rw [hy]; simp [evalPol]
    · rw [FreeAlgebra.lift_ι_apply]; exact he
  | mul Φ₁ Φ₂ h₁ h₂ =>
    intro x
    obtain ⟨y₂, hy₂, he₂⟩ := h₂ x
    obtain ⟨y₁, hy₁, he₁⟩ := h₁ (Function.update x τ y₂)
    refine ⟨y₁, ?_, ?_⟩
    · rw [hy₁, Function.update_self, hy₂, map_mul, Module.End.mul_apply]
    · rw [map_mul, map_mul, Module.End.mul_apply, he₂, he₁, Function.update_idem]
  | add Φ₁ Φ₂ h₁ h₂ =>
    intro x
    obtain ⟨y₁, hy₁, he₁⟩ := h₁ x
    obtain ⟨y₂, hy₂, he₂⟩ := h₂ x
    refine ⟨y₁ + y₂, ?_, ?_⟩
    · rw [Submodule.coe_add, hy₁, hy₂, map_add, LinearMap.add_apply]
    · rw [map_add, map_add, LinearMap.add_apply, he₁, he₂, MultilinearMap.map_update_add]

theorem scalar_of {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] (τ : ι)
    (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam))
    (Fab : Fin N × Fin N → FreeAlgebra O (Letter O N ι))
    (hF : ∀ (p : Fin N × Fin N) (x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ))),
      ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)),
        (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O p.1 p.2 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧
        evalE O N lam P (Fab p) (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y))
    (Φ : FreeAlgebra O (Fin N × Fin N)) (c : O)
    (hΦ : ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)), evalPol O N Φ f = c • f) :
    evalE O N lam P (FreeAlgebra.lift O Fab Φ) = c • (1 : Module.End O (NablaT O N lam)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  obtain ⟨y, hy, he⟩ := pure_step τ lam P Fab hF Φ x
  have hyc : y = c • x τ := Subtype.ext (by rw [hy, hΦ _ (x τ).2]; rfl)
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, he, hyc,
    MultilinearMap.map_update_smul, Function.update_eq_self]
  simp

def evalA (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) (hP : ∀ σ w, IsProj O N lam σ w (P σ w)) :
    FreeAlgebra O (Letter O N ι) →ₐ[O] alg O N lam :=
  FreeAlgebra.lift O (Sum.elim (grpA O N lam) fun p =>
    ⟨P p.1 p.2, Algebra.subset_adjoin (Or.inr ⟨p.1, p.2, hP p.1 p.2⟩)⟩)

theorem evalA_coe (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) (hP : ∀ σ w, IsProj O N lam σ w (P σ w))
    (Φ : FreeAlgebra O (Letter O N ι)) :
    ((evalA O N lam P hP Φ : alg O N lam) : Module.End O (NablaT O N lam)) = evalE O N lam P Φ := by
  have h : (alg O N lam).val.comp (evalA O N lam P hP) = evalE O N lam P := by
    apply FreeAlgebra.hom_ext
    funext p
    rcases p with g | p
    · simp [evalA, evalE, grpA]
    · simp [evalA, evalE]
  exact DFunLike.congr_fun h Φ

theorem compat {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] {lam mu : ι → ℕ → ℕ} {ϖ : O}
    {Gm : Type} [AddCommGroup Gm] [Module (alg O N lam) Gm]
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) (hP : ∀ σ w, IsProj O N lam σ w (P σ w))
    (Q : ι → (Fin N → ℕ) → Module.End O (NablaT O N mu)) (hQ : ∀ σ w, IsProj O N mu σ w (Q σ w))
    (ψ : Gm →+ (NablaT O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu))))
    (h2 : ∀ (c : O) z, ψ (algebraMap O (alg O N lam) c • z) = c • ψ z)
    (h3 : ∀ g z y, ψ z = Submodule.Quotient.mk y →
      ψ (grpA O N lam g • z) = Submodule.Quotient.mk (grp O N mu g y))
    (h4 : ∀ τ w (a : alg O N lam) (a' : Module.End O (NablaT O N mu)), IsProj O N lam τ w a →
      IsProj O N mu τ w a' → ∀ z y, ψ z = Submodule.Quotient.mk y → ψ (a • z) = Submodule.Quotient.mk (a' y))
    (Φ : FreeAlgebra O (Letter O N ι)) :
    ∀ z y, ψ z = Submodule.Quotient.mk y →
      ψ (evalA O N lam P hP Φ • z) = Submodule.Quotient.mk (evalE O N mu Q Φ y) := by
  induction Φ using FreeAlgebra.induction with
  | grade0 r =>
    intro z y h
    rw [AlgHom.commutes, AlgHom.commutes, h2, h, Module.algebraMap_end_apply, Submodule.Quotient.mk_smul]
  | grade1 p =>
    intro z y h
    rcases p with g | ⟨σ, w⟩
    · simp only [evalA, evalE, FreeAlgebra.lift_ι_apply, Sum.elim_inl]; exact h3 g z y h
    · simp only [evalA, evalE, FreeAlgebra.lift_ι_apply, Sum.elim_inr]
      exact h4 σ w _ (Q σ w) (hP σ w) (hQ σ w) z y h
  | mul Φ₁ Φ₂ h₁ h₂ =>
    intro z y h
    rw [map_mul, map_mul, mul_smul, Module.End.mul_apply]
    exact h₁ _ _ (h₂ z y h)
  | add Φ₁ Φ₂ h₁ h₂ =>
    intro z y h
    rw [map_add, map_add, add_smul, map_add, LinearMap.add_apply, h₁ z y h, h₂ z y h, Submodule.Quotient.mk_add]

theorem dvd_of_smul_eq_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V : Type}
    [AddCommGroup V] [Module O V] {ϖ : O} (hϖ : Irreducible ϖ) (d : O) (y : V)
    (hne : (Submodule.Quotient.mk y : V ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O V)) ≠ 0)
    (h0 : d • (Submodule.Quotient.mk y : V ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O V)) = 0) : ϖ ∣ d := by
  by_contra hd
  have hu : IsUnit d := by
    by_contra hnu
    have hm : d ∈ IsLocalRing.maximalIdeal O := hnu
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hm
    exact hd hm
  obtain ⟨u, rfl⟩ := hu
  apply hne
  have h1 := congrArg (fun q => (↑u⁻¹ : O) • q) h0
  simpa [smul_smul] using h1

theorem int_dvd_of {O : Type} [CommRing O] {ϖ : O} (hϖ : ¬ IsUnit ϖ) {l : ℕ} (hl : l.Prime)
    (hϖl : ϖ ∣ (l : O)) (d : ℤ) (hd : ϖ ∣ (d : O)) : (l : ℤ) ∣ d := by
  by_contra h
  have hc : IsCoprime (l : ℤ) d := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h' : Nat.Coprime l d.natAbs := (Nat.Prime.coprime_iff_not_dvd hl).2 (fun h' => h (Int.natCast_dvd.2 h'))
    simpa [Int.gcd] using h'
  obtain ⟨u, v, huv⟩ := hc
  have h1 : ϖ ∣ ((u * l + v * d : ℤ) : O) := by
    push_cast
    exact dvd_add (dvd_mul_of_dvd_right hϖl _) (dvd_mul_of_dvd_right hd _)
  rw [huv, Int.cast_one] at h1
  exact hϖ (isUnit_of_dvd_one h1)

set_option synthInstance.maxHeartbeats 400000 in

theorem linkage : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type)
    [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (l : ℕ) (ϖ : O), l.Prime → Irreducible ϖ →
    ϖ ∣ (l : O) → (∀ τ, Antitone (res N (lam τ))) → (∀ τ, Antitone (res N (mu τ))) →
    ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm → SubQ O N lam ϖ Gm →
    Embeds O N lam mu ϖ Gm → ∀ τ,
    (∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) =
      ∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l)) := by
  intro O _ _ _ _ N ι _ _ lam mu l ϖ hl hϖ hϖl hlam hmu Gm _ _ _ hSub hEmb τ
  obtain ⟨U, π, hπ, -⟩ := hSub
  obtain ⟨ψ, hψ, h2, h3, h4⟩ := hEmb
  choose P hP _ using fun σ w => GlobalTheory.T.existsUnique_dualWeylWeightProjector O N ι lam σ w
  choose Q hQ _ using fun σ w => GlobalTheory.T.existsUnique_dualWeylWeightProjector O N ι mu σ w
  obtain ⟨M, hM⟩ : ∃ M, M = ∑ c : Fin N, lam τ c + ∑ c : Fin N, mu τ c := ⟨_, rfl⟩
  choose Fab hFab using fun p : Fin N × Fin N => GlobalTheory.T.polarisationOperator_formula_groupAndProjectors O N ι τ M p.1 p.2
  obtain ⟨Fk, hFk⟩ := GlobalTheory.T.capelliCoeff_dualWeyl_eq_coeff_prod O N
  have hscal : ∀ (nu : ι → ℕ → ℕ) (R : ι → (Fin N → ℕ) → Module.End O (NablaT O N nu)),
      (∀ σ, Antitone (res N (nu σ))) → (∀ σ w, IsProj O N nu σ w (R σ w)) → ∑ c : Fin N, nu τ c ≤ M → ∀ k,
      evalE O N nu R (FreeAlgebra.lift O Fab (Fk k)) =
        (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((nu τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • 1 := by
    intro nu R hnu hR hb k
    apply scalar_of τ nu R Fab (fun p x => hFab p nu R hnu hR hb x)
    intro f hf
    exact hFk (res N (nu τ)) (hnu τ) f hf k
  obtain ⟨z, hz⟩ := exists_ne (0 : Gm)
  obtain ⟨u, rfl⟩ := hπ z
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (ψ (π u))
  have hne : (Submodule.Quotient.mk y : NablaT O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu))) ≠ 0 := by
    rw [hy]; intro h; apply hz; apply hψ; rw [h, map_zero]
  have key : ∀ k, ϖ ∣ ((((∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k -
      (∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ)) : O) := by
    intro k
    apply dvd_of_smul_eq_zero hϖ _ y hne
    have hL := hscal lam P hlam hP (by omega) k
    have hMu := hscal mu Q hmu hQ (by omega) k
    have hc := compat P hP Q hQ ψ h2 h3 h4 (FreeAlgebra.lift O Fab (Fk k)) (π u) y hy.symm
    have hA : evalA O N lam P hP (FreeAlgebra.lift O Fab (Fk k)) • π u =
        algebraMap O (alg O N lam) (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • π u := by
      have hu' : evalA O N lam P hP (FreeAlgebra.lift O Fab (Fk k)) • u =
          algebraMap O (alg O N lam) (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • u := by
        apply Subtype.ext
        change ((evalA O N lam P hP _ : alg O N lam) : Module.End O _) (u : NablaT O N lam) =
          ((algebraMap O (alg O N lam) _ : alg O N lam) : Module.End O _) (u : NablaT O N lam)
        rw [evalA_coe, hL, LinearMap.smul_apply, Module.End.one_apply, Subalgebra.coe_algebraMap,
          Module.algebraMap_end_apply]
      rw [← π.map_smul, hu', π.map_smul]
    rw [hA, h2, hMu, ← hy] at hc
    rw [Int.cast_sub, sub_smul, sub_eq_zero, hc]
    simp [Submodule.Quotient.mk_smul]
  have hmap : ∀ nu : ι → ℕ → ℕ,
      (∏ a : Fin N, (Polynomial.X + Polynomial.C (((nu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) =
        (∏ a : Fin N, (Polynomial.X + Polynomial.C (((nu τ a : ℤ) - (a : ℕ) : ℤ)))).map (Int.castRingHom (ZMod l)) := by
    intro nu; simp [Polynomial.map_prod]
  rw [hmap lam, hmap mu]
  ext k
  rw [Polynomial.coeff_map, Polynomial.coeff_map, eq_intCast, eq_intCast, ZMod.intCast_eq_intCast_iff_dvd_sub, ← neg_sub]
  exact dvd_neg.2 (int_dvd_of hϖ.not_isUnit hl hϖl _ (key k))

end GlobalTheory.CapelliLink

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleModule_linkage_dualWeylLattice_reduction : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (l : ℕ) (ϖ : O), l.Prime → Irreducible ϖ → ϖ ∣ (l : O) → (∀ τ, Antitone (res N (lam τ))) → (∀ τ, Antitone (res N (mu τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm → SubQ O N lam ϖ Gm → Embeds O N lam mu ϖ Gm → ∀ τ, (∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) = ∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l)) := by
  atlas_forward_decl GlobalTheory.CapelliLink.linkage
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.Published.ChebotarevDegreeOne → ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool) (P : Par) (W : Wts ι), (∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ))) → ∀ (F : Frame l ι P.Nr), F.Ok → ∀ (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (jK : F.K →* alg F.O P.Nr W.lam), F.IsJ W.lam jK → ∀ (ϖ : F.O), Irreducible ϖ → ϖ ∣ ((l : ℕ) : F.O) → (∀ τ, Antitone (res P.Nr (W.lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O P.Nr W.lam) Gm] [IsScalarTower F.O (alg F.O P.Nr W.lam) Gm] [Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)], F.IsHecke W.lam jK Gm → IsSimpleModule (alg F.O P.Nr W.lam) Gm → SubQ F.O P.Nr W.lam ϖ Gm → ∀ (mu : ι → ℕ → ℕ), (∀ τ, Antitone (res P.Nr (mu τ)) ∧ ∑ a : Fin P.Nr, mu τ a = ∑ a : Fin P.Nr, W.lam τ a ∧ (∀ a : Fin P.Nr, W.lam τ (P.Nr - 1) ≤ mu τ a ∧ mu τ a ≤ W.lam τ 0)) → Embeds F.O P.Nr W.lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal] (θ0 : F.I → PadicAlgCl l), F.IsEig W.lam θ0 → Bk θ0 → F.Over θ0 m → ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  intro E Ω _ _ _ _ _ _ hCheb l _ ι _ _ inc fr cjj P W hlink F hF Bk hG jK hJ ϖ hϖ hϖl hlam Gm _ _ _ _ _ hH hS hSQ mu hmu hemb m _ θ0 h0e h0b h0o hns
  obtain ⟨θ, hθe, hθo⟩ := GlobalTheory.T.exists_charZero_eigenform_surviving_compositionFactor l ι P.Nr F W.lam mu jK ϖ hF hJ hϖ Gm hH hemb m hns
  obtain ⟨θ', hθ'e, -, hc⟩ := GlobalTheory.T.exists_galoisConj_eigenSystem_congruent l ι P.Nr F mu hF θ θ0 m hθe hθo h0o
  have hB : BlockFor Ω inc P W mu :=
    GlobalTheory.T.blockData_of_congruent_heckeSystem hCheb E Ω l ι inc P W F Bk hG mu θ' θ0 (fun τ => (hmu τ).1) hθ'e h0e h0b hc
  have hnt : Nontrivial Gm := IsSimpleModule.nontrivial (alg F.O P.Nr W.lam) Gm
  have hlnk := GlobalTheory.T.simpleModule_linkage_dualWeylLattice_reduction F.O P.Nr ι W.lam mu l ϖ (Fact.out) hϖ hϖl hlam (fun τ => (hmu τ).1) Gm hnt hSQ hemb
  exact hlink mu (fun τ => ⟨(hmu τ).1, (hmu τ).2.1, (hmu τ).2.2, hlnk τ⟩) hB
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeLink_of_surviving_simple_subquotient : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.Published.ChebotarevDegreeOne → ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool) (P : Par) (W : Wts ι), (∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ))) → ∀ (F : Frame l ι P.Nr), F.Ok → ∀ (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (jK : F.K →* alg F.O P.Nr W.lam), F.IsJ W.lam jK → ∀ (ϖ : F.O), Irreducible ϖ → ϖ ∣ ((l : ℕ) : F.O) → (∀ τ, Antitone (res P.Nr (W.lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O P.Nr W.lam) Gm] [IsScalarTower F.O (alg F.O P.Nr W.lam) Gm] [Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)], F.IsHecke W.lam jK Gm → IsSimpleModule (alg F.O P.Nr W.lam) Gm → SubQ F.O P.Nr W.lam ϖ Gm → ∀ (mu : ι → ℕ → ℕ), (∀ τ, Antitone (res P.Nr (mu τ)) ∧ ∑ a : Fin P.Nr, mu τ a = ∑ a : Fin P.Nr, W.lam τ a ∧ (∀ a : Fin P.Nr, W.lam τ (P.Nr - 1) ≤ mu τ a ∧ mu τ a ≤ W.lam τ 0)) → Embeds F.O P.Nr W.lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal] (θ0 : F.I → PadicAlgCl l), F.IsEig W.lam θ0 → Bk θ0 → F.Over θ0 m → ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  atlas_forward_decl GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving
end
