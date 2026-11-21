import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
import BuildAid.ForwardExisting

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.CentralIdem

theorem trace_mem_adjoin {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hT : T ^ (n + 1) = T) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    LinearMap.trace ℂ V T ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  haveI : NeZero n := ⟨hn⟩
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  apply Subalgebra.multiset_sum_mem
  intro μ hμ
  have hr : T.charpoly.IsRoot μ := Polynomial.isRoot_of_mem_roots hμ
  have he : T.HasEigenvalue μ := (Module.End.hasEigenvalue_iff_isRoot_charpoly T μ).2 hr
  obtain ⟨v, hv⟩ := he.exists_hasEigenvector
  have h1 := hv.pow_apply (n + 1)
  rw [hT, hv.apply_eq_smul] at h1
  have h2 : μ = μ ^ (n + 1) := smul_left_injective ℂ hv.2 h1
  by_cases h0 : μ = 0
  · rw [h0]; exact Subalgebra.zero_mem _
  · have h3 : μ ^ n = 1 := by
      rw [pow_succ] at h2
      exact mul_right_cancel₀ h0 (by rw [one_mul]; exact h2.symm)
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h3
    rw [← hi]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) _

theorem trace_lmul {Γ : Type} [Group Γ] [Finite Γ] (x : MonoidAlgebra ℂ Γ) :
    LinearMap.trace ℂ _ (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x) = (Nat.card Γ : ℂ) * x.coeff 1 := by
  classical
  haveI := Fintype.ofFinite Γ
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis Γ ℂ), Matrix.trace]
  have : ∀ g : Γ, (LinearMap.toMatrix (MonoidAlgebra.basis Γ ℂ) (MonoidAlgebra.basis Γ ℂ)
      (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x)).diag g = x.coeff 1 := by
    intro g
    rw [Matrix.diag, LinearMap.toMatrix_apply]
    have hb : MonoidAlgebra.basis Γ ℂ g = MonoidAlgebra.single g 1 := by simp
    rw [hb]
    change (x * MonoidAlgebra.single g (1 : ℂ)).coeff g = _
    rw [MonoidAlgebra.coeff_mul_single_apply]
    simp
  rw [Finset.sum_congr rfl fun g _ => this g]
  simp

theorem centralIdemCoeff : CentralIdemCoeff := by
  intro Γ _ _ e he hc ζ hζ h
  haveI : Module.Finite ℂ (MonoidAlgebra ℂ Γ) := Module.Finite.of_basis (MonoidAlgebra.basis Γ ℂ)
  set x : MonoidAlgebra ℂ Γ := MonoidAlgebra.single h⁻¹ (1 : ℂ) * e with hx
  have hcm : Commute (MonoidAlgebra.single h⁻¹ (1 : ℂ)) e := (hc _).symm
  have hid : IsIdempotentElem e := he
  have hp : x ^ (Nat.card Γ + 1) = x := by
    rw [hx, hcm.mul_pow, hid.pow_succ_eq, MonoidAlgebra.single_pow, one_pow, pow_succ,
      pow_card_eq_one', one_mul]
  have hT := trace_mem_adjoin (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x) (n := Nat.card Γ)
    Nat.card_pos.ne' (by rw [← map_pow, hp]) hζ
  rw [trace_lmul, hx, MonoidAlgebra.coeff_single_mul_apply] at hT
  simpa using hT

end GlobalTheory.CentralIdem
end

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.CentralIdem

theorem exists_central_lift {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) {Γ : Type} [Group Γ] [Finite Γ] (x : MonoidAlgebra B Γ)
    (hx : ∀ z, x * z = z * x) (hr : ∀ h, x.coeff h ∈ f.range) :
    ∃ z ∈ Subalgebra.center A (MonoidAlgebra A Γ), ∀ h : Γ, f (z.coeff h) = x.coeff h := by
  choose c hc using hr
  let z : MonoidAlgebra A Γ := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c)
  have hz : ∀ h, f (z.coeff h) = x.coeff h := fun h => hc h
  have hco : ∀ (y : MonoidAlgebra A Γ) h, (MonoidAlgebra.mapRingHom Γ f y).coeff h = f (y.coeff h) := by
    intro y h; simp
  have hinj : Function.Injective (MonoidAlgebra.mapRingHom Γ f) := by
    intro a b hab
    ext h
    apply hf
    rw [← hco, ← hco, hab]
  have hzx : MonoidAlgebra.mapRingHom Γ f z = x := by
    ext h
    rw [hco, hz]
  refine ⟨z, ?_, hz⟩
  rw [Subalgebra.mem_center_iff]
  intro b
  apply hinj
  rw [map_mul, map_mul, hzx, hx]

theorem card_mul_idem_from_center : ∀ (D : D7) (i : D.nd.Loc) (Γ : Type) [Group Γ] [Finite Γ] (e : MonoidAlgebra ℂ Γ), e * e = e → (∀ z, e * z = z * e) → (∃ ζ : D.nd.O i, IsPrimitiveRoot (iotaO D.nd D.naut i ζ) (Nat.card Γ)) → ∃ z ∈ Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) Γ), ∀ h : Γ, iotaO D.nd D.naut i (MonoidAlgebra.coeff z h) = (Nat.card Γ : ℂ) * e.coeff h := by
  intro D i Γ _ _ e he hc ⟨ζ, hζ⟩
  have hinj : Function.Injective (iotaO D.nd D.naut i) :=
    ((D.naut.iotaQC i).injective.comp (D.naut.iotaQ i).injective).comp (IsFractionRing.injective _ _)
  have hco : ∀ h, ((Nat.card Γ : ℂ) • e).coeff h = (Nat.card Γ : ℂ) * e.coeff h := by
    intro h; simp
  obtain ⟨z, hz, hz'⟩ := exists_central_lift (iotaO D.nd D.naut i) hinj ((Nat.card Γ : ℂ) • e)
    (fun z => by rw [smul_mul_assoc, mul_smul_comm, hc]) (fun h => by
      rw [hco]
      have h1 := centralIdemCoeff Γ e he hc _ hζ h
      have h2 : Algebra.adjoin ℤ ({iotaO D.nd D.naut i ζ} : Set ℂ) ≤
          subalgebraOfSubring (iotaO D.nd D.naut i).range :=
        Algebra.adjoin_le (by rintro _ rfl; exact ⟨ζ, rfl⟩)
      exact h2 h1)
  exact ⟨z, hz, fun h => by rw [hz', hco]⟩

end GlobalTheory.CentralIdem
end

section
section
noncomputable section

namespace GlobalTheory.Pass.CentralStep

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem main : StepCentral := by
  intro _ D P i s
  classical
  have hcard : D.what₂.restRowsFiniteGroupCard = Nat.card (G0g D.nd) := by
    rw [D.nd.restN_card_levelGroup_eq, Nat.card_pi, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    change _ = ∏ _y : D.nd.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))
    rw [Finset.prod_const, Finset.card_univ, D.nd.card_PlG k]
  haveI : Finite (G0g D.nd) := Nat.finite_of_card_ne_zero (hcard ▸ D.what₂.restRowsFiniteGroupCard_pos.ne')
  have key : ∀ L : List (Σ k : Fin 2, D.nd.PlG k),
      let e := (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))).prod
      e * e = e ∧ ∀ z, e * z = z * e := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      obtain ⟨h1, h2⟩ := ih
      have hc := Subalgebra.mem_center_iff.1 (GlobalTheory.SeriesSupportTest.atPlace_central D a.1 a.2 _
        (D.ntypes.eSer_central a.1 (s a)))
      have hi : ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) * ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) =
          ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) := by
        rw [GlobalTheory.SeriesSupportTest.atPlace_eq, ← map_mul, D.ntypes.eSer_idem]
      simp only [List.map_cons, List.prod_cons]
      refine ⟨?_, fun z => ?_⟩
      · rw [mul_assoc, ← mul_assoc _ (ArithmeticCylinders.atPlace D a.1 a.2 _), hc, mul_assoc, h1, ← mul_assoc, hi]
      · rw [mul_assoc, h2, ← mul_assoc, ← hc, mul_assoc]
  obtain ⟨h1, h2⟩ := key Finset.univ.toList
  obtain ⟨ζ, hζ⟩ := P.zetaPrimitiveRoot i
  have hinj : Function.Injective (iotaO D.nd D.naut i) :=
    ((D.naut.iotaQC i).injective.comp (D.naut.iotaQ i).injective).comp (IsFractionRing.injective _ _)
  obtain ⟨z, hz, hz'⟩ := GlobalTheory.CentralIdem.card_mul_idem_from_center D i (G0g D.nd) _ h1 h2
    ⟨ζ, hcard ▸ hζ.map_of_injective hinj⟩
  refine ⟨⟨z, hz⟩, Finset.univ.toList, Finset.nodup_toList _, by simp, ?_⟩
  ext h
  rw [hcard]
  simpa [PairedCharacterCondition.mapCoef] using hz' h

end GlobalTheory.Pass.CentralStep

end
end

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_elements_from_idempotent_coeffs : StepCentral := by
  atlas_forward_decl GlobalTheory.Pass.CentralStep.main
end
