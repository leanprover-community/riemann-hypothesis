import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistLocalToGlobalStrictlyHenselianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfSubsingletonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInvOfDirectedUnionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceCechDescentIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfClosedCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceTensorPowerIntegralClosur

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem hInv_quot_inf (q : ℕ) [NeZero q] (R : Type) [CommRing R] (I J : Ideal R)
    (hq : IsUnit (q : R)) (hI : HInv q (R ⧸ I)) (hJ : HInv q (R ⧸ J))
    (hIJ : HInv q (R ⧸ (I ⊔ J))) : HInv q (R ⧸ (I ⊓ J)) := by
  set K := I ⊓ J with hK
  let f := Ideal.Quotient.mk K
  have hqA : IsUnit (q : R ⧸ K) := by simpa using hq.map f
  have hinf : Ideal.map f I ⊓ Ideal.map f J ≤ nilradical (R ⧸ K) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp hx.1
    obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp hx.2
    have h1 : b - a ∈ K := Ideal.Quotient.eq.mp hab
    have haJ : a ∈ J := by
      have := J.sub_mem hb h1.2
      simpa using this
    have : f a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ⟨ha, haJ⟩
    rw [this]
    exact (nilradical (R ⧸ K)).zero_mem
  have eI : (R ⧸ K) ⧸ Ideal.map f I ≃+* R ⧸ I := DoubleQuot.quotQuotEquivQuotOfLE inf_le_left
  have eJ : (R ⧸ K) ⧸ Ideal.map f J ≃+* R ⧸ J := DoubleQuot.quotQuotEquivQuotOfLE inf_le_right
  have eIJ : (R ⧸ K) ⧸ (Ideal.map f I ⊔ Ideal.map f J) ≃+* R ⧸ (I ⊔ J) :=
    (Ideal.quotEquivOfEq (Ideal.map_sup f I J).symm).trans
      (DoubleQuot.quotQuotEquivQuotOfLE (inf_le_left.trans le_sup_left))
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q (R ⧸ K) (Ideal.map f I) (Ideal.map f J) hinf hqA
    (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eI.symm hI) (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eJ.symm hJ)
    (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eIJ.symm hIJ)

theorem ringKrullDim_quot_sup_succ_le (R : Type) [CommRing R] (p J : Ideal R) [p.IsPrime]
    (hJ : ¬ J ≤ p) : ringKrullDim (R ⧸ (p ⊔ J)) + 1 ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨x, hxJ, hxp⟩ := Set.not_subset.mp hJ
  let g := Ideal.Quotient.mk p
  have hx0 : g x ≠ 0 := fun h => hxp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hnzd : g x ∈ nonZeroDivisors (R ⧸ p) := mem_nonZeroDivisors_of_ne_zero hx0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
  have hle : Ideal.span {g x} ≤ Ideal.map g (p ⊔ J) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem g (Ideal.mem_sup_right hxJ)
  have h2 : ringKrullDim ((R ⧸ p) ⧸ Ideal.map g (p ⊔ J)) ≤
      ringKrullDim ((R ⧸ p) ⧸ Ideal.span {g x}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
  have e : (R ⧸ p) ⧸ Ideal.map g (p ⊔ J) ≃+* R ⧸ (p ⊔ J) :=
    DoubleQuot.quotQuotEquivQuotOfLE le_sup_left
  have h3 : ringKrullDim (R ⧸ (p ⊔ J)) ≤ ringKrullDim ((R ⧸ p) ⧸ Ideal.map g (p ⊔ J)) :=
    ringKrullDim_le_of_surjective e.toRingHom e.surjective
  have h4 : ringKrullDim (R ⧸ (p ⊔ J)) + 1 ≤ ringKrullDim ((R ⧸ p) ⧸ Ideal.span {g x}) + 1 := by
    gcongr
    exact h3.trans h2
  exact h4.trans h1

theorem withBot_lt_of_add_one_le (a : WithBot ℕ∞) (d : ℕ) (h : a + 1 ≤ (d : WithBot ℕ∞)) :
    a < (d : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((d : ℕ∞)) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_le_coe] at h2
      simp at h2
    | coe n =>
      have h' : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by exact_mod_cast h
      have : n + 1 ≤ d := by exact_mod_cast h'
      have : n < d := by omega
      exact_mod_cast this

end GlobalTheory

namespace GlobalTheory

theorem hInv_of_domains_of_dim_lt : ∀ (q : ℕ) [NeZero q] (d : ℕ),
    (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) →
    (∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D) →
    ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R ≤ d → HInv q R := by
  intro q _ d hlt hdom R _ _ hq hd
  have key : ∀ s : Finset (Ideal R), (∀ p ∈ s, p.IsPrime) → HInv q (R ⧸ s.inf id) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      haveI : Subsingleton (R ⧸ (∅ : Finset (Ideal R)).inf id) :=
        Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton q _ inferInstance
    | insert p s hps ih =>
      intro hs
      have hp : p.IsPrime := hs p (Finset.mem_insert_self p s)
      have ihs := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
      rw [Finset.inf_insert, id]
      by_cases hJ : s.inf id ≤ p
      · rw [inf_eq_right.mpr hJ]; exact ihs
      · haveI : @Algebra.FiniteType ℤ (R ⧸ p) _ _ (Ring.toIntAlgebra _) := by
          convert (inferInstance : Algebra.FiniteType ℤ (R ⧸ p))
          all_goals first | rfl | exact Subsingleton.elim _ _
        haveI : @Algebra.FiniteType ℤ (R ⧸ (p ⊔ s.inf id)) _ _ (Ring.toIntAlgebra _) := by
          convert (inferInstance : Algebra.FiniteType ℤ (R ⧸ (p ⊔ s.inf id)))
          all_goals first | rfl | exact Subsingleton.elim _ _
        refine hInv_quot_inf q R p (s.inf id) hq ?_ ihs ?_
        · exact hdom (R ⧸ p) (by simpa using hq.map (Ideal.Quotient.mk p))
            ((ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective).trans hd)
        · refine hlt (R ⧸ (p ⊔ s.inf id)) (by simpa using hq.map (Ideal.Quotient.mk (p ⊔ s.inf id))) ?_
          refine withBot_lt_of_add_one_le _ d ?_
          exact (ringKrullDim_quot_sup_succ_le R p (s.inf id) hJ).trans
            ((ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective).trans hd)
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  have hN : hfin.toFinset.inf id = nilradical R := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset, minimalPrimes, Ideal.sInf_minimalPrimes]
    rfl
  have hred : HInv q (R ⧸ nilradical R) := by
    rw [← hN]
    refine key _ (fun p hp => ?_)
    rw [Set.Finite.mem_toFinset] at hp
    exact hp.1.1
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q R (nilradical R) (nilradical R) (by simp) hq hred hred (by rwa [sup_idem])

end GlobalTheory
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_domains_of_dim_lt : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → (∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D) → ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R ≤ d → HInv q R := by
  first | (exact @GlobalTheory.hInv_of_domains_of_dim_lt) | (exact GlobalTheory.hInv_of_domains_of_dim_lt) | (intros; apply GlobalTheory.hInv_of_domains_of_dim_lt  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_homotopy_invariance_tensor_power_integral_closure : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ k : ℕ, HInv q (PiTensorProduct D (fun _ : Fin (k + 1) => integralClosure D (AlgebraicClosure (FractionRing D)))) := by
  first | (exact @GlobalTheory.EtC.hInv_tensorPower_integralClosure) | (exact GlobalTheory.EtC.hInv_tensorPower_integralClosure) | (intros; apply GlobalTheory.EtC.hInv_tensorPower_integralClosure  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem GlobalTheory.homotopyInvariance_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) := by
  classical
  intro q _ A _ _ hq
  have hfg : ∀ d : ℕ, ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R := by
    intro d
    induction d with
    | zero =>
      intro R _ _ _ hd
      apply GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton
      by_contra h
      rw [not_subsingleton_iff_nontrivial] at h
      exact absurd hd (not_lt.mpr (by exact_mod_cast ringKrullDim_nonneg_of_nontrivial))
    | succ d ih =>
      intro R _ _ hR hd
      have hdom : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D := by
        intro D _ _ _ hD hDd
        refine GlobalTheory.T.etaleHomotopyInvariance_cechDescent_integral q D (integralClosure D (AlgebraicClosure (FractionRing D))) inferInstance ?_ hD (GlobalTheory.T.etale_homotopy_invariance_tensor_power_integral_closure q d ih D hD hDd)
        intro x hx
        have hinj : Function.Injective (algebraMap D (AlgebraicClosure (FractionRing D))) := by
          rw [IsScalarTower.algebraMap_eq D (FractionRing D) (AlgebraicClosure (FractionRing D))]
          exact (algebraMap (FractionRing D) _).injective.comp (IsFractionRing.injective D (FractionRing D))
        have h0 : x = 0 := by
          apply hinj
          have := congrArg Subtype.val (RingHom.mem_ker.mp hx)
          simpa using this
        rw [h0]; exact zero_mem _
      refine GlobalTheory.T.etaleHomotopyInvariantTwists_of_domains_of_dim_lt q d ih hdom R hR ?_
      revert hd
      induction ringKrullDim R with
      | bot => intro _; exact bot_le
      | coe n =>
        intro h
        have h' : n < ((d + 1 : ℕ) : ℕ∞) := WithBot.coe_lt_coe.mp h
        exact WithBot.coe_le_coe.mpr (Order.le_of_lt_add_one (by simpa using h'))
  let S : Finset A → Subalgebra ℤ A := fun s => Algebra.adjoin ℤ (insert (↑(hq.unit⁻¹) : A) (s : Set A))
  have hmono : Monotone S := fun s t hst => Algebra.adjoin_mono (Set.insert_subset_insert (by exact_mod_cast hst))
  have hcov : ∀ a, ∃ s, a ∈ S s := fun a => ⟨{a}, Algebra.subset_adjoin (by simp)⟩
  have hunit : ∀ s, IsUnit (q : S s) := by
    intro s
    have hm : (↑(hq.unit⁻¹) : A) ∈ S s := Algebra.subset_adjoin (Set.mem_insert _ _)
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hm⟩, ?_⟩
    apply Subtype.ext
    simp
  have hinv : ∀ s, HInv q (S s) := by
    intro s
    have : Algebra.FiniteType ℤ (S s) := by
      have hfg' : (S s).FG := by
        have : (insert (↑(hq.unit⁻¹) : A) (s : Set A)) = ((insert (↑(hq.unit⁻¹) : A) s : Finset A) : Set A) := by simp
        rw [show S s = Algebra.adjoin ℤ (insert (↑(hq.unit⁻¹) : A) (s : Set A)) from rfl, this]
        exact Subalgebra.fg_adjoin_finset _
      exact Subalgebra.fg_iff_finiteType _ |>.mp hfg'
    have hlt := GlobalTheory.ringKrullDim_lt_top_of_essFiniteType (S s)
    obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (S s) ≤ d := by
      revert hlt
      induction ringKrullDim (S s) with
      | bot => intro _; exact ⟨0, bot_le⟩
      | coe n =>
        intro h
        induction n with
        | top => exact absurd h (lt_irrefl _)
        | coe m => exact ⟨m, le_rfl⟩
    exact hfg (d + 1) (S s) (hunit s) (lt_of_le_of_lt hd (by exact_mod_cast Nat.lt_succ_self d))
  intro i
  exact GlobalTheory.T.hInv_of_directed_union_subalgebras q A (Finset A) S hmono hcov hunit hinv i
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homotopyInvariance_tateTwist_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) := by
  first | (exact @GlobalTheory.homotopyInvariance_strictlyHenselian) | (exact GlobalTheory.homotopyInvariance_strictlyHenselian) | (intros; apply GlobalTheory.homotopyInvariance_strictlyHenselian  <;> assumption)
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace GlobalTheory.PolynomialPushoutEquivalence

theorem eqv_iso (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := by
  intro n

  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem eqv_comp (R : Type) [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n

  have e : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext (pull_comp R f g F n)
  rw [e]
  exact (hf n).comp (hg n)

theorem isPushout_poly {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    IsPushout (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (Polynomial.mapRingHom φ)) (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)) := by

  let _ : Algebra A B := φ.toAlgebra
  let _ : Algebra (Polynomial A) (Polynomial B) := Polynomial.algebra A B
  exact CommRingCat.isPushout_of_isPushout A (Polynomial A) B (Polynomial B)

theorem main (q : ℕ) (A : Type) [CommRing A] (i : ℤ) (A' : Type) [CommRing A']
    (s : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A))
    (h : Eqv (ZMod q) (E := sp (Polynomial A')) (spMap Polynomial.C) (tw q i)) :
    Eqv (ZMod q) (sch.map (pullback.map
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 (Spec (CommRingCat.of A))) s
      (𝟙 (Spec (CommRingCat.of A))) s (Spec.map (CommRingCat.ofHom Polynomial.C)) (𝟙 _) (𝟙 _)
      (by simp) (by simp))) (tw q i) := by

  set φ : A →+* A' := (Spec.preimage s).hom with hφ
  have hs : s = Spec.map (CommRingCat.ofHom φ) := by simp [φ]

  have sq : IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ)))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A' →+* Polynomial A')))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 (Spec (CommRingCat.of A))) s := by
    rw [Category.comp_id, hs]
    exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_poly φ)

  have e : pullback.map
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 (Spec (CommRingCat.of A))) s
      (𝟙 (Spec (CommRingCat.of A))) s (Spec.map (CommRingCat.ofHom Polynomial.C)) (𝟙 _) (𝟙 _)
      (by simp) (by simp) =
      sq.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A' →+* Polynomial A')) ≫
        inv (pullback.snd (𝟙 (Spec (CommRingCat.of A))) s) := by
    rw [← Category.assoc, IsIso.eq_comp_inv, sq.isoPullback_inv_snd]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  rw [e, Functor.map_comp, Functor.map_comp]
  exact eqv_comp _ _ _ _ (eqv_iso _ _ _) (eqv_comp _ _ _ _ h (eqv_iso _ _ _))

end GlobalTheory.PolynomialPushoutEquivalence

end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.HomotopyInv

variable {R : Type} [CommRing R]

theorem eqv_comp {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv R} (hf : Eqv R f F) (hg : Eqv R g F) :
    Eqv R (f ≫ g) F := fun n => by
  have h : (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n :=
    funext fun x => pull_comp R f g F n x
  rw [h]
  exact (hf n).comp (hg n)

attribute [local instance] Polynomial.algebra

theorem eqv_baseChange (q : ℕ) (A : Type) [CommRing A] (i : ℤ) (A' : Type) [CommRing A']
    (s : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A))
    (h : Eqv _ (spMap (Polynomial.C : A' →+* Polynomial A')) (tw q i)) :
    Eqv _ (sch.map (pullback.map (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 _) s (𝟙 _) s
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) := by
  first
  | exact @_root_.GlobalTheory.PolynomialPushoutEquivalence.main
  | exact _root_.GlobalTheory.PolynomialPushoutEquivalence.main
  | (apply _root_.GlobalTheory.PolynomialPushoutEquivalence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialPushoutEquivalence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialPushoutEquivalence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialPushoutEquivalence.main ..)

theorem homotopy_invariance_etale : GlobalTheory.EtC.C4 := by
  intro q _ A _ hq i
  have hqΓ : IsUnit ((q : ℕ) : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  refine GlobalTheory.T.etC_b3 q (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))
    (𝟙 (Spec (CommRingCat.of A))) hqΓ i ?_
  intro A' _ s hA'
  refine eqv_baseChange q A i A' s ?_
  have hq' : IsUnit (q : A') := by simpa using hq.map (Spec.preimage s).hom
  exact GlobalTheory.T.homotopyInvariance_tateTwist_strictlyHenselian q A' hA' hq' i

end GlobalTheory.EtC.HomotopyInv
end
end
