import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentAbsIntClosedLocalDomaiStatement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsLocalRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralStrictHenselianAcyclicFinitary

section
open GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem laurentPi_bijective : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)], Function.Bijective (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) := by
  intro n B _
  have hap : ∀ (x : LaurentPolynomial (∀ j, B j)) k, (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) x k = laurentMap (Pi.evalRingHom B k) x := fun _ _ => rfl
  constructor
  · rw [injective_iff_map_eq_zero]
    intro p hp
    have hc : p.coeff = 0 := by
      ext m j
      have h1 := congrArg (fun r : ∀ j, LaurentPolynomial (B j) => (r j).coeff m) hp
      simp only [hap, Pi.zero_apply, laurentMap_coeff, Finsupp.mapRange_apply] at h1
      simpa using h1
    exact AddMonoidAlgebra.ext hc
  · intro F
    have hsub : ∀ j (q : LaurentPolynomial (B j)), Pi.single j q ∈ (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)).range := by
      intro j q
      induction q using LaurentPolynomial.induction_on' with
      | add p r hp hr =>
        rw [Pi.single_add]; exact Subring.add_mem _ hp hr
      | C_mul_T m a =>
        refine ⟨LaurentPolynomial.C (Pi.single j a) * LaurentPolynomial.T m, ?_⟩
        funext k
        simp only [hap, map_mul, laurentMap_C, laurentMap_T, Pi.evalRingHom_apply]
        by_cases hk : k = j
        · subst hk; simp
        · simp [Pi.single_eq_of_ne hk]
    rw [← Finset.univ_sum_single F]
    obtain ⟨p, hp⟩ := Subring.sum_mem _ (fun j (_ : j ∈ Finset.univ) => hsub j (F j))
    exact ⟨p, hp⟩

end GlobalTheory.EtC.GmStep
end

section
open GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_pi_bijective : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)], Function.Bijective (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) := by
  first | (exact @GlobalTheory.EtC.GmStep.laurentPi_bijective) | (exact GlobalTheory.EtC.GmStep.laurentPi_bijective) | (intros; apply GlobalTheory.EtC.GmStep.laurentPi_bijective  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section
namespace GlobalTheory.EtC.GmStep.KillColim

theorem laurentMap_coeff_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (p : LaurentPolynomial A) (m : ℤ) : (laurentMap f p).coeff m = f (p.coeff m) := by
  rw [laurentMap_coeff, Finsupp.mapRange_apply]

theorem laurentMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (laurentMap g).comp (laurentMap f) = laurentMap (g.comp f) := by
  refine RingHom.ext fun p => ?_
  · apply AddMonoidAlgebra.coeff_injective
    ext m
    simp [laurentMap_coeff_apply]

theorem laurentMap_id (A : Type) [CommRing A] : laurentMap (RingHom.id A) = RingHom.id _ := by
  refine RingHom.ext fun p => ?_
  · apply AddMonoidAlgebra.coeff_injective
    ext m
    simp [laurentMap_coeff_apply]

theorem laurentMap_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : Function.Injective (laurentMap f) := by
  intro p r h
  apply AddMonoidAlgebra.coeff_injective
  ext m
  apply hf
  rw [← laurentMap_coeff_apply, ← laurentMap_coeff_apply, h]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Functor.map_comp, ← Spec.map_comp]; rfl

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]

def diag : Finset S ⥤ CommRingCat.{0} where
  obj t := CommRingCat.of (LaurentPolynomial (Algebra.adjoin A (t : Set S)))
  map {t u} h := CommRingCat.ofHom
    (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.2 h.le))).toRingHom)
  map_id t := by
    ext1
    refine (Eq.trans ?_ (laurentMap_id _)).trans rfl
    congr 1
  map_comp f g := by
    ext1
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [laurentMap_comp]
    rfl

def cocone : Cocone (diag A S) where
  pt := CommRingCat.of (LaurentPolynomial S)
  ι := { app := fun t => CommRingCat.ofHom (laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom)
         naturality := fun t u h => by
           ext1
           simp only [diag, Functor.const_obj_map, Category.comp_id, CommRingCat.hom_comp,
             CommRingCat.hom_ofHom]
           rw [laurentMap_comp]
           rfl }

theorem cocone_ι_apply (t : Finset S) (p) :
    ((cocone A S).ι.app t).hom p = laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom p := rfl

theorem val_CT (t : Finset S) (a : Algebra.adjoin A (t : Set S)) (n : ℤ) :
    laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom (LaurentPolynomial.C a * LaurentPolynomial.T n) =
      LaurentPolynomial.C (a : S) * LaurentPolynomial.T n := by
  rw [map_mul, laurentMap_C, laurentMap_T]
  rfl

theorem ι_map {t u : Finset S} (h : t ⟶ u) (p : LaurentPolynomial (Algebra.adjoin A (t : Set S))) :
    laurentMap (Algebra.adjoin A (u : Set S)).val.toRingHom (((diag A S).map h).hom p) =
      ((cocone A S).ι.app t).hom p := by
  show ((diag A S).map h ≫ (cocone A S).ι.app u).hom p = _
  rw [(cocone A S).w]

theorem lm_val_incl {t u : Finset S} (h : (t : Set S) ⊆ u) (p : LaurentPolynomial (Algebra.adjoin A (t : Set S))) :
    laurentMap (Algebra.adjoin A (u : Set S)).val.toRingHom
        (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom p) =
      laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom p := by
  apply AddMonoidAlgebra.coeff_injective
  ext m
  simp only [laurentMap_coeff_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_val,
    Subalgebra.coe_inclusion]

theorem exists_finset_adjoin_laurent_preimage (x : LaurentPolynomial S) : ∃ (t : Finset S) (y : LaurentPolynomial (Algebra.adjoin A (t : Set S))),
    x = laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom y := by
  classical
  induction x using LaurentPolynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨t, y, rfl⟩ := hp
    obtain ⟨t', y', rfl⟩ := hr
    have h1 : (t : Set S) ⊆ ((t ⊔ t' : Finset S) : Set S) := Finset.coe_subset.2 le_sup_left
    have h2 : (t' : Set S) ⊆ ((t ⊔ t' : Finset S) : Set S) := Finset.coe_subset.2 le_sup_right
    refine ⟨t ⊔ t', laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono h1)).toRingHom y +
      laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono h2)).toRingHom y', ?_⟩
    rw [map_add, lm_val_incl A S h1, lm_val_incl A S h2]
  | C_mul_T n a =>
    have hmem : a ∈ Algebra.adjoin A (({a} : Finset S) : Set S) :=
      Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self a))
    refine ⟨{a}, LaurentPolynomial.C (⟨a, hmem⟩ : Algebra.adjoin A (({a} : Finset S) : Set S)) *
      LaurentPolynomial.T n, ?_⟩
    rw [val_CT]

theorem laurent_adjoin_eq_of_image_eq [DecidableEq S] {i j : Finset S} (xi : LaurentPolynomial (Algebra.adjoin A (i : Set S)))
    (xj : LaurentPolynomial (Algebra.adjoin A (j : Set S)))
    (h : laurentMap (Algebra.adjoin A (i : Set S)).val.toRingHom xi =
      laurentMap (Algebra.adjoin A (j : Set S)).val.toRingHom xj) :
    laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono
        (Finset.coe_subset.2 (le_sup_left : i ≤ i ⊔ j)))).toRingHom xi =
      laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono
        (Finset.coe_subset.2 (le_sup_right : j ≤ i ⊔ j)))).toRingHom xj := by
  refine laurentMap_injective (Algebra.adjoin A ((i ⊔ j : Finset S) : Set S)).val.toRingHom
    Subtype.val_injective ?_
  exact (lm_val_incl A S (Finset.coe_subset.2 (le_sup_left : i ≤ i ⊔ j)) xi).trans
    (h.trans (lm_val_incl A S (Finset.coe_subset.2 (le_sup_right : j ≤ i ⊔ j)) xj).symm)

def coconeIsColimit : IsColimit (cocone A S) := by
  classical
  haveI : ReflectsColimitsOfShape (Finset S) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (cocone A S)) ?_ ?_)
  · intro x
    exact exists_finset_adjoin_laurent_preimage A S x
  · intro i j xi xj h
    exact ⟨i ⊔ j, homOfLE le_sup_left, homOfLE le_sup_right, laurent_adjoin_eq_of_image_eq A S xi xj h⟩

end GlobalTheory.EtC.GmStep.KillColim
end

namespace GlobalTheory.EtC.GmStep.KillColim

theorem val_laurent (A S : Type) [CommRing A] [CommRing S] [Algebra A S] (t : Finset S) :
    (laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom).comp
        (laurentMap (algebraMap A (Algebra.adjoin A (t : Set S)))) = laurentMap (algebraMap A S) := by
  rw [laurentMap_comp]
  congr 1

theorem incl_laurent (A S : Type) [CommRing A] [CommRing S] [Algebra A S] {t u : Finset S}
    (h : (t : Set S) ⊆ u) :
    (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono (R := A) h)).toRingHom).comp
        (laurentMap (algebraMap A (Algebra.adjoin A (t : Set S)))) =
      laurentMap (algebraMap A (Algebra.adjoin A (u : Set S))) := by
  rw [laurentMap_comp]
  congr 1

theorem kill_colim : ∀ (q : ℕ) (A S : Type) [CommRing A] [CommRing S] [Algebra A S], IsUnit (q : A) →
    ∀ (n i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) n i),
    pull _ (spMap (laurentMap (algebraMap A S))) _ _ x = 0 →
    ∃ t : Finset S, pull _ (spMap (laurentMap (algebraMap A (Algebra.adjoin A (t : Set S))))) _ _ x = 0 := by
  intro q A S _ _ _ hq n i x hx
  classical
  have hu : IsUnit (q : (diag A S).obj ∅) := by
    have := hq.map ((LaurentPolynomial.C : Algebra.adjoin A ((∅ : Finset S) : Set S) →+* _).comp
      (algebraMap A _))
    rw [map_natCast] at this
    exact this
  have e1 : spMap ((cocone A S).ι.app ∅).hom ≫
      spMap (laurentMap (algebraMap A (Algebra.adjoin A ((∅ : Finset S) : Set S)))) =
      spMap (laurentMap (algebraMap A S)) :=
    (spMap_comp' _ (laurentMap (Algebra.adjoin A ((∅ : Finset S) : Set S)).val.toRingHom)).trans
      (congrArg spMap (val_laurent A S ∅))
  have hy0 : pull _ (spMap ((cocone A S).ι.app ∅).hom) _ _
      (pull _ (spMap (laurentMap (algebraMap A (Algebra.adjoin A ((∅ : Finset S) : Set S))))) _ _ x) = 0 :=
    (pull_comp _ _ _ _ _ x).symm.trans ((congrArg (fun g => pull _ g (tw q i) n x) e1).trans hx)
  obtain ⟨k, f, hk⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (diag A S) (cocone A S) (coconeIsColimit A S) n i).2 ∅ _ hu hy0
  have e2 : spMap ((diag A S).map f).hom ≫
      spMap (laurentMap (algebraMap A (Algebra.adjoin A ((∅ : Finset S) : Set S)))) =
      spMap (laurentMap (algebraMap A (Algebra.adjoin A (k : Set S)))) :=
    (spMap_comp' _ (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono (R := A)
      (Finset.coe_subset.2 f.le))).toRingHom)).trans
      (congrArg spMap (incl_laurent A S (Finset.coe_subset.2 f.le)))
  exact ⟨k, (congrArg (fun g => pull _ g (tw q i) n x) e2).symm.trans ((pull_comp _ _ _ _ _ x).trans hk)⟩

end GlobalTheory.EtC.GmStep.KillColim
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_class_vanishes_finitely_generated_subalgebra : ∀ (q : ℕ) (A S : Type) [CommRing A] [CommRing S] [Algebra A S], IsUnit (q : A) → ∀ (n i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) n i), pull _ (spMap (laurentMap (algebraMap A S))) _ _ x = 0 → ∃ t : Finset S, pull _ (spMap (laurentMap (algebraMap A (Algebra.adjoin A (t : Set S))))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.GmStep.KillColim.kill_colim) | (exact GlobalTheory.EtC.GmStep.KillColim.kill_colim) | (intros; apply GlobalTheory.EtC.GmStep.KillColim.kill_colim  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section
namespace GlobalTheory.EtC.GmKill

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Functor.map_comp, ← Spec.map_comp]; rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (sp A) := by
  change sch.map (Spec.map (𝟙 _)) = _
  rw [Spec.map_id, CategoryTheory.Functor.map_id]

theorem subsingleton_of_ringEquiv (q : ℕ) (d i : ℤ) {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    [Subsingleton (Ht q (sp A) d i)] : Subsingleton (Ht q (sp B) d i) := by
  constructor
  intro x y
  have h : ∀ z : Ht q (sp B) d i,
      pull _ (spMap (e : A →+* B)) _ _ (pull _ (spMap (e.symm : B →+* A)) _ _ z) = z := by
    intro z
    rw [← pull_comp, spMap_comp]
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by ext; simp
    rw [this, spMap_id, pull_id]
  rw [← h x, ← h y, Subsingleton.elim (pull _ (spMap (e.symm : B →+* A)) _ _ x) (pull _ _ _ _ y)]

theorem subsingleton_prod (q : ℕ) (d i : ℤ) (A B : Type) [CommRing A] [CommRing B]
    [Subsingleton (Ht q (sp A) d i)] [Subsingleton (Ht q (sp B) d i)] :
    Subsingleton (Ht q (sp (A × B)) d i) := by
  constructor
  intro x y
  exact (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A B d i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

theorem subsingleton_of_subsingleton_ring (q : ℕ) (d i : ℤ) (A : Type) [CommRing A] [Subsingleton A] :
    Subsingleton (Ht q (sp A) d i) := by
  constructor
  intro a b
  obtain ⟨x, hx⟩ := (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A A d i).2 (a, b)
  have hfs : RingHom.fst A A = RingHom.snd A A := RingHom.ext fun _ => Subsingleton.elim _ _
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [← h1, ← h2, hfs]

def piFinSuccRingEquiv (n : ℕ) (B : Fin (n + 1) → Type) [∀ j, CommRing (B j)] :
    (∀ j, B j) ≃+* B 0 × ∀ j : Fin n, B j.succ where
  toFun f := (f 0, fun j => f j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_mul' f g := rfl
  map_add' f g := rfl

theorem subsingleton_pi (q : ℕ) (d i : ℤ) : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)],
    (∀ j, Subsingleton (Ht q (sp (B j)) d i)) → Subsingleton (Ht q (sp (∀ j, B j)) d i) := by
  intro n
  induction n with
  | zero =>
    intro B _ _
    exact subsingleton_of_subsingleton_ring q d i _
  | succ n ih =>
    intro B _ hB
    have := ih (fun j => B j.succ) (fun j => hB j.succ)
    have := hB 0
    have := subsingleton_prod q d i (B 0) (∀ j : Fin n, B j.succ)
    exact subsingleton_of_ringEquiv q d i (piFinSuccRingEquiv n B).symm

theorem isIntegral_pi {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x :=
  _root_.GlobalTheory.IntegralPi.main x hx

theorem isLocalRing_closure (A : Type) [CommRing A] [HenselianLocalRing A] (P : Ideal A) [P.IsPrime] :
    IsLocalRing (integralClosure (A ⧸ P) (AlgebraicClosure (FractionRing (A ⧸ P)))) := by
  haveI : IsLocalRing (A ⧸ P) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  haveI : HenselianLocalRing (A ⧸ P) := GlobalTheory.henselianLocalRing_of_finite A (A ⧸ P)
  exact GlobalTheory.EtC.Psi.isLocalRing_integralClosure _ _

theorem main : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ (n i : ℤ), 2 ≤ n → ∀ x : Ht q (sp (LaurentPolynomial A)) n i,
  ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), Module.Finite A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧
    pull _ (spMap (laurentMap (algebraMap A A'))) _ _ x = 0 := by
  classical
  intro q _ A _ _ hA hq n i hn x
  obtain ⟨hHens, -⟩ := hA
  let ι := {p : Ideal A // p ∈ minimalPrimes A}
  haveI : Finite ι := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  letI : Fintype ι := Fintype.ofFinite ι
  let σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let P : Fin (Fintype.card ι) → Ideal A := fun k => (σ k).1
  haveI hP : ∀ k, (P k).IsPrime := fun k => (σ k).2.1.1
  let T : Fin (Fintype.card ι) → Type := fun k =>
    integralClosure (A ⧸ P k) (AlgebraicClosure (FractionRing (A ⧸ P k)))
  letI : ∀ k, Algebra A (T k) := fun k => ((algebraMap (A ⧸ P k) (T k)).comp (Ideal.Quotient.mk (P k))).toAlgebra
  have hint : ∀ k (s : T k), IsIntegral A s := by
    intro k s
    have h : ((algebraMap (A ⧸ P k) (T k)).comp (Ideal.Quotient.mk (P k))).IsIntegral :=
      RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
        (fun s => Algebra.IsIntegral.isIntegral s)
    exact h s
  haveI : Algebra.IsIntegral A (∀ k, T k) := ⟨fun s => isIntegral_pi s (fun k => hint k (s k))⟩
  have hS : Subsingleton (Ht q (sp (LaurentPolynomial (∀ k, T k))) n i) := by
    have hT : ∀ k, Subsingleton (Ht q (sp (LaurentPolynomial (T k))) n i) := by
      intro k
      haveI := isLocalRing_closure A (P k)
      have hqk : IsUnit (q : T k) := by simpa using hq.map (algebraMap A (T k))
      exact (GlobalTheory.T.tateTwistCohomology_laurent_absIntClosedLocalDomain q (T k) (GlobalTheory.aic_integralClosure_algebraicClosure (A ⧸ P k)) hqk n i).1 hn
    haveI := subsingleton_pi q n i _ (fun k => LaurentPolynomial (T k)) hT
    exact subsingleton_of_ringEquiv q n i (RingEquiv.ofBijective _ (GlobalTheory.T.laurent_pi_bijective _ T)).symm
  have hx0 : pull _ (spMap (laurentMap (algebraMap A (∀ k, T k)))) _ _ x = 0 := Subsingleton.elim _ _
  obtain ⟨t, ht⟩ := GlobalTheory.T.laurent_class_vanishes_finitely_generated_subalgebra q A (∀ k, T k) hq n i x hx0
  refine ⟨Algebra.adjoin A (t : Set (∀ k, T k)), inferInstance, inferInstance,
    GlobalTheory.EtC.IntAcyc.finite_finDiag A (∀ k, T k) t, ?_, ht⟩
  intro a ha
  rw [RingHom.mem_ker] at ha
  have ha' : algebraMap A (∀ k, T k) a = 0 := by
    have := congrArg Subtype.val ha
    exact this
  have hmem : ∀ k, a ∈ P k := by
    intro k
    have h1 : algebraMap A (T k) a = 0 := congrFun ha' k
    have h2 : algebraMap (A ⧸ P k) (AlgebraicClosure (FractionRing (A ⧸ P k))) (Ideal.Quotient.mk (P k) a) = 0 :=
      congrArg Subtype.val h1
    rw [IsScalarTower.algebraMap_eq (A ⧸ P k) (FractionRing (A ⧸ P k)) (AlgebraicClosure (FractionRing (A ⧸ P k))),
      RingHom.comp_apply] at h2
    have h3 := (IsFractionRing.injective (A ⧸ P k) (FractionRing (A ⧸ P k)))
      ((algebraMap (FractionRing (A ⧸ P k)) _).injective (h2.trans (map_zero _).symm) |>.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.1 h3
  change a ∈ (⊥ : Ideal A).radical
  rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
  intro p hp
  obtain ⟨k, hk⟩ := σ.surjective ⟨p, hp⟩
  have := hmem k
  simp only [P, hk] at this
  exact this

end GlobalTheory.EtC.GmKill

end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_cohomology_finite_killing : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ (n i : ℤ), 2 ≤ n → ∀ x : Ht q (sp (LaurentPolynomial A)) n i,
  ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), Module.Finite A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧
    pull _ (spMap (laurentMap (algebraMap A A'))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.GmKill.main) | (exact GlobalTheory.EtC.GmKill.main) | (intros; apply GlobalTheory.EtC.GmKill.main  <;> assumption)
end
