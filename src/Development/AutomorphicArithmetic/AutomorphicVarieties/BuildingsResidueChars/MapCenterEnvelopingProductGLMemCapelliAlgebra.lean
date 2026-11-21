import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.HasUnivOfStep
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HarishChandraProjQuantumDetEqProd
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Vieta

section
theorem UpperTheory.center_tensorProduct_le_sup_map_center :
    ∀ (A B : Type) [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B], Subalgebra.center ℂ (TensorProduct ℂ A B) ≤ (Subalgebra.center ℂ A).map (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorProduct ℂ A B) ⊔ (Subalgebra.center ℂ B).map (Algebra.TensorProduct.includeRight : B →ₐ[ℂ] TensorProduct ℂ A B) := by
  intro A B _ _ _ _ z hz
  have hz' := Subalgebra.mem_center_iff.1 hz
  have h1 : z ∈ Subalgebra.centralizer ℂ
      ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorProduct ℂ A B).range :
        Set (TensorProduct ℂ A B)) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g _
    exact hz' g
  rw [Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct] at h1
  obtain ⟨w, hw⟩ := h1
  have hw' : Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (AlgHom.id ℂ B) w = z := hw
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (AlgHom.id ℂ B)) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (R := ℂ) (M := B)
      (Subalgebra.center ℂ A).val.toLinearMap Subtype.val_injective
    exact h
  have h2 : w ∈ Subalgebra.centralizer ℂ
      ((Algebra.TensorProduct.includeRight :
        B →ₐ[ℂ] TensorProduct ℂ (Subalgebra.center ℂ A) B).range :
        Set (TensorProduct ℂ (Subalgebra.center ℂ A) B)) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g _
    apply hinj
    rw [map_mul, map_mul, hw']
    exact hz' _
  rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct] at h2
  obtain ⟨v, hv⟩ := h2
  have hv' : Algebra.TensorProduct.map (AlgHom.id ℂ (Subalgebra.center ℂ A))
      (Subalgebra.center ℂ B).val v = w := hv
  rw [← hw', ← hv']
  clear hv' hv hw' hw hz' hz
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact Subalgebra.zero_mem _
  | add x y hx hy => rw [map_add, map_add]; exact Subalgebra.add_mem _ hx hy
  | tmul a b =>
    have e : Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (AlgHom.id ℂ B)
        (Algebra.TensorProduct.map (AlgHom.id ℂ (Subalgebra.center ℂ A))
          (Subalgebra.center ℂ B).val (a ⊗ₜ[ℂ] b)) =
        (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorProduct ℂ A B) (a : A) *
        (Algebra.TensorProduct.includeRight : B →ₐ[ℂ] TensorProduct ℂ A B) (b : B) := by
      simp
    rw [e]
    exact Algebra.mul_mem_sup ⟨a, a.2, rfl⟩ ⟨b, b.2, rfl⟩
end

section
open UpperTheory.V.Af.CuspFin

private theorem glRel_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) : Formalism.REAL.GlRel (fun a b => f (X a b)) := by
  intro i j k l
  have := congrArg f (h i j k l)
  simpa [apply_ite f] using this

private theorem comm_LR {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (a : A) (b : B) :
    Commute ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorProduct ℂ A B) a)
      ((Algebra.TensorProduct.includeRight : B →ₐ[ℂ] TensorProduct ℂ A B) b) := by
  simp [Commute, SemiconjBy]

private theorem map_cap {ι κ A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : ι → Fin n → Fin n → A) (F : κ → Fin n → Fin n → B) (e : ι → κ)
    (h : ∀ v, F (e v) = fun i j => f (E v i j)) : (capAlg E).map f ≤ capAlg F := by
  unfold capAlg
  rw [AlgHom.map_adjoin]
  refine Algebra.adjoin_mono ?_
  rintro _ ⟨_, ⟨v, u, rfl⟩, rfl⟩
  exact ⟨e v, u, by rw [map_qdet, h]⟩

private theorem map_gen {ι κ A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : ι → Fin n → Fin n → A) (F : κ → Fin n → Fin n → B) (e : ι → κ)
    (hg : Algebra.adjoin ℂ {z | ∃ v i j, z = E v i j} = ⊤)
    (h : ∀ v, F (e v) = fun i j => f (E v i j)) (a : A) :
    f a ∈ Algebra.adjoin ℂ {z | ∃ v i j, z = F v i j} := by
  have : (Algebra.adjoin ℂ {z | ∃ v i j, z = E v i j}).map f ≤ Algebra.adjoin ℂ {z | ∃ v i j, z = F v i j} := by
    rw [AlgHom.map_adjoin]
    refine Algebra.adjoin_mono ?_
    rintro _ ⟨_, ⟨v, i, j, rfl⟩, rfl⟩
    exact ⟨e v, i, j, by rw [h]⟩
  exact this ⟨a, by rw [hg]; trivial, rfl⟩

theorem UpperTheory.capelliAlgebra_map_of_glRelations :
    ∀ (n : ℕ) (ι κ : Type), UpperTheory.V.Af.CuspFin.HasUniv ι n → UpperTheory.V.Af.CuspFin.HasUniv κ n → UpperTheory.V.Af.CuspFin.HasUniv (ι ⊕ κ) n := by
  rintro n ι κ ⟨A, _, _, E, hE⟩ ⟨B, _, _, F, hF⟩
  let L : A →ₐ[ℂ] TensorProduct ℂ A B := Algebra.TensorProduct.includeLeft
  let R : B →ₐ[ℂ] TensorProduct ℂ A B := Algebra.TensorProduct.includeRight
  let G : ι ⊕ κ → Fin n → Fin n → TensorProduct ℂ A B :=
    Sum.elim (fun v i j => L (E v i j)) (fun v i j => R (F v i j))
  refine ⟨TensorProduct ℂ A B, inferInstance, inferInstance, G, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rintro (v | v)
    · exact glRel_map L (hE.rel.1 v)
    · exact glRel_map R (hF.rel.1 v)
  · rintro (v | v) (w | w) hvw i j k l
    · exact (hE.rel.2 v w (fun h => hvw (congrArg _ h)) i j k l).map L
    · exact comm_LR _ _
    · exact (comm_LR _ _).symm
    · exact (hF.rel.2 v w (fun h => hvw (congrArg _ h)) i j k l).map R
  · refine eq_top_iff.2 fun z hz => ?_
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul a b =>
      have : a ⊗ₜ[ℂ] b = L a * R b := by simp [L, R]
      rw [this]
      exact mul_mem (map_gen L E G Sum.inl hE.gen (fun _ => rfl) a) (map_gen R F G Sum.inr hF.gen (fun _ => rfl) b)
    | add x y hx hy => exact add_mem hx hy
  · intro C _ _ H hH
    obtain ⟨f, hf⟩ := hE.univ C (fun v => H (Sum.inl v))
      ⟨fun v => hH.1 _, fun v w hvw => hH.2 _ _ fun h => hvw (Sum.inl_injective h)⟩
    obtain ⟨g, hg⟩ := hF.univ C (fun v => H (Sum.inr v))
      ⟨fun v => hH.1 _, fun v w hvw => hH.2 _ _ fun h => hvw (Sum.inr_injective h)⟩
    have hc : ∀ a b, Commute (f a) (g b) := by
      intro a b
      have ha := map_gen f E (fun v => H (Sum.inl v)) id hE.gen (fun v => by funext i j; simp [hf]) a
      have hb := map_gen g F (fun v => H (Sum.inr v)) id hF.gen (fun v => by funext i j; simp [hg]) b
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb ?_
      rintro _ ⟨w, k, l, rfl⟩
      refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha ?_).symm
      rintro _ ⟨v, i, j, rfl⟩
      exact hH.2 _ _ Sum.inr_ne_inl _ _ _ _
    refine ⟨Algebra.TensorProduct.lift f g hc, ?_⟩
    rintro (v | v) i j
    · simp [G, L, hf]
    · simp [G, R, hg]
  · refine (UpperTheory.center_tensorProduct_le_sup_map_center A B).trans (sup_le ?_ ?_)
    · exact (Subalgebra.map_mono hE.centre).trans (map_cap L E G Sum.inl fun _ => rfl)
    · exact (Subalgebra.map_mono hF.centre).trans (map_cap R F G Sum.inr fun _ => rfl)
end

section
open MvPolynomial in
theorem UpperTheory.symmetricSubalgebra_le_adjoin_range_prod_C_add_X_complex :
    ∀ n : ℕ, MvPolynomial.symmetricSubalgebra (Fin n) ℂ ≤ Algebra.adjoin ℂ (Set.range fun u : ℂ => ∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k : MvPolynomial (Fin n) ℂ)) := by
  intro n
  set S := Algebra.adjoin ℂ (Set.range fun u : ℂ => ∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k : MvPolynomial (Fin n) ℂ)) with hS
  have hv : ∀ u : ℂ, ∏ k : Fin n, (C u + X k : MvPolynomial (Fin n) ℂ)
      = ∑ j ∈ Finset.range (n + 1), u ^ (n - j) • esymm (Fin n) ℂ j := by
    intro u
    have h := congrArg (Polynomial.eval (C u : MvPolynomial (Fin n) ℂ))
      (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n))
    simp only [Polynomial.eval_prod, Polynomial.eval_finset_sum, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Fintype.card_fin] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_C_mul, map_pow, mul_comm]
  have he : ∀ j, j < n + 1 → esymm (Fin n) ℂ j ∈ S := by
    intro j hj
    by_contra hc
    obtain ⟨φ, hφ, h0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := Subalgebra.toSubmodule S) hc inferInstance
    have h1 : ∀ x ∈ S, φ x = 0 := fun x hx => (Submodule.eq_bot_iff _).1 h0 _ ⟨x, hx, rfl⟩
    have hp : (∑ i ∈ Finset.range (n + 1), Polynomial.monomial (n - i) (φ (esymm (Fin n) ℂ i))) = 0 := by
      apply Polynomial.funext
      intro u
      have h2 := h1 _ (Algebra.subset_adjoin ⟨u, rfl⟩)
      simp only [hv, map_sum, map_smul, smul_eq_mul] at h2
      simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial, Polynomial.eval_zero]
      rw [← h2]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h3 := congrArg (fun p => Polynomial.coeff p (n - j)) hp
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at h3
    rw [Finset.sum_eq_single j] at h3
    · exact hφ (by simpa using h3)
    · intro b hb hbj
      rw [Finset.mem_range] at hb
      rw [if_neg (by omega)]
    · intro h
      exact absurd (Finset.mem_range.2 hj) h
  intro p hp
  obtain ⟨q, hq⟩ := (esymmAlgHom_fin_bijective ℂ n).2 ⟨p, hp⟩
  have hq' : p = aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) q := by
    rw [← esymmAlgHom_apply, hq]
  rw [hq']
  have : Algebra.adjoin ℂ (Set.range fun i : Fin n => esymm (Fin n) ℂ (i + 1)) ≤ S :=
    Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact he _ (by have := i.2; omega))
  apply this
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨q, rfl⟩
end

section
open GroundTheory.Automorphic.HarishChandra in
private theorem qdet_mem_center (n : ℕ) (u : ℂ) :
    Formalism.REAL.qdet (fun i j : Fin n => e (i, j)) u ∈ Subalgebra.center ℂ (U n) := by
  have hgl : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) := by
    intro i j k l
    exact e_mul_sub_mul (i, j) (k, l)
  refine mem_center_of_commute_e fun a => ?_
  exact (Formalism.REAL.qDetCentral (U n) n _ hgl u a.1 a.2).symm

open GroundTheory.Automorphic.HarishChandra in
private theorem hc_qdet (n : ℕ) (u : ℂ) :
    harishChandraHom (⟨_, qdet_mem_center n (u + ((n : ℂ) - 1) / 2)⟩ : Subalgebra.center ℂ (U n)) =
      ∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k : MvPolynomial (Fin n) ℂ) := by
  rw [harishChandraHom_apply]
  dsimp only
  rw [UpperTheory.harishChandraProj_quantumDet_eq_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold GroundTheory.Automorphic.HarishChandra.translate
  rw [map_add, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq,
    add_comm (MvPolynomial.X k), ← add_assoc, ← map_add]
  congr 2
  simp only [rhoVec, Pi.neg_apply]
  ring

theorem UpperTheory.center_envelopingGL_le_adjoin_quantumDet :
    ∀ n : ℕ, Subalgebra.center ℂ (GroundTheory.Automorphic.HarishChandra.U n) ≤ Algebra.adjoin ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet (fun i j : Fin n => GroundTheory.Automorphic.HarishChandra.e (i, j)) u) := by
  intro n z hz
  open GroundTheory.Automorphic.HarishChandra in
  let A : Subalgebra ℂ (Subalgebra.center ℂ (U n)) :=
    Algebra.adjoin ℂ (Set.range fun u : ℂ => ⟨_, qdet_mem_center n u⟩)
  have hle : MvPolynomial.symmetricSubalgebra (Fin n) ℂ ≤
      A.map GroundTheory.Automorphic.HarishChandra.harishChandraHom := by
    refine (UpperTheory.symmetricSubalgebra_le_adjoin_range_prod_C_add_X_complex n).trans (Algebra.adjoin_le ?_)
    rintro _ ⟨u, rfl⟩
    exact ⟨_, Algebra.subset_adjoin ⟨_, rfl⟩, hc_qdet n u⟩
  obtain ⟨a, ha, hae⟩ :=
    hle (GroundTheory.Automorphic.HarishChandra.harishChandraHom_mem_symmetricSubalgebra ⟨z, hz⟩)
  have haz : a = ⟨z, hz⟩ := GroundTheory.Automorphic.HarishChandra.harishChandraHom_injective hae
  have hval : A.map (Subalgebra.center ℂ (GroundTheory.Automorphic.HarishChandra.U n)).val =
      Algebra.adjoin ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet
        (fun i j : Fin n => GroundTheory.Automorphic.HarishChandra.e (i, j)) u) := by
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  rw [← hval]
  exact ⟨a, ha, by rw [haz]; rfl⟩
end

section
open GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace UpperTheory.V.Af.CuspFin.One

private noncomputable def lin {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) :
    gl n →ₗ[ℂ] A where
  toFun X := ∑ a : Fin n × Fin n, X a.1 a.2 • F a.1 a.2
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [Finset.smul_sum, mul_smul]

private theorem lin_E {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) (a : Fin n × Fin n) :
    lin F (E a) = F a.1 a.2 := by
  obtain ⟨i, j⟩ := a
  show ∑ b : Fin n × Fin n, (E (i, j)) b.1 b.2 • F b.1 b.2 = F i j
  rw [Finset.sum_eq_single (i, j)]
  · simp [E]
  · rintro ⟨k, l⟩ _ hb
    have : ¬ (i = k ∧ j = l) := fun h => hb (by rw [h.1, h.2])
    simp [E, Matrix.single_apply, this]
  · simp

private theorem lin_lie {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (hF : Formalism.REAL.GlRel F) (X Y : gl n) : lin F ⁅X, Y⁆ = ⁅lin F X, lin F Y⁆ := by
  have hE : ∀ a b : Fin n × Fin n, lin F ⁅E a, E b⁆ = ⁅lin F (E a), lin F (E b)⁆ := by
    intro a b
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket, E_mul_sub_mul, lin_E, lin_E,
      hF, map_sub]
    congr 1 <;> split_ifs <;> simp_all [lin_E]
  rw [eq_sum_E X, eq_sum_E Y]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, hE]

private noncomputable def lie {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (hF : Formalism.REAL.GlRel F) : gl n →ₗ⁅ℂ⁆ A :=
  { lin F with map_lie' := fun {X Y} => lin_lie F hF X Y }

end UpperTheory.V.Af.CuspFin.One

open UpperTheory.V.Af.CuspFin UpperTheory.V.Af.CuspFin.One in
theorem UpperTheory.glRelations_hasUniversalProperty :
    ∀ n : ℕ, UpperTheory.V.Af.CuspFin.HasUniv Unit n := by
  intro n
  refine ⟨U n, inferInstance, inferInstance, fun _ i j => e (i, j), ⟨fun _ => ?_, fun v v' h => (h rfl).elim⟩,
    ?_, fun A _ _ E' hE => ?_, ?_⟩
  · intro i j k l
    rw [e_mul_sub_mul]
  · refine eq_top_iff.2 fun u hu => ?_
    clear hu
    induction u using U.induction with
    | halg r => exact Subalgebra.algebraMap_mem _ r
    | hι X =>
      rw [ι_eq_sum_e]
      refine Subalgebra.sum_mem _ fun a _ => Subalgebra.smul_mem _ (Algebra.subset_adjoin ?_) _
      exact ⟨(), a.1, a.2, rfl⟩
    | hmul a b ha hb => exact Subalgebra.mul_mem _ ha hb
    | hadd a b ha hb => exact Subalgebra.add_mem _ ha hb
  · refine ⟨UniversalEnvelopingAlgebra.lift ℂ (lie (E' ()) (hE.1 ())), fun v i j => ?_⟩
    rw [e, UniversalEnvelopingAlgebra.lift_ι_apply]
    exact lin_E (E' ()) (i, j)
  · refine (UpperTheory.center_envelopingGL_le_adjoin_quantumDet n).trans (Algebra.adjoin_mono ?_)
    rintro _ ⟨u, rfl⟩
    exact ⟨(), u, rfl⟩
end

section
attribute [local instance 100] LieRing.ofAssociativeRing

open UpperTheory.V.Af.CuspFin in
theorem UpperTheory.map_center_envelopingProductGL_mem_capelliAlgebra :
    ∀ (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (ι : Type) [Fintype ι] (n : ℕ) (b : Module.Basis (ι × Fin n × Fin n) ℝ 𝔤), (∀ v i j k l, ⁅b (v, i, j), b (v, k, l)⁆ = (if j = k then b (v, i, l) else 0) - (if l = i then b (v, k, j) else 0)) → (∀ v v', v ≠ v' → ∀ i j k l, ⁅b (v, i, j), b (v', k, l)⁆ = 0) → ∀ (A : Type) [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (ψ : UniversalEnvelopingAlgebra ℝ 𝔤 →ₐ[ℝ] A), ∀ z ∈ Subalgebra.center ℝ (UniversalEnvelopingAlgebra ℝ 𝔤), ψ z ∈ UpperTheory.V.Af.CuspFin.capAlg fun v i j => ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j))) := by
  intro 𝔤 _ _ ι _ n b h1 h2 A _ _ _ _ ψ z hz
  obtain ⟨T, _, _, E, hE⟩ := hasUniv_of_sum (UpperTheory.glRelations_hasUniversalProperty n) (UpperTheory.capelliAlgebra_map_of_glRelations n) ι
  letI : Algebra ℝ T := Algebra.compHom T (algebraMap ℝ ℂ)
  haveI : IsScalarTower ℝ ℂ T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let l : 𝔤 →ₗ[ℝ] T := b.constr ℝ fun p => E p.1 p.2.1 p.2.2
  have hl : ∀ v i j, l (b (v, i, j)) = E v i j := fun v i j => b.constr_basis ℝ _ _
  have hlie : ∀ x y, l ⁅x, y⁆ = l x * l y - l y * l x := by
    have key : (LieModule.toEnd ℝ 𝔤 𝔤 : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] 𝔤).compr₂ l =
        (LinearMap.mul ℝ T).compl₁₂ l l - ((LinearMap.mul ℝ T).compl₁₂ l l).flip := by
      refine LinearMap.ext_basis b b ?_
      rintro ⟨v, i, j⟩ ⟨v', k, m⟩
      change l ⁅b (v, i, j), b (v', k, m)⁆ =
        l (b (v, i, j)) * l (b (v', k, m)) - l (b (v', k, m)) * l (b (v, i, j))
      rw [hl, hl]
      by_cases hv : v = v'
      · subst hv
        rw [h1, hE.rel.1 v i j k m, map_sub]
        congr 1 <;> split_ifs <;> simp [hl]
      · rw [h2 v v' hv, map_zero, (hE.rel.2 v v' hv i j k m).eq, sub_self]
    intro x y
    exact LinearMap.congr_fun₂ key x y
  let L : 𝔤 →ₗ⁅ℝ⁆ T := { l with map_lie' := fun {x y} => hlie x y }
  let f : UniversalEnvelopingAlgebra ℝ 𝔤 →ₐ[ℝ] T := UniversalEnvelopingAlgebra.lift ℝ L
  have hf : ∀ v i j, f (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j))) = E v i j := fun v i j => by
    rw [← hl]
    exact UniversalEnvelopingAlgebra.lift_ι_apply ℝ L _
  have hcen : f z ∈ Subalgebra.center ℂ T := by
    rw [Subalgebra.mem_center_iff]
    intro t
    have ht : t ∈ Algebra.adjoin ℂ {z | ∃ v i j, z = E v i j} := hE.gen ▸ Algebra.mem_top
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ht ?_).symm.eq
    rintro _ ⟨v, i, j, rfl⟩
    rw [← hf, Commute, SemiconjBy, ← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 hz]
  have hbr : ∀ x y : 𝔤,
      ψ (UniversalEnvelopingAlgebra.ι ℝ x) * ψ (UniversalEnvelopingAlgebra.ι ℝ y) -
        ψ (UniversalEnvelopingAlgebra.ι ℝ y) * ψ (UniversalEnvelopingAlgebra.ι ℝ x) =
      ψ (UniversalEnvelopingAlgebra.ι ℝ ⁅x, y⁆) := fun x y => by
    rw [LieHom.map_lie, Ring.lie_def, map_sub, map_mul, map_mul]
  have hrel : MultiRel fun v i j => ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j))) := by
    refine ⟨fun v i j k m => ?_, fun v v' hv i j k m => ?_⟩
    · rw [hbr, h1, map_sub, map_sub]
      congr 1 <;> split_ifs <;> simp
    · rw [Commute, SemiconjBy, ← sub_eq_zero, hbr, h2 v v' hv, map_zero, map_zero]
  obtain ⟨ρ, hρ⟩ := hE.univ A _ hrel
  have hcomp : (ρ.restrictScalars ℝ).comp f = ψ := by
    apply UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun x => LinearMap.congr_fun (f := LieHom.toLinearMap _)
      (g := LieHom.toLinearMap _) (b.ext ?_) x
    rintro ⟨v, i, j⟩
    change ρ (f (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))) =
      ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))
    rw [hf, hρ]
  have hψ : ψ z = ρ (f z) := by rw [← hcomp]; rfl
  rw [hψ]
  have hle : capAlg E ≤ (capAlg fun v i j =>
      ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))).comap ρ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, u, rfl⟩
    refine Algebra.subset_adjoin ⟨v, u, ?_⟩
    refine (map_qdet ρ _ _).trans ?_
    simp only [hρ]
  exact hle (hE.centre hcen)
end
