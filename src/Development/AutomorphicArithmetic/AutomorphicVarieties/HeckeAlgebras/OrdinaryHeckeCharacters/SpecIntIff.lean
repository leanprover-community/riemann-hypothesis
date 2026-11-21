import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckeFixedLevelSpaces.FreeMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckeFixedLevelSpaces.AddOnePowEqRingHomImageAddPrimeMulZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SqBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExpCharIntegralityCriterion
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Matrix in
private theorem ofBasis {G : Type} [Group G] (I : Iwa G) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω]
    {M : Type} [AddCommGroup M] [Module Ω M] {κ : Type} [Fintype κ] [DecidableEq κ] (k0 : κ) (b : Module.Basis κ Ω M)
    (ρ : Representation Ω G M) (A : G → κ → κ → Ω) (hA : ∀ g i j, b.repr (ρ g (b j)) i = A g i j)
    (hK : ∀ x, x ∈ I.N ∨ x ∈ I.T ∨ x ∈ I.Nm 0 → ∀ i j, A x i j ∈ (algebraMap O Ω).range)
    (hP : ∀ a ∈ I.P, ∀ i j, (A a k0 k0)⁻¹ * A a i j ∈ (algebraMap O Ω).range)
    (hN : ∀ x ∈ I.Nf, ∀ j, A x k0 j = if j = k0 then 1 else 0)
    (hT : ∀ x ∈ I.Tf, ∀ j, j ≠ k0 → A x k0 j = 0)
    (hz : ∀ i j, j ≠ k0 → ∃ x ∈ maximalIdeal O, (A I.z k0 k0)⁻¹ * A I.z i j = algebraMap O Ω x)
    (hc : ∀ k : ℕ, ∃ c, ∀ y, y ∈ I.Nm c ∨ y ∈ I.Tc c → ∀ i j, ∃ x ∈ maximalIdeal O ^ k,
      A y i j = (if i = j then 1 else 0) + algebraMap O Ω x)
    (hZ : ∀ t ∈ I.Tf, t ∈ Subgroup.center G → ∀ i j, A t i j = if i = j then A t k0 k0 else 0) :
    ∃ R : WtRep I O Ω, (∃ e : (Fin (R.d + 1) → Ω) ≃ₗ[Ω] M,
      ∀ g x, e ((R.ξ g : Matrix (Fin (R.d + 1)) (Fin (R.d + 1)) Ω) *ᵥ x) = ρ g (e x)) ∧ ∀ t : I.Tf, (R.χ t : Ω) = A t k0 k0 := by
  obtain ⟨d, hd⟩ : ∃ d, Fintype.card κ = d + 1 := Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos_iff.2 ⟨k0⟩).ne'
  let σ₀ := (Fintype.equivFinOfCardEq hd).symm
  let σ : Fin (d + 1) ≃ κ := σ₀.trans (Equiv.swap (σ₀ 0) k0)
  have h0 : σ 0 = k0 := Equiv.swap_apply_left _ _
  have h0' : ∀ j, σ j = k0 ↔ j = 0 := fun j => by rw [← h0, σ.injective.eq_iff]
  let b' := b.reindex σ.symm
  let ξ : G →* GL (Fin (d + 1)) Ω :=
    MonoidHom.toHomUnits (((LinearMap.toMatrixAlgEquiv b').toAlgHom.toRingHom.toMonoidHom).comp ρ)
  have hξ' : ∀ g, (ξ g).val = LinearMap.toMatrix b' b' (ρ g) := fun g => rfl
  have hξ : ∀ g i j, ξ g i j = A g (σ i) (σ j) := fun g i j => by
    rw [← hA]
    change (ξ g).val i j = _
    rw [hξ', LinearMap.toMatrix_apply]
    simp [b']
  let χ₀ : I.Tf →* Ω :=
    { toFun := fun t => ξ t 0 0
      map_one' := by simp
      map_mul' := fun s t => by
        change (ξ (s * t)).val 0 0 = _
        rw [map_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single 0]
        · intro j _ hj
          have : (ξ s).val 0 j = 0 := by
            change ξ s 0 j = 0
            rw [hξ, h0]
            exact hT _ s.2 _ fun h => hj ((h0' j).1 h)
          rw [this, zero_mul]
        · simp }
  have hχ : ∀ t : I.Tf, (χ₀.toHomUnits t : Ω) = A t k0 k0 := fun t => by rw [← h0, ← hξ]; rfl
  refine ⟨{ d := d, ξ := ξ, χ := χ₀.toHomUnits, c0 := 0
            int_N := fun x hx i j => by rw [hξ]; exact hK x (.inl hx) _ _
            integral_torusCharacter := fun x hx i j => by rw [hξ]; exact hK x (.inr (.inl hx)) _ _
            int_Nm := fun x hx i j => by rw [hξ]; exact hK x (.inr (.inr hx)) _ _
            int_P := fun a ha i j => by rw [hξ, Units.val_inv_eq_inv_val, hχ]; exact hP a ha _ _
            row_N := fun x hx j => by rw [hξ, h0, hN x hx]; simp only [h0']
            torusAction := fun t j => by
              rw [hξ, h0, hχ]
              split_ifs with h
              · rw [h, h0]
              · exact hT _ t.2 _ fun h' => h ((h0' j).1 h')
            nilpotent_central_action := fun i j hj => by
              rw [hξ, Units.val_inv_eq_inv_val, hχ]
              exact hz _ _ fun h' => hj ((h0' j).1 h')
            cont_Nm := fun k => (hc k).imp fun c h y hy i j => by
              simpa only [hξ, σ.injective.eq_iff] using h y (.inl hy) (σ i) (σ j)
            continuous_torusCharacter := fun k => (hc k).imp fun c h t ht => by
              simpa only [hχ, if_true] using h t (.inr ht) k0 k0
            central := fun t ht i j => by
              rw [hξ, hχ, hZ _ t.2 ht]
              simp only [σ.injective.eq_iff] }, ⟨b'.equivFun.symm, fun g x => ?_⟩, hχ⟩
  rw [LinearEquiv.symm_apply_eq]
  change (ξ g).val *ᵥ x = b'.repr _
  rw [hξ', ← LinearMap.toMatrix_mulVec_repr b' b']
  congr 1
  exact (b'.equivFun.apply_symm_apply x).symm

private theorem prod_zpow_const {K ι : Type} [Field K] {s : K} (hs : s ≠ 0) (μ : ι → ℤ) (F : Finset ι) :
    ∏ i ∈ F, s ^ μ i = s ^ ∑ i ∈ F, μ i := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hs, ih]

private theorem prod_delta {O K E : Type} [CommRing O] [CommRing K] [Algebra O K] [Fintype E] [DecidableEq E] {κ : E → Type}
    [∀ e, DecidableEq (κ e)] [DecidableEq (∀ e, κ e)] (𝔞 : Ideal O) (i j : ∀ e, κ e) (y : E → O) (hy : ∀ e, y e ∈ 𝔞) :
    ∃ x ∈ 𝔞, ∏ e, ((if i e = j e then 1 else 0) + algebraMap O K (y e)) = (if i = j then 1 else 0) + algebraMap O K x := by
  refine ⟨∏ e, ((if i e = j e then 1 else 0) + y e) - ∏ e, (if i e = j e then 1 else 0), ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, map_prod, map_prod]
    exact Finset.prod_congr rfl fun e _ => by rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 (hy e), add_zero]
  · rw [Fintype.prod_boole]
    simp only [map_sub, map_prod, map_add, ← funext_iff, apply_ite (algebraMap O K), map_one, map_zero]
    split_ifs <;> ring

theorem UpperTheory.V.Hi.wtRep :
    ∀ (L : Type) [Field L] [NumberField L] (l : ℕ) [Fact l.Prime] (n : ℕ) (V : Type) [Fintype V] (S : V → W.Plc L) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (c : Coef l), ∃ c' : Coef l, c.O ≤ c'.O ∧
      letI : Algebra c'.O ℂ := (ι.toRingHom.comp (algebraMap c'.O (Qbar l))).toAlgebra
      ∃ R : WtRep (iwS n S) c'.O ℂ, IsAlgWt ι lam R.ξ ∧ ∀ (t : (iwS n S).Tf) (y : ∀ v, Fin n → ((S v).adicCompletion L)ˣ), (∀ v, (t : GV n S) v = diagT _ (Fin n) (y v)) → (R.χ t : ℂ) = ι (∏ v, ∏ i, algPow (S v) (lowW lam i) (y v i : (S v).adicCompletion L)) := by
  intro L _ _ l _ n V _ S ι lam c
  classical
  haveI : ∀ v, Finite (W.Emb l (S v)) := fun v => GlobalTheory.HeckeGal.finite_contEmb _
  letI : ∀ v, Fintype (W.Emb l (S v)) := fun v => Fintype.ofFinite _
  obtain ⟨c', hc, hc'⟩ : ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ e ∈ (Finset.univ : Finset (Emb l S)),
      ∀ x : 𝒪[(S e.1).adicCompletion L], e.2.1 (x : (S e.1).adicCompletion L) ∈ c'.O := by
    induction (Finset.univ : Finset (Emb l S)) using Finset.induction_on with
    | empty => exact ⟨c, le_rfl, by simp⟩
    | insert e F _ ih =>
      obtain ⟨c₁, h₁, h₁'⟩ := ih
      obtain ⟨c₂, h₂, h₂'⟩ := (UpperTheory.expChar_integrality_criterion L l _ e.2).1 c₁
      refine ⟨c₂, h₁.trans h₂, fun e' he' x => ?_⟩
      rcases Finset.mem_insert.1 he' with rfl | he'
      exacts [h₂' x, h₂ (h₁' e' he' x)]
  refine ⟨c', hc, ?_⟩
  letI : Algebra c'.O ℂ := (ι.toRingHom.comp (algebraMap c'.O (Qbar l))).toAlgebra
  have hinj : Function.Injective (algebraMap c'.O ℂ) := ι.injective.comp Subtype.val_injective
  let ψ : ∀ e : Emb l S, (S e.1).adicCompletion L →+* ℂ := fun e => ι.toRingHom.comp e.2.1
  let φ : ∀ e : Emb l S, 𝒪[(S e.1).adicCompletion L] →+* c'.O := fun e =>
    (e.2.1.comp (algebraMap _ _)).codRestrict c'.O (hc' e (Finset.mem_univ _))
  have hφ : ∀ e x, algebraMap c'.O ℂ (φ e x) = ψ e x := fun e x => rfl
  have hφm : ∀ e k, ∀ x ∈ maximalIdeal _ ^ k, φ e x ∈ maximalIdeal c'.O ^ k := fun e k x hx => by
    have h1 : (maximalIdeal _).map (φ e) ≤ maximalIdeal c'.O :=
      Ideal.map_le_iff_le_comap.2 fun x hx => (UpperTheory.expChar_integrality_criterion L l _ e.2).2 c' x hx _
    refine Ideal.pow_right_mono h1 k ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  choose κ _ _ k0 b μ hI hU hD h0 hle hlt using fun e : Emb l S => sqBasis c'.O ℂ hinj n (lam e.res)
  let A : GV n S → (∀ e, κ e) → (∀ e, κ e) → ℂ := fun g i j => ∏ e,
    (b e).repr (GlobalTheory.Branching.sqRep ℂ n (lam e.res) (Matrix.GeneralLinearGroup.map (ψ e) (g e.1)) (b e (j e))) (i e)
  have hA : ∀ g i j, (Basis.piTensorProduct b).repr (algRep S ι lam g (Basis.piTensorProduct b j)) i = A g i j := by
    intro g i j
    rw [Basis.piTensorProduct_apply]
    erw [PiTensorProduct.map_tprod]
    rw [Basis.piTensorProduct_repr_tprod_apply]
    rfl
  have hK : ∀ (k : ℕ) (g : GV n S), (∀ v, g v ∈ Kc _ n k) → ∀ i j, ∃ x ∈ maximalIdeal c'.O ^ k,
      A g i j = (if i = j then 1 else 0) + algebraMap c'.O ℂ x := by
    intro k g hg i j
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible c'.O
    have hm : maximalIdeal c'.O ^ k = Ideal.span {p ^ k} := by
      rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow]
    choose h hh hh' using hg
    choose x hx using fun e : Emb l S => hI e (p ^ k) (pow_ne_zero _ hp.ne_zero)
      (Matrix.GeneralLinearGroup.map (φ e) (h e.1)) (fun a a' => by
        have h1 : ((h e.1).val - 1) a a' ∈ maximalIdeal _ ^ k := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub, sub_eq_zero]
          refine (congrArg (fun u : GL (Fin n) _ => u.val a a') (MonoidHom.mem_ker.1 (hh e.1))).trans ?_
          simp only [Units.val_one, Matrix.one_apply]
          split_ifs <;> simp
        have h2 := hφm e k _ h1
        rw [hm, Ideal.mem_span_singleton] at h2
        convert h2 using 1
        simp only [Matrix.sub_apply, Matrix.one_apply, map_sub, apply_ite (φ e), map_one, map_zero]
        rfl) (i e) (j e)
    obtain ⟨y, hy, hy'⟩ := prod_delta (K := ℂ) (maximalIdeal c'.O ^ k) i j (fun e => p ^ k * x e) fun e => by
      rw [hm]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    refine ⟨y, hy, ?_⟩
    rw [← hy']
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [← hx e, ← hh' e.1]
    rfl
  have hDiag : ∀ (g : GV n S) (y : ∀ v, Fin n → ((S v).adicCompletion L)ˣ), (∀ v, g v = diagT _ (Fin n) (y v)) → ∀ i j,
      A g i j = if i = j then ∏ e, ∏ a, ψ e (y e.1 a) ^ μ e (j e) a else 0 := by
    intro g y hy i j
    have h1 : ∀ e : Emb l S, (Matrix.GeneralLinearGroup.map (ψ e) (g e.1)).val = Matrix.diagonal fun a => ψ e (y e.1 a) := fun e => by
      change (g e.1).val.map (ψ e) = _
      rw [hy, val_diagT, Matrix.diagonal_map (map_zero _)]
    have h2 : ∀ e : Emb l S, (b e).repr (GlobalTheory.Branching.sqRep ℂ n (lam e.res) (Matrix.GeneralLinearGroup.map (ψ e) (g e.1))
        (b e (j e))) (i e) = (if i e = j e then 1 else 0) * ∏ a, ψ e (y e.1 a) ^ μ e (j e) a := fun e => by
      rw [hD e _ _ (h1 e), map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_comm]
      simp only [eq_comm]
    refine (Finset.prod_congr rfl fun e _ => h2 e).trans ?_
    rw [Finset.prod_mul_distrib, Fintype.prod_boole]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (congrFun hij), one_mul]
    · rw [if_neg hij, if_neg fun h => hij (funext h), zero_mul]
  have hPw : ∀ (g : GV n S) (a : V → Fin n → ℤ), (∀ v, Antitone (a v)) → (∀ v, g v = upow _ n (a v)) → ∀ i j,
      ∃ x, (A g k0 k0)⁻¹ * A g i j = algebraMap c'.O ℂ x ∧
        ((∃ e, ∑ s, a e.1 s * μ e (k0 e) s < ∑ s, a e.1 s * μ e (j e) s) → x ∈ maximalIdeal c'.O) := by
    intro g a ha hg i j
    by_cases hij : i = j
    swap
    · exact ⟨0, by rw [hDiag g _ hg i j, if_neg hij, mul_zero, map_zero], fun _ => zero_mem _⟩
    let p : ∀ v, 𝒪[(S v).adicCompletion L] := fun v =>
      ⟨unif ((S v).adicCompletion L), ((GlAx.unif_spec (k := (S v).adicCompletion L)).trans_lt uniformizer_lt_one).le⟩
    have hp : ∀ v, p v ∈ maximalIdeal _ ^ 1 := fun v => (GlAx.mem_pow 1 _).2 (by
      rw [Nat.cast_one, zpow_one]; exact GlAx.unif_spec.le)
    have hp0 : ∀ e : Emb l S, ψ e (p e.1) ≠ 0 := fun e => (_root_.map_ne_zero _).2 (Units.ne_zero _)
    refine ⟨∏ e, φ e (p e.1) ^ (∑ s, a e.1 s * μ e (j e) s - ∑ s, a e.1 s * μ e (k0 e) s).toNat, ?_, ?_⟩
    · rw [hDiag g _ hg, hDiag g _ hg, if_pos rfl, if_pos hij, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, map_prod]
      refine Finset.prod_congr rfl fun e _ => ?_
      have h1 : ∀ m : Fin n → ℤ, ∏ s, ψ e ((unif ((S e.1).adicCompletion L) ^ a e.1 s : _ˣ) : (S e.1).adicCompletion L) ^ m s =
          ψ e (p e.1) ^ ∑ s, a e.1 s * m s := fun m => by
        rw [← prod_zpow_const (hp0 e)]
        exact Finset.prod_congr rfl fun s _ => by rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← zpow_mul]
      rw [h1, h1, map_pow, hφ, ← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.2 (hle e _ _ (ha _))), zpow_sub₀ (hp0 e),
        div_eq_inv_mul]
    · rintro ⟨e, he⟩
      refine Ideal.prod_mem _ (Finset.mem_univ e) (Ideal.pow_mem_of_mem _ ?_ _ (by omega))
      simpa only [pow_one] using hφm e 1 _ (hp e.1)
  obtain ⟨R, hR, hχ⟩ := ofBasis (iwS n S) c'.O ℂ k0 (Basis.piTensorProduct b) (algRep S ι lam) A hA
    (fun x hx i j => by
      obtain ⟨y, -, hy⟩ := hK 0 x (fun v => by
        rw [GlAx.Kc_zero]
        rcases hx with hx | hx | hx
        exacts [(hx v trivial).2, GlAx.T_le_KO (hx v trivial), GlAx.Kc_le _ (hx v trivial).2]) i j
      rw [hy]
      refine add_mem ?_ ⟨y, rfl⟩
      split_ifs
      exacts [one_mem _, zero_mem _])
    (fun g hg i j => by
      choose a ha ha' using fun v => hg v trivial
      obtain ⟨x, hx, -⟩ := hPw g a ha ha' i j
      exact ⟨x, hx.symm⟩)
    (fun x hx j => by
      have h1 := fun v => (mem_unipB _).1 (hx v trivial)
      have h2 : ∀ e : Emb l S, _ := fun e => hU e (Matrix.GeneralLinearGroup.map (ψ e) (x e.1))
        (fun a a' h => (congrArg (ψ e) ((h1 e.1).1 a a' h)).trans (map_zero _)) (j e)
      have h3 : ∀ (e : Emb l S) a, (Matrix.GeneralLinearGroup.map (ψ e) (x e.1)).val a a = 1 := fun e a =>
        (congrArg (ψ e) ((h1 e.1).2 a)).trans (map_one _)
      simp only [A, h2, h3, one_zpow, Finset.prod_const_one, Fintype.prod_boole, ← funext_iff])
    (fun x hx j hj => by
      choose y hy using fun v => hx v trivial
      rw [hDiag x y (fun v => (hy v).symm), if_neg hj.symm])
    (fun i j hj => by
      obtain ⟨x, hx, hx'⟩ := hPw (iwS n S).z (fun _ s => (n : ℤ) - 1 - (s : ℕ)) (fun _ => GlAx.z_anti) (fun _ => rfl) i j
      obtain ⟨e, he⟩ := Function.ne_iff.1 hj
      exact ⟨x, hx' ⟨e, hlt e _ he⟩, hx⟩)
    (fun k => ⟨k, fun y hy i j => by
      refine hK k y (fun v => GlAx.Kc_anti (Nat.le_succ k) ?_) i j
      rcases hy with hy | hy
      exacts [(hy v trivial).2, (hy v trivial).2]⟩)
    (fun x hx hZ i j => by
      choose y hy using fun v => hx v trivial
      rw [hDiag x y (fun v => (hy v).symm), hDiag x y (fun v => (hy v).symm), if_pos rfl]
      refine if_congr Iff.rfl (Finset.prod_congr rfl fun e _ => ?_) rfl
      have h1 : x e.1 ∈ Subgroup.center _ := Subgroup.mem_center_iff.2 fun g => by
        simpa using congrFun (Subgroup.mem_center_iff.1 hZ (Pi.mulSingle e.1 g)) e.1
      obtain ⟨s, hs⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 h1
      have h2 : ∀ a, (y e.1 a : (S e.1).adicCompletion L) = s := fun a => by
        have := congrFun (congrFun hs a) a
        rw [← hy, val_diagT] at this
        simpa using this.symm
      rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨a⟩⟩
      · simp
      have h3 : ψ e s ≠ 0 := (_root_.map_ne_zero _).2 (h2 a ▸ Units.ne_zero _)
      have h4 := hle e (j e) 1 antitone_const
      have h5 := hle e (j e) (-1) antitone_const
      simp only [Pi.one_apply, Pi.neg_apply, one_mul, neg_mul, Finset.sum_neg_distrib] at h4 h5
      simp only [h2, prod_zpow_const h3]
      rw [le_antisymm h4 (by linarith)])
  refine ⟨R, hR, fun t y hy => ?_⟩
  rw [hχ, hDiag _ y hy, if_pos rfl, Fintype.prod_sigma, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_comm, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [algPow, finprod_eq_prod_of_fintype, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_zpow₀, h0]
  rfl
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem spec_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem spec_int {l : ℕ} [Fact l.Prime] (c : Coef l) (ι : Qbar l ≃+* ℂ) [Algebra c.O ℂ]
    (h : ∀ a : c.O, algebraMap c.O ℂ a = ι a) (μ : ℂ) : IsIntegral c.O μ ↔ ‖ι.symm μ‖ ≤ 1 := by
  let e : Qbar l →ₐ[c.O] ℂ := { ι.toRingHom with commutes' := fun a => (h a).symm }
  have h1 : IsIntegral c.O (e (ι.symm μ)) ↔ IsIntegral c.O (ι.symm μ) := isIntegral_algHom_iff e ι.injective
  have h2 : e (ι.symm μ) = μ := ι.apply_symm_apply μ
  rw [h2] at h1
  rw [h1, ← spec_intIff]
  exact ⟨fun h => isIntegral_trans _ h, fun h => h.tower_top⟩

private theorem spec_unit {l : ℕ} [Fact l.Prime] (c : Coef l) (ι : Qbar l ≃+* ℂ) [Algebra c.O ℂ]
    (h : ∀ a : c.O, algebraMap c.O ℂ a = ι a) (μ : ℂ) : IsIntUnit c.O μ ↔ ‖ι.symm μ‖ = 1 := by
  rw [IsIntUnit, spec_int c ι h, spec_int c ι h, map_inv₀, norm_inv]
  constructor
  · rintro ⟨h0, h1, h2⟩
    have h3 : 0 < ‖ι.symm μ‖ := norm_pos_iff.2 ((map_ne_zero ι.symm).2 h0)
    exact le_antisymm h1 ((inv_le_one₀ h3).1 h2)
  · intro h1
    refine ⟨fun h0 => ?_, h1.le, by rw [h1, inv_one]⟩
    rw [h0, map_zero, norm_zero] at h1
    exact zero_ne_one h1

private theorem spec_chi {G : Type} [Group G] {I : Iwa G} {O Ω : Type} [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω]
    (hinj : Function.Injective (algebraMap O Ω)) (R : WtRep I O Ω) :
    ∃ ψ : I.T →* Oˣ, ∀ t : I.T, algebraMap O Ω (ψ t) = R.χ ⟨t, I.T_le t.2⟩ := by
  have h : ∀ t : I.T, ∃ a : O, algebraMap O Ω a = R.χ ⟨t, I.T_le t.2⟩ := fun t => by
    have h1 := R.integral_torusCharacter t t.2 0 0
    have h2 := R.torusAction ⟨t, I.T_le t.2⟩ 0
    rw [if_pos rfl] at h2
    rw [← h2]
    exact h1
  choose a ha using h
  let f : I.T →* O :=
    { toFun := a
      map_one' := hinj (by rw [ha, map_one]; exact congrArg Units.val (map_one R.χ))
      map_mul' := fun s t => hinj (by
        rw [map_mul, ha, ha, ha, ← Units.val_mul, ← map_mul]
        rfl) }
  exact ⟨f.toHomUnits, ha⟩

private theorem spec_cl {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ)
    (x : A →+* Qbar l) (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) (K : H.Lev) (e : ℕ) (φ : H.X.I.T →* ℂˣ)
    (hφ : ∀ v i y, (φ (eV n H.Sl v i y) : ℂ) = ι (H.finPart θ x lam v i y)) :
    H.ClAt θ ι x lam ξ K e = H.X.Cl (H.τC ι) ξ (H.lev K) e φ := by
  ext F
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, -⟩, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨⟨h1, h2⟩, h3, h4, ?_⟩
    let M : Submonoid H.X.I.T :=
      { carrier := {t | H.X.rpF ℂ d H.m t F = (((φ t)⁻¹ : ℂˣ) : ℂ) • F}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          have ha' : H.X.rpF ℂ d H.m a F = (((φ a)⁻¹ : ℂˣ) : ℂ) • F := ha
          have hb' : H.X.rpF ℂ d H.m b F = (((φ b)⁻¹ : ℂˣ) : ℂ) • F := hb
          change H.X.rpF ℂ d H.m ((a : GV n H.Sl) * b) F = (((φ (a * b))⁻¹ : ℂˣ) : ℂ) • F
          rw [map_mul, Module.End.mul_apply, hb', map_smul, ha', smul_smul, map_mul, mul_inv_rev, Units.val_mul] }
    refine Sp.torus_mem_submonoid_of_elementaryTorus H.Sl M fun v i y => ?_
    have h6 : F ∈ ⨅ (v) (i) (y), Module.End.eigenspace (H.X.rpF ℂ d H.m (eV n H.Sl v i y : H.X.I.T))
      (ι (H.finPart θ x lam v i y))⁻¹ := h5
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at h6
    change H.X.rpF ℂ d H.m _ F = _
    rw [Units.val_inv_eq_inv_val, hφ]
    exact h6 v i y
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    refine ⟨⟨⟨⟨⟨h1, fun u hu => h2 u (Subgroup.mem_sup_left hu)⟩, h2⟩, h3⟩, h4⟩, ?_⟩
    change F ∈ ⨅ (v) (i) (y), Module.End.eigenspace (H.X.rpF ℂ d H.m (eV n H.Sl v i y : H.X.I.T))
      (ι (H.finPart θ x lam v i y))⁻¹
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro v i y
    rw [← hφ, ← Units.val_inv_eq_inv_val]
    exact h5 _

attribute [local instance 2000] UpperTheory.V.W.coefLocal

theorem UpperTheory.V.Hi.spec :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ), ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n), H.Arith θ x.toRingHom lam → ∃ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam ⟨e0, he0⟩
  haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨⟨c1, -, hx1⟩, a, ha1, -, ha⟩ := (GradeZeroInterpolatingElement.coPt c A).1 x
  obtain ⟨c', hc', hR⟩ := wtRep L l n H.V H.Sl ι lam c1
  letI : Algebra c'.O ℂ := (ι.toRingHom.comp (algebraMap c'.O (Qbar l))).toAlgebra
  have hal : ∀ a : c'.O, algebraMap c'.O ℂ a = ι a := fun _ => rfl
  obtain ⟨R, hR, hχ⟩ : ∃ R : WtRep H.X.I c'.O ℂ, IsAlgWt (S := H.Sl) ι lam R.ξ ∧ _ := hR
  haveI : IsCNL c'.O := { complete := (abelian₂.dvr_finite l c'.O).1, finite := (abelian₂.dvr_finite l c'.O).2.1 }
  let y : A →+* c'.O := x.toRingHom.codRestrict c'.O fun b => hc' (hx1 b)
  letI : Algebra A c'.O := y.toAlgebra
  letI : Algebra A ℂ := (ι.toRingHom.comp x.toRingHom).toAlgebra
  haveI : IsScalarTower A c'.O ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hinj : Function.Injective (algebraMap c'.O ℂ) := ι.injective.comp Subtype.val_injective
  haveI : IsLocalHom (algebraMap A c'.O) := ⟨fun b hu => by
    by_contra hb
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h1 : x b * (w : PadicAlgCl l) = 1 := congrArg Subtype.val hw
    have h2 : ‖x b‖ ≤ a := by simpa using ha 1 b (by rwa [pow_one])
    have h3 := congrArg norm h1
    rw [norm_mul, norm_one] at h3
    have h4 := mul_le_of_le_one_right (norm_nonneg (x b))
      ((spec_intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) w).map c'.O.val) : ‖(w : PadicAlgCl l)‖ ≤ 1)
    linarith⟩
  obtain ⟨ψ, hψ⟩ := spec_chi hinj R
  let φ : H.X.I.T →* c'.Oˣ := (Units.map y.toMonoidHom).comp θ / ψ
  have hφχ : ∀ t : H.X.I.T, algebraMap A ℂ (θ t) = algebraMap c'.O ℂ (φ t) * R.χ ⟨t, H.X.I.T_le t.2⟩ := fun t => by
    rw [← hψ, ← map_mul, ← Units.val_mul]
    simp only [φ, MonoidHom.div_apply, div_mul_cancel]
    rfl
  have hφe : ∀ v i z, algebraMap c'.O ℂ (φ (eV n H.Sl v i z)) = ι (H.finPart θ x.toRingHom lam v i z) := fun v i z => by
    rw [HSet.finPart, map_div₀, ← Sp.chi_eV H.Sl ι lam R.χ hχ]
    exact (eq_div_iff (Units.ne_zero _)).2 (hφχ _).symm
  have htriv : ∀ v i (z : Uo ((H.Sl v).adicCompletion L)), (z : ((H.Sl v).adicCompletion L)ˣ) ∈ Uc _ (max e0 R.c0 + 1) →
      H.finPart θ x.toRingHom lam v i z = 1 := fun v i z hz =>
    he0 v i z (Sp.Uc_anti _ ((le_max_left _ _).trans (Nat.le_succ _)) hz)
  have hφ1 : ∀ t : H.X.I.T, (t : GV n H.Sl) ∈ H.X.I.Tc (max e0 R.c0) → φ t = 1 :=
    Sp.gen_Tc H.Sl (MonoidHom.mker φ) _ fun v i z hz => Units.ext (hinj ((hφe v i z).trans (by
      rw [htriv v i z hz]; simp)))
  have hτ : H.τC ι = (Matrix.GeneralLinearGroup.map (algebraMap A ℂ)).comp (H.τA A) := by
    ext u i j
    exact congrArg ι (x.commutes _).symm
  obtain ⟨h1, sp, h2, h3, h4, h5, h6, h7⟩ := Sp.absSpec H.X hinj R (H.τA A) θ hθ.cont φ (max e0 R.c0) (le_max_right _ _) hφ1 hφχ
    H.lev (Sp.lev_dir H) hH.fin hθ.free (H.τC ι) hτ _ rfl
  have hcl := fun K e => spec_cl H θ ι x.toRingHom lam R.ξ K e ((Units.map (algebraMap c'.O ℂ).toMonoidHom).comp φ) hφe
  have hlow : ∀ v j, (R.χ ⟨alV n H.Sl v j, H.X.I.P_le _ (Sp.alV_mem H.Sl v j)⟩ : ℂ) = H.lowVal ι lam v j :=
    Sp.chi_alV H.Sl ι lam R.χ hχ
  have hU : ∀ v (j : Fin n), H.opC ι lam (R.d + 1) (.inr (v, j)) = H.X.UF H.m R ⟨_, Sp.alV_mem H.Sl v (j + 1)⟩ := fun v j => by
    rw [Frame.UF, Units.val_inv_eq_inv_val, hlow]
    rfl
  have hz : H.uzC ι lam (R.d + 1) = H.X.UF H.m R ⟨_, H.X.I.z_mem⟩ := by
    have := congrArg Units.val (Sp.weightChar_central_eq_prod_uniformizerDiag H.Sl R.χ)
    rw [Units.coe_prod] at this
    simp only [Units.coe_prod] at this
    rw [Frame.UF, Units.val_inv_eq_inv_val, HSet.uzC]
    congr 2
    exact (this.trans (Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun j _ => hlow v j)).symm
  refine ⟨R.d + 1, R.ξ, max e0 R.c0, sp, hR, htriv, fun K e he => ?_, fun K e he i F hF => ?_,
    fun K e he i F hF h0 μ hμ => ?_, h2, h3, fun K e he => ?_, h5, fun K i f hf => ?_, fun K K' q g f hf _ => ?_⟩
  · rw [hcl]
    exact (h1 K e he).1
  · rw [hcl] at hF ⊢
    rcases i with ⟨w, j⟩ | ⟨v, j⟩
    · obtain ⟨κ, _, u, hu⟩ := Sp.lev_sph H w.1 (j + 1)
      obtain ⟨e1, e2⟩ := hu ℂ _ (H.X.raF (R.d + 1) (H.τC ι))
      have e3 : H.opC ι lam (R.d + 1) (.inl (w, j)) = _ := e1
      rw [e3]
      exact Sp.sum_cl H.X R _ _ e _ _ u F hF (e2 hH w.2 K F hF.1.2)
    · rw [hU]
      exact ((h1 K e he).2.1 _).1 F hF
  · rw [hcl] at hF
    rw [← spec_int c' ι hal]
    rcases i with ⟨w, j⟩ | ⟨v, j⟩
    · obtain ⟨κ, _, u, hu⟩ := Sp.lev_sph H w.1 (j + 1)
      have e3 : H.opC ι lam (R.d + 1) (.inl (w, j)) = _ := (hu ℂ _ (H.X.raF (R.d + 1) (H.τC ι))).1
      rw [e3] at hμ
      exact (h1 K e he).2.2 κ u F hF h0 μ hμ
    · rw [hU] at hμ
      exact ((h1 K e he).2.1 _).2 F hF h0 μ hμ
  · rw [h4 K e he, HSet.OrdAt, hcl, hz]
    refine le_antisymm (iSup_le fun μ => ?_) (iSup_le fun μ => ?_)
    · exact le_iSup_of_le ⟨μ.1, (spec_unit c' ι hal _).1 μ.2⟩ le_rfl
    · exact le_iSup_of_le ⟨μ.1, (spec_unit c' ι hal _).2 μ.2⟩ le_rfl
  · rcases i with ⟨w, j⟩ | ⟨v, j⟩
    · obtain ⟨κ, _, u, hu⟩ := Sp.lev_sph H w.1 (j + 1)
      obtain ⟨e1, e2⟩ := hu ℂ _ (H.X.raF (R.d + 1) (H.τC ι))
      have e3 : H.opC ι lam (R.d + 1) (.inl (w, j)) = _ := e1
      have e4 : H.op A (.inl (w, j)) = _ := (hu A _ (H.X.ra (H.τA A))).1
      rw [e3, e4]
      exact h7 K K κ u (e2 hH w.2 K) f hf
    · rw [hU]
      exact h6 K ⟨_, Sp.alV_mem H.Sl v (j + 1)⟩ f hf
  · obtain ⟨K'', hK⟩ := Sp.lev_act H hH K q g
    have := h7 K K'' Unit (fun _ => H.sec (H.wq q) g) (fun F hF => by
      rw [Fintype.sum_unique]
      exact hK ℂ _ _ F hF) f hf
    rw [Fintype.sum_unique, Fintype.sum_unique] at this
    exact this
end
