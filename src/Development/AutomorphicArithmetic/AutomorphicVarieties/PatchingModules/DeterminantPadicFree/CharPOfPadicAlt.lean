import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDvrIc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDvrPs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ExtFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SelSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DetPush

section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem exists_injective_roots_in_integral_closure {A L : Type} [CommRing A] [Field L] [Algebra A L] {n : ℕ} (p : Polynomial A)
    (hm : p.Monic) (hn : (p.map (algebraMap A L)).natDegree = n) (hsep : (p.map (algebraMap A L)).Separable)
    (hs : (p.map (algebraMap A L)).Splits) :
    ∃ al : Fin n → integralClosure A L, Function.Injective al ∧
      p.map (algebraMap A (integralClosure A L)) = ∏ b, (Polynomial.X - Polynomial.C (al b)) := by
  classical
  set pL := p.map (algebraMap A L) with hpL
  have hmL : pL.Monic := hm.map _
  have hroots : pL = (pL.roots.map fun x => Polynomial.X - Polynomial.C x).prod :=
    hs.eq_prod_roots_of_monic hmL
  have hnd : pL.roots.Nodup := Polynomial.nodup_roots hsep
  set s := pL.roots.toFinset with hsdef
  have hcard : s.card = n := by
    rw [hsdef, Multiset.toFinset_card_of_nodup hnd, ← hs.natDegree_eq_card_roots, hn]
  have hint : ∀ x ∈ s, x ∈ integralClosure A L := by
    intro x hx
    rw [hsdef, Multiset.mem_toFinset, Polynomial.mem_roots hmL.ne_zero, Polynomial.IsRoot,
      hpL, Polynomial.eval_map] at hx
    exact ⟨p, hm, hx⟩
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hcard)).symm
  refine ⟨fun b => ⟨(e b : L), hint _ (e b).2⟩, ?_, ?_⟩
  · intro b b' h
    have h2 := congrArg Subtype.val h
    exact e.injective (Subtype.ext h2)
  · apply Polynomial.map_injective (integralClosure A L).val.toRingHom Subtype.val_injective
    rw [Polynomial.map_map, Polynomial.map_prod]
    have h1 : ((integralClosure A L).val.toRingHom).comp (algebraMap A (integralClosure A L)) =
        algebraMap A L := by
      ext a
      rfl
    rw [h1]
    change pL = _
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [hroots]
    have h3 : ∏ b : Fin n, (Polynomial.X - Polynomial.C ((e b : L))) =
        ∏ x ∈ s, (Polynomial.X - Polynomial.C x) := by
      rw [Equiv.prod_comp e (fun x : s => Polynomial.X - Polynomial.C (x : L))]
      exact Finset.prod_coe_sort s (fun x => Polynomial.X - Polynomial.C x)
    convert h3.symm using 1
    · rw [Finset.prod_eq_multiset_prod, hsdef, Multiset.toFinset_val, hnd.dedup]
    · rfl

theorem UpperTheory.V.Pa.Det.splitEx :
    ∀ (l : ℕ) [Fact l.Prime] {K : Type} [Field K] [Finite K] [CharP K l] {q n : ℕ} (P : Fin q → Polynomial (PowerSeries K)), (∀ a, (P a).Monic ∧ (P a).natDegree = n ∧ ((P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))).Separable) → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (_ : IsEqDVR l A') (j : PowerSeries K →+* A') (al : Fin q → Fin n → A'), Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ ∀ a, Function.Injective (al a) ∧ (P a).map j = ∏ b, (Polynomial.X - Polynomial.C (al a b)) := by
  intro l _ K _ _ _ q n P hP
  classical
  have hQ0 : (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => ((hP a).1.map _).ne_zero
  haveI hsepE : Algebra.IsSeparable (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))) := by
    rw [← IntermediateField.isSeparable_top,
      ← (isSplittingField_iff_intermediateField.mp
        (inferInstance : Polynomial.IsSplittingField (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))) (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))).2,
      IntermediateField.isSeparable_adjoin_iff_isSeparable]
    intro x hx
    have h0 := Polynomial.aeval_eq_zero_of_mem_rootSet hx
    rw [map_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨a, _, ha⟩ := h0
    exact (hP a).2.2.of_dvd (minpoly.dvd (FractionRing (PowerSeries K)) x ha)
  haveI hcA : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have hfinA : Finite (IsLocalRing.ResidueField (PowerSeries K)) :=
    Finite.of_equiv K (PowerSeries.residueFieldOfPowerSeries).symm.toEquiv
  set_option synthInstance.maxHeartbeats 400000 in
  obtain ⟨hfin, _, _, hdvr, hcB, hloc, hres⟩ :=
    UpperTheory.V.AlgebraTools.integralClosure_complete_dvr (PowerSeries K) (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))
  have hinjAE : Function.Injective (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) := by
    rw [IsScalarTower.algebraMap_eq (PowerSeries K) (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))]
    exact (algebraMap (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))).injective.comp (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  have hj : Function.Injective (algebraMap (PowerSeries K) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))) := by
    intro x y h
    apply hinjAE
    exact congrArg Subtype.val h
  haveI hcharA : CharP (PowerSeries K) l := charP_of_injective_ringHom (PowerSeries.C (R := K)).injective l
  haveI hcharB : CharP ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) l := charP_of_injective_ringHom hj l
  have hal : ∀ a, ∃ al : Fin n → ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))), Function.Injective al ∧
      (P a).map (algebraMap (PowerSeries K) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))) = ∏ b, (Polynomial.X - Polynomial.C (al b)) := by
    intro a
    have hdeg : ((P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))).natDegree = n := by
      rw [(hP a).1.natDegree_map]
      exact (hP a).2.1
    have hmapE : (P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) =
        ((P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))).map (algebraMap (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    have hsepa : ((P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))).Separable := by
      rw [hmapE]
      exact (hP a).2.2.map
    have hspl : ((P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))).Splits := by
      rw [hmapE]
      refine Polynomial.Splits.of_dvd (Polynomial.SplittingField.splits (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))
        (Polynomial.map_ne_zero hQ0) ?_
      exact Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ a))
    exact exists_injective_roots_in_integral_closure (P a) (hP a).1 hdeg hsepa hspl
  choose al hal1 hal2 using hal
  exact ⟨↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))), inferInstance, inferInstance, hdvr, ⟨hcB, hres hfinA, hcharB⟩, algebraMap (PowerSeries K) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))), al,
    hj, hloc, RingHom.finite_algebraMap.mpr hfin, fun a => ⟨hal1 a, hal2 a⟩⟩
end

section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem padic_hom_unique {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (hl : (l : R) = 0)
    (f g : ℤ_[l] →+* R) : f = g := by
  ext z
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 z)
  have hz : z = y * (l : ℤ_[l]) + (z.appr 1 : ℤ_[l]) := by
    rw [pow_one] at hy; rw [hy]; ring
  rw [hz]
  simp [hl]

private theorem adic_push {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (f : R →+* R')
    [IsLocalHom f] {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap f := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    exact map_nonunit f y hy
  exact (ha N).comp (Ideal.quotientMap _ f hle)

private theorem span_push {K K' : Type} [Field K] [Field K'] {n a : ℕ} (j : PowerSeries K →+* PowerSeries K')
    (hj : Function.Injective j) (S : Set (Matrix (Fin n) (Fin n) (PowerSeries K)))
    (h : ∀ Z ∈ Ev (PowerSeries K) (PowerSeries K) n a, ∃ s : ℕ,
      (PowerSeries.X : PowerSeries K) ^ s • Z ∈ Submodule.span (PowerSeries K) S) :
    ∀ Z ∈ Ev (PowerSeries K') (PowerSeries K') n a, ∃ s : ℕ,
      (PowerSeries.X : PowerSeries K') ^ s • Z ∈ Submodule.span (PowerSeries K') ((fun M => M.map j) '' S) := by
  have hmap : ∀ M ∈ Submodule.span (PowerSeries K) S,
      M.map j ∈ Submodule.span (PowerSeries K') ((fun M => M.map j) '' S) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM => exact Submodule.subset_span ⟨M, hM, rfl⟩
    | zero => simp
    | add M N _ _ h1 h2 => rw [Matrix.map_add _ (map_add j)]; exact add_mem h1 h2
    | smul c M _ h1 =>
      have : (c • M).map j = j c • M.map j := by ext1 p q; simp
      rw [this]; exact Submodule.smul_mem _ _ h1
  have hX : j PowerSeries.X ≠ 0 := fun e => PowerSeries.X_ne_zero (hj (e.trans (map_zero j).symm))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hX (PowerSeries.X_irreducible (R := K'))
  obtain ⟨u, hu⟩ := hm.dvd
  intro Z hZ
  have key : ∀ p q : Fin n, ∃ s : ℕ, (PowerSeries.X : PowerSeries K') ^ s • Matrix.single p q (Z p q) ∈
      Submodule.span (PowerSeries K') ((fun M => M.map j) '' S) := by
    intro p q
    by_cases hpq : ((p : ℕ) < a) ↔ ((q : ℕ) < a)
    · have hE : Matrix.single p q (1 : PowerSeries K) ∈ Ev (PowerSeries K) (PowerSeries K) n a := by
        intro p' q'
        refine ⟨fun _ => trivial, fun e => ?_⟩
        rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
        rintro ⟨rfl, rfl⟩
        exact e hpq
      obtain ⟨s, hs⟩ := h _ hE
      refine ⟨m * s, ?_⟩
      have : (PowerSeries.X : PowerSeries K') ^ (m * s) • Matrix.single p q (Z p q) =
          (u ^ s * Z p q) • ((PowerSeries.X : PowerSeries K) ^ s • Matrix.single p q (1 : PowerSeries K)).map j := by
        ext1 p' q'
        rw [pow_mul, hu]
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
        split_ifs
        · simp only [mul_one, map_pow]; ring
        · simp
      rw [this]
      exact Submodule.smul_mem _ _ (hmap _ hs)
    · have : Z p q = 0 := (Submodule.mem_bot _).1 ((hZ p q).2 hpq)
      exact ⟨0, by simp [this]⟩
  choose s hs using key
  refine ⟨∑ p, ∑ q, s p q, ?_⟩
  rw [Matrix.matrix_eq_sum_single Z, Finset.smul_sum]
  refine Submodule.sum_mem _ fun p _ => ?_
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun q _ => ?_
  have hle : s p q ≤ ∑ p, ∑ q, s p q :=
    le_trans (Finset.single_le_sum (f := fun q => s p q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q))
      (Finset.single_le_sum (f := fun p => ∑ q, s p q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hle
  rw [hd, pow_add, mul_smul]
  exact Submodule.smul_mem _ _ (hs p q)

private theorem pushCh_inj {H A B : Type} [Group H] [CommRing A] [CommRing B] {f : A →+* B}
    (hf : Function.Injective f) {χ χ' : H →* Aˣ} (h : pushCh f χ = pushCh f χ') : χ = χ' := by
  ext g
  exact hf (congrArg Units.val (DFunLike.congr_fun h g))

private noncomputable def pushNP {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (K' : Type) [Field K'] [Finite K']
    [Algebra ℤ_[l] K'] (j : x.A →+* PowerSeries K') (hj : Function.Injective j) [IsLocalHom j]
    (he : pushCh j (F.eps ℤ_[l] x.A) = F.eps ℤ_[l] (PowerSeries K')) : NP F n where
  K := K'
  ρ := pushRep j x.ρ
  cont p q := adic_push j (x.cont p q)
  form g := by
    have h := congrArg (fun M => M.map j) (x.form g)
    have h1 : mat (pushRep j x.ρ) g = (mat x.ρ g).map j := rfl
    have h2 : mat (pushRep j x.ρ) (F.conj g) = (mat x.ρ (F.conj g)).map j := rfl
    have h3 : ((F.eps ℤ_[l] (PowerSeries K') g ^ (1 - (n : ℤ)) : (PowerSeries K')ˣ) : PowerSeries K') =
        j ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) := by
      rw [← he]
      exact (congrArg Units.val (map_zpow (Units.map (j : x.A →* PowerSeries K')) _ _)).symm
    rw [h1, h2, h3]
    simp only [Units.val_one, mul_one, Matrix.map_mul] at h ⊢
    rw [← Matrix.transpose_map, h]
    ext1 p q
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  a := x.a
  a_pos := x.a_pos
  a_le := x.a_le
  blk g p q := ⟨fun _ => trivial, fun e => by
    have : mat x.ρ g p q = 0 := (x.blk g p q).2 e
    show j (mat x.ρ g p q) = 0
    rw [this, map_zero]⟩
  span Z hZ := by
    have := span_push j hj _ x.span Z hZ
    rwa [Set.image_image] at this
  ine u g hg := by
    show GeneralLinearGroup.map j (x.ρ g) = 1
    rw [x.ine u g hg, map_one]
  ψ v i := pushCh j (x.ψ v i)
  ψ_mu v i g hg := by
    show Units.map _ (x.ψ v i g) = 1
    rw [x.ψ_mu v i g hg, map_one]
  w v := GeneralLinearGroup.map j (x.w v)
  ty := x.ty
  w_blk v p q e := by
    show j (x.w v p q) = 0
    rw [x.w_blk v p q e, map_zero]
  tri v g := by
    have e : (GeneralLinearGroup.map j (x.w v))⁻¹ * pushRep j x.ρ (F.φ v g) * GeneralLinearGroup.map j (x.w v) =
        GeneralLinearGroup.map j ((x.w v)⁻¹ * x.ρ (F.φ v g) * x.w v) := by
      rw [map_mul, map_mul, map_inv]; rfl
    rw [e]
    refine ⟨fun p q hpq => ?_, fun p => ?_⟩
    · show j (((x.w v)⁻¹ * x.ρ (F.φ v g) * x.w v : GL (Fin n) x.A) p q) = 0
      rw [(x.tri v g).1 p q hpq, map_zero]
    · show j (((x.w v)⁻¹ * x.ρ (F.φ v g) * x.w v : GL (Fin n) x.A) p p) = j _
      rw [(x.tri v g).2 p]
  N1 v := by
    refine ⟨fun p q hpq e => (x.N1 v).1 p q hpq (pushCh_inj hj e), fun p q hpq e => (x.N1 v).2 p q hpq (pushCh_inj hj ?_)⟩
    rw [e, ← he]
    ext g
    simp

theorem UpperTheory.V.Pa.Det.extEx :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (A' : Type) [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [IsEqDVR l A'] (j₀ : x.A →+* A'), Function.Injective j₀ → IsLocalHom j₀ → j₀.Finite → ∃ (x' : NP F n) (j : x.A →+* x'.A) (e : x'.A ≃+* A'), x.Ext2 x' j ∧ (∀ a, e (j a) = j₀ a) ∧ Nat.card x'.K = Nat.card (ResidueField A') := by
  intro l _ F n x A' _ _ _ hA j₀ hinj hloc hfin
  haveI := hA.complete
  haveI := hA.finite
  haveI := hA.char
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A'
  obtain ⟨e, -, -⟩ := UpperTheory.V.AlgebraTools.powerSeries_equiv_of_complete_dvr A' l t ht
  letI : Algebra ℤ_[l] (ResidueField A') := ((residue A').comp (j₀.comp (algebraMap ℤ_[l] x.A))).toAlgebra
  let j : x.A →+* PowerSeries (ResidueField A') := (e.symm : A' →+* _).comp j₀
  have hj : Function.Injective j := e.symm.injective.comp hinj
  haveI hl : IsLocalHom j := ⟨fun a ha => hloc.1 a (by simpa using ha.map e)⟩
  have hjf : j.Finite := RingHom.Finite.comp (RingHom.Finite.of_surjective _ e.symm.surjective) hfin
  have h0 : (l : PowerSeries (ResidueField A')) = 0 := e.injective (by simp)
  have he : pushCh j (F.eps ℤ_[l] x.A) = F.eps ℤ_[l] (PowerSeries (ResidueField A')) := by
    have := padic_hom_unique h0 (j.comp ((algebraMap ℤ_[l] x.A).comp (algebraMap ℤ_[l] ℤ_[l])))
      ((algebraMap ℤ_[l] _).comp (algebraMap ℤ_[l] ℤ_[l]))
    unfold GFrame.eps
    rw [← this]
    rfl
  exact ⟨pushNP x (ResidueField A') j hj he, j, e, ⟨⟨hj, hl, hjf, rfl, rfl, fun _ _ => rfl⟩, fun _ => rfl, rfl⟩,
    fun a => e.apply_symm_apply _, rfl⟩
end

section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem map_finite {K L : Type} [Field K] [Field L] [Finite L] (f : K →+* L) :
    (PowerSeries.map f).Finite := by
  classical
  letI := f.toAlgebra
  letI := (PowerSeries.map f).toAlgebra
  haveI : Module.Finite K L := Module.Finite.of_finite
  let b := Module.finBasis K L
  show Module.Finite (PowerSeries K) (PowerSeries L)
  refine ⟨⟨Finset.univ.image (fun i => PowerSeries.C (b i)), ?_⟩⟩
  rw [eq_top_iff]
  intro φ _
  have key : φ = ∑ i, (PowerSeries.mk fun n => b.repr (PowerSeries.coeff n φ) i) •
      PowerSeries.C (b i) := by
    ext n
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_sum, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact (b.sum_repr _).symm.trans (Finset.sum_congr rfl fun i _ => Algebra.smul_def _ _)
  rw [key]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp

private theorem bijective_residue_comp_powerSeries_C (F : Type) [Field F] :
    Function.Bijective ((residue (PowerSeries F)).comp (PowerSeries.C (R := F))) := by
  refine ⟨RingHom.injective _, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective y
  refine ⟨PowerSeries.constantCoeff x, ?_⟩
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal,
    mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, map_sub, PowerSeries.constantCoeff_C,
    sub_self]
  exact not_isUnit_zero

theorem UpperTheory.V.Pa.Det.resExt :
    ∀ (l : ℕ) [Fact l.Prime] {K : Type} [Field K] [Finite K] [CharP K l] (d D : ℕ), Nat.card K = l ^ d → d ∣ D → D ≠ 0 → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (_ : IsEqDVR l A') (j : PowerSeries K →+* A'), Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ Nat.card (ResidueField A') = l ^ D ∧ Irreducible (j PowerSeries.X) := by
  intro l _ K _ _ _ d D hK hdD hD
  have hd : d ≠ 0 := by
    rintro rfl
    exact hD (zero_dvd_iff.mp hdD)
  letI : Algebra (ZMod l) K := ZMod.algebra K l
  let e := GaloisField.algEquivGaloisField l d hK
  obtain ⟨g⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod l)
    (K := GaloisField l d) (L := GaloisField l D)
    (by rw [GaloisField.finrank l hd, GaloisField.finrank l hD]; exact hdD)
  let φ : K →+* GaloisField l D := (g.comp e.toAlgHom).toRingHom
  have hcc : ∀ ψ : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.map φ ψ) =
      φ (PowerSeries.constantCoeff ψ) := by
    intro ψ
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  haveI : CharP (PowerSeries (GaloisField l D)) l :=
    charP_of_injective_ringHom (PowerSeries.C (R := GaloisField l D)).injective l
  haveI : UpperTheory.V.Pa.IsEqDVR l (PowerSeries (GaloisField l D)) :=
    ⟨by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance,
      Finite.of_surjective _ (bijective_residue_comp_powerSeries_C (GaloisField l D)).2, inferInstance⟩
  refine ⟨PowerSeries (GaloisField l D), inferInstance, inferInstance, inferInstance, inferInstance,
    PowerSeries.map φ, PowerSeries.map_injective _ φ.injective, ⟨fun ψ hψ => ?_⟩,
    map_finite φ, ?_, ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, hcc, isUnit_iff_ne_zero,
      map_ne_zero_iff _ φ.injective] at hψ
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    exact hψ
  · rw [← Nat.card_congr (Equiv.ofBijective _ (bijective_residue_comp_powerSeries_C (GaloisField l D))),
      GaloisField.card l D hD]
  · rw [PowerSeries.map_X]
    exact PowerSeries.X_irreducible
end

section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.extTrans :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' x'' : NP F n) (j : x.A →+* x'.A) (j' : x'.A →+* x''.A), x.Ext2 x' j → x'.Ext2 x'' j' → x.Ext2 x'' (j'.comp j) := by
  intro l _ F n x x' x'' j j' h1 h2
  obtain ⟨⟨hi, hl, hf, hρ, ha, hψ⟩, hw, ht⟩ := h1
  obtain ⟨⟨hi', hl', hf', hρ', ha', hψ'⟩, hw', ht'⟩ := h2
  refine ⟨⟨hi'.comp hi, @RingHom.isLocalHom_comp _ _ _ _ _ _ j' j hl' hl, hf'.comp hf, ?_, ha'.trans ha, ?_⟩,
    ?_, ht'.trans ht⟩
  · rw [hρ', hρ]
    simp only [pushRep, GeneralLinearGroup.map_comp, MonoidHom.comp_assoc]
  · intro v i
    rw [hψ', hψ]
    ext g
    simp [pushCh]
  · intro v
    rw [hw', hw, GeneralLinearGroup.map_comp]
    rfl
end

section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem mapL {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (j : A →+* B) (p : B →+ A)
    (hp : ∀ a y, p (j a * y) = a * p y) (M : Matrix (Fin n) (Fin n) A) (Z : Matrix (Fin n) (Fin n) B) :
    (M.map j * Z).map p = M * Z.map p := by
  ext a b
  simp [Matrix.mul_apply, map_sum, hp]

private theorem mapR {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (j : A →+* B) (p : B →+ A)
    (hp : ∀ a y, p (j a * y) = a * p y) (M : Matrix (Fin n) (Fin n) A) (Z : Matrix (Fin n) (Fin n) B) :
    (Z * M.map j).map p = Z.map p * M := by
  ext a b
  simp only [Matrix.mul_apply, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm, hp, mul_comm]

theorem UpperTheory.V.Pa.Det.compSel :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → ∀ (p : x'.A →+ x.A), (∀ a y, p (j a * y) = a * p y) → (∀ N : ℕ, ∃ N' : ℕ, ∀ y ∈ Ideal.span {x'.t} ^ N', p y ∈ Ideal.span {x.t} ^ N) → (∀ z ∈ SelZ F x'.t (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (Od x'.A x'.A n x'.a), (fun g => (z g).map p) ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a)) ∧ ∀ z ∈ Bd F (x'.ρX x'.A) (Od x'.A x'.A n x'.a), (fun g => (z g).map p) ∈ Bd F (x.ρX x.A) (Od x.A x.A n x.a) := by
  intro l _ F n x x' j hE p hp hc
  obtain ⟨⟨-, -, -, hρ, ha, -⟩, hw, -⟩ := hE
  have e1 : ∀ g, x'.ρX x'.A g = (x.ρX x.A g).map j := by
    intro g
    ext a b
    simp [NP.ρX, hρ, mat]
  have e2 : ∀ v, x'.wX x'.A v = (x.wX x.A v).map j := by
    intro v
    ext a b
    simp [NP.wX, hw]
  have e3 : ∀ v, x'.wiX x'.A v = (x.wiX x.A v).map j := by
    intro v
    ext a b
    simp only [NP.wiX, hw, ← map_inv]
    rfl
  have hOd : ∀ Y ∈ Od x'.A x'.A n x'.a, Y.map p ∈ Od x.A x.A n x.a := by
    intro Y hY a b
    refine ⟨fun h => ?_, fun _ => trivial⟩
    have := (hY a b).1 (by rw [ha]; exact h)
    rw [Submodule.mem_bot] at this ⊢
    simp [this]
  have hsub : ∀ Y Z : Matrix (Fin n) (Fin n) x'.A, (Y - Z).map p = Y.map p - Z.map p := by
    intro Y Z; ext a b; simp
  have hadd : ∀ Y Z : Matrix (Fin n) (Fin n) x'.A, (Y + Z).map p = Y.map p + Z.map p := by
    intro Y Z; ext a b; simp
  have hd : ∀ Y g, (dY F (x'.ρX x'.A) Y g).map p = dY F (x.ρX x.A) (Y.map p) g := by
    intro Y g
    simp only [dY]
    rw [hsub, e1, e1, mapR j p hp, mapL j p hp]
  refine ⟨?_, ?_⟩
  · rintro z ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun g => hOd _ (h1 g), ?_, ?_, ?_, ?_, ?_⟩
    · intro a b N
      obtain ⟨N', hN⟩ := hc N
      have := h2 a b N'
      rw [IsLocallyConstant.iff_eventually_eq] at this ⊢
      intro g
      filter_upwards [this g] with h hh
      rw [Ideal.Quotient.eq] at hh ⊢
      have := hN _ hh
      rw [map_sub] at this
      exact this
    · intro g h
      simp only
      rw [h3, hadd, e1, e1, mapR j p hp, mapL j p hp]
    · intro g
      simp only
      rw [h4]
      ext a b
      simp
    · intro u g hg
      simp only
      rw [h5 u g hg]
      ext a b
      simp
    · intro v
      obtain ⟨Y, hY, hL⟩ := h6 v
      refine ⟨Y.map p, hOd _ hY, fun g => ?_⟩
      have key : x.wiX x.A v * ((z (F.φ v g)).map p - dY F (x.ρX x.A) (Y.map p) (F.φ v g)) * x.wX x.A v =
          (x'.wiX x'.A v * (z (F.φ v g) - dY F (x'.ρX x'.A) Y (F.φ v g)) * x'.wX x'.A v).map p := by
        rw [e2, e3, mapR j p hp, mapL j p hp, hsub, hd]
      refine ⟨fun a b hab => ?_, fun hg a => ?_⟩
      · simp only
        rw [key, Matrix.map_apply, (hL g).1 a b hab, map_zero]
      · simp only
        rw [key, Matrix.map_apply, (hL g).2 hg a, map_zero]
  · rintro z ⟨Y, hY, hT, rfl⟩
    refine ⟨Y.map p, hOd _ hY, ?_, funext fun g => hd Y g⟩
    ext a b
    have := congrFun (congrFun hT a) b
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    simp [this]
end

section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem adicCont_map {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] (j : R →+* S)
    (I : Ideal R) (J : Ideal S) (h : I.map j ≤ J) (f : Γ → R) (hf : AdicCont I f) :
    AdicCont J fun g => j (f g) := by
  intro N
  have hN : I ^ N ≤ (J ^ N).comap j := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono h N
  exact (hf N).comp (Ideal.quotientMap (J ^ N) j hN)

private theorem od_map {R S : Type} [CommRing R] [CommRing S] (j : R →+* S) {n a : ℕ}
    {Z : Matrix (Fin n) (Fin n) R} (h : Z ∈ Od R R n a) : Z.map j ∈ Od S S n a := by
  intro i k
  refine ⟨fun e => ?_, fun _ => Submodule.mem_top⟩
  have := (h i k).1 e
  rw [Submodule.mem_bot] at this ⊢
  simp [this]

theorem UpperTheory.V.Pa.Det.pushSel :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → (∀ z ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a), (fun g => (z g).map j) ∈ SelZ F x'.t (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (Od x'.A x'.A n x'.a)) ∧ (∀ z ∈ Bd F (x.ρX x.A) (Od x.A x.A n x.a), (fun g => (z g).map j) ∈ Bd F (x'.ρX x'.A) (Od x'.A x'.A n x'.a)) ∧ ∀ z v Y, LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) z v Y → LocAt F (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (fun g => (z g).map j) v (Y.map j) := by
  intro l _ F n x x' j hE
  obtain ⟨⟨-, hloc, -, hρ, ha, -⟩, hw, -⟩ := hE
  have eρ : ∀ g, x'.ρX x'.A g = j.mapMatrix (x.ρX x.A g) := by
    intro g
    ext i k : 1
    simp only [NP.ρX, hρ]
    rfl
  have ew : ∀ v, x'.wX x'.A v = j.mapMatrix (x.wX x.A v) := by
    intro v
    ext i k : 1
    simp only [NP.wX, hw]
    rfl
  have ewi : ∀ v, x'.wiX x'.A v = j.mapMatrix (x.wiX x.A v) := by
    intro v
    ext i k : 1
    simp only [NP.wiX, hw, ← map_inv]
    rfl
  have ed : ∀ Y g, dY F (x'.ρX x'.A) (Y.map j) g = j.mapMatrix (dY F (x.ρX x.A) Y g) := by
    intro Y g
    simp only [dY, eρ, map_sub, map_mul]
    rfl
  have hL : ∀ z v Y, LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) z v Y →
      LocAt F (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (fun g => (z g).map j) v (Y.map j) := by
    intro z v Y h g
    have key : x'.wiX x'.A v * ((z (F.φ v g)).map j - dY F (x'.ρX x'.A) (Y.map j) (F.φ v g)) * x'.wX x'.A v
        = j.mapMatrix (x.wiX x.A v * (z (F.φ v g) - dY F (x.ρX x.A) Y (F.φ v g)) * x.wX x.A v) := by
      rw [ed, ew, ewi, map_mul, map_mul, map_sub]
      rfl
    refine ⟨fun i k hik => ?_, fun hg i => ?_⟩
    · simp only [key, RingHom.mapMatrix_apply, Matrix.map_apply, (h g).1 i k hik, map_zero]
    · simp only [key, RingHom.mapMatrix_apply, Matrix.map_apply, (h g).2 hg i, map_zero]
  have ht : (Ideal.span {algebraMap x.A x.A x.t}).map j ≤ Ideal.span {algebraMap x'.A x'.A x'.t} := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    change (PowerSeries.X : PowerSeries x'.K) ∣ j PowerSeries.X
    rw [PowerSeries.X_dvd_iff]
    by_contra hne
    have hu : IsUnit (j PowerSeries.X) := PowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit hne)
    have hX := PowerSeries.isUnit_iff_constantCoeff.1 (hloc.map_nonunit _ hu)
    simp at hX
  refine ⟨?_, ?_, hL⟩
  · rintro z ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun g => ha ▸ od_map j (h1 g), fun i k => adicCont_map j _ _ ht _ (h2 i k), fun g h => ?_,
      fun g => ?_, fun u g hg => ?_, fun v => ?_⟩
    · change j.mapMatrix (z (g * h)) = j.mapMatrix (z g) + _ * j.mapMatrix (z h) * _
      rw [h3, eρ, eρ, map_add, map_mul, map_mul]
    · ext i k : 1
      simp [h4]
    · simp [h5 u g hg]
    · obtain ⟨Y, hY, hl⟩ := h6 v
      exact ⟨Y.map j, ha ▸ od_map j hY, hL z v Y hl⟩
  · rintro z ⟨Y, hY, hT, rfl⟩
    refine ⟨Y.map j, ha ▸ od_map j hY, ?_, ?_⟩
    · rw [← Matrix.transpose_map, hT]
      ext i k : 1
      simp
    · funext g
      exact (ed Y g).symm
end

section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.kapPush :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → ∀ k : Kap x, ∃ (k' : Kap x') (e : k'.g = k.g), (∀ i g, k'.κ i g = (k.κ (Fin.cast e i) g).map j) ∧ ∀ i v, k'.Y i v = (k.Y (Fin.cast e i) v).map j := by
  intro l _ F n x x' j hE k
  obtain ⟨m, b, p, -, hb, hp, -, hc, e, u, -, hu⟩ := UpperTheory.V.Pa.Det.extFree j hE.1.1 hE.1.2.1 hE.1.2.2.1
  obtain ⟨pS, pB, pL⟩ := UpperTheory.V.Pa.Det.pushSel x x' j hE
  have cS := fun i => (UpperTheory.V.Pa.Det.compSel x x' j hE (p i) (hp i) (fun N => (hc N).imp fun _ h y hy => h y hy i)).1
  have cB := fun i => (UpperTheory.V.Pa.Det.compSel x x' j hE (p i) (hp i) (fun N => (hc N).imp fun _ h y hy => h y hy i)).2
  obtain ⟨S, hS⟩ := (UpperTheory.V.Pa.Det.selSub F x'.t (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (Od x'.A x'.A n x'.a)).2
  have ha : x'.a = x.a := hE.1.2.2.2.2.1
  refine ⟨⟨k.g, fun i g => (k.κ i g).map j, fun i => pS _ (k.mem i), fun i v => (k.Y i v).map j, ?_,
    fun i v => pL _ _ _ (k.loc i v), ?_, ?_⟩, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro i v r s
    refine ⟨fun h => ?_, fun _ => Submodule.mem_top⟩
    have := (k.Y_mem i v r s).1 (by rw [← ha]; exact h)
    rw [Submodule.mem_bot] at this ⊢
    simp [this]
  · intro c hcB
    have h0 : ∀ i, (fun a => p i (c a)) = 0 := by
      intro i
      apply k.indep
      convert cB i _ hcB using 1
      funext g
      ext r s : 1
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_comm (c a), hp, mul_comm]
    funext a
    rw [hb (c a)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show p i (c a) = 0 from congrFun (h0 i) a, map_zero, zero_mul]
  · intro z hz
    choose s c hsc using fun i => k.gen _ (cS i z hz)
    have hle : ∀ i, s i ≤ ∑ i, s i := fun i =>
      Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    set N := ∑ i, s i with hN
    let d : Fin m → x'.A := fun i => ((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) * b i * j (x.t ^ (N - s i))
    have h3 : (u : x'.A) ^ N * ((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow, Units.val_one]
    have key : ∀ y : x'.A, ∑ i, d i * j (x.t ^ s i * p i y) = x'.t ^ (e * N) * y := by
      intro y
      conv_rhs => rw [hb y, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h4 : j (x.t ^ (N - s i)) * j (x.t ^ s i) = (u : x'.A) ^ N * x'.t ^ (e * N) := by
        rw [← map_mul, ← pow_add, Nat.sub_add_cancel (hle i), map_pow, hu, mul_pow, pow_mul]
      simp only [d, map_mul]
      linear_combination (((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) * b i * j (p i y)) * h4
        + (x'.t ^ (e * N) * b i * j (p i y)) * h3
    refine ⟨e * N, fun a => ∑ i, d i * j (c i a), ?_⟩
    have hm : ∑ i, d i • (fun g => ((x.t ^ s i • (fun g => (z g).map (p i)) - ∑ a, c i a • k.κ a) g).map j) ∈ S := by
      refine S.sum_mem fun i _ => S.smul_mem _ ?_
      have := pB _ (hsc i)
      rw [← hS] at this
      exact this
    rw [← hS, SetLike.mem_coe]
    convert hm using 1
    funext g
    ext r t : 1
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul, map_sum, map_sub, mul_sub, Finset.sum_sub_distrib, key, Finset.sum_mul,
      Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    simp only [map_mul, mul_assoc]
end

section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem charP_of_padic {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) :
    CharP K l := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpr : p.Prime := CharP.char_is_prime K p
  by_cases h : p = l
  · subst h
    exact hp
  · exfalso
    have hu : IsUnit (p : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes Fact.out hpr).2 (Ne.symm h)
    have hu' := hu.map f
    rw [map_natCast, CharP.cast_eq_zero] at hu'
    exact not_isUnit_zero hu'

theorem UpperTheory.V.Pa.Det.onePt :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) {q : ℕ} (sg : Fin q → F.G₀), (∀ a, ((mat x.ρ (sg a)).charpoly.map (algebraMap x.A (FractionRing x.A))).Separable) → Detects k (Set.range sg) → ∃ d : ℕ, d ≠ 0 ∧ ∀ D, d ∣ D → D ≠ 0 → ∃ (x' : NP F n) (j : x.A →+* x'.A) (k' : Kap x') (al : Fin q → Fin n → x'.A), x.Ext x' j ∧ Nat.card x'.K = l ^ D ∧ Detects k' (Set.range sg) ∧ ∀ a, Function.Injective (al a) ∧ (mat x'.ρ (sg a)).charpoly = ∏ b, (Polynomial.X - Polynomial.C (al a b)) := by
  intro l _ F n x k q sg hsep hdet
  haveI : CharP x.K l := charP_of_padic (algebraMap ℤ_[l] x.K)
  have hmat : ∀ (y y' : NP F n) (j : y.A →+* y'.A), y.Ext y' j → ∀ g, mat y'.ρ g = (mat y.ρ g).map j := by
    intro y y' j h g
    rw [h.2.2.2.1]
    rfl
  obtain ⟨A1, _, _, _, _, j1, al1, hj1i, hj1l, hj1f, hal1⟩ :=
    Det.splitEx l (n := n) (fun a => (mat x.ρ (sg a)).charpoly)
      (fun a => ⟨Matrix.charpoly_monic _, by simp [Matrix.charpoly_natDegree_eq_dim], hsep a⟩)
  obtain ⟨x1, J1, e1, hE1, he1, -⟩ := Det.extEx x A1 j1 hj1i hj1l hj1f
  haveI : CharP x1.K l := charP_of_padic (algebraMap ℤ_[l] x1.K)
  haveI := Fintype.ofFinite x1.K
  obtain ⟨d, -, hcard⟩ := FiniteField.card x1.K l
  refine ⟨(d : ℕ), d.ne_zero, ?_⟩
  intro D hdD hD0
  obtain ⟨A2, _, _, _, _, j2, hj2i, hj2l, hj2f, hres2, -⟩ :=
    Det.resExt l (K := x1.K) d D (by rw [Nat.card_eq_fintype_card]; exact hcard) hdD hD0
  obtain ⟨x2, J2, e2, hE2, -, hc2⟩ := Det.extEx x1 A2 j2 hj2i hj2l hj2f
  have hE := Det.extTrans x x1 x2 J1 J2 hE1 hE2
  obtain ⟨k', e, hk, -⟩ := Det.kapPush x x2 _ hE k
  refine ⟨x2, J2.comp J1, k', fun a b => J2 (e1.symm (al1 a b)), hE.1, by rw [hc2, hres2],
    Det.detPush x x2 _ hE k k' e hk _ hdet, fun a => ⟨?_, ?_⟩⟩
  · exact hE2.1.1.comp (e1.symm.injective.comp (hal1 a).1)
  · have h1 : J1 = (e1.symm : A1 →+* x1.A).comp j1 := by
      refine RingHom.ext fun t => ?_
      simp [← he1 t]
    have key : Polynomial.map J1 (mat x.ρ (sg a)).charpoly =
        ∏ b, (Polynomial.X - Polynomial.C (e1.symm (al1 a b))) := by
      rw [h1, ← Polynomial.map_map, (hal1 a).2, Polynomial.map_prod]
      simp
    rw [hmat x x2 _ hE.1, Matrix.charpoly_map, ← Polynomial.map_map, key, Polynomial.map_prod]
    simp
end
