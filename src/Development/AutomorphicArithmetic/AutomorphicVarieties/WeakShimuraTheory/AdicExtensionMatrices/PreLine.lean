import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PdMapAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem res_ps {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsCO Λ (PowerSeries (ResidueField Λ))]
    (x : PowerSeries (ResidueField Λ)) :
    res Λ (PowerSeries (ResidueField Λ)) x = PowerSeries.constantCoeff x := by
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (PowerSeries.constantCoeff x)
  have hm : x - algebraMap Λ (PowerSeries (ResidueField Λ)) a ∈
      maximalIdeal (PowerSeries (ResidueField Λ)) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, map_sub,
      PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C,
      IsLocalRing.ResidueField.algebraMap_eq, ha, sub_self]
    exact not_isUnit_zero
  have h0 := (res_eq_zero_iff Λ (PowerSeries (ResidueField Λ)) _).2 hm
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, ha]

theorem UpperTheory.V.Ws.sxResLift :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} [IsCO Λ (PowerSeries (ResidueField Λ))] (Q : PD Φ.ι Γ (ResidueField Λ)[X]), Φ.IsRes (C.comp ((residue Λ).comp a)) Q → Φ.IsRes ((residue Λ).comp a) (Q.map (evalRingHom 0)) ∧ Φ.Lifts a (Q.map (evalRingHom 0)) (Q.map (Polynomial.coeToPowerSeries.ringHom : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ))) := by
  intro O Γ _ _ _ Φ Λ _ _ a _ Q h
  have hev : (evalRingHom (0 : ResidueField Λ)).comp (C.comp ((residue Λ).comp a)) =
      (residue Λ).comp a := by
    ext x
    simp
  have hco : (Polynomial.coeToPowerSeries.ringHom :
      (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)).comp (C.comp ((residue Λ).comp a)) =
      (algebraMap Λ (PowerSeries (ResidueField Λ))).comp a := by
    ext x
    simp [PowerSeries.algebraMap_apply, IsLocalRing.ResidueField.algebraMap_eq]
  have hcont : ∀ {R' : Type} [CommRing R'] (f : (ResidueField Λ)[X] →+* R') (J : Ideal R'),
      (Q.map f).Cont J := by
    intro R' _ f J i j
    exact adicCont_map f bot_le (h.cont i j)
  have hpt : ∀ p : (ResidueField Λ)[X],
      res Λ (PowerSeries (ResidueField Λ)) (p : PowerSeries (ResidueField Λ)) = eval 0 p := by
    intro p
    rw [res_ps, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      coeff_zero_eq_eval_zero]
  obtain ⟨_, hp1, hr1⟩ := sxPdMap (C.comp ((residue Λ).comp a)) (evalRingHom 0) Q
  obtain ⟨_, hp2, _⟩ := sxPdMap (C.comp ((residue Λ).comp a))
    (Polynomial.coeToPowerSeries.ringHom :
      (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) Q
  refine ⟨⟨?_, ?_, hcont _ _⟩, ⟨?_, hcont _ _, ?_⟩⟩
  · have := hp1 h.pair
    rwa [hev] at this
  · have := hr1 h.res
    rwa [hev] at this
  · have := hp2 h.pair
    rwa [hco] at this
  · apply PD.ext
    · refine MonoidHom.ext fun g => Matrix.ext fun i j => ?_
      exact hpt (Q.r g i j)
    · funext v
      refine Matrix.ext fun i j => ?_
      exact hpt (Q.n v i j)
end

section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem cp_low {R : Type} [CommRing R] (M : M4 R) (σ : Equiv.Perm (Fin 4))
    (h : ∀ i j, i < j → M (σ i) (σ j) = 0) : M.charpoly = ∏ i, (X - C (M i i)) := by
  have h1 : (Matrix.reindex σ.symm σ.symm M).charpoly = M.charpoly := Matrix.charpoly_reindex _ _
  rw [← h1, ← Matrix.charpoly_transpose, Matrix.charpoly_of_upperTriangular]
  · simpa using Equiv.prod_comp σ fun i => X - C (M i i)
  · intro i j hij
    simpa using h j i hij

theorem UpperTheory.V.Ws.sxCpRes :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {R : Type} [CommRing R] (a : O →+* R) (P : PD Φ.ι Γ R), Φ.Res a P → ∀ g, (P.r g).charpoly = ∏ i, (X - C (a (Φ.χ i g))) := by
  intro O Γ _ _ Φ R _ a P h g
  simp only [← h.diag g]
  rcases h.shape with ⟨h1, -⟩ | h1
  · refine cp_low _ (Equiv.swap 1 2) fun i j hij => h1 g _ _ ?_ ?_
    · exact fun e => hij.ne ((Equiv.swap 1 2).injective e)
    · revert i j; decide
  · refine cp_low _ 1 fun i j hij => h1 g _ _ hij.ne ?_
    revert i j; decide
end

section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem preLine_desc {Λ A T S : Type} [CommRing Λ] [CommRing A] [CommRing T] [CommRing S] [Algebra Λ A]
    [Algebra Λ T] [Algebra Λ S] (f : A →ₐ[Λ] S) (j : T →ₐ[Λ] S) (hj : Function.Injective j)
    (h : ∀ x, f x ∈ j.range) : ∃ g : A →ₐ[Λ] T, ∀ x, j (g x) = f x := by
  refine ⟨(AlgEquiv.ofInjective j hj).symm.toAlgHom.comp (f.codRestrict j.range h), fun x => ?_⟩
  have := congrArg Subtype.val ((AlgEquiv.ofInjective j hj).apply_symm_apply ⟨f x, h x⟩)
  exact this

theorem UpperTheory.V.Ws.sxPreLine :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} (Y : Pre Φ a), Y.Line := by
  intro O Γ _ _ _ Φ Λ _ _ a Y Q hQ
  haveI h0 : IsCO Λ (ResidueField Λ) := (co_res Λ).1
  haveI hS : IsCO Λ (PowerSeries (ResidueField Λ)) := co_mvps Λ (ResidueField Λ) Unit
  obtain ⟨h1, h2⟩ := sxResLift Q hQ
  obtain ⟨f, hf⟩ := Y.univ _ _ _ h1 h2
  let j : (ResidueField Λ)[X] →ₐ[Λ] PowerSeries (ResidueField Λ) :=
    { (Polynomial.coeToPowerSeries.ringHom : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) with
      commutes' := fun x => by
        simp [Polynomial.algebraMap_apply, PowerSeries.algebraMap_apply] }
  have hj : Function.Injective j := Polynomial.coe_injective _
  have hf' : Y.P.map (f : Y.A →+* PowerSeries (ResidueField Λ)) = Q.map (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) := hf
  have hr : ∀ g i l, f (Y.P.r g i l) = j (Q.r g i l) := fun g i l =>
    congrArg (fun P : PD Φ.ι Γ _ => P.r g i l) hf'
  have hn : ∀ v i l, f (Y.P.n v i l) = j (Q.n v i l) := fun v i l =>
    congrArg (fun P : PD Φ.ι Γ _ => P.n v i l) hf'
  have hB : f.comp (IsScalarTower.toAlgHom Λ Y.B Y.A) = (j.comp Polynomial.CAlgHom).comp (res Λ Y.B) := by
    refine Y.genB _ _ _ (fun g n => ?_) (fun v i s hs => ?_)
    · show (f : Y.A →+* PowerSeries (ResidueField Λ)) (algebraMap Y.B Y.A _) =
        (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) ((C : ResidueField Λ →+* (ResidueField Λ)[X]) ((res Λ Y.B : Y.B →+* ResidueField Λ) _))
      rw [← coeff_map, ← coeff_map, ← coeff_map, ← coeff_map, ← coeff_map, Y.cp_map, Y.cp_red,
        ← Matrix.charpoly_map]
      have e : (Y.P.r g).map (f : Y.A →+* PowerSeries (ResidueField Λ)) = (Q.r g).map (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) := by
        ext1 i l
        exact hr g i l
      rw [e, Matrix.charpoly_map, sxCpRes _ Q hQ.res g]
      simp [Polynomial.map_prod]
    · show (f : Y.A →+* PowerSeries (ResidueField Λ)) (algebraMap Y.B Y.A _) = (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) (C (res Λ Y.B _))
      rw [Y.ψ_map v i s hs, Y.ψ_red v i s hs, ← (sxPdMap ((algebraMap Λ Y.A).comp a) _ Y.P).1, hf',
        (sxPdMap (C.comp ((residue Λ).comp a)) _ Q).1, hQ.res.char v s hs]
      rfl
  have hB' : ∀ b, f (algebraMap Y.B Y.A b) = j (C (res Λ Y.B b)) := fun b => DFunLike.congr_fun hB b
  have hrange : ∀ x, f x ∈ j.range := by
    intro x
    have hx : x ∈ Algebra.adjoin Y.B _ := Y.gen ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ⟨_, (hr _ _ _).symm⟩
      · exact ⟨_, (hn _ _ _).symm⟩
    | algebraMap b => exact ⟨_, (hB' b).symm⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  obtain ⟨g, hg⟩ := preLine_desc f j hj hrange
  refine ⟨g, ?_, fun b hb => hj ?_⟩
  · refine PD.ext (MonoidHom.ext fun s => Matrix.ext fun i l => hj ?_) (funext fun v => Matrix.ext fun i l => hj ?_)
    · exact (hg _).trans (hr s i l)
    · exact (hg _).trans (hn v i l)
  · rw [hg, hB', (res_eq_zero_iff Λ Y.B b).2 hb, map_zero]
end
