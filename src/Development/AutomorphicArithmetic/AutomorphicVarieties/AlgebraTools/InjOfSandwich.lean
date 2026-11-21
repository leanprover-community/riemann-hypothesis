import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.nakayama

section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem grSpan_mem {Λ : Type} [CommRing Λ] {σ : Type} (d : σ → ℕ)
    (J : Ideal (MvPowerSeries σ Λ)) (T : Finset σ) (hJ : ∀ s, MvPowerSeries.X s ^ d s ∈ J) :
    ∀ g : MvPowerSeries σ Λ,
      (∀ n : σ →₀ ℕ, (∀ s ∈ T, n s < d s) → MvPowerSeries.coeff n g = 0) → g ∈ J := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    have h0 : g = 0 := by
      ext n
      exact hg n (by simp)
    rw [h0]
    exact J.zero_mem
  | insert t T ht ih =>
    intro g hg
    let h : MvPowerSeries σ Λ := fun n => MvPowerSeries.coeff (n + Finsupp.single t (d t)) g
    let g' : MvPowerSeries σ Λ := fun n => if n t < d t then MvPowerSeries.coeff n g else 0
    have hh : ∀ n, MvPowerSeries.coeff n h = MvPowerSeries.coeff (n + Finsupp.single t (d t)) g :=
      fun n => rfl
    have hg' : ∀ n, MvPowerSeries.coeff n g' = if n t < d t then MvPowerSeries.coeff n g else 0 :=
      fun n => rfl
    have hsplit : g = MvPowerSeries.X t ^ d t * h + g' := by
      ext n
      rw [map_add, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul, hg', hh]
      by_cases hn : d t ≤ n t
      · have hle : Finsupp.single t (d t) ≤ n := Finsupp.single_le_iff.2 hn
        rw [if_pos hle, if_neg (by omega), one_mul, tsub_add_cancel_of_le hle, add_zero]
      · have hle : ¬ Finsupp.single t (d t) ≤ n := fun h' => hn (Finsupp.single_le_iff.1 h')
        rw [if_neg hle, if_pos (by omega), zero_add]
    rw [hsplit]
    refine J.add_mem (J.mul_mem_right _ (hJ t)) (ih g' fun n hn => ?_)
    rw [hg']
    split_ifs with hnt
    · exact hg n fun s hs => by
        rcases Finset.mem_insert.1 hs with rfl | hs'
        · exact hnt
        · exact hn s hs'
    · rfl

private theorem grSpan_prod {Λ : Type} [CommRing Λ] {σ : Type} [Fintype σ] (a : σ → ℕ) :
    (∏ s, MvPowerSeries.X s ^ a s : MvPowerSeries σ Λ) =
      MvPowerSeries.monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  classical
  simp_rw [MvPowerSeries.X_pow_eq]
  rw [Finsupp.equivFunOnFinite_symm_eq_sum]
  induction (Finset.univ : Finset σ) using Finset.induction_on with
  | empty => simp
  | insert x t hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, MvPowerSeries.monomial_mul_monomial, one_mul]

private theorem grSpan_small {Λ : Type} [CommRing Λ] {σ : Type} [Fintype σ] [DecidableEq σ]
    (d : σ → ℕ) (f : MvPowerSeries σ Λ) (n : σ →₀ ℕ) (hn : ∀ s, n s < d s) :
    MvPowerSeries.coeff n (f - ∑ α : (∀ s, Fin (d s)),
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun s => (α s : ℕ)) f •
        (∏ s, MvPowerSeries.X s ^ (α s : ℕ) : MvPowerSeries σ Λ)) = 0 := by
  rw [map_sub, map_sum, sub_eq_zero]
  simp only [grSpan_prod, map_smul, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (fun s => ⟨n s, hn s⟩ : ∀ s, Fin (d s))]
  · simp [Finsupp.equivFunOnFinite_symm_coe]
  · intro β _ hβ
    rw [if_neg]
    intro h
    apply hβ
    funext s
    exact Fin.ext (by have := DFunLike.congr_fun h s; simpa using this.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem UpperTheory.V.AlgebraTools.mvPowerSeries_span_monomials :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ] (σ : Type) [Fintype σ] (d : σ → ℕ) (w : σ → MvPowerSeries σ Λ),
      (∀ s, w s - MvPowerSeries.X s ^ d s ∈ (IsLocalRing.maximalIdeal Λ).map (MvPowerSeries.C : Λ →+* MvPowerSeries σ Λ)) →
      Submodule.span Λ (Set.range fun α : (∀ s, Fin (d s)) =>
        Ideal.Quotient.mk (Ideal.span (Set.range w)) (∏ s, MvPowerSeries.X s ^ (α s : ℕ))) = ⊤ := by
  intro Λ _ _ _ _ σ _ d w hw
  classical
  set m := IsLocalRing.maximalIdeal Λ with hm
  have hjac : m.map (algebraMap Λ (MvPowerSeries σ Λ)) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_jacobson_bot]
    intro y
    have key : ∀ c : Λ, IsUnit (r * c + 1) := by
      intro c
      by_contra hu
      have h1 : r * c + 1 ∈ m := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hu)
      have h2 : r * c ∈ m := Ideal.mul_mem_right _ _ hr
      have h3 := Ideal.sub_mem _ h1 h2
      rw [add_sub_cancel_left] at h3
      exact (IsLocalRing.maximalIdeal.isMaximal Λ).ne_top ((Ideal.eq_top_iff_one _).2 h3)
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simpa [MvPowerSeries.algebraMap_apply] using key _
  haveI hQA : IsHausdorff (m.map (algebraMap Λ (MvPowerSeries σ Λ)))
      (MvPowerSeries σ Λ ⧸ Ideal.span (Set.range w)) := IsHausdorff.of_le_jacobson _ _ hjac
  haveI : IsHausdorff m (MvPowerSeries σ Λ ⧸ Ideal.span (Set.range w)) :=
    IsHausdorff.of_map (S := MvPowerSeries σ Λ)
      (J := m.map (algebraMap Λ (MvPowerSeries σ Λ))) (hIJ := le_rfl)
  obtain ⟨hnak, -⟩ := UpperTheory.V.abelian₂.nakayama Λ m (MvPowerSeries σ Λ ⧸ Ideal.span (Set.range w))
  rw [← (Fintype.equivFin (∀ s, Fin (d s))).symm.surjective.range_comp]
  apply hnak
  rw [(Fintype.equivFin (∀ s, Fin (d s))).symm.surjective.range_comp, eq_top_iff]
  rintro x -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hJ : ∀ s, MvPowerSeries.X s ^ d s ∈
      Ideal.span (Set.range w) ⊔ m.map (MvPowerSeries.C : Λ →+* MvPowerSeries σ Λ) := fun s => by
    have h1 : w s ∈ Ideal.span (Set.range w) ⊔ m.map (MvPowerSeries.C : Λ →+* MvPowerSeries σ Λ) :=
      Ideal.mem_sup_left (Ideal.subset_span ⟨s, rfl⟩)
    have h2 : w s - MvPowerSeries.X s ^ d s ∈
        Ideal.span (Set.range w) ⊔ m.map (MvPowerSeries.C : Λ →+* MvPowerSeries σ Λ) :=
      Ideal.mem_sup_right (hw s)
    simpa using Ideal.sub_mem _ h1 h2
  have hmem := grSpan_mem d _ Finset.univ hJ _
    (fun n hn => grSpan_small d f n (fun s => hn s (Finset.mem_univ s)))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
  have hab' := hab.symm
  rw [sub_eq_iff_eq_add] at hab'
  rw [hab', map_add, map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_right ?_) (Submodule.mem_sup_left ?_)
  · have h1 : Ideal.Quotient.mk (Ideal.span (Set.range w)) b ∈
        ((m.map (algebraMap Λ (MvPowerSeries σ Λ))) • ⊤ :
          Submodule (MvPowerSeries σ Λ) (MvPowerSeries σ Λ ⧸ Ideal.span (Set.range w))) := by
      have e : Ideal.Quotient.mk (Ideal.span (Set.range w)) b =
          b • Ideal.Quotient.mk (Ideal.span (Set.range w)) 1 := by
        rw [map_one, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
      rw [e]
      exact Submodule.smul_mem_smul hb Submodule.mem_top
    have h2 := Submodule.restrictScalars_map_smul_eq m
      (⊤ : Submodule (MvPowerSeries σ Λ) (MvPowerSeries σ Λ ⧸ Ideal.span (Set.range w)))
    rw [Submodule.restrictScalars_top] at h2
    rw [← h2, Submodule.restrictScalars_mem]
    exact h1
  · rw [map_sum]
    refine Submodule.sum_mem _ fun α _ => ?_
    have e := map_smul (Ideal.Quotient.mkₐ Λ (Ideal.span (Set.range w)))
      (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun s => (α s : ℕ)) f)
      (∏ s, MvPowerSeries.X s ^ (α s : ℕ))
    rw [Ideal.Quotient.mkₐ_eq_mk] at e
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)
end

section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem inj_of_sandwich {R Q F ι : Type*} [CommRing R] [AddCommGroup Q] [Module R Q]
    [AddCommGroup F] [Module R F] [Fintype ι] (g : (ι → R) →ₗ[R] Q) (f : Q →ₗ[R] F)
    (e : F ≃ₗ[R] (ι → R)) (hg : Function.Surjective g) (hf : Function.Surjective f) :
    Function.Injective f := by
  have hs : Function.Surjective (e.toLinearMap ∘ₗ f ∘ₗ g) := e.surjective.comp (hf.comp hg)
  have hi := OrzechProperty.injective_of_surjective_endomorphism _ hs
  intro a b hab
  obtain ⟨x, rfl⟩ := hg a
  obtain ⟨y, rfl⟩ := hg b
  have : x = y := hi (by simp [hab])
  rw [this]

theorem UpperTheory.V.AlgebraTools.groupRing_ker :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ] (l : ℕ), l.Prime → (l : Λ) ∈ IsLocalRing.maximalIdeal Λ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (e : σ → ℕ) (φ : MvPowerSeries σ Λ →ₐ[Λ] MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s)))), (∀ s : σ, φ (1 + MvPowerSeries.X s) = MonoidAlgebra.of Λ (∀ s, Multiplicative (ZMod (l ^ e s))) (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s))))) → Function.Surjective φ →
      RingHom.ker φ = Ideal.span (Set.range fun s => (1 + MvPowerSeries.X s : MvPowerSeries σ Λ) ^ l ^ e s - 1) := by
  intro Λ _ _ _ _ l hl hlm σ _ _ e φ hφ hsurj
  haveI : ∀ s, NeZero (l ^ e s) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩
  set w : σ → MvPowerSeries σ Λ := fun s => (1 + MvPowerSeries.X s) ^ l ^ e s - 1 with hw
  set I : Ideal (MvPowerSeries σ Λ) := Ideal.span (Set.range w) with hI
  have hle : I ≤ RingHom.ker φ := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    have h1 : (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s))) :
        ∀ s, Multiplicative (ZMod (l ^ e s))) ^ (l ^ e s) = 1 := by
      rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero,
        Pi.mulSingle_one]
    simp only [SetLike.mem_coe, RingHom.mem_ker, hw, map_sub, map_pow, hφ, map_one]
    rw [← map_pow, h1, map_one, sub_self]
  have hwm : ∀ s, w s - MvPowerSeries.X s ^ (l ^ e s) ∈
      Ideal.map MvPowerSeries.C (IsLocalRing.maximalIdeal Λ) := by
    intro s
    obtain ⟨m, hm⟩ : ∃ m, l ^ e s = m + 1 := ⟨l ^ e s - 1, (Nat.succ_pred_eq_of_pos (pow_pos hl.pos _)).symm⟩
    have hlC : ((l : ℕ) : MvPowerSeries σ Λ) ∈ Ideal.map MvPowerSeries.C (IsLocalRing.maximalIdeal Λ) := by
      rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := Λ))]
      exact Ideal.mem_map_of_mem _ hlm
    simp only [hw]
    rw [add_comm, add_pow, hm, Finset.sum_range_succ, Finset.sum_range_succ']
    have key : ∀ k ∈ Finset.range m, MvPowerSeries.X s ^ (k + 1) * (1 : MvPowerSeries σ Λ) ^ (m + 1 - (k + 1)) *
        (((m + 1).choose (k + 1) : ℕ) : MvPowerSeries σ Λ) ∈ Ideal.map MvPowerSeries.C (IsLocalRing.maximalIdeal Λ) := by
      intro k hk
      have hd : l ∣ (m + 1).choose (k + 1) := by
        rw [← hm]
        refine hl.dvd_choose_pow (Nat.succ_ne_zero k) ?_
        rw [hm]; have := Finset.mem_range.mp hk; omega
      obtain ⟨t, ht⟩ := hd
      rw [ht, Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hlC)
    have hsum := Ideal.sum_mem _ key
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one,
      Nat.sub_zero, one_mul] at hsum ⊢
    convert hsum using 1
    ring
  have hIφ : ∀ a ∈ I, φ a = 0 := fun a ha => hle ha
  refine le_antisymm ?_ hle
  have hspan := UpperTheory.V.AlgebraTools.mvPowerSeries_span_monomials Λ σ (fun s => l ^ e s) w hwm
  let ψ := Ideal.Quotient.liftₐ I φ hIφ
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk I x, rfl⟩
  let v := fun α : ((s : σ) → Fin (l ^ e s)) => Ideal.Quotient.mk I (∏ s, MvPowerSeries.X s ^ (α s : ℕ))
  have hg : Function.Surjective (Fintype.linearCombination Λ v) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hspan
  let eqv : ((s : σ) → Fin (l ^ e s)) ≃ (∀ s, Multiplicative (ZMod (l ^ e s))) :=
    Equiv.piCongrRight fun s => (ZMod.finEquiv (l ^ e s)).toEquiv.trans Multiplicative.ofAdd
  let E : MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s))) ≃ₗ[Λ] (((s : σ) → Fin (l ^ e s)) → Λ) :=
    (MonoidAlgebra.coeffLinearEquiv Λ).trans
      ((Finsupp.linearEquivFunOnFinite Λ Λ _).trans (LinearEquiv.funCongrLeft Λ Λ eqv))
  have hinj := inj_of_sandwich (Fintype.linearCombination Λ v) ψ.toLinearMap E hg hψs
  intro x hx
  have h0 : ψ (Ideal.Quotient.mk I x) = 0 := hx
  have : Ideal.Quotient.mk I x = 0 := hinj (by simpa using h0)
  exact Ideal.Quotient.eq_zero_iff_mem.mp this
end
